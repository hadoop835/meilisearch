use std::io::ErrorKind;

use actix_web::http::header::CONTENT_TYPE;
use actix_web::web::Data;
use actix_web::{web, HttpMessage, HttpRequest, HttpResponse};
use bstr::ByteSlice;
use deserr::actix_web::AwebQueryParameter;
use deserr::Deserr;
use futures::StreamExt;
use index_scheduler::IndexScheduler;
use log::debug;
use meilisearch_types::deserr::query_params::Param;
use meilisearch_types::deserr::DeserrQueryParamError;
use meilisearch_types::document_formats::{read_csv, read_json, read_ndjson, PayloadType};
use meilisearch_types::error::deserr_codes::*;
use meilisearch_types::error::{Code, ResponseError};
use meilisearch_types::heed::RoTxn;
use meilisearch_types::index_uid::IndexUid;
use meilisearch_types::milli::update::IndexDocumentsMethod;
use meilisearch_types::milli::InternalError;
use meilisearch_types::star_or::OptionStarOrList;
use meilisearch_types::tasks::KindWithContent;
use meilisearch_types::{milli, Document, Index};
use mime::Mime;
use once_cell::sync::Lazy;
use serde::Deserialize;
use serde_json::Value;
use tempfile::tempfile;
use tokio::fs::File;
use tokio::io::{AsyncSeekExt, AsyncWriteExt, BufWriter};

use crate::analytics::{Analytics, DocumentDeletionKind};
use crate::error::MeilisearchHttpError;
use crate::error::PayloadError::ReceivePayload;
use crate::extractors::authentication::policies::*;
use crate::extractors::authentication::GuardedData;
use crate::extractors::payload::Payload;
use crate::extractors::sequential_extractor::SeqHandler;
use crate::routes::{PaginationView, SummarizedTaskView, PAGINATION_DEFAULT_LIMIT};

static ACCEPTED_CONTENT_TYPE: Lazy<Vec<String>> = Lazy::new(|| {
    vec!["application/json".to_string(), "application/x-ndjson".to_string(), "text/csv".to_string()]
});

/// Extracts the mime type from the content type and return
/// a meilisearch error if anything bad happen.
fn extract_mime_type(req: &HttpRequest) -> Result<Option<Mime>, MeilisearchHttpError> {
    match req.mime_type() {
        Ok(Some(mime)) => Ok(Some(mime)),
        Ok(None) => Ok(None),
        Err(_) => match req.headers().get(CONTENT_TYPE) {
            Some(content_type) => Err(MeilisearchHttpError::InvalidContentType(
                content_type.as_bytes().as_bstr().to_string(),
                ACCEPTED_CONTENT_TYPE.clone(),
            )),
            None => Err(MeilisearchHttpError::MissingContentType(ACCEPTED_CONTENT_TYPE.clone())),
        },
    }
}

#[derive(Deserialize)]
pub struct DocumentParam {
    index_uid: String,
    document_id: String,
}

pub fn configure(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::resource("")
            .route(web::get().to(SeqHandler(get_all_documents)))
            .route(web::post().to(SeqHandler(replace_documents)))
            .route(web::put().to(SeqHandler(update_documents)))
            .route(web::delete().to(SeqHandler(clear_all_documents))),
    )
    // this route needs to be before the /documents/{document_id} to match properly
    .service(web::resource("/delete-batch").route(web::post().to(SeqHandler(delete_documents))))
    .service(
        web::resource("/{document_id}")
            .route(web::get().to(SeqHandler(get_document)))
            .route(web::delete().to(SeqHandler(delete_document))),
    );
}

#[derive(Debug, Deserr)]
#[deserr(error = DeserrQueryParamError, rename_all = camelCase, deny_unknown_fields)]
pub struct GetDocument {
    #[deserr(default, error = DeserrQueryParamError<InvalidDocumentFields>)]
    fields: OptionStarOrList<String>,
}

pub async fn get_document(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_GET }>, Data<IndexScheduler>>,
    document_param: web::Path<DocumentParam>,
    params: AwebQueryParameter<GetDocument, DeserrQueryParamError>,
) -> Result<HttpResponse, ResponseError> {
    let DocumentParam { index_uid, document_id } = document_param.into_inner();
    let index_uid = IndexUid::try_from(index_uid)?;

    let GetDocument { fields } = params.into_inner();
    let attributes_to_retrieve = fields.merge_star_and_none();

    let index = index_scheduler.index(&index_uid)?;
    let document = retrieve_document(&index, &document_id, attributes_to_retrieve)?;
    debug!("returns: {:?}", document);
    Ok(HttpResponse::Ok().json(document))
}

pub async fn delete_document(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_DELETE }>, Data<IndexScheduler>>,
    path: web::Path<DocumentParam>,
    req: HttpRequest,
    analytics: web::Data<dyn Analytics>,
) -> Result<HttpResponse, ResponseError> {
    let DocumentParam { index_uid, document_id } = path.into_inner();
    let index_uid = IndexUid::try_from(index_uid)?;

    analytics.delete_documents(DocumentDeletionKind::PerDocumentId, &req);

    let task = KindWithContent::DocumentDeletion {
        index_uid: index_uid.to_string(),
        documents_ids: vec![document_id],
    };
    let task: SummarizedTaskView =
        tokio::task::spawn_blocking(move || index_scheduler.register(task)).await??.into();
    debug!("returns: {:?}", task);
    Ok(HttpResponse::Accepted().json(task))
}

#[derive(Debug, Deserr)]
#[deserr(error = DeserrQueryParamError, rename_all = camelCase, deny_unknown_fields)]
pub struct BrowseQuery {
    #[deserr(default, error = DeserrQueryParamError<InvalidDocumentOffset>)]
    offset: Param<usize>,
    #[deserr(default = Param(PAGINATION_DEFAULT_LIMIT), error = DeserrQueryParamError<InvalidDocumentLimit>)]
    limit: Param<usize>,
    #[deserr(default, error = DeserrQueryParamError<InvalidDocumentFields>)]
    fields: OptionStarOrList<String>,
}

pub async fn get_all_documents(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_GET }>, Data<IndexScheduler>>,
    index_uid: web::Path<String>,
    params: AwebQueryParameter<BrowseQuery, DeserrQueryParamError>,
) -> Result<HttpResponse, ResponseError> {
    let index_uid = IndexUid::try_from(index_uid.into_inner())?;
    debug!("called with params: {:?}", params);
    let BrowseQuery { limit, offset, fields } = params.into_inner();
    let attributes_to_retrieve = fields.merge_star_and_none();

    let index = index_scheduler.index(&index_uid)?;
    let (total, documents) = retrieve_documents(&index, offset.0, limit.0, attributes_to_retrieve)?;

    let ret = PaginationView::new(offset.0, limit.0, total as usize, documents);

    debug!("returns: {:?}", ret);
    Ok(HttpResponse::Ok().json(ret))
}

#[derive(Deserialize, Debug, Deserr)]
#[deserr(error = DeserrQueryParamError, rename_all = camelCase, deny_unknown_fields)]
pub struct UpdateDocumentsQuery {
    #[deserr(default, error = DeserrQueryParamError<InvalidIndexPrimaryKey>)]
    pub primary_key: Option<String>,
    #[deserr(default, try_from(char) = from_char_csv_delimiter -> DeserrQueryParamError<InvalidDocumentCsvDelimiter>, error = DeserrQueryParamError<InvalidDocumentCsvDelimiter>)]
    pub csv_delimiter: Option<u8>,
}

fn from_char_csv_delimiter(
    c: char,
) -> Result<Option<u8>, DeserrQueryParamError<InvalidDocumentCsvDelimiter>> {
    if c.is_ascii() {
        Ok(Some(c as u8))
    } else {
        Err(DeserrQueryParamError::new(
            format!("csv delimiter must be an ascii character. Found: `{}`", c),
            Code::InvalidDocumentCsvDelimiter,
        ))
    }
}

pub async fn replace_documents(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_ADD }>, Data<IndexScheduler>>,
    index_uid: web::Path<String>,
    params: AwebQueryParameter<UpdateDocumentsQuery, DeserrQueryParamError>,
    body: Payload,
    req: HttpRequest,
    analytics: web::Data<dyn Analytics>,
) -> Result<HttpResponse, ResponseError> {
    let index_uid = IndexUid::try_from(index_uid.into_inner())?;

    debug!("called with params: {:?}", params);
    let params = params.into_inner();

    analytics.add_documents(&params, index_scheduler.index(&index_uid).is_err(), &req);

    let allow_index_creation = index_scheduler.filters().allow_index_creation(&index_uid);
    let task = document_addition(
        extract_mime_type(&req)?,
        index_scheduler,
        index_uid,
        params.primary_key,
        params.csv_delimiter,
        body,
        IndexDocumentsMethod::ReplaceDocuments,
        allow_index_creation,
    )
    .await?;

    Ok(HttpResponse::Accepted().json(task))
}

pub async fn update_documents(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_ADD }>, Data<IndexScheduler>>,
    index_uid: web::Path<String>,
    params: AwebQueryParameter<UpdateDocumentsQuery, DeserrQueryParamError>,
    body: Payload,
    req: HttpRequest,
    analytics: web::Data<dyn Analytics>,
) -> Result<HttpResponse, ResponseError> {
    let index_uid = IndexUid::try_from(index_uid.into_inner())?;

    debug!("called with params: {:?}", params);
    let params = params.into_inner();

    analytics.update_documents(&params, index_scheduler.index(&index_uid).is_err(), &req);

    let allow_index_creation = index_scheduler.filters().allow_index_creation(&index_uid);
    let task = document_addition(
        extract_mime_type(&req)?,
        index_scheduler,
        index_uid,
        params.primary_key,
        params.csv_delimiter,
        body,
        IndexDocumentsMethod::UpdateDocuments,
        allow_index_creation,
    )
    .await?;

    Ok(HttpResponse::Accepted().json(task))
}

#[allow(clippy::too_many_arguments)]
async fn document_addition(
    mime_type: Option<Mime>,
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_ADD }>, Data<IndexScheduler>>,
    index_uid: IndexUid,
    primary_key: Option<String>,
    csv_delimiter: Option<u8>,
    mut body: Payload,
    method: IndexDocumentsMethod,
    allow_index_creation: bool,
) -> Result<SummarizedTaskView, MeilisearchHttpError> {
    let format = match (
        mime_type.as_ref().map(|m| (m.type_().as_str(), m.subtype().as_str())),
        csv_delimiter,
    ) {
        (Some(("application", "json")), None) => PayloadType::Json,
        (Some(("application", "x-ndjson")), None) => PayloadType::Ndjson,
        (Some(("text", "csv")), None) => PayloadType::Csv { delimiter: b',' },
        (Some(("text", "csv")), Some(delimiter)) => PayloadType::Csv { delimiter },

        (Some(("application", "json")), Some(_)) => {
            return Err(MeilisearchHttpError::CsvDelimiterWithWrongContentType(String::from(
                "application/json",
            )))
        }
        (Some(("application", "x-ndjson")), Some(_)) => {
            return Err(MeilisearchHttpError::CsvDelimiterWithWrongContentType(String::from(
                "application/x-ndjson",
            )))
        }
        (Some((type_, subtype)), _) => {
            return Err(MeilisearchHttpError::InvalidContentType(
                format!("{}/{}", type_, subtype),
                ACCEPTED_CONTENT_TYPE.clone(),
            ))
        }
        (None, _) => {
            return Err(MeilisearchHttpError::MissingContentType(ACCEPTED_CONTENT_TYPE.clone()))
        }
    };

    let (uuid, mut update_file) = index_scheduler.create_update_file()?;

    let temp_file = match tempfile() {
        Ok(file) => file,
        Err(e) => return Err(MeilisearchHttpError::Payload(ReceivePayload(Box::new(e)))),
    };

    let async_file = File::from_std(temp_file);
    let mut buffer = BufWriter::new(async_file);

    let mut buffer_write_size: usize = 0;
    while let Some(result) = body.next().await {
        let byte = result?;

        if byte.is_empty() && buffer_write_size == 0 {
            return Err(MeilisearchHttpError::MissingPayload(format));
        }

        match buffer.write_all(&byte).await {
            Ok(()) => buffer_write_size += 1,
            Err(e) => return Err(MeilisearchHttpError::Payload(ReceivePayload(Box::new(e)))),
        }
    }

    if let Err(e) = buffer.flush().await {
        return Err(MeilisearchHttpError::Payload(ReceivePayload(Box::new(e))));
    }

    if buffer_write_size == 0 {
        return Err(MeilisearchHttpError::MissingPayload(format));
    }

    if let Err(e) = buffer.seek(std::io::SeekFrom::Start(0)).await {
        return Err(MeilisearchHttpError::Payload(ReceivePayload(Box::new(e))));
    }

    let read_file = buffer.into_inner().into_std().await;
    let documents_count = tokio::task::spawn_blocking(move || {
        let documents_count = match format {
            PayloadType::Json => read_json(&read_file, update_file.as_file_mut())?,
            PayloadType::Csv { delimiter } => {
                read_csv(&read_file, update_file.as_file_mut(), delimiter)?
            }
            PayloadType::Ndjson => read_ndjson(&read_file, update_file.as_file_mut())?,
        };
        // we NEED to persist the file here because we moved the `udpate_file` in another task.
        update_file.persist()?;
        Ok(documents_count)
    })
    .await;

    let documents_count = match documents_count {
        Ok(Ok(documents_count)) => documents_count,
        // in this case the file has not possibly be persisted.
        Ok(Err(e)) => return Err(e),
        Err(e) => {
            // Here the file MAY have been persisted or not.
            // We don't know thus we ignore the file not found error.
            match index_scheduler.delete_update_file(uuid) {
                Ok(()) => (),
                Err(index_scheduler::Error::FileStore(file_store::Error::IoError(e)))
                    if e.kind() == ErrorKind::NotFound => {}
                Err(e) => {
                    log::warn!("Unknown error happened while deleting a malformed update file with uuid {uuid}: {e}");
                }
            }
            // We still want to return the original error to the end user.
            return Err(e.into());
        }
    };

    let task = KindWithContent::DocumentAdditionOrUpdate {
        method,
        content_file: uuid,
        documents_count,
        primary_key,
        allow_index_creation,
        index_uid: index_uid.to_string(),
    };

    let scheduler = index_scheduler.clone();
    let task = match tokio::task::spawn_blocking(move || scheduler.register(task)).await? {
        Ok(task) => task,
        Err(e) => {
            index_scheduler.delete_update_file(uuid)?;
            return Err(e.into());
        }
    };

    debug!("returns: {:?}", task);
    Ok(task.into())
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum DocumentDeletionQuery {
    Ids(Vec<Value>),
    Object { filter: Option<Value> },
}

/// Parses a Json encoded document id and validate it, returning a user error when it is one.
/// FIXME: stolen from milli
fn validate_document_id_value(document_id: Value) -> String {
    match document_id {
        Value::String(string) => match validate_document_id(&string) {
            Some(s) if s.len() == string.len() => string,
            Some(s) => s.to_string(),
            None => panic!(),
        },
        Value::Number(number) if number.is_i64() => number.to_string(),
        _content => panic!(),
    }
}

/// FIXME: stolen from milli
fn validate_document_id(document_id: &str) -> Option<&str> {
    if !document_id.is_empty()
        && document_id.chars().all(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_'))
    {
        Some(document_id)
    } else {
        None
    }
}

pub async fn delete_documents(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_DELETE }>, Data<IndexScheduler>>,
    index_uid: web::Path<String>,
    body: web::Json<DocumentDeletionQuery>,
    req: HttpRequest,
    analytics: web::Data<dyn Analytics>,
) -> Result<HttpResponse, ResponseError> {
    debug!("called with params: {:?}", body);
    let index_uid = IndexUid::try_from(index_uid.into_inner())?;
    let index_uid = index_uid.into_inner();

    analytics.delete_documents(DocumentDeletionKind::PerBatch, &req);

    let ids = match body.into_inner() {
        DocumentDeletionQuery::Ids(body) => body
            .iter()
            .map(|v| v.as_str().map(String::from).unwrap_or_else(|| v.to_string()))
            .collect(),
        DocumentDeletionQuery::Object { filter } => {
            debug!("filter: {:?}", filter);

            // FIXME: spawn_blocking
            if let Some(ref filter) = filter {
                if let Some(facets) = crate::search::parse_filter(filter)? {
                    debug!("facets: {:?}", facets);

                    let index = index_scheduler.index(&index_uid)?;
                    let rtxn = index.read_txn()?;
                    let filtered_candidates = facets.evaluate(&rtxn, &index)?;
                    debug!("filtered_candidates.len(): {:?}", filtered_candidates.len());

                    // FIXME: unwraps
                    let primary_key = index.primary_key(&rtxn)?.unwrap();
                    let primary_key = index.fields_ids_map(&rtxn)?.id(primary_key).unwrap();

                    let documents = index.documents(&rtxn, filtered_candidates.into_iter())?;
                    debug!("documents.len(): {:?}", documents.len());
                    let documents: Vec<String> = documents
                        .into_iter()
                        .map(|(_, document)| {
                            let value = document.get(primary_key).unwrap();
                            let value: Value = serde_json::from_slice(value)
                                .map_err(InternalError::SerdeJson)
                                .unwrap();

                            validate_document_id_value(value)
                        })
                        .collect();
                    debug!("documents: {:?}", documents);
                    documents
                } else {
                    vec![]
                }
            } else {
                vec![]
            }
        }
    };

    let task =
        KindWithContent::DocumentDeletion { index_uid: index_uid.to_string(), documents_ids: ids };
    let task: SummarizedTaskView =
        tokio::task::spawn_blocking(move || index_scheduler.register(task)).await??.into();

    debug!("returns: {:?}", task);
    Ok(HttpResponse::Accepted().json(task))
}

pub async fn clear_all_documents(
    index_scheduler: GuardedData<ActionPolicy<{ actions::DOCUMENTS_DELETE }>, Data<IndexScheduler>>,
    index_uid: web::Path<String>,
    req: HttpRequest,
    analytics: web::Data<dyn Analytics>,
) -> Result<HttpResponse, ResponseError> {
    let index_uid = IndexUid::try_from(index_uid.into_inner())?;
    analytics.delete_documents(DocumentDeletionKind::ClearAll, &req);

    let task = KindWithContent::DocumentClear { index_uid: index_uid.to_string() };
    let task: SummarizedTaskView =
        tokio::task::spawn_blocking(move || index_scheduler.register(task)).await??.into();

    debug!("returns: {:?}", task);
    Ok(HttpResponse::Accepted().json(task))
}

fn all_documents<'a>(
    index: &Index,
    rtxn: &'a RoTxn,
) -> Result<impl Iterator<Item = Result<Document, ResponseError>> + 'a, ResponseError> {
    let fields_ids_map = index.fields_ids_map(rtxn)?;
    let all_fields: Vec<_> = fields_ids_map.iter().map(|(id, _)| id).collect();

    Ok(index.all_documents(rtxn)?.map(move |ret| {
        ret.map_err(ResponseError::from).and_then(|(_key, document)| -> Result<_, ResponseError> {
            Ok(milli::obkv_to_json(&all_fields, &fields_ids_map, document)?)
        })
    }))
}

fn retrieve_documents<S: AsRef<str>>(
    index: &Index,
    offset: usize,
    limit: usize,
    attributes_to_retrieve: Option<Vec<S>>,
) -> Result<(u64, Vec<Document>), ResponseError> {
    let rtxn = index.read_txn()?;

    let mut documents = Vec::new();
    for document in all_documents(index, &rtxn)?.skip(offset).take(limit) {
        let document = match &attributes_to_retrieve {
            Some(attributes_to_retrieve) => permissive_json_pointer::select_values(
                &document?,
                attributes_to_retrieve.iter().map(|s| s.as_ref()),
            ),
            None => document?,
        };
        documents.push(document);
    }

    let number_of_documents = index.number_of_documents(&rtxn)?;
    Ok((number_of_documents, documents))
}

fn retrieve_document<S: AsRef<str>>(
    index: &Index,
    doc_id: &str,
    attributes_to_retrieve: Option<Vec<S>>,
) -> Result<Document, ResponseError> {
    let txn = index.read_txn()?;

    let fields_ids_map = index.fields_ids_map(&txn)?;
    let all_fields: Vec<_> = fields_ids_map.iter().map(|(id, _)| id).collect();

    let internal_id = index
        .external_documents_ids(&txn)?
        .get(doc_id.as_bytes())
        .ok_or_else(|| MeilisearchHttpError::DocumentNotFound(doc_id.to_string()))?;

    let document = index
        .documents(&txn, std::iter::once(internal_id))?
        .into_iter()
        .next()
        .map(|(_, d)| d)
        .ok_or_else(|| MeilisearchHttpError::DocumentNotFound(doc_id.to_string()))?;

    let document = meilisearch_types::milli::obkv_to_json(&all_fields, &fields_ids_map, document)?;
    let document = match &attributes_to_retrieve {
        Some(attributes_to_retrieve) => permissive_json_pointer::select_values(
            &document,
            attributes_to_retrieve.iter().map(|s| s.as_ref()),
        ),
        None => document,
    };

    Ok(document)
}
