use std::future::{ready, Ready};

use actix_web::http::header;
use actix_web::HttpResponse;
use actix_web::{
    dev::{self, Service, ServiceRequest, ServiceResponse, Transform},
    Error,
};
use futures_util::future::LocalBoxFuture;
use lazy_static::lazy_static;
use meilisearch_auth::actions;
use meilisearch_lib::MeiliSearch;
use meilisearch_types::error::ResponseError;
use prometheus::{
    opts, register_histogram_vec, register_int_counter_vec, register_int_gauge,
    register_int_gauge_vec, Encoder, HistogramVec, IntGauge, IntGaugeVec, TextEncoder,
};
use prometheus::{HistogramTimer, IntCounterVec};
use tokio::task::spawn_blocking;

use crate::extractors::authentication::policies::ActionPolicy;
use crate::extractors::authentication::GuardedData;

fn create_buckets<const N: usize>() -> [f64; N] {
    let mut array = [0.0; N];

    for i in 0..N {
        array[i] = ((i + 1) as f64) / N as f64;
    }

    array
}

lazy_static! {
    pub static ref HTTP_RESPONSE_TIME_CUSTOM_BUCKETS: [f64; 20] = create_buckets();
    pub static ref HTTP_REQUESTS_TOTAL: IntCounterVec = register_int_counter_vec!(
        opts!("http_requests_total", "HTTP requests total"),
        &["method", "path"]
    )
    .expect("Can't create a metric");
    pub static ref MEILISEARCH_ON_DISK_SIZE: IntGauge = register_int_gauge!(opts!(
        "meilisearch_on_disk_size",
        "Meilisearch On Disk Size"
    ))
    .expect("Can't create a metric");
    pub static ref MEILISEARCH_DB_SIZE: IntGauge =
        register_int_gauge!(opts!("meilisearch_db_size", "Meilisearch DB Size"))
            .expect("Can't create a metric");
    pub static ref MEILISEARCH_INDEX_DB_SIZE: IntGaugeVec = register_int_gauge_vec!(
        opts!("meilisearch_index_db_size", "Meilisearch Index DB Size"),
        &["index"]
    )
    .expect("Can't create a metric");
    pub static ref MEILISEARCH_INDEX_ON_DISK_SIZE: IntGaugeVec = register_int_gauge_vec!(
        opts!(
            "meilisearch_index_on_disk_size",
            "Meilisearch Index On Disk Size"
        ),
        &["index"]
    )
    .expect("Can't create a metric");
    pub static ref MEILISEARCH_INDEX_COUNT: IntGauge =
        register_int_gauge!(opts!("meilisearch_index_count", "Meilisearch Index Count"),)
            .expect("Can't create a metric");
    pub static ref MEILISEARCH_INDEX_DOCS_COUNT: IntGaugeVec = register_int_gauge_vec!(
        opts!(
            "meilisearch_index_docs_count",
            "Meilisearch Index Docs Count"
        ),
        &["index"]
    )
    .expect("Can't create a metric");
    pub static ref HTTP_RESPONSE_TIME_SECONDS: HistogramVec = register_histogram_vec!(
        "http_response_time_seconds",
        "HTTP response times",
        &["method", "path"],
        HTTP_RESPONSE_TIME_CUSTOM_BUCKETS.to_vec()
    )
    .expect("Can't create a metric");
}

pub async fn get_metrics(
    meilisearch: GuardedData<ActionPolicy<{ actions::METRICS_GET }>, MeiliSearch>,
) -> Result<HttpResponse, ResponseError> {
    let indexes = meilisearch.index_resolver.list().await?;

    MEILISEARCH_INDEX_COUNT.set(indexes.len() as i64);

    let (mut total_used_size, mut total_on_disk_size) = (0, 0);
    // TODO: TAMO: unwrap
    for (index_uid, index) in indexes {
        let rtxn = index.read_txn().unwrap();
        let number_of_documents = index.number_of_documents(&rtxn).unwrap();
        drop(rtxn);

        let (used_size, on_disk_size) =
            spawn_blocking::<_, _>(move || (index.used_size(), index.on_disk_size()))
                .await
                .unwrap();

        let (used_size, on_disk_size) = (used_size.unwrap(), on_disk_size.unwrap());

        MEILISEARCH_INDEX_DOCS_COUNT
            .with_label_values(&[&index_uid])
            .set(number_of_documents as i64);
        MEILISEARCH_INDEX_DB_SIZE
            .with_label_values(&[&index_uid])
            .set(used_size as i64);
        MEILISEARCH_INDEX_ON_DISK_SIZE
            .with_label_values(&[&index_uid])
            .set(on_disk_size as i64);

        total_used_size += used_size;
        total_on_disk_size += on_disk_size;
    }

    total_used_size += meilisearch.task_store.used_size().await?;
    total_on_disk_size += meilisearch.task_store.on_disk_size().await?;
    total_on_disk_size += meilisearch
        .update_file_store
        .get_total_size()
        .await
        .unwrap();

    MEILISEARCH_ON_DISK_SIZE.set(total_on_disk_size as i64);
    MEILISEARCH_DB_SIZE.set(total_used_size as i64);

    let encoder = TextEncoder::new();
    let mut buffer = vec![];
    encoder
        .encode(&prometheus::gather(), &mut buffer)
        .expect("Failed to encode metrics");

    Ok(HttpResponse::Ok()
        .insert_header(header::ContentType(mime::TEXT_PLAIN))
        .body(buffer))
}

pub struct RouteMetrics;

// Middleware factory is `Transform` trait from actix-service crate
// `S` - type of the next service
// `B` - type of response's body
impl<S, B> Transform<S, ServiceRequest> for RouteMetrics
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = RouteMetricsMiddleware<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(RouteMetricsMiddleware { service }))
    }
}

pub struct RouteMetricsMiddleware<S> {
    service: S,
}

impl<S, B> Service<ServiceRequest> for RouteMetricsMiddleware<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = LocalBoxFuture<'static, Result<Self::Response, Self::Error>>;

    dev::forward_ready!(service);

    fn call(&self, req: ServiceRequest) -> Self::Future {
        let mut histogram_timer: Option<HistogramTimer> = None;
        let request_path = req.path();
        let is_registered_resource = req.resource_map().has_resource(request_path);
        if is_registered_resource {
            let request_method = req.method().to_string();
            histogram_timer = Some(
                HTTP_RESPONSE_TIME_SECONDS
                    .with_label_values(&[&request_method, request_path])
                    .start_timer(),
            );
            HTTP_REQUESTS_TOTAL
                .with_label_values(&[&request_method, request_path])
                .inc();
        }

        let fut = self.service.call(req);

        Box::pin(async move {
            let res = fut.await?;

            if let Some(histogram_timer) = histogram_timer {
                histogram_timer.observe_duration();
            };
            Ok(res)
        })
    }
}
