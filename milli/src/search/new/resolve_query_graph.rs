#![allow(clippy::too_many_arguments)]

use std::collections::VecDeque;

use fxhash::FxHashMap;
use heed::{BytesDecode, RoTxn};
use roaring::RoaringBitmap;

use super::db_cache::DatabaseCache;
use super::interner::{DedupInterner, Interned};
use super::query_graph::QueryNodeData;
use super::query_term::{
    Lazy, OneTypoSubTerm, Phrase, QueryTermSubset, TwoTypoSubTerm, ZeroTypoSubTerm,
};
use super::small_bitmap::SmallBitmap;
use super::{QueryGraph, SearchContext};
use crate::search::new::query_term::LocatedQueryTermSubset;
use crate::{CboRoaringBitmapCodec, Index, Result, RoaringBitmapCodec};

#[derive(Default)]
pub struct QueryTermDocIdsCache {
    pub phrases: FxHashMap<Interned<Phrase>, RoaringBitmap>,
}
impl QueryTermDocIdsCache {
    /// Get the document ids associated with the given phrase
    pub fn get_phrase_docids<'s, 'ctx>(
        &'s mut self,
        index: &Index,
        txn: &'ctx RoTxn,
        db_cache: &mut DatabaseCache<'ctx>,
        word_interner: &DedupInterner<String>,
        phrase_interner: &DedupInterner<Phrase>,
        phrase: Interned<Phrase>,
    ) -> Result<&'s RoaringBitmap> {
        if self.phrases.contains_key(&phrase) {
            return Ok(&self.phrases[&phrase]);
        };
        let docids = resolve_phrase(index, txn, db_cache, word_interner, phrase_interner, phrase)?;
        let _ = self.phrases.insert(phrase, docids);
        let docids = &self.phrases[&phrase];
        Ok(docids)
    }
}
pub fn compute_query_term_subset_docids(
    ctx: &mut SearchContext,
    term: &QueryTermSubset,
) -> Result<RoaringBitmap> {
    let SearchContext {
        index,
        txn,
        db_cache,
        word_interner,
        phrase_interner,
        term_interner,
        term_docids,
    } = ctx;
    let full_term = term_interner.get_mut(term.original);
    let mut docids = RoaringBitmap::new();

    // The order is important
    if !term.two_typo_subset.is_empty() && full_term.two_typo.is_uninit() {
        full_term.compute_fully_if_needed(index, txn, word_interner, phrase_interner)?;
        assert!(full_term.one_typo.is_init());
        assert!(full_term.two_typo.is_init());
    } else if !term.one_typo_subset.is_empty() && full_term.one_typo.is_uninit() {
        // TODO: do less work than this here!
        full_term.compute_fully_if_needed(index, txn, word_interner, phrase_interner)?;
        assert!(full_term.one_typo.is_init());
    }

    if !term.zero_typo_subset.is_empty() {
        let ZeroTypoSubTerm { phrase, zero_typo, prefix_of, synonyms, use_prefix_db } =
            &full_term.zero_typo;
        for word in zero_typo.iter().chain(prefix_of.iter()) {
            if let Some(word_docids) = db_cache.get_word_docids(index, txn, word_interner, *word)? {
                docids |=
                    RoaringBitmapCodec::bytes_decode(word_docids).ok_or(heed::Error::Decoding)?;
            }
        }
        for phrase in phrase.iter().chain(synonyms.iter()) {
            docids |= term_docids.get_phrase_docids(
                index,
                txn,
                db_cache,
                word_interner,
                phrase_interner,
                *phrase,
            )?;
        }

        if let Some(prefix) = use_prefix_db {
            if let Some(prefix_docids) =
                db_cache.get_word_prefix_docids(index, txn, word_interner, *prefix)?
            {
                docids |=
                    RoaringBitmapCodec::bytes_decode(prefix_docids).ok_or(heed::Error::Decoding)?;
            }
        }
    }

    if !term.one_typo_subset.is_empty() {
        let OneTypoSubTerm { split_words, one_typo } =
            if let Lazy::Init(t) = &full_term.one_typo { t } else { panic!() };
        for word in one_typo.iter() {
            if let Some(word_docids) = db_cache.get_word_docids(index, txn, word_interner, *word)? {
                docids |=
                    RoaringBitmapCodec::bytes_decode(word_docids).ok_or(heed::Error::Decoding)?;
            }
        }
        for phrase in split_words.iter() {
            docids |= term_docids.get_phrase_docids(
                index,
                txn,
                db_cache,
                word_interner,
                phrase_interner,
                *phrase,
            )?;
        }
    }
    if !term.two_typo_subset.is_empty() {
        let TwoTypoSubTerm { two_typos } = if let Lazy::Init(t) = &full_term.two_typo {
            t
        } else {
            panic!();
        };

        for word in two_typos.iter() {
            if let Some(word_docids) = db_cache.get_word_docids(index, txn, word_interner, *word)? {
                docids |=
                    RoaringBitmapCodec::bytes_decode(word_docids).ok_or(heed::Error::Decoding)?;
            }
        }
    }

    Ok(docids)
}

pub fn resolve_query_graph(
    ctx: &mut SearchContext,
    q: &QueryGraph,
    universe: &RoaringBitmap,
) -> Result<RoaringBitmap> {
    // TODO: there must be a faster way to compute this big
    // roaring bitmap expression

    let mut nodes_resolved = SmallBitmap::for_interned_values_in(&q.nodes);
    let mut path_nodes_docids = q.nodes.map(|_| RoaringBitmap::new());

    let mut next_nodes_to_visit = VecDeque::new();
    next_nodes_to_visit.push_back(q.root_node);

    while let Some(node_id) = next_nodes_to_visit.pop_front() {
        let node = q.nodes.get(node_id);
        let predecessors = &node.predecessors;
        if !predecessors.is_subset(&nodes_resolved) {
            next_nodes_to_visit.push_back(node_id);
            continue;
        }
        // Take union of all predecessors
        let mut predecessors_docids = RoaringBitmap::new();
        for p in predecessors.iter() {
            predecessors_docids |= path_nodes_docids.get(p);
        }

        let node_docids = match &node.data {
            QueryNodeData::Term(LocatedQueryTermSubset { term_subset, positions: _ }) => {
                let term_docids = compute_query_term_subset_docids(ctx, term_subset)?;
                predecessors_docids & term_docids
            }
            QueryNodeData::Deleted => {
                panic!()
            }
            QueryNodeData::Start => universe.clone(),
            QueryNodeData::End => {
                return Ok(predecessors_docids);
            }
        };
        nodes_resolved.insert(node_id);
        *path_nodes_docids.get_mut(node_id) = node_docids;

        for succ in node.successors.iter() {
            if !next_nodes_to_visit.contains(&succ) && !nodes_resolved.contains(succ) {
                next_nodes_to_visit.push_back(succ);
            }
        }

        for prec in node.predecessors.iter() {
            if q.nodes.get(prec).successors.is_subset(&nodes_resolved) {
                path_nodes_docids.get_mut(prec).clear();
            }
        }
    }
    panic!()
}

pub fn resolve_phrase<'ctx>(
    index: &Index,
    txn: &'ctx RoTxn,
    db_cache: &mut DatabaseCache<'ctx>,
    word_interner: &DedupInterner<String>,
    phrase_interner: &DedupInterner<Phrase>,
    phrase: Interned<Phrase>,
) -> Result<RoaringBitmap> {
    let Phrase { words } = phrase_interner.get(phrase).clone();
    let mut candidates = RoaringBitmap::new();
    let mut first_iter = true;
    let winsize = words.len().min(3);

    if words.is_empty() {
        return Ok(candidates);
    }

    for win in words.windows(winsize) {
        // Get all the documents with the matching distance for each word pairs.
        let mut bitmaps = Vec::with_capacity(winsize.pow(2));
        for (offset, &s1) in win
            .iter()
            .enumerate()
            .filter_map(|(index, word)| word.as_ref().map(|word| (index, word)))
        {
            for (dist, &s2) in win
                .iter()
                .skip(offset + 1)
                .enumerate()
                .filter_map(|(index, word)| word.as_ref().map(|word| (index, word)))
            {
                if dist == 0 {
                    match db_cache.get_word_pair_proximity_docids(
                        index,
                        txn,
                        word_interner,
                        s1,
                        s2,
                        1,
                    )? {
                        Some(m) => bitmaps.push(CboRoaringBitmapCodec::deserialize_from(m)?),
                        // If there are no documents for this pair, there will be no
                        // results for the phrase query.
                        None => return Ok(RoaringBitmap::new()),
                    }
                } else {
                    let mut bitmap = RoaringBitmap::new();
                    for dist in 0..=dist {
                        if let Some(m) = db_cache.get_word_pair_proximity_docids(
                            index,
                            txn,
                            word_interner,
                            s1,
                            s2,
                            dist as u8 + 1,
                        )? {
                            bitmap |= CboRoaringBitmapCodec::deserialize_from(m)?;
                        }
                    }
                    if bitmap.is_empty() {
                        return Ok(bitmap);
                    } else {
                        bitmaps.push(bitmap);
                    }
                }
            }
        }

        // We sort the bitmaps so that we perform the small intersections first, which is faster.
        bitmaps.sort_unstable_by_key(|a| a.len());

        for bitmap in bitmaps {
            if first_iter {
                candidates = bitmap;
                first_iter = false;
            } else {
                candidates &= bitmap;
            }
            // There will be no match, return early
            if candidates.is_empty() {
                break;
            }
        }
    }
    Ok(candidates)
}
