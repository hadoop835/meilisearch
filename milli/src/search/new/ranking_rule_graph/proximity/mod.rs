pub mod build;
pub mod compute_docids;

use roaring::RoaringBitmap;

use super::condition_docids_cache::ComputedCondition;
use super::{DeadEndsCache, RankingRuleGraph, RankingRuleGraphTrait};
use crate::search::new::interner::{DedupInterner, Interned, MappedInterner};
use crate::search::new::logger::SearchLogger;
use crate::search::new::query_term::QueryTermSubset;
use crate::search::new::{QueryGraph, QueryNode, SearchContext};
use crate::Result;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ProximityCondition {
    Uninit {
        left_term: QueryTermSubset,
        right_term: QueryTermSubset,
        right_term_ngram_len: u8,
        cost: u8,
    },
    Term {
        term: QueryTermSubset,
    },
}

pub enum ProximityGraph {}

impl RankingRuleGraphTrait for ProximityGraph {
    type Condition = ProximityCondition;

    fn resolve_condition(
        ctx: &mut SearchContext,
        condition: &Self::Condition,
        universe: &RoaringBitmap,
    ) -> Result<ComputedCondition> {
        compute_docids::compute_docids(ctx, condition, universe)
    }

    fn build_edges(
        ctx: &mut SearchContext,
        conditions_interner: &mut DedupInterner<Self::Condition>,
        source_node: &QueryNode,
        dest_node: &QueryNode,
    ) -> Result<Vec<(u8, Option<Interned<Self::Condition>>)>> {
        build::build_edges(ctx, conditions_interner, source_node, dest_node)
    }

    fn log_state(
        graph: &RankingRuleGraph<Self>,
        paths: &[Vec<Interned<ProximityCondition>>],
        dead_ends_cache: &DeadEndsCache<Self::Condition>,
        universe: &RoaringBitmap,
        distances: &MappedInterner<QueryNode, Vec<u64>>,
        cost: u64,
        logger: &mut dyn SearchLogger<QueryGraph>,
    ) {
        logger.log_proximity_state(graph, paths, dead_ends_cache, universe, distances, cost);
    }

    fn label_for_condition(ctx: &mut SearchContext, condition: &Self::Condition) -> Result<String> {
        match condition {
            ProximityCondition::Uninit { cost, .. } => {
                //  TODO
                Ok(format!("{cost}: cost"))
            }
            ProximityCondition::Term { term } => {
                let original_term = ctx.term_interner.get(term.original);
                let original_word = ctx.word_interner.get(original_term.original);
                Ok(format!("{original_word} : exists"))
            }
        }
    }
}
