use roaring::RoaringBitmap;

use super::condition_docids_cache::ComputedCondition;
use super::{DeadEndsCache, RankingRuleGraph, RankingRuleGraphTrait};
use crate::search::new::interner::{DedupInterner, Interned, MappedInterner};
use crate::search::new::logger::SearchLogger;
use crate::search::new::query_graph::QueryNodeData;
use crate::search::new::query_term::{
    DerivationsSubset, LocatedQueryTermSubset, NumberOfTypos, QueryTerm, QueryTermSubset,
};
use crate::search::new::resolve_query_graph::compute_query_term_subset_docids;
use crate::search::new::{QueryGraph, QueryNode, SearchContext};
use crate::Result;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TypoCondition {
    original_term: Interned<QueryTerm>,
    nbr_typos: NumberOfTypos,
    subset: DerivationsSubset,
}

pub enum TypoGraph {}

impl RankingRuleGraphTrait for TypoGraph {
    type Condition = TypoCondition;

    fn resolve_condition<'db_cache>(
        ctx: &mut SearchContext,
        condition: &Self::Condition,
        universe: &RoaringBitmap,
    ) -> Result<ComputedCondition> {
        let TypoCondition { original_term, nbr_typos, subset } = condition;

        let mut term_subset = QueryTermSubset {
            original: *original_term,
            zero_typo_subset: DerivationsSubset::Nothing,
            one_typo_subset: DerivationsSubset::Nothing,
            two_typo_subset: DerivationsSubset::Nothing,
        };
        match nbr_typos {
            NumberOfTypos::Zero => term_subset.zero_typo_subset = subset.clone(),
            NumberOfTypos::One => term_subset.one_typo_subset = subset.clone(),
            NumberOfTypos::Two => term_subset.two_typo_subset = subset.clone(),
        }

        // maybe compute_query_term_subset_docids should accept a universe as argument
        let mut docids = compute_query_term_subset_docids(ctx, &term_subset)?;
        docids &= universe;

        Ok(ComputedCondition {
            docids,
            universe_len: universe.len(),
            from_subset: DerivationsSubset::Nothing,
            to_subset: subset.clone(),
        })
    }

    fn build_edges(
        ctx: &mut SearchContext,
        conditions_interner: &mut DedupInterner<Self::Condition>,
        _from_node: &QueryNode,
        to_node: &QueryNode,
    ) -> Result<Vec<(u8, Option<Interned<Self::Condition>>)>> {
        match &to_node.data {
            QueryNodeData::Term(LocatedQueryTermSubset { term_subset, positions }) => {
                let original_full_term = ctx.term_interner.get(term_subset.original);

                let mut edges = vec![];
                // Ngrams have a base typo cost
                // 2-gram -> equivalent to 1 typo
                // 3-gram -> equivalent to 2 typos
                let base_cost = positions.len().min(3) as u8;

                for nbr_typos in 0..=original_full_term.max_nbr_typos {
                    let (subset, nbr_typos) = match nbr_typos {
                        0 => (&term_subset.zero_typo_subset, NumberOfTypos::Zero),
                        1 => (&term_subset.one_typo_subset, NumberOfTypos::One),
                        2 => (&term_subset.two_typo_subset, NumberOfTypos::Two),
                        _ => panic!(),
                    };
                    if matches!(subset, DerivationsSubset::Nothing) {
                        continue;
                    }
                    edges.push((
                        nbr_typos as u8 + base_cost,
                        Some(conditions_interner.insert(TypoCondition {
                            original_term: term_subset.original,
                            nbr_typos,
                            subset: subset.clone(),
                        })),
                    ));
                }
                Ok(edges)
            }
            QueryNodeData::End => Ok(vec![(0, None)]),
            QueryNodeData::Deleted | QueryNodeData::Start => panic!(),
        }
    }

    fn log_state(
        graph: &RankingRuleGraph<Self>,
        paths: &[Vec<Interned<TypoCondition>>],
        dead_ends_cache: &DeadEndsCache<TypoCondition>,
        universe: &RoaringBitmap,
        distances: &MappedInterner<QueryNode, Vec<u64>>,
        cost: u64,
        logger: &mut dyn SearchLogger<QueryGraph>,
    ) {
        logger.log_typo_state(graph, paths, dead_ends_cache, universe, distances, cost);
    }

    fn label_for_condition(ctx: &mut SearchContext, condition: &Self::Condition) -> Result<String> {
        let TypoCondition { original_term, nbr_typos, subset: _ } = condition;
        let original_term = ctx.term_interner.get(*original_term);
        let original = ctx.word_interner.get(original_term.original);

        Ok(format!("{original}: {nbr_typos:?}"))
    }
}
