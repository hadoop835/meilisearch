use fxhash::FxHashSet;
use roaring::RoaringBitmap;

use super::{DeadEndsCache, RankingRuleGraph, RankingRuleGraphTrait};
use crate::search::new::interner::{DedupInterner, Interned, MappedInterner};
use crate::search::new::logger::SearchLogger;
use crate::search::new::query_graph::QueryNodeData;
use crate::search::new::query_term::{
    LocatedQueryTerm, OneTypoSubTerm, Phrase, QueryTerm, TwoTypoSubTerm, ZeroTypoSubTerm, NumberOfTypos,
};
use crate::search::new::{QueryGraph, QueryNode, SearchContext};
use crate::Result;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TypoCondition {
    full_term: Interned<QueryTerm>,
    nbr_typos: NumberOfTypos,
}

pub enum TypoGraph {}

impl RankingRuleGraphTrait for TypoGraph {
    type Condition = TypoCondition;

    fn resolve_condition<'db_cache>(
        ctx: &mut SearchContext,
        condition: &Self::Condition,
        universe: &RoaringBitmap,
        // TODO: return type could be a Cow of roaring bitmap
    ) -> Result<(RoaringBitmap, FxHashSet<Interned<String>>, FxHashSet<Interned<Phrase>>)> {
        let SearchContext {
            index,
            txn,
            db_cache,
            word_interner,
            phrase_interner,
            term_interner,
            term_docids,
            zero_typo_subterm_interner,
            one_typo_subterm_interner,
            two_typo_subterm_interner,
        } = ctx;
        let TypoCondition { full_term, nbr_typos } = condition;
        let full_term = term_interner.get_mut(*full_term);
        let (subterm_docids, used_words, used_phrases) = match nbr_typos {
            NumberOfTypos::Zero => {
                let docids = term_docids.get_zero_typo_term_docids(
                    index,
                    txn,
                    db_cache,
                    zero_typo_subterm_interner,
                    word_interner,
                    phrase_interner,
                    full_term.zero_typo,
                )?;
                let ZeroTypoSubTerm { phrase, zero_typo, prefix_of, synonyms, use_prefix_db } =
                    zero_typo_subterm_interner.get(full_term.zero_typo);
                let used_words = zero_typo
                    .iter()
                    .chain(prefix_of.iter())
                    .chain(use_prefix_db.iter())
                    .copied()
                    .collect();
                let used_phrases = phrase.iter().chain(synonyms.iter()).copied().collect();
                (docids, used_words, used_phrases)
            }
            NumberOfTypos::One => {
                let one_typo = if let Some(one_typo) = full_term.one_typo {
                    one_typo
                } else {
                    todo!();
                };
                let docids = term_docids.get_one_typo_term_docids(
                    index,
                    txn,
                    db_cache,
                    one_typo_subterm_interner,
                    word_interner,
                    phrase_interner,
                    one_typo,
                )?;
                let OneTypoSubTerm { split_words, one_typo } =
                    one_typo_subterm_interner.get(one_typo);

                let used_words = one_typo.iter().copied().collect();
                let used_phrases = split_words.iter().copied().collect();
                (docids, used_words, used_phrases)
            }
            NumberOfTypos::Two => {
                let two_typo = if let Some(two_typo) = full_term.two_typo {
                    two_typo
                } else {
                    todo!();
                };
                let docids = term_docids.get_two_typo_term_docids(
                    index,
                    txn,
                    db_cache,
                    two_typo_subterm_interner,
                    word_interner,
                    two_typo,
                )?;
                let TwoTypoSubTerm { two_typos } = two_typo_subterm_interner.get(two_typo);
                let used_words = two_typos.iter().copied().collect();
                (docids, used_words, FxHashSet::default())
            }
        };

        Ok((universe & subterm_docids, used_words, used_phrases))
    }

    fn build_edges(
        _ctx: &mut SearchContext,
        conditions_interner: &mut DedupInterner<Self::Condition>,
        _from_node: &QueryNode,
        to_node: &QueryNode,
    ) -> Result<Vec<(u8, Option<Interned<Self::Condition>>)>> {
        match &to_node.data {
            QueryNodeData::Term(LocatedQueryTerm { value, positions }) => {
                let mut edges = vec![];
                // Ngrams have a base typo cost
                // 2-gram -> equivalent to 1 typo
                // 3-gram -> equivalent to 2 typos

                // TODO: a term should have a max_nbr_typo field?
                let base_cost = positions.len().min(2) as u8;

                for nbr_typos in 0..=2 {
                    let nbr_typos = match nbr_typos {
                        0 => NumberOfTypos::Zero,
                        1 => NumberOfTypos::One,
                        2 => NumberOfTypos::Two,
                        _ => panic!(),
                    };
                    edges.push((
                        nbr_typos as u8 + base_cost,
                        Some(
                            conditions_interner
                                .insert(TypoCondition { full_term: *value, nbr_typos }),
                        ),
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
        let TypoCondition { full_term, nbr_typos } = condition;
        let full_term = ctx.term_interner.get(*full_term);
        let original = ctx.word_interner.get(full_term.original);
        Ok(format!("{original} : {nbr_typos:?}"))
    }
}
