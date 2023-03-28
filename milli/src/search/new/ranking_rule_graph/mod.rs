/*! Module implementing the graph used for the graph-based ranking rules
and its related algorithms.

A ranking rule graph is built on top of the [`QueryGraph`]: the nodes stay
the same but the edges are replaced.
*/

mod build;
mod cheapest_paths;
mod condition_docids_cache;
mod dead_ends_cache;

/// Implementation of the `proximity` ranking rule
mod proximity;
/// Implementation of the `typo` ranking rule
mod typo;

use std::hash::Hash;

pub use condition_docids_cache::ConditionDocIdsCache;
pub use dead_ends_cache::DeadEndsCache;
pub use proximity::{ProximityCondition, ProximityGraph};
use roaring::RoaringBitmap;
pub use typo::{TypoCondition, TypoGraph};

use self::condition_docids_cache::ComputedCondition;

use super::interner::{DedupInterner, FixedSizeInterner, Interned, MappedInterner};
use super::logger::SearchLogger;
use super::small_bitmap::SmallBitmap;
use super::{QueryGraph, QueryNode, SearchContext};
use crate::Result;

/// An edge in the ranking rule graph.
///
/// It contains:
/// 1. The source and destination nodes
/// 2. The cost of traversing this edge
/// 3. The condition associated with it
#[derive(Clone)]
pub struct Edge<E> {
    pub source_node: Interned<QueryNode>,
    pub dest_node: Interned<QueryNode>,
    pub cost: u8,
    pub condition: Option<Interned<E>>,
}

impl<E> Hash for Edge<E> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.source_node.hash(state);
        self.dest_node.hash(state);
        self.cost.hash(state);
        self.condition.hash(state);
    }
}

impl<E> Eq for Edge<E> {}

impl<E> PartialEq for Edge<E> {
    fn eq(&self, other: &Self) -> bool {
        self.source_node == other.source_node
            && self.dest_node == other.dest_node
            && self.cost == other.cost
            && self.condition == other.condition
    }
}

/// A trait to be implemented by a marker type to build a graph-based ranking rule.
///
/// It mostly describes how to:
/// 1. Retrieve the set of edges (their cost and condition) between two nodes.
/// 2. Compute the document ids satisfying a condition
pub trait RankingRuleGraphTrait: Sized {
    type Condition: Sized + Clone + PartialEq + Eq + Hash;

    /// Return the label of the given edge condition, to be used when visualising
    /// the ranking rule graph.
    fn label_for_condition(ctx: &mut SearchContext, condition: &Self::Condition) -> Result<String>;

    /// Compute the document ids associated with the given edge condition,
    /// restricted to the given universe.
    fn resolve_condition(
        ctx: &mut SearchContext,
        condition: &Self::Condition,
        universe: &RoaringBitmap,
    ) -> Result<ComputedCondition>;

    /// Return the costs and conditions of the edges going from the source node to the destination node
    fn build_edges(
        ctx: &mut SearchContext,
        conditions_interner: &mut DedupInterner<Self::Condition>,
        source_node: &QueryNode,
        dest_node: &QueryNode,
    ) -> Result<Vec<(u8, Option<Interned<Self::Condition>>)>>;

    fn log_state(
        graph: &RankingRuleGraph<Self>,
        paths: &[Vec<Interned<Self::Condition>>],
        dead_ends_cache: &DeadEndsCache<Self::Condition>,
        universe: &RoaringBitmap,
        costs: &MappedInterner<QueryNode, Vec<u64>>,
        cost: u64,
        logger: &mut dyn SearchLogger<QueryGraph>,
    );
}

/// The graph used by graph-based ranking rules.
///
/// It is built on top of a [`QueryGraph`], keeping the same nodes
/// but replacing the edges.
pub struct RankingRuleGraph<G: RankingRuleGraphTrait> {
    pub query_graph: QueryGraph,
    pub edges_store: FixedSizeInterner<Option<Edge<G::Condition>>>,
    pub edges_of_node: MappedInterner<QueryNode, SmallBitmap<Option<Edge<G::Condition>>>>,
    pub conditions_interner: FixedSizeInterner<G::Condition>,
    pub from_nodes_of_condition: MappedInterner<G::Condition, SmallBitmap<QueryNode>>,
    pub to_nodes_of_condition: MappedInterner<G::Condition, SmallBitmap<QueryNode>>,
}
impl<G: RankingRuleGraphTrait> Clone for RankingRuleGraph<G> {
    fn clone(&self) -> Self {
        Self {
            query_graph: self.query_graph.clone(),
            edges_store: self.edges_store.clone(),
            edges_of_node: self.edges_of_node.clone(),
            conditions_interner: self.conditions_interner.clone(),
            from_nodes_of_condition: self.from_nodes_of_condition.clone(),
            to_nodes_of_condition: self.to_nodes_of_condition.clone(),
        }
    }
}
impl<G: RankingRuleGraphTrait> RankingRuleGraph<G> {
    /// Remove all edges with the given condition
    pub fn remove_edges_with_condition(&mut self, condition_to_remove: Interned<G::Condition>) {
        for (edge_id, edge_opt) in self.edges_store.iter_mut() {
            let Some(edge) = edge_opt.as_mut() else { continue };
            let Some(condition) = edge.condition else { continue };

            if condition == condition_to_remove {
                let (source_node, _dest_node) = (edge.source_node, edge.dest_node);
                *edge_opt = None;
                self.edges_of_node.get_mut(source_node).remove(edge_id);
            }
        }
    }
}
