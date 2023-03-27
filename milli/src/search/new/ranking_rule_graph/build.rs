use super::{Edge, RankingRuleGraph, RankingRuleGraphTrait};
use crate::search::new::interner::{DedupInterner, Interned};
use crate::search::new::query_graph::QueryNode;
use crate::search::new::small_bitmap::SmallBitmap;
use crate::search::new::{QueryGraph, SearchContext};
use crate::Result;
use fxhash::FxHashMap;
use std::collections::HashSet;

impl<G: RankingRuleGraphTrait> RankingRuleGraph<G> {
    // TODO: here, the docids of all the edges should already be computed!
    // an edge condition would then be reduced to a (ptr to) a roaring bitmap?
    // we could build fewer of them by directly comparing them with the universe
    // (e.g. for each word pairs?) with `deserialize_within_universe` maybe
    //

    /// Build the ranking rule graph from the given query graph
    pub fn build(ctx: &mut SearchContext, query_graph: QueryGraph) -> Result<Self> {
        let QueryGraph { nodes: graph_nodes, .. } = &query_graph;

        let mut conditions_interner = DedupInterner::default();

        let mut edges_store = DedupInterner::default();
        let mut edges_of_node = query_graph.nodes.map(|_| HashSet::new());

        let mut from_nodes_of_condition =
            FxHashMap::<Interned<G::Condition>, SmallBitmap<QueryNode>>::default();
        let mut to_nodes_of_condition =
            FxHashMap::<Interned<G::Condition>, SmallBitmap<QueryNode>>::default();

        for (source_id, source_node) in graph_nodes.iter() {
            let new_edges = edges_of_node.get_mut(source_id);

            for dest_idx in source_node.successors.iter() {
                let dest_node = graph_nodes.get(dest_idx);
                let edges = G::build_edges(ctx, &mut conditions_interner, source_node, dest_node)?;
                if edges.is_empty() {
                    continue;
                }

                for (cost, condition) in edges {
                    let new_edge_id = edges_store.insert(Some(Edge {
                        source_node: source_id,
                        dest_node: dest_idx,
                        cost,
                        condition,
                    }));
                    if let Some(condition) = condition {
                        let from_nodes_of_condition = from_nodes_of_condition
                            .entry(condition)
                            .or_insert(SmallBitmap::for_interned_values_in(graph_nodes));
                        from_nodes_of_condition.insert(source_id);
                        let to_nodes_of_condition = to_nodes_of_condition
                            .entry(condition)
                            .or_insert(SmallBitmap::for_interned_values_in(graph_nodes));
                        to_nodes_of_condition.insert(dest_idx);
                    }
                    new_edges.insert(new_edge_id);
                }
            }
        }
        let edges_store = edges_store.freeze();
        let edges_of_node =
            edges_of_node.map(|edges| SmallBitmap::from_iter(edges.iter().copied(), &edges_store));

        let conditions_interner = conditions_interner.freeze();
        let from_nodes_of_condition = conditions_interner.map_indexes(|c| {
            from_nodes_of_condition
                .get(&c)
                .cloned()
                .unwrap_or(SmallBitmap::for_interned_values_in(graph_nodes))
        });
        let to_nodes_of_condition = conditions_interner.map_indexes(|c| {
            to_nodes_of_condition
                .get(&c)
                .cloned()
                .unwrap_or(SmallBitmap::for_interned_values_in(graph_nodes))
        });

        Ok(RankingRuleGraph {
            query_graph,
            edges_store,
            edges_of_node,
            conditions_interner,
            from_nodes_of_condition,
            to_nodes_of_condition,
        })
    }
}
