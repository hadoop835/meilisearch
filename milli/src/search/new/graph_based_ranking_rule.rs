/*! Implementation of a generic graph-based ranking rule.

A graph-based ranking rule is a ranking rule that works by representing
its possible operations and their relevancy cost as a directed acyclic multi-graph
built on top of the query graph. It then computes its buckets by finding the
cheapest paths from the start node to the end node and computing the document ids
that satisfy those paths.

For example, the proximity ranking rule builds a graph where the edges between two
nodes represent a condition that the term of the source node is in a certain proximity
to the term of the destination node. With the query "pretty house by" where the term
"pretty" has three possible proximities to the term "house" and "house" has two
proximities to "by", the graph will look like this:

```txt
┌───────┐     ┌───────┐─────1────▶┌───────┐──1──▶┌─────┐    ┌───────┐
│ START │──0─▶│pretty │─────2────▶│ house │      │ by  │─0─▶│  END  │
└───────┘     └───────┘─────3────▶└───────┘──2-─▶└─────┘    └───────┘
```
The proximity ranking rule's first bucket will be determined by the union of all
the shortest paths from START to END, which in this case is:
```txt
START --0-> pretty --1--> house --1--> by --0--> end
```
The path's corresponding document ids are found by taking the intersection of the
document ids of each edge. That is, we find the documents where both `pretty` is
1-close to `house` AND `house` is 1-close to `by`.

For the second bucket, we get the union of the second-cheapest paths, which are:
```txt
START --0-> pretty --1--> house --2--> by --0--> end
START --0-> pretty --2--> house --1--> by --0--> end
```
That is we find the documents where either:
- `pretty` is 1-close to `house` AND `house` is 2-close to `by`
- OR: `pretty` is 2-close to `house` AND `house` is 1-close to `by`
*/

use std::ops::ControlFlow;

use roaring::RoaringBitmap;

use super::interner::MappedInterner;
use super::logger::SearchLogger;
use super::query_graph::QueryNode;
use super::ranking_rule_graph::{
    ConditionDocIdsCache, DeadEndsCache, /*ProximityGraph,*/ RankingRuleGraph,
    RankingRuleGraphTrait, TypoGraph,
};
use super::small_bitmap::SmallBitmap;
use super::{QueryGraph, RankingRule, RankingRuleOutput, SearchContext};
use crate::search::new::query_graph::QueryNodeData;
use crate::search::new::query_term::DerivationsSubset;
use crate::Result;

// pub type Proximity = GraphBasedRankingRule<ProximityGraph>;
// impl Default for GraphBasedRankingRule<ProximityGraph> {
//     fn default() -> Self {
//         Self::new("proximity".to_owned())
//     }
// }
pub type Typo = GraphBasedRankingRule<TypoGraph>;
impl Default for GraphBasedRankingRule<TypoGraph> {
    fn default() -> Self {
        Self::new("typo".to_owned())
    }
}

/// A generic graph-based ranking rule
pub struct GraphBasedRankingRule<G: RankingRuleGraphTrait> {
    id: String,
    // When the ranking rule is not iterating over its buckets,
    // its state is `None`.
    state: Option<GraphBasedRankingRuleState<G>>,
}
impl<G: RankingRuleGraphTrait> GraphBasedRankingRule<G> {
    /// Creates the ranking rule with the given identifier
    pub fn new(id: String) -> Self {
        Self { id, state: None }
    }
}

/// The internal state of a graph-based ranking rule during iteration
pub struct GraphBasedRankingRuleState<G: RankingRuleGraphTrait> {
    /// The current graph
    graph: RankingRuleGraph<G>,
    /// Cache to retrieve the docids associated with each edge
    conditions_cache: ConditionDocIdsCache<G>,
    /// Cache used to optimistically discard paths that resolve to no documents.
    dead_ends_cache: DeadEndsCache<G::Condition>,
    /// A structure giving the list of possible costs from each node to the end node
    all_costs: MappedInterner<QueryNode, Vec<u64>>,
    /// An index in the first element of `all_distances`, giving the cost of the next bucket
    cur_distance_idx: usize,
}

impl<'ctx, G: RankingRuleGraphTrait> RankingRule<'ctx, QueryGraph> for GraphBasedRankingRule<G> {
    fn id(&self) -> String {
        self.id.clone()
    }
    fn start_iteration(
        &mut self,
        ctx: &mut SearchContext<'ctx>,
        _logger: &mut dyn SearchLogger<QueryGraph>,
        _universe: &RoaringBitmap,
        query_graph: &QueryGraph,
    ) -> Result<()> {
        let graph = RankingRuleGraph::build(ctx, query_graph.clone())?;
        let condition_docids_cache = ConditionDocIdsCache::default();
        let dead_ends_cache = DeadEndsCache::new(&graph.conditions_interner);

        // Then pre-compute the cost of all paths from each node to the end node
        let all_costs = graph.initialize_distances_with_necessary_edges();

        let state = GraphBasedRankingRuleState {
            graph,
            conditions_cache: condition_docids_cache,
            dead_ends_cache,
            all_costs,
            cur_distance_idx: 0,
        };

        self.state = Some(state);

        Ok(())
    }

    fn next_bucket(
        &mut self,
        ctx: &mut SearchContext<'ctx>,
        logger: &mut dyn SearchLogger<QueryGraph>,
        universe: &RoaringBitmap,
    ) -> Result<Option<RankingRuleOutput<QueryGraph>>> {
        // If universe.len() <= 1, the bucket sort algorithm
        // should not have called this function.
        assert!(universe.len() > 1);
        // Will crash if `next_bucket` is called before `start_iteration` or after `end_iteration`,
        // should never happen
        let mut state = self.state.take().unwrap();

        // If the cur_distance_idx does not point to a valid cost in the `all_distances`
        // structure, then we have computed all the buckets and can return.
        if state.cur_distance_idx >= state.all_costs.get(state.graph.query_graph.root_node).len() {
            self.state = None;
            return Ok(None);
        }

        // Retrieve the cost of the paths to compute
        let cost = state.all_costs.get(state.graph.query_graph.root_node)[state.cur_distance_idx];
        state.cur_distance_idx += 1;

        let mut bucket = RoaringBitmap::new();

        let GraphBasedRankingRuleState {
            graph,
            conditions_cache: condition_docids_cache,
            dead_ends_cache,
            all_costs,
            cur_distance_idx: _,
        } = &mut state;

        let original_universe = universe;
        let mut universe = universe.clone();

        let original_graph = graph.clone();
        let mut used_conditions = SmallBitmap::for_interned_values_in(&graph.conditions_interner);
        let mut considered_paths = vec![];
        let mut good_paths = vec![];

        // For each path of the given cost, we will compute its associated
        // document ids.
        // In case the path does not resolve to any document id, we try to figure out why
        // and update the `dead_ends_cache` accordingly.
        // Updating the dead_ends_cache helps speed up the execution of `visit_paths_of_cost` and reduces
        // the number of future candidate paths given by that same function.
        graph.visit_paths_of_cost(
            graph.query_graph.root_node,
            cost,
            all_costs,
            dead_ends_cache,
            |path, graph, dead_ends_cache| {
                if universe.is_empty() {
                    return Ok(ControlFlow::Break(()));
                }

                /* TODO: there are a couple ways to improve the speed of path computation.

                1. Since the `visit_paths_of_cost` method uses a depth-first-search, we know that
                consecutive calls to this closure have a high chance of giving paths sharing
                some prefix. It would be good to reuse `subpath_docids` and `visited_conditions`
                to find out what this common prefix is, to avoid recomputing it. In a way, doing
                this serves as the dual of the DeadEndsCache: it takes advantage of our knowledge that
                some paths *aren't* deadends. There is however a subtlety in that the universe might
                have changed between the two consecutive calls. This is why we should subtract the docids
                of the previous path (if successful) to the `subpath_docids`, at the same time as we do
                it for the universe.

                2. We perform way too many intersections with the universe. For the first visited path,
                the operation we do is essentially:
                        universe & (c1 & universe) & (c2 & universe) & (c3 & universe) & etc.
                This is a good idea *only if the universe is very small*. But if the universe is (almost)
                a superset of each condition, then these intersections serve no purpose and slow down the search.
                Maybe in the future we have a `deserialize_within_universe` method, which would speed up
                these intersections. But for now, we have to be careful.

                3. We could know in advance how many paths of a certain cost exist, and only update the
                DeadEndsCache if (m)any remaining paths exist. There is a subtlety here because
                on the next call of `next_bucket`, we will want an updated and correct DeadEndsCache.
                We need to think about that. We could also avoid putting forbidden edges in this cache
                if we know, somehow, that we won't visit this edge again.

                4. Finally, but that will be a long term difficult project. We should compute the path *lazily*.
                That is, when we do `path_docids &= condition`. We shouldn't *actually* perform the intersection,
                but simply register that operation. It's only when we ask if the path_docids is empty that
                **the minimum amount of work to determine whether the path is empty** is carried out. In practice,
                that means performing a MultiOps on each container, in order or not, until any resulting container
                is found to be non-empty. (In fact, when we ask `is_empty`, we should probably find the container
                that has the highest chance of being non-empty and compute that one first).

                */

                // Accumulate the path for logging purposes only
                considered_paths.push(path.to_vec());

                let mut path_docids = universe.clone();

                // We store the edges and their docids in vectors in case the path turns out to be
                // empty and we need to figure out why it was empty.
                let mut visited_conditions = vec![];
                // let mut cached_condition_docids = vec![];
                let mut subpath_docids = vec![];

                for (latest_condition_path_idx, &latest_condition) in path.iter().enumerate() {
                    visited_conditions.push(latest_condition);

                    let condition_docids = &condition_docids_cache
                        .get_computed_condition(ctx, latest_condition, graph, &universe)?
                        .docids;

                    // If the edge is empty, then the path will be empty as well, we update the graph
                    // and caches accordingly and skip to the next candidate path.
                    if condition_docids.is_empty() {
                        // 1. Store in the cache that this edge is empty for this universe
                        dead_ends_cache.forbid_condition(latest_condition);
                        // 2. remove all the edges with this condition from the ranking rule graph
                        graph.remove_edges_with_condition(latest_condition);
                        return Ok(ControlFlow::Continue(()));
                    }
                    path_docids &= condition_docids;
                    subpath_docids.push(path_docids.clone());

                    // If the (sub)path is empty, we try to figure out why and update the caches accordingly.
                    if path_docids.is_empty() {
                        let len_prefix = subpath_docids.len() - 1;
                        // First, we know that this path is empty, and thus any path
                        // that is a superset of it will also be empty.
                        dead_ends_cache.forbid_condition_after_prefix(
                            visited_conditions[..len_prefix].iter().copied(),
                            latest_condition,
                        );

                        if visited_conditions.len() > 1 {
                            let mut subprefix = vec![];
                            // Deadend if the intersection between this edge and any
                            // previous prefix is disjoint with the universe
                            for (past_condition, subpath_docids) in visited_conditions[..len_prefix]
                                .iter()
                                .zip(subpath_docids[..len_prefix].iter())
                            {
                                if *past_condition == latest_condition {
                                    todo!();
                                };
                                subprefix.push(*past_condition);
                                if condition_docids.is_disjoint(subpath_docids) {
                                    dead_ends_cache.forbid_condition_after_prefix(
                                        subprefix.iter().copied(),
                                        latest_condition,
                                    );
                                }
                            }

                            // keep the same prefix and check the intersection with
                            // all the remaining conditions
                            let mut forbidden = dead_ends_cache.forbidden.clone();
                            let mut cursor = dead_ends_cache;
                            for &c in visited_conditions[..len_prefix].iter() {
                                cursor = cursor.advance(c).unwrap();
                                forbidden.union(&cursor.forbidden);
                            }

                            let past_path_docids = &subpath_docids[subpath_docids.len() - 2];

                            let remaining_conditions =
                                path[latest_condition_path_idx..].iter().skip(1);
                            for next_condition in remaining_conditions {
                                if forbidden.contains(*next_condition) {
                                    continue;
                                }
                                let next_condition_docids = &condition_docids_cache
                                    .get_computed_condition(ctx, *next_condition, graph, &universe)?
                                    .docids;

                                if past_path_docids.is_disjoint(next_condition_docids) {
                                    cursor.forbid_condition(*next_condition);
                                }
                            }
                        }

                        return Ok(ControlFlow::Continue(()));
                    }
                }
                assert!(!path_docids.is_empty());
                // Accumulate the path for logging purposes only
                good_paths.push(path.to_vec());
                for condition in path {
                    used_conditions.insert(*condition);
                }
                bucket |= &path_docids;
                // Reduce the size of the universe so that we can more optimistically discard candidate paths
                universe -= path_docids;

                if universe.is_empty() {
                    Ok(ControlFlow::Break(()))
                } else {
                    Ok(ControlFlow::Continue(()))
                }
            },
        )?;
        // println!("  {} paths of cost {} in {}", paths.len(), cost, self.id);
        G::log_state(
            &original_graph,
            &good_paths,
            dead_ends_cache,
            original_universe,
            all_costs,
            cost,
            logger,
        );

        // We modify the next query graph so that it only contains the subgraph
        // that was used to compute this bucket
        // But we only do it in case the bucket length is >1, because otherwise
        // we know the child ranking rule won't be called anyway
        let mut next_query_graph = original_graph.query_graph;

        if bucket.len() > 1 {
            next_query_graph.simplify();

            let mut subset_for_node = next_query_graph.nodes.map(|_| DerivationsSubset::Nothing);
            for condition in used_conditions.iter() {
                let (from_subset, to_subset) =
                    condition_docids_cache.get_subsets_used_by_condition(condition);
                let from_nodes = original_graph.from_nodes_of_condition.get(condition);
                for from_node in from_nodes.iter() {
                    let existing_subset = subset_for_node.get_mut(from_node);
                    existing_subset.union(from_subset);
                }

                let to_nodes = original_graph.to_nodes_of_condition.get(condition);
                for to_node in to_nodes.iter() {
                    let existing_subset = subset_for_node.get_mut(to_node);
                    existing_subset.union(to_subset);
                }
            }

            for (node_id, node) in next_query_graph.nodes.iter_mut() {
                let term = match &mut node.data {
                    QueryNodeData::Term(term) => term,
                    QueryNodeData::Deleted | QueryNodeData::Start | QueryNodeData::End => continue,
                };
                let used_subset = subset_for_node.get(node_id);
                term.term_subset.zero_typo_subset.intersect(used_subset);
                term.term_subset.one_typo_subset.intersect(used_subset);
                term.term_subset.two_typo_subset.intersect(used_subset);
            }
            let mut unused_nodes = SmallBitmap::for_interned_values_in(&next_query_graph.nodes);
            for (node_id, node) in next_query_graph.nodes.iter() {
                match &node.data {
                    QueryNodeData::Term(term) => {
                        if term.term_subset.zero_typo_subset.is_empty()
                            && term.term_subset.one_typo_subset.is_empty()
                            && term.term_subset.two_typo_subset.is_empty()
                        {
                            unused_nodes.insert(node_id);
                        }
                    }
                    QueryNodeData::Deleted | QueryNodeData::Start | QueryNodeData::End => {}
                }
            }

            // 3. Remove the empty nodes from the graph
            next_query_graph
                .remove_nodes_keep_edges(unused_nodes.iter().collect::<Vec<_>>().as_slice());
        }

        self.state = Some(state);

        Ok(Some(RankingRuleOutput { query: next_query_graph, candidates: bucket }))
    }

    fn end_iteration(
        &mut self,
        _ctx: &mut SearchContext<'ctx>,
        _logger: &mut dyn SearchLogger<QueryGraph>,
    ) {
        self.state = None;
    }
}
