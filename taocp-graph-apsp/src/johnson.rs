use std::collections::{BinaryHeap, VecDeque};

use taocp_graph::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct ApspJohnson<W> {
    ds: Vec<Vec<W>>,
    ps: Vec<Vec<usize>>,
}

impl<W: WeightBase> ApspJohnson<W> {
    /// src から dst への最短距離を返す。
    /// src から dst へ到達不能な場合、W::INF を返す。
    pub fn distance(&self, src: usize, dst: usize) -> W {
        self.ds[src][dst]
    }

    /// src から dst への最短経路 [src, ..., dst] を返す。
    /// src から dst へ到達不能な場合、None を返す。
    pub fn path(&self, src: usize, dst: usize) -> Option<Vec<usize>> {
        if self.ds[src][dst] == W::INF {
            return None;
        }

        let mut path = vec![dst];

        let mut v = dst;
        while v != src {
            v = self.ps[src][v];
            path.push(v);
        }
        path.reverse();

        Some(path)
    }

    fn new(ds: Vec<Vec<W>>, ps: Vec<Vec<usize>>) -> Self {
        Self { ds, ps }
    }
}

pub fn apsp_johnson<G, W>(g: &G) -> Option<ApspJohnson<W>>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let hs = get_potential(g)?;

    let (ds, ps): (Vec<_>, Vec<_>) = (0..n).map(|start| dijkstra(g, start, &hs)).unzip();

    Some(ApspJohnson::new(ds, ps))
}

/// 負閉路がある場合、None を返す。
fn get_potential<G, W>(g: &G) -> Option<Vec<W>>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut hs = vec![W::zero(); n];
    let mut queue = SpfaQueue::new(n);

    while !queue.is_empty() && queue.peek_edge_count() < n - 1 {
        let (src, edge_count) = queue.pop();

        for (dst, weight) in g.neighbors(src) {
            let h_new = hs[src] + weight;
            if h_new < hs[dst] {
                hs[dst] = h_new;
                queue.push(dst, edge_count + 1);
            }
        }
    }

    while !queue.is_empty() {
        let (src, _) = queue.pop();

        for (dst, weight) in g.neighbors(src) {
            if hs[src] + weight < hs[dst] {
                return None;
            }
        }
    }

    Some(hs)
}

#[derive(Debug)]
struct SpfaQueue {
    queue: VecDeque<(usize, usize)>,
    contains: Vec<bool>,
}

impl SpfaQueue {
    fn new(n: usize) -> Self {
        let queue: VecDeque<_> = (0..n).map(|v| (v, 0)).collect();

        Self {
            queue,
            contains: vec![true; n],
        }
    }

    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn push(&mut self, v: usize, edge_count: usize) {
        if !self.contains[v] {
            self.queue.push_back((v, edge_count));
            self.contains[v] = true;
        }
    }

    fn peek_edge_count(&self) -> usize {
        self.queue.front().unwrap().1
    }

    fn pop(&mut self) -> (usize, usize) {
        let (v, edge_count) = self.queue.pop_front().unwrap();
        debug_assert!(self.contains[v]);
        self.contains[v] = false;
        (v, edge_count)
    }
}

fn dijkstra<G, W>(g: &G, start: usize, hs: &[W]) -> (Vec<W>, Vec<usize>)
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut ds = vec![W::INF; n];
    let mut ps = vec![usize::max_value(); n];
    let mut heap = BinaryHeap::new();

    ds[start] = W::zero();
    heap.push(HeapEntry::new(start, W::zero()));

    let mut remain = n;
    while let Some(HeapEntry { v: src, d }) = heap.pop() {
        if ds[src] < d {
            continue;
        }

        remain -= 1;
        if remain == 0 {
            break;
        }

        for (dst, weight) in g.neighbors(src) {
            let weight = weight + hs[src] - hs[dst];
            debug_assert!(weight >= W::zero());
            let d_new = d + weight;
            if d_new < ds[dst] {
                ds[dst] = d_new;
                ps[dst] = src;
                heap.push(HeapEntry::new(dst, d_new));
            }
        }
    }

    for dst in 0..n {
        if ds[dst] != W::INF {
            ds[dst] += hs[dst] - hs[start];
        }
    }

    (ds, ps)
}

#[derive(Debug, Eq, PartialEq)]
struct HeapEntry<W> {
    v: usize,
    d: W,
}

impl<W: WeightBase> HeapEntry<W> {
    fn new(v: usize, d: W) -> Self {
        Self { v, d }
    }
}

impl<W: WeightBase> Ord for HeapEntry<W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.d.cmp(&self.d)
    }
}

impl<W: WeightBase> PartialOrd for HeapEntry<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use proconio::{input, source::once::OnceSource};

    use taocp_graph::{GraphEdge, GraphEdgeSrcDstWeight, GraphVV};
    use taocp_prelude::Inf;

    use super::*;

    #[test]
    fn apsp_johnson_trivial() {
        {
            let g = GraphVV::<i32>::new(1);
            let apsp = apsp_johnson(&g);
            assert!(apsp.is_some());
            let apsp = apsp.unwrap();
            assert_eq!(apsp.distance(0, 0), 0);
            assert_eq!(apsp.path(0, 0), Some(vec![0]));
        }
        {
            let g = GraphVV::<i32>::from_edges(2, &[GraphEdge::new(1, 0, 10)]);
            let apsp = apsp_johnson(&g);
            assert!(apsp.is_some());
            let apsp = apsp.unwrap();
            assert_eq!(apsp.distance(0, 0), 0);
            assert_eq!(apsp.distance(0, 1), i32::INF);
            assert_eq!(apsp.distance(1, 0), 10);
            assert_eq!(apsp.distance(1, 1), 0);
            assert_eq!(apsp.path(0, 0), Some(vec![0]));
            assert_eq!(apsp.path(0, 1), None);
            assert_eq!(apsp.path(1, 0), Some(vec![1, 0]));
            assert_eq!(apsp.path(1, 1), Some(vec![1]));
        }
        {
            let g = GraphVV::<i32>::from_edges(
                3,
                &[
                    GraphEdge::new(0, 0, -1),
                    GraphEdge::new(1, 0, 100),
                    GraphEdge::new(1, 2, -10),
                ],
            );
            assert!(apsp_johnson(&g).is_none());
        }
    }

    #[test]
    fn apsp_johnson_normal() {
        // sample 2 of https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 6
            0 1 1
            0 2 -5
            1 2 2
            1 3 4
            2 3 1
            3 2 7
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDstWeight<i32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);
        let apsp = apsp_johnson(&g);

        assert!(apsp.is_some());
        let apsp = apsp.unwrap();

        assert_eq!(apsp.distance(0, 0), 0);
        assert_eq!(apsp.distance(0, 1), 1);
        assert_eq!(apsp.distance(0, 2), -5);
        assert_eq!(apsp.distance(0, 3), -4);
        assert_eq!(apsp.distance(1, 0), i32::INF);
        assert_eq!(apsp.distance(1, 1), 0);
        assert_eq!(apsp.distance(1, 2), 2);
        assert_eq!(apsp.distance(1, 3), 3);
        assert_eq!(apsp.distance(2, 0), i32::INF);
        assert_eq!(apsp.distance(2, 1), i32::INF);
        assert_eq!(apsp.distance(2, 2), 0);
        assert_eq!(apsp.distance(2, 3), 1);
        assert_eq!(apsp.distance(3, 0), i32::INF);
        assert_eq!(apsp.distance(3, 1), i32::INF);
        assert_eq!(apsp.distance(3, 2), 7);
        assert_eq!(apsp.distance(3, 3), 0);

        assert_eq!(apsp.path(0, 3), Some(vec![0, 2, 3]));
    }

    #[test]
    fn apsp_johnson_negative_cycle() {
        // sample 3 of https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 6
            0 1 1
            0 2 5
            1 2 2
            1 3 4
            2 3 1
            3 2 -7
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDstWeight<i32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);

        assert!(apsp_johnson(&g).is_none());
    }
}
