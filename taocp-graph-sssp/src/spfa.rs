use std::collections::VecDeque;

use taocp_graph::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct SsspSpfa<W> {
    start: usize,
    ds: Vec<W>,
    ps: Vec<usize>,
    has_negative_cycle: bool,
}

impl<W: WeightBase> SsspSpfa<W> {
    /// 始点から dst への最短距離を返す。
    /// dst が到達不能な場合、W::INF を返す。
    /// dst が到達可能な負閉路上にある場合、-W::INF を返す。
    pub fn distance_to(&self, dst: usize) -> W {
        self.ds[dst]
    }

    /// 始点から dst への最短経路 [start, ..., dst] を返す。
    /// dst が到達不能であるか、または負閉路上にある場合、None を返す。
    pub fn path_to(&self, dst: usize) -> Option<Vec<usize>> {
        if self.ds[dst] == W::INF || self.ds[dst] == -W::INF {
            return None;
        }

        let mut path = vec![dst];

        let mut v = dst;
        while v != self.start {
            v = self.ps[v];
            path.push(v);
        }
        path.reverse();

        Some(path)
    }

    /// 始点から到達可能な負閉路があるかどうかを返す。
    /// 到達不能な負閉路については関知しないことに注意。
    pub fn has_negative_cycle(&self) -> bool {
        self.has_negative_cycle
    }

    fn new(n: usize, start: usize) -> Self {
        Self {
            start,
            ds: vec![W::INF; n],
            ps: vec![usize::max_value(); n],
            has_negative_cycle: false,
        }
    }

    fn relax(&mut self, src: usize, dst: usize, d: W) -> bool {
        if d < self.ds[dst] {
            self.ds[dst] = d;
            self.ps[dst] = src;
            true
        } else {
            false
        }
    }
}

pub fn sssp_spfa<G, W>(g: &G, start: usize) -> SsspSpfa<W>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut state = SsspSpfa::new(n, start);
    let mut queue = SpfaQueue::new(n);

    state.ds[start] = W::zero();
    queue.push(start, 0);

    // 到達可能な負閉路がない場合、真の最短経路は高々 n-1 本の辺からなる。
    while !queue.is_empty() && queue.peek_edge_count() < n - 1 {
        let (src, edge_count) = queue.pop();

        for (dst, weight) in g.neighbors(src) {
            if state.relax(src, dst, state.ds[src] + weight) {
                queue.push(dst, edge_count + 1);
            }
        }
    }

    // n-1 本の辺からなる経路で緩和が起こった頂点たちからさらに探索する。
    // ここで緩和が起こった場合、辺の行き先への真の最短距離は -INF となる。
    while !queue.is_empty() && queue.peek_edge_count() < n {
        let (src, edge_count) = queue.pop();

        for (dst, weight) in g.neighbors(src) {
            if state.ds[src] + weight < state.ds[dst] {
                state.ds[dst] = -W::INF;
                state.has_negative_cycle = true;
                queue.push(dst, edge_count + 1);
            }
        }
    }

    // 到達可能な負閉路がある場合、-INF が全頂点に伝播する経路は高々 2n-1 本の辺からなる。
    while !queue.is_empty() && queue.peek_edge_count() < 2 * n - 1 {
        let (src, edge_count) = queue.pop();

        for (dst, _) in g.neighbors(src) {
            if state.ds[dst] != -W::INF {
                state.ds[dst] = -W::INF;
                queue.push(dst, edge_count + 1);
            }
        }
    }

    state
}

#[derive(Debug)]
struct SpfaQueue {
    queue: VecDeque<(usize, usize)>,
    contains: Vec<bool>,
}

impl SpfaQueue {
    fn new(n: usize) -> Self {
        Self {
            queue: VecDeque::with_capacity(n),
            contains: vec![false; n],
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

#[cfg(test)]
mod tests {
    use proconio::{input, source::once::OnceSource};

    use taocp_graph::{GraphEdge, GraphEdgeSrcDstWeight, GraphVV};
    use taocp_prelude::Inf;

    use super::*;

    #[test]
    fn sssp_spfa_trivial() {
        {
            let g = GraphVV::<i32>::new(1);
            let sssp = sssp_spfa(&g, 0);
            assert!(!sssp.has_negative_cycle());
            assert_eq!(sssp.distance_to(0), 0);
            assert_eq!(sssp.path_to(0), Some(vec![0]));
        }
        {
            let g = GraphVV::<i32>::new(2);
            let sssp = sssp_spfa(&g, 0);
            assert!(!sssp.has_negative_cycle());
            assert_eq!(sssp.distance_to(0), 0);
            assert_eq!(sssp.distance_to(1), i32::INF);
            assert_eq!(sssp.path_to(0), Some(vec![0]));
            assert_eq!(sssp.path_to(1), None);
        }
        {
            let g = GraphVV::<i32>::new(2);
            let sssp = sssp_spfa(&g, 1);
            assert!(!sssp.has_negative_cycle());
            assert_eq!(sssp.distance_to(0), i32::INF);
            assert_eq!(sssp.distance_to(1), 0);
            assert_eq!(sssp.path_to(0), None);
            assert_eq!(sssp.path_to(1), Some(vec![1]));
        }
        {
            let g = GraphVV::from_edges(3, &[GraphEdge::new(2, 1, 1), GraphEdge::new(1, 1, -1)]);
            let sssp = sssp_spfa(&g, 2);
            assert!(sssp.has_negative_cycle());
            assert_eq!(sssp.distance_to(0), i32::INF);
            assert_eq!(sssp.distance_to(1), -i32::INF);
            assert_eq!(sssp.distance_to(2), 0);
            assert_eq!(sssp.path_to(0), None);
            assert_eq!(sssp.path_to(1), None);
            assert_eq!(sssp.path_to(2), Some(vec![2]));
        }
    }

    #[test]
    fn sssp_spfa_normal() {
        // sample 3 of https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_B
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 5
            0 1 2
            0 2 3
            1 2 -5
            1 3 1
            2 3 2
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDstWeight<i32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);
        let sssp = sssp_spfa(&g, 1);

        assert!(!sssp.has_negative_cycle());

        assert_eq!(sssp.distance_to(0), i32::INF);
        assert_eq!(sssp.distance_to(1), 0);
        assert_eq!(sssp.distance_to(2), -5);
        assert_eq!(sssp.distance_to(3), -3);

        assert_eq!(sssp.path_to(0), None);
        assert_eq!(sssp.path_to(1), Some(vec![1]));
        assert_eq!(sssp.path_to(2), Some(vec![1, 2]));
        assert_eq!(sssp.path_to(3), Some(vec![1, 2, 3]));
    }

    #[test]
    fn sssp_spfa_negative_cycle() {
        // sample 2 of https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_B
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 6
            0 1 2
            0 2 3
            1 2 -5
            1 3 1
            2 3 2
            3 1 0
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDstWeight<i32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);
        let sssp = sssp_spfa(&g, 0);

        assert!(sssp.has_negative_cycle());

        assert_eq!(sssp.distance_to(0), 0);
        assert_eq!(sssp.distance_to(1), -i32::INF);
        assert_eq!(sssp.distance_to(2), -i32::INF);
        assert_eq!(sssp.distance_to(3), -i32::INF);

        assert_eq!(sssp.path_to(0), Some(vec![0]));
        assert_eq!(sssp.path_to(1), None);
        assert_eq!(sssp.path_to(2), None);
        assert_eq!(sssp.path_to(3), None);
    }
}
