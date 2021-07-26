use taocp_graph::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct SsspBellmanFord<W> {
    start: usize,
    ds: Vec<W>,
    ps: Vec<usize>,
    has_negative_cycle: bool,
}

impl<W: WeightBase> SsspBellmanFord<W> {
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

    fn mark_negative_cycle(&mut self, v: usize) {
        self.ds[v] = -W::INF;
        self.has_negative_cycle = true;
    }
}

pub fn sssp_bellman_ford<G, W>(g: &G, start: usize) -> SsspBellmanFord<W>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut state = SsspBellmanFord::new(n, start);
    state.ds[start] = W::zero();

    for _ in 0..n - 1 {
        let mut relaxed = false;

        for src in 0..n {
            if state.ds[src] == W::INF {
                continue;
            }

            for (dst, weight) in g.neighbors(src) {
                relaxed |= state.relax(src, dst, state.ds[src] + weight);
            }
        }

        if !relaxed {
            return state;
        }
    }

    {
        let mut relaxed = false;

        for src in 0..n {
            if state.ds[src] == W::INF {
                continue;
            }

            for (dst, weight) in g.neighbors(src) {
                if state.ds[src] + weight < state.ds[dst] {
                    state.mark_negative_cycle(dst);
                    relaxed = true;
                }
            }
        }

        if !relaxed {
            return state;
        }
    }

    for _ in 0..n - 1 {
        let mut relaxed = false;

        for src in 0..n {
            if state.ds[src] == -W::INF {
                for (dst, _) in g.neighbors(src) {
                    state.mark_negative_cycle(dst);
                    relaxed = true;
                }
            }
        }

        if !relaxed {
            return state;
        }
    }

    state
}

#[cfg(test)]
mod tests {
    use proconio::{input, source::once::OnceSource};

    use taocp_graph::{GraphEdgeSrcDstWeight, GraphVV};
    use taocp_prelude::Inf;

    use super::*;

    #[test]
    fn sssp_bellman_ford_normal() {
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
        let sssp = sssp_bellman_ford(&g, 1);

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
    fn sssp_bellman_ford_negative_cycle() {
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
        let sssp = sssp_bellman_ford(&g, 0);

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
