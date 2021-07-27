use taocp_graph::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct ApspFloydWarshall<W> {
    ds: Vec<Vec<W>>,
    nxt: Vec<Vec<usize>>,
    has_negative_cycle: bool,
}

impl<W: WeightBase> ApspFloydWarshall<W> {
    /// src から dst への最短距離を返す。
    /// src から dst へ到達不能な場合、W::INF を返す。
    /// src から dst への経路上に負閉路がある場合、-W::INF を返す。
    pub fn distance(&self, src: usize, dst: usize) -> W {
        self.ds[src][dst]
    }

    /// src から dst への最短経路 [src, ..., dst] を返す。
    /// src から dst へ到達不能であるか、または経路上に負閉路がある場合、None を返す。
    pub fn path(&self, src: usize, dst: usize) -> Option<Vec<usize>> {
        if self.ds[src][dst] == W::INF || self.ds[src][dst] == -W::INF {
            return None;
        }

        let mut path = vec![src];

        let mut v = src;
        while v != dst {
            v = self.nxt[v][dst];
            path.push(v);
        }

        Some(path)
    }

    pub fn has_negative_cycle(&self) -> bool {
        self.has_negative_cycle
    }

    fn new<G: GraphBase<Weight = W>>(g: &G) -> Self {
        let n = g.node_count();

        let mut ds = vec![vec![W::INF; n]; n];
        let mut nxt = vec![vec![usize::max_value(); n]; n];

        for i in 0..n {
            ds[i][i] = W::zero();
            nxt[i][i] = i;
        }

        for src in 0..n {
            for (dst, weight) in g.neighbors(src) {
                if src == dst {
                    // 自己辺は重みが負なら -INF とし、さもなくば無視する。
                    ds[src][dst] = if weight < W::zero() {
                        -W::INF
                    } else {
                        W::zero()
                    };
                } else {
                    ds[src][dst] = weight;
                    nxt[src][dst] = dst;
                }
            }
        }

        Self {
            ds,
            nxt,
            has_negative_cycle: false,
        }
    }
}

pub fn apsp_floyd_warshall<G, W>(g: &G) -> ApspFloydWarshall<W>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut state = ApspFloydWarshall::new(g);

    for k in 0..n {
        for i in 0..n {
            if state.ds[i][k] == W::INF {
                continue;
            }
            for j in 0..n {
                if state.ds[k][j] == W::INF {
                    continue;
                }

                // 緩和の際、-INF より小さくならないようにすることでオーバーフローを防ぐ。
                // (-INF は 2 倍してもオーバーフローしないと仮定している)
                let d_new = state.ds[i][k] + state.ds[k][j];
                if d_new < state.ds[i][j] {
                    state.ds[i][j] = d_new.max(-W::INF);
                    state.nxt[i][j] = k;
                }
            }
        }
    }

    // この時点で負閉路上にある任意の頂点 v について ds[v][v] < 0 となっている。
    // そのような頂点 v があれば ds[v][v] = -INF とし、負閉路フラグを立てる。
    for v in 0..n {
        if state.ds[v][v] < W::zero() {
            state.ds[v][v] = -W::INF;
            state.has_negative_cycle = true;
        }
    }

    // 経路上に負閉路があるペアについて最短距離を -INF とする。
    if state.has_negative_cycle {
        for k in 0..n {
            for i in 0..n {
                if state.ds[i][k] == W::INF {
                    continue;
                }
                for j in 0..n {
                    if state.ds[k][j] == W::INF {
                        continue;
                    }

                    if state.ds[k][k] == -W::INF {
                        state.ds[i][j] = -W::INF;
                    }
                }
            }
        }
    }

    state
}

#[cfg(test)]
mod tests {
    use proconio::{input, source::once::OnceSource};

    use taocp_graph::{GraphEdge, GraphEdgeSrcDstWeight, GraphVV};
    use taocp_prelude::Inf;

    use super::*;

    #[test]
    fn apsp_floyd_warshall_trivial() {
        {
            let g = GraphVV::<i32>::new(1);
            let apsp = apsp_floyd_warshall(&g);
            assert!(!apsp.has_negative_cycle());
            assert_eq!(apsp.distance(0, 0), 0);
            assert_eq!(apsp.path(0, 0), Some(vec![0]));
        }
        {
            let g = GraphVV::<i32>::from_edges(2, &[GraphEdge::new(1, 0, 10)]);
            let apsp = apsp_floyd_warshall(&g);
            assert!(!apsp.has_negative_cycle());
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
            let apsp = apsp_floyd_warshall(&g);
            assert!(apsp.has_negative_cycle());
            assert_eq!(apsp.distance(0, 0), -i32::INF);
            assert_eq!(apsp.distance(1, 0), -i32::INF);
            assert_eq!(apsp.distance(1, 2), -10);
            assert_eq!(apsp.path(0, 0), None);
            assert_eq!(apsp.path(1, 0), None);
            assert_eq!(apsp.path(1, 2), Some(vec![1, 2]));
        }
    }

    #[test]
    fn apsp_floyd_warshall_normal() {
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
        let apsp = apsp_floyd_warshall(&g);

        assert!(!apsp.has_negative_cycle());

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
    fn apsp_floyd_warshall_negative_cycle() {
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
        let apsp = apsp_floyd_warshall(&g);

        assert!(apsp.has_negative_cycle());

        assert_eq!(apsp.distance(0, 0), 0);
        assert_eq!(apsp.distance(0, 1), 1);
        assert_eq!(apsp.distance(0, 2), -i32::INF);
        assert_eq!(apsp.distance(0, 3), -i32::INF);
        assert_eq!(apsp.distance(1, 0), i32::INF);
        assert_eq!(apsp.distance(1, 1), 0);
        assert_eq!(apsp.distance(1, 2), -i32::INF);
        assert_eq!(apsp.distance(1, 3), -i32::INF);
        assert_eq!(apsp.distance(2, 0), i32::INF);
        assert_eq!(apsp.distance(2, 1), i32::INF);
        assert_eq!(apsp.distance(2, 2), -i32::INF);
        assert_eq!(apsp.distance(2, 3), -i32::INF);
        assert_eq!(apsp.distance(3, 0), i32::INF);
        assert_eq!(apsp.distance(3, 1), i32::INF);
        assert_eq!(apsp.distance(3, 2), -i32::INF);
        assert_eq!(apsp.distance(3, 3), -i32::INF);

        assert_eq!(apsp.path(0, 1), Some(vec![0, 1]));
        assert_eq!(apsp.path(0, 3), None);
    }
}
