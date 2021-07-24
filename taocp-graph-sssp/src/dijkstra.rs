use std::collections::BinaryHeap;

use taocp_graph::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct SsspDijkstra<W> {
    start: usize,
    ds: Vec<W>,
    ps: Vec<usize>,
}

impl<W: WeightBase> SsspDijkstra<W> {
    pub fn distance_to(&self, dst: usize) -> Option<W> {
        if self.ds[dst] == Self::inf() {
            return None;
        }
        Some(self.ds[dst])
    }

    pub fn path_to(&self, dst: usize) -> Option<Vec<usize>> {
        if self.ds[dst] == Self::inf() {
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

    fn inf() -> W {
        W::max_value()
    }

    fn new(n: usize, start: usize) -> Self {
        Self {
            start,
            ds: vec![Self::inf(); n],
            ps: vec![usize::max_value(); n],
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

/// g は負辺を持ってはならない。
pub fn sssp_dijkstra<G, W>(g: &G, start: usize) -> SsspDijkstra<W>
where
    G: GraphBase<Weight = W>,
    W: WeightBase,
{
    let n = g.node_count();

    let mut state = SsspDijkstra::new(n, start);
    let mut heap = BinaryHeap::new();

    macro_rules! relax {
        ($src:expr, $dst:expr, $d:expr) => {{
            if state.relax($src, $dst, $d) {
                heap.push(HeapEntry::new($dst, $d));
            }
        }};
    }

    relax!(start, start, W::zero());

    let mut remain = n;
    while !heap.is_empty() {
        let HeapEntry { v: src, d } = heap.pop().unwrap();
        if state.ds[src] < d {
            continue;
        }

        remain -= 1;
        if remain == 0 {
            break;
        }

        for (dst, weight) in g.neighbors(src) {
            assert!(weight >= W::zero());
            relax!(src, dst, d + weight);
        }
    }

    state
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

    use taocp_graph::{GraphEdgeSrcDstWeight, GraphVV};

    use super::*;

    #[test]
    fn test_sssp_dijkstra() {
        {
            let g = GraphVV::<u32>::new(1);
            let sssp = sssp_dijkstra(&g, 0);
            assert_eq!(sssp.distance_to(0), Some(0));
            assert_eq!(sssp.path_to(0), Some(vec![0]));
        }
        {
            let g = GraphVV::<u32>::new(2);
            let sssp = sssp_dijkstra(&g, 0);
            assert_eq!(sssp.distance_to(0), Some(0));
            assert_eq!(sssp.distance_to(1), None);
            assert_eq!(sssp.path_to(0), Some(vec![0]));
            assert_eq!(sssp.path_to(1), None);
        }
        {
            // sample of https://judge.yosupo.jp/problem/shortest_path
            #[rustfmt::skip]
            let source = OnceSource::from(r#"
                5 7
                0 3 5
                0 4 3
                2 4 2
                4 3 10
                4 0 7
                2 1 5
                1 0 1
            "#);

            input! {
                from source,
                n: usize,
                m: usize,
                edges: [GraphEdgeSrcDstWeight<u32>; m],
            }

            let g = GraphVV::from_edges(n, &edges);
            let sssp = sssp_dijkstra(&g, 2);

            assert_eq!(sssp.distance_to(3), Some(11));
            assert_eq!(sssp.path_to(3), Some(vec![2, 1, 0, 3]));
        }
    }
}