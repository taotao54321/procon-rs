//! 重み付き単純グラフに限定する。

mod dump;
mod read;

pub use dump::*;
pub use read::*;

// TODO: 宣言と impl で同じトレイト境界を 2 回書くのをどうにかしたい
pub trait WeightBase:
    Sized
    + Copy
    + Eq
    + Ord
    + Default
    + std::str::FromStr
    + std::fmt::Debug
    + std::fmt::Display
    + std::ops::Add<Self, Output = Self>
    + std::ops::Sub<Self, Output = Self>
    + std::ops::AddAssign<Self>
    + std::ops::SubAssign<Self>
    + std::iter::Sum
    + num_traits::Zero
    + num_traits::One
    + taocp_prelude::Inf
{
}

impl<T> WeightBase for T where
    T: Sized
        + Copy
        + Eq
        + Ord
        + Default
        + std::str::FromStr
        + std::fmt::Debug
        + std::fmt::Display
        + std::ops::Add<Self, Output = Self>
        + std::ops::Sub<Self, Output = Self>
        + std::ops::AddAssign<Self>
        + std::ops::SubAssign<Self>
        + std::iter::Sum
        + num_traits::Zero
        + num_traits::One
        + taocp_prelude::Inf
{
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GraphEdge<W> {
    src: usize,
    dst: usize,
    weight: W,
}

impl<W: WeightBase> GraphEdge<W> {
    pub fn new(src: usize, dst: usize, weight: W) -> Self {
        Self { src, dst, weight }
    }

    pub fn new_unweighted(src: usize, dst: usize) -> Self {
        Self::new(src, dst, W::one())
    }

    pub fn src(self) -> usize {
        self.src
    }

    pub fn dst(self) -> usize {
        self.dst
    }

    pub fn weight(self) -> W {
        self.weight
    }

    pub fn reversed(self) -> Self {
        Self::new(self.dst, self.src, self.weight)
    }
}

pub trait GraphBase {
    type Weight;

    fn node_count(&self) -> usize;

    /// 片方向の辺の数を返す。無向グラフの場合、2*(無向辺の数) が返ることになる。
    fn edge_count(&self) -> usize;

    fn neighbors(&self, src: usize) -> Box<dyn Iterator<Item = (usize, Self::Weight)> + '_>;

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight>;
}

#[derive(Clone, Debug)]
pub struct GraphVV<W> {
    inner: Vec<Vec<(usize, W)>>,
}

impl<W: WeightBase> GraphVV<W> {
    pub fn new(n: usize) -> Self {
        Self {
            inner: vec![vec![]; n],
        }
    }

    pub fn from_edges(n: usize, edges: &[GraphEdge<W>]) -> Self {
        let mut this = Self::new(n);
        edges.iter().for_each(|&e| this.add_edge(e));
        this
    }

    pub fn from_edges_bidi(n: usize, edges: &[GraphEdge<W>]) -> Self {
        let mut this = Self::new(n);
        edges.iter().for_each(|&e| this.add_edge_bidi(e));
        this
    }

    /// 片方向の辺を追加する。
    /// 単純性を崩してはならない。
    pub fn add_edge(&mut self, edge: GraphEdge<W>) {
        let GraphEdge { src, dst, weight } = edge;

        self.inner[src].push((dst, weight));
    }

    /// 双方向の辺を追加する。
    /// 単純性を崩してはならない。
    pub fn add_edge_bidi(&mut self, edge: GraphEdge<W>) {
        self.add_edge(edge);
        self.add_edge(edge.reversed());
    }
}

impl<W: WeightBase> GraphBase for GraphVV<W> {
    type Weight = W;

    fn node_count(&self) -> usize {
        self.inner.len()
    }

    fn edge_count(&self) -> usize {
        self.inner.iter().map(|v| v.len()).sum()
    }

    fn neighbors(&self, src: usize) -> Box<dyn Iterator<Item = (usize, Self::Weight)> + '_> {
        Box::new(self.inner[src].iter().copied())
    }

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight> {
        self.inner[src]
            .iter()
            .find(|&&(e_dst, _)| e_dst == dst)
            .map(|&(_, w)| w)
    }
}

#[derive(Clone, Debug)]
pub struct GraphMat<W> {
    inner: Vec<Vec<Option<W>>>,
}

impl<W: WeightBase> GraphMat<W> {
    pub fn new(n: usize) -> Self {
        Self {
            inner: vec![vec![None; n]; n],
        }
    }

    pub fn from_edges(n: usize, edges: &[GraphEdge<W>]) -> Self {
        let mut this = Self::new(n);
        edges.iter().for_each(|&e| this.add_edge(e));
        this
    }

    pub fn from_edges_bidi(n: usize, edges: &[GraphEdge<W>]) -> Self {
        let mut this = Self::new(n);
        edges.iter().for_each(|&e| this.add_edge_bidi(e));
        this
    }

    /// 片方向の辺を追加する。
    /// 単純性を崩してはならない。
    pub fn add_edge(&mut self, edge: GraphEdge<W>) {
        let GraphEdge { src, dst, weight } = edge;

        assert!(self.inner[src][dst].is_none());

        self.inner[src][dst] = Some(weight);
    }

    /// 双方向の辺を追加する。
    /// 単純性を崩してはならない。
    pub fn add_edge_bidi(&mut self, edge: GraphEdge<W>) {
        self.add_edge(edge);
        self.add_edge(edge.reversed());
    }
}

impl<W: WeightBase> GraphBase for GraphMat<W> {
    type Weight = W;

    fn node_count(&self) -> usize {
        self.inner.len()
    }

    fn edge_count(&self) -> usize {
        self.inner.iter().flatten().filter(|o| o.is_some()).count()
    }

    fn neighbors(&self, src: usize) -> Box<dyn Iterator<Item = (usize, Self::Weight)> + '_> {
        Box::new(
            self.inner[src]
                .iter()
                .enumerate()
                .filter_map(|(dst, o)| o.map(|w| (dst, w))),
        )
    }

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight> {
        self.inner[src][dst]
    }
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use taocp_prelude::OrdFloat;

    use super::*;

    #[test]
    fn graph_vv_new() {
        {
            let g = GraphVV::<i32>::new(0);
            assert_eq!(g.node_count(), 0);
            assert_eq!(g.edge_count(), 0);
        }
        {
            let g = GraphVV::<i32>::new(1);
            assert_eq!(g.node_count(), 1);
            assert_eq!(g.edge_count(), 0);
        }
        {
            let g = GraphVV::<i32>::new(10);
            assert_eq!(g.node_count(), 10);
            assert_eq!(g.edge_count(), 0);
        }
        {
            let g = GraphVV::<OrdFloat<f64>>::new(10);
            assert_eq!(g.node_count(), 10);
            assert_eq!(g.edge_count(), 0);
        }
    }

    #[test]
    fn graph_vv_from_edges() {
        let edges = [
            GraphEdge::new(0, 1, 10),
            GraphEdge::new(0, 2, 20),
            GraphEdge::new(1, 3, 30),
            GraphEdge::new(3, 0, 40),
            GraphEdge::new(3, 1, 50),
        ];
        let g = GraphVV::from_edges(4, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 5);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20)]);
        assert_equal(g.neighbors(1), vec![(3, 30)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![(0, 40), (1, 50)]);

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(50));
        assert_eq!(g.weight_of(0, 3), None);
    }

    #[test]
    fn graph_vv_from_edges_bidi() {
        let edges = [
            GraphEdge::new(0, 1, 10),
            GraphEdge::new(0, 2, 20),
            GraphEdge::new(1, 3, 30),
            GraphEdge::new(3, 0, 40),
        ];
        let g = GraphVV::from_edges_bidi(4, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 8);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20), (3, 40)]);
        assert_equal(g.neighbors(1), vec![(0, 10), (3, 30)]);
        assert_equal(g.neighbors(2), vec![(0, 20)]);
        assert_equal(g.neighbors(3), vec![(1, 30), (0, 40)]);

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(30));
        assert_eq!(g.weight_of(1, 2), None);
    }

    #[test]
    fn graph_mat_new() {
        {
            let g = GraphMat::<i32>::new(0);
            assert_eq!(g.node_count(), 0);
            assert_eq!(g.edge_count(), 0);
        }
        {
            let g = GraphMat::<i32>::new(1);
            assert_eq!(g.node_count(), 1);
            assert_eq!(g.edge_count(), 0);
        }
        {
            let g = GraphMat::<i32>::new(10);
            assert_eq!(g.node_count(), 10);
            assert_eq!(g.edge_count(), 0);
        }
    }

    #[test]
    fn graph_mat_from_edges() {
        let edges = [
            GraphEdge::new(0, 1, 10),
            GraphEdge::new(0, 2, 20),
            GraphEdge::new(1, 3, 30),
            GraphEdge::new(3, 0, 40),
            GraphEdge::new(3, 1, 50),
        ];
        let g = GraphMat::from_edges(4, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 5);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20)]);
        assert_equal(g.neighbors(1), vec![(3, 30)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![(0, 40), (1, 50)]);

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(50));
        assert_eq!(g.weight_of(0, 3), None);
    }

    #[test]
    fn graph_mat_from_edges_bidi() {
        let edges = [
            GraphEdge::new(0, 1, 10),
            GraphEdge::new(0, 2, 20),
            GraphEdge::new(1, 3, 30),
            GraphEdge::new(3, 0, 40),
        ];
        let g = GraphMat::from_edges_bidi(4, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 8);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20), (3, 40)]);
        assert_equal(g.neighbors(1), vec![(0, 10), (3, 30)]);
        assert_equal(g.neighbors(2), vec![(0, 20)]);
        assert_equal(g.neighbors(3), vec![(0, 40), (1, 30)]);

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(30));
        assert_eq!(g.weight_of(1, 2), None);
    }
}
