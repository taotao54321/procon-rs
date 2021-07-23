//! 重み付き単純グラフに限定する。

pub mod sssp;

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
    + num_traits::Bounded
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
        + num_traits::Bounded
{
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GraphEdge<W> {
    dst: usize,
    weight: W,
}

impl<W: WeightBase> GraphEdge<W> {
    pub fn new(dst: usize, weight: W) -> Self {
        GraphEdge { dst, weight }
    }

    pub fn dst(self) -> usize {
        self.dst
    }

    pub fn weight(self) -> W {
        self.weight
    }
}

pub trait GraphBase {
    type Weight;

    fn node_count(&self) -> usize;
    fn edge_count(&self) -> usize;

    fn edges_from(&self, src: usize) -> Box<dyn Iterator<Item = GraphEdge<Self::Weight>> + '_>;

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight>;
}

#[derive(Clone, Debug)]
pub struct GraphVV<W> {
    inner: Vec<Vec<GraphEdge<W>>>,
}

impl<W: WeightBase> GraphVV<W> {
    pub fn new(n: usize) -> Self {
        Self {
            inner: vec![vec![]; n],
        }
    }

    /// 単純性を崩してはならない。
    pub fn add_edge(&mut self, src: usize, edge: GraphEdge<W>) {
        self.inner[src].push(edge);
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

    fn edges_from(&self, src: usize) -> Box<dyn Iterator<Item = GraphEdge<Self::Weight>> + '_> {
        Box::new(self.inner[src].iter().copied())
    }

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight> {
        self.inner[src]
            .iter()
            .find(|e| e.dst == dst)
            .map(|e| e.weight)
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

    /// 単純性を崩してはならない。
    pub fn add_edge(&mut self, src: usize, edge: GraphEdge<W>) {
        assert!(self.inner[src][edge.dst].is_none());

        self.inner[src][edge.dst] = Some(edge.weight);
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

    fn edges_from(&self, src: usize) -> Box<dyn Iterator<Item = GraphEdge<Self::Weight>> + '_> {
        Box::new(
            self.inner[src]
                .iter()
                .enumerate()
                .filter_map(|(dst, o)| o.map(|w| GraphEdge::new(dst, w))),
        )
    }

    fn weight_of(&self, src: usize, dst: usize) -> Option<Self::Weight> {
        self.inner[src][dst]
    }
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use super::*;

    #[test]
    fn graph_vv() {
        let mut g = GraphVV::<i32>::new(4);

        g.add_edge(0, GraphEdge::new(1, 10));
        g.add_edge(0, GraphEdge::new(2, 20));
        g.add_edge(1, GraphEdge::new(3, 30));
        g.add_edge(3, GraphEdge::new(0, 40));
        g.add_edge(3, GraphEdge::new(1, 50));

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 5);

        assert_equal(
            g.edges_from(0),
            vec![GraphEdge::new(1, 10), GraphEdge::new(2, 20)],
        );
        assert_equal(g.edges_from(1), vec![GraphEdge::new(3, 30)]);
        assert_eq!(g.edges_from(2).next(), None);
        assert_equal(
            g.edges_from(3),
            vec![GraphEdge::new(0, 40), GraphEdge::new(1, 50)],
        );

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(50));
        assert_eq!(g.weight_of(0, 3), None);
    }

    #[test]
    fn graph_mat() {
        let mut g = GraphMat::<i32>::new(4);

        g.add_edge(0, GraphEdge::new(1, 10));
        g.add_edge(0, GraphEdge::new(2, 20));
        g.add_edge(1, GraphEdge::new(3, 30));
        g.add_edge(3, GraphEdge::new(0, 40));
        g.add_edge(3, GraphEdge::new(1, 50));

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 5);

        assert_equal(
            g.edges_from(0),
            vec![GraphEdge::new(1, 10), GraphEdge::new(2, 20)],
        );
        assert_equal(g.edges_from(1), vec![GraphEdge::new(3, 30)]);
        assert_eq!(g.edges_from(2).next(), None);
        assert_equal(
            g.edges_from(3),
            vec![GraphEdge::new(0, 40), GraphEdge::new(1, 50)],
        );

        assert_eq!(g.weight_of(0, 1), Some(10));
        assert_eq!(g.weight_of(3, 1), Some(50));
        assert_eq!(g.weight_of(0, 3), None);
    }
}
