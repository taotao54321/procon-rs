use std::convert::Infallible;
use std::fmt::Debug;
use std::io::BufRead;
use std::marker::PhantomData;
use std::str::FromStr;

use proconio::source::{Readable, Source};

use crate::{GraphEdge, WeightBase};

pub enum GraphEdgeSrcDst<W = i32> {
    _Phantom(Infallible, PhantomData<W>),
}
impl<W: WeightBase> Readable for GraphEdgeSrcDst<W> {
    type Output = GraphEdge<W>;
    fn read<R: BufRead, S: Source<R>>(source: &mut S) -> Self::Output {
        let src = usize::read(source);
        let dst = usize::read(source);
        GraphEdge::new_unweighted(src, dst)
    }
}

pub enum GraphEdgeSrcDst1<W = i32> {
    _Phantom(Infallible, PhantomData<W>),
}
impl<W: WeightBase> Readable for GraphEdgeSrcDst1<W> {
    type Output = GraphEdge<W>;
    fn read<R: BufRead, S: Source<R>>(source: &mut S) -> Self::Output {
        let src = usize::read(source) - 1;
        let dst = usize::read(source) - 1;
        GraphEdge::new_unweighted(src, dst)
    }
}

pub enum GraphEdgeSrcDstWeight<W> {
    _Phantom(Infallible, PhantomData<W>),
}
impl<W: WeightBase> Readable for GraphEdgeSrcDstWeight<W>
where
    <W as FromStr>::Err: Debug,
{
    type Output = GraphEdge<W>;
    fn read<R: BufRead, S: Source<R>>(source: &mut S) -> Self::Output {
        let src = usize::read(source);
        let dst = usize::read(source);
        let weight = W::read(source);
        GraphEdge::new(src, dst, weight)
    }
}

pub enum GraphEdgeSrcDst1Weight<W> {
    _Phantom(Infallible, PhantomData<W>),
}
impl<W: WeightBase> Readable for GraphEdgeSrcDst1Weight<W>
where
    <W as FromStr>::Err: Debug,
{
    type Output = GraphEdge<W>;
    fn read<R: BufRead, S: Source<R>>(source: &mut S) -> Self::Output {
        let src = usize::read(source) - 1;
        let dst = usize::read(source) - 1;
        let weight = W::read(source);
        GraphEdge::new(src, dst, weight)
    }
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;
    use proconio::{input, source::once::OnceSource};

    use crate::{GraphBase, GraphVV};

    use super::*;

    #[test]
    fn graph_edge_src_dst() {
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 3
            0 1
            0 2
            1 3
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDst; m],
        }

        let g = GraphVV::from_edges(n, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 3);

        assert_equal(g.neighbors(0), vec![(1, 1), (2, 1)]);
        assert_equal(g.neighbors(1), vec![(3, 1)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![]);
    }

    #[test]
    fn graph_edge_src_dst_1() {
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 3
            1 2
            1 3
            2 4
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDst1; m],
        }

        let g = GraphVV::from_edges(n, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 3);

        assert_equal(g.neighbors(0), vec![(1, 1), (2, 1)]);
        assert_equal(g.neighbors(1), vec![(3, 1)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![]);
    }

    #[test]
    fn graph_edge_src_dst_weight() {
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 3
            0 1 10
            0 2 20
            1 3 30
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDstWeight<u32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 3);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20)]);
        assert_equal(g.neighbors(1), vec![(3, 30)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![]);
    }

    #[test]
    fn graph_edge_src_dst_1_weight() {
        #[rustfmt::skip]
        let source = OnceSource::from(r#"
            4 3
            1 2 10
            1 3 20
            2 4 30
        "#);

        input! {
            from source,
            n: usize,
            m: usize,
            edges: [GraphEdgeSrcDst1Weight<u32>; m],
        }

        let g = GraphVV::from_edges(n, &edges);

        assert_eq!(g.node_count(), 4);
        assert_eq!(g.edge_count(), 3);

        assert_equal(g.neighbors(0), vec![(1, 10), (2, 20)]);
        assert_equal(g.neighbors(1), vec![(3, 30)]);
        assert_equal(g.neighbors(2), vec![]);
        assert_equal(g.neighbors(3), vec![]);
    }
}
