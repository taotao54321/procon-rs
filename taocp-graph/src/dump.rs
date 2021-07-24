use crate::{GraphBase, WeightBase};

#[derive(Debug)]
pub struct GraphDump {
    directed: bool,
    weighted: bool,
    node_origin: usize,
}

impl GraphDump {
    pub fn new() -> Self {
        Self {
            directed: true,
            weighted: true,
            node_origin: 0,
        }
    }

    pub fn directed(mut self, directed: bool) -> Self {
        self.directed = directed;
        self
    }

    pub fn weighted(mut self, weighted: bool) -> Self {
        self.weighted = weighted;
        self
    }

    /// 頂点番号の始点を設定する。
    /// 0 なら 0-based, 1 なら 1-based になる。
    pub fn node_origin(mut self, node_origin: usize) -> Self {
        self.node_origin = node_origin;
        self
    }

    pub fn dump<G>(self, g: &G) -> String
    where
        G: GraphBase,
        G::Weight: WeightBase,
    {
        let mut buf = vec![];

        if self.directed {
            Self::write_directed(&mut buf, g, self.weighted, self.node_origin).unwrap();
        } else {
            Self::write_undirected(&mut buf, g, self.weighted, self.node_origin).unwrap();
        }

        String::from_utf8(buf).unwrap()
    }

    fn write_directed<Wtr, G>(
        wtr: &mut Wtr,
        g: &G,
        weighted: bool,
        node_origin: usize,
    ) -> std::io::Result<()>
    where
        Wtr: std::io::Write,
        G: GraphBase,
        G::Weight: WeightBase,
    {
        let n = g.node_count();
        let m = g.edge_count();

        writeln!(wtr, "{} {}", n, m)?;

        for src in 0..n {
            for (dst, weight) in g.neighbors(src) {
                let src = src + node_origin;
                let dst = dst + node_origin;

                if weighted {
                    writeln!(wtr, "{} {} {}", src, dst, weight)?;
                } else {
                    writeln!(wtr, "{} {}", src, dst)?;
                }
            }
        }

        Ok(())
    }

    /// src < dst なる辺のみを出力する。
    /// グラフの単純性や無向性の厳密なチェックは行わない。
    fn write_undirected<Wtr, G>(
        wtr: &mut Wtr,
        g: &G,
        weighted: bool,
        node_origin: usize,
    ) -> std::io::Result<()>
    where
        Wtr: std::io::Write,
        G: GraphBase,
        G::Weight: WeightBase,
    {
        let n = g.node_count();
        let m = g.edge_count();
        assert!(m % 2 == 0);

        writeln!(wtr, "{} {}", n, m / 2)?;

        for src in 0..n {
            for (dst, weight) in g.neighbors(src).filter(|&(dst, _)| src < dst) {
                let src = src + node_origin;
                let dst = dst + node_origin;

                if weighted {
                    writeln!(wtr, "{} {} {}", src, dst, weight)?;
                } else {
                    writeln!(wtr, "{} {}", src, dst)?;
                }
            }
        }

        Ok(())
    }
}

impl Default for GraphDump {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::{GraphEdge, GraphVV};

    use super::*;

    #[test]
    fn dump_directed_weighted() {
        {
            const EXPECT: &str = r#"0 0
"#;

            let g = GraphVV::<i32>::new(0);
            assert_eq!(GraphDump::new().dump(&g), EXPECT);
        }
        {
            const EXPECT: &str = r#"4 3
0 1 10
0 2 20
1 3 30
"#;
            const EXPECT1: &str = r#"4 3
1 2 10
1 3 20
2 4 30
"#;

            let g = GraphVV::from_edges(
                4,
                &[
                    GraphEdge::new(0, 1, 10),
                    GraphEdge::new(0, 2, 20),
                    GraphEdge::new(1, 3, 30),
                ],
            );
            assert_eq!(GraphDump::new().dump(&g), EXPECT);
            assert_eq!(GraphDump::new().node_origin(1).dump(&g), EXPECT1);
        }
    }

    #[test]
    fn dump_directed_unweighted() {
        {
            const EXPECT: &str = r#"0 0
"#;

            let g = GraphVV::<i32>::new(0);
            assert_eq!(GraphDump::new().weighted(false).dump(&g), EXPECT);
        }
        {
            const EXPECT: &str = r#"4 3
0 1
0 2
1 3
"#;
            const EXPECT1: &str = r#"4 3
1 2
1 3
2 4
"#;

            let g = GraphVV::<i32>::from_edges(
                4,
                &[
                    GraphEdge::new_unweighted(0, 1),
                    GraphEdge::new_unweighted(0, 2),
                    GraphEdge::new_unweighted(1, 3),
                ],
            );
            assert_eq!(GraphDump::new().weighted(false).dump(&g), EXPECT);
            assert_eq!(
                GraphDump::new().weighted(false).node_origin(1).dump(&g),
                EXPECT1
            );
        }
    }

    #[test]
    fn dump_undirected_weighted() {
        {
            const EXPECT: &str = r#"0 0
"#;

            let g = GraphVV::<i32>::new(0);
            assert_eq!(GraphDump::new().directed(false).dump(&g), EXPECT);
        }
        {
            const EXPECT: &str = r#"4 3
0 1 10
0 2 20
1 3 30
"#;
            const EXPECT1: &str = r#"4 3
1 2 10
1 3 20
2 4 30
"#;

            let g = GraphVV::<i32>::from_edges_bidi(
                4,
                &[
                    GraphEdge::new(0, 1, 10),
                    GraphEdge::new(2, 0, 20),
                    GraphEdge::new(3, 1, 30),
                ],
            );
            assert_eq!(GraphDump::new().directed(false).dump(&g), EXPECT);
            assert_eq!(
                GraphDump::new().directed(false).node_origin(1).dump(&g),
                EXPECT1
            );
        }
    }

    #[test]
    fn dump_undirected_unweighted() {
        {
            const EXPECT: &str = r#"0 0
"#;

            let g = GraphVV::<i32>::new(0);
            assert_eq!(
                GraphDump::new().directed(false).weighted(false).dump(&g),
                EXPECT
            );
        }
        {
            const EXPECT: &str = r#"4 3
0 1
0 2
1 3
"#;
            const EXPECT1: &str = r#"4 3
1 2
1 3
2 4
"#;

            let g = GraphVV::<i32>::from_edges_bidi(
                4,
                &[
                    GraphEdge::new_unweighted(0, 1),
                    GraphEdge::new_unweighted(2, 0),
                    GraphEdge::new_unweighted(3, 1),
                ],
            );
            assert_eq!(
                GraphDump::new().directed(false).weighted(false).dump(&g),
                EXPECT
            );
            assert_eq!(
                GraphDump::new()
                    .directed(false)
                    .weighted(false)
                    .node_origin(1)
                    .dump(&g),
                EXPECT1
            );
        }
    }
}
