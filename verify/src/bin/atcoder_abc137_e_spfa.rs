// verification-helper: PROBLEM https://atcoder.jp/contests/abc137/tasks/abc137_e

use proconio::input;

use taocp_graph::*;
use taocp_graph_sssp::*;
use taocp_prelude::*;

fn main() {
    input! {
        n: usize,
        m: usize,
        p: i32,
        edges: [GraphEdgeSrcDst1Weight<i32>; m],
    }
    let edges = edges
        .into_iter()
        .map(|e| GraphEdge::new(e.src(), e.dst(), p - e.weight()))
        .collect::<Vec<_>>();

    let g = GraphVV::from_edges(n, &edges);

    let sssp = sssp_spfa(&g, 0);
    let d = sssp.distance_to(n - 1);
    assert_ne!(d, i32::INF);

    if d == -i32::INF {
        println!("-1");
    } else {
        let ans = -d.min(0);
        println!("{}", ans);
    }
}
