// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C

use itertools::Itertools as _;
use proconio::input;

use taocp_graph::*;
use taocp_graph_apsp::*;
use taocp_prelude::*;

fn main() {
    input! {
        n: usize,
        m: usize,
        edges: [GraphEdgeSrcDstWeight<i64>; m],
    }

    let g = GraphVV::from_edges(n, &edges);

    let apsp = apsp_floyd_warshall(&g);

    if apsp.has_negative_cycle() {
        println!("NEGATIVE CYCLE");
        return;
    }

    for src in 0..n {
        println!(
            "{}",
            (0..n)
                .map(|dst| apsp.distance(src, dst))
                .map(fmt_dist)
                .join(" ")
        );
    }
}

fn fmt_dist(d: i64) -> String {
    if d == i64::INF {
        "INF".to_owned()
    } else {
        format!("{}", d)
    }
}
