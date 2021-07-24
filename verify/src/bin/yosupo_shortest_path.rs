// verification-helper: PROBLEM https://judge.yosupo.jp/problem/shortest_path

use proconio::input;

use taocp_graph::*;
use taocp_graph_sssp::*;

fn main() {
    input! {
        n: usize,
        m: usize,
        start: usize,
        goal: usize,
        edges: [GraphEdgeSrcDstWeight<i64>; m],
    }

    let g = GraphVV::from_edges(n, &edges);

    let sssp = sssp_dijkstra(&g, start);

    if let Some(path) = sssp.path_to(goal) {
        println!("{} {}", sssp.distance_to(goal).unwrap(), path.len() - 1);
        for e in path.windows(2) {
            println!("{} {}", e[0], e[1]);
        }
    } else {
        println!("-1");
    }
}
