// verification-helper: PROBLEM https://judge.yosupo.jp/problem/shortest_path

use proconio::input;

use taocp_graph::*;

fn main() {
    input! {
        n: usize,
        m: usize,
        start: usize,
        goal: usize,
    }

    let mut g = GraphVV::<u64>::new(n);
    for _ in 0..m {
        input! {
            src: usize,
            dst: usize,
            weight: u64,
        }
        g.add_edge(src, GraphEdge::new(dst, weight));
    }

    let res = sssp::dijkstra(&g, start);

    if let Some(path) = res.path_to(goal) {
        println!("{} {}", res.distance_to(goal).unwrap(), path.len() - 1);
        for e in path.windows(2) {
            println!("{} {}", e[0], e[1]);
        }
    } else {
        println!("-1");
    }
}
