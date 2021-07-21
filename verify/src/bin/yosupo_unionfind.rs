// verification-helper: PROBLEM https://judge.yosupo.jp/problem/unionfind

use proconio::input;

use taocp_union_find::*;

fn main() {
    input! {
        n: usize,
        q: usize,
    }

    let mut uf = UnionFind::new(n);

    for _ in 0..q {
        input! { cmd: u32 }

        match cmd {
            0 => {
                input! { v: usize, w: usize }
                uf.unite(v, w);
            }
            1 => {
                input! { v: usize, w: usize }
                let ans = if uf.is_same(v, w) { 1 } else { 0 };
                println!("{}", ans);
            }
            _ => panic!("invalid command: {}", cmd),
        }
    }
}
