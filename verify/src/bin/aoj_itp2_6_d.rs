// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/lesson/8/ITP2/6/ITP2_6_D

use proconio::input;

use taocp_prelude::*;

fn main() {
    input! {
        n: usize,
        xs: [u32; n],
        q: usize,
    }

    for _ in 0..q {
        input! { k: u32 }

        let lb = xs.partition_point(|&x| x < k);
        let ub = xs.partition_point(|&x| x <= k);

        println!("{} {}", lb, ub);
    }
}
