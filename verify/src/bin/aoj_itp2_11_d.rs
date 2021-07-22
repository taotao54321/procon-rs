// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/lesson/8/ITP2/11/ITP2_11_D

use proconio::input;

use taocp_bit::*;

fn main() {
    input! {
        n: u32,
        k: u32,
    }

    for x in bit_combinations::<u32>(n, k) {
        print!("{}:", x);
        for i in bit_positions_one(x) {
            print!(" {}", i);
        }
        println!();
    }
}
