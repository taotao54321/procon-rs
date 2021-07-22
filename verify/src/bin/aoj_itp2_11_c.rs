// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/lesson/8/ITP2/11/ITP2_11_C

use proconio::input;

use taocp_bit::*;

fn main() {
    input! {
        _n: u32,
        k: u32,
        is: [u32; k],
    }

    let x = is
        .into_iter()
        .map(u32::bit_new_single)
        .fold(0, std::ops::BitOr::bitor);

    for y in bit_subsets(x) {
        print!("{}:", y);
        for i in bit_positions_one(y) {
            print!(" {}", i);
        }
        println!();
    }
}
