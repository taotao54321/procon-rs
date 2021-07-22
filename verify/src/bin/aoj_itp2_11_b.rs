// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/lesson/8/ITP2/11/ITP2_11_B

use proconio::input;

use taocp_bit::*;

fn main() {
    input! {
        n: u32,
        k: u32,
        is: [u32; k],
    }

    let univ = u32::bit_new_repunit(n);

    let x = is
        .into_iter()
        .map(u32::bit_new_single)
        .fold(0, std::ops::BitOr::bitor);

    for y in bit_supersets(univ, x) {
        print!("{}:", y);
        for i in bit_positions_one(y) {
            print!(" {}", i);
        }
        println!();
    }
}
