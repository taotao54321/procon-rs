// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/library/7/DPL/5/DPL_5_A

use proconio::input;

use procon_rs_modint::*;

type ModInt = ModInt1000000007;

fn main() {
    input! {
        n: u32,
        k: ModInt,
    }

    let ans = k.pow(n.into());

    println!("{}", ans);
}
