// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/courses/library/7/DPL/5/DPL_5_B

use proconio::input;

use taocp_modint::*;
use taocp_modint_math::*;

type ModInt = ModInt1000000007;

fn main() {
    input! {
        n: u32,
        k: u32,
    }

    let ans1 = permutation::<ModInt>(k, n);
    let ans2 = FactorialTable::<ModInt>::new().permutation(k, n);
    let ans3 = PermutationTable::<ModInt>::new().get(k, n);

    assert_eq!(ans1, ans2);
    assert_eq!(ans1, ans3);

    println!("{}", ans1);
}
