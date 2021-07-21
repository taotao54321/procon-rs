use procon_rs_modint::ModIntBase;

/// 法: 任意
/// 計算量: O(n)
pub fn factorial<Z: ModIntBase>(n: u32) -> Z {
    (1..=n).fold(Z::new_unchecked(1), std::ops::Mul::mul)
}

/// 法: 任意
/// 計算量: O(r)
pub fn permutation<Z: ModIntBase>(n: u32, r: u32) -> Z {
    if n < r {
        return Z::new_unchecked(0);
    }

    (n - r + 1..=n).fold(Z::new_unchecked(1), std::ops::Mul::mul)
}

/// 法: 素数
/// 計算量: O(r)
pub fn binomial<Z: ModIntBase>(n: u32, r: u32) -> Z {
    if n < r {
        return Z::new_unchecked(0);
    }

    let numer = (n - r + 1..=n).fold(Z::new_unchecked(1), std::ops::Mul::mul);
    let denom = (1..=r).fold(Z::new_unchecked(1), std::ops::Mul::mul);

    numer * denom.inv()
}

/// 法: 素数
/// 計算量: 初期化 O(N), クエリ O(1)
#[derive(Debug)]
pub struct FactorialTable<Z> {
    facs: Vec<Z>,
    ifacs: Vec<Z>,
}

impl<Z: ModIntBase> FactorialTable<Z> {
    pub fn new() -> Self {
        Self {
            facs: vec![Z::new_unchecked(1)],
            ifacs: vec![Z::new_unchecked(1)],
        }
    }

    pub fn with_max(n: u32) -> Self {
        let mut this = Self::new();
        this.prepare(n);
        this
    }

    pub fn factorial(&mut self, n: u32) -> Z {
        self.prepare(n);
        self.facs[n as usize]
    }

    pub fn factorial_inv(&mut self, n: u32) -> Z {
        self.prepare(n);
        self.ifacs[n as usize]
    }

    pub fn permutation(&mut self, n: u32, r: u32) -> Z {
        if n < r {
            return Z::new_unchecked(0);
        }

        self.prepare(n);
        self.facs[n as usize] * self.ifacs[(n - r) as usize]
    }

    pub fn binomial(&mut self, n: u32, r: u32) -> Z {
        if n < r {
            return Z::new_unchecked(0);
        }

        self.prepare(n);
        self.facs[n as usize] * self.ifacs[r as usize] * self.ifacs[(n - r) as usize]
    }

    fn prepare(&mut self, n: u32) {
        let n = n as usize;

        let len_pre = self.facs.len();
        if n < len_pre {
            return;
        }

        self.facs.reserve(n + 1);
        self.ifacs.resize(n + 1, Z::new_unchecked(0));

        for i in len_pre..=n {
            self.facs.push(self.facs[i - 1] * i);
        }

        self.ifacs[n] = self.facs[n].inv();
        for i in (len_pre..n).rev() {
            self.ifacs[i] = self.ifacs[i + 1] * (i + 1);
        }
    }
}

impl<Z: ModIntBase> Default for FactorialTable<Z> {
    fn default() -> Self {
        Self::new()
    }
}

/// 法: 任意
/// 計算量: 初期化 O(N^2), クエリ O(1)
#[derive(Debug)]
pub struct PermutationTable<Z> {
    perms: Vec<Vec<Z>>,
}

impl<Z: ModIntBase> PermutationTable<Z> {
    pub fn new() -> Self {
        Self { perms: vec![] }
    }

    pub fn with_max(n: u32) -> Self {
        let mut this = Self::new();
        this.prepare(n);
        this
    }

    pub fn get(&mut self, n: u32, r: u32) -> Z {
        if n < r {
            return Z::new_unchecked(0);
        }

        self.prepare(n);
        self.perms[n as usize][r as usize]
    }

    fn prepare(&mut self, n: u32) {
        let n = n as usize;

        let len_pre = self.perms.len();
        if n < len_pre {
            return;
        }

        self.perms.reserve(n + 1);

        for i in len_pre..=n {
            self.perms.push(
                std::iter::once(Z::new_unchecked(1))
                    .chain((1..=i).rev().scan(Z::new_unchecked(1), |prod, x| {
                        *prod *= x;
                        Some(*prod)
                    }))
                    .collect(),
            );
        }
    }
}

impl<Z: ModIntBase> Default for PermutationTable<Z> {
    fn default() -> Self {
        Self::new()
    }
}

/// 法: 任意
/// 計算量: 初期化 O(N^2), クエリ O(1)
#[derive(Debug)]
pub struct BinomialTable<Z> {
    binoms: Vec<Vec<Z>>,
}

impl<Z: ModIntBase> BinomialTable<Z> {
    pub fn new() -> Self {
        Self {
            binoms: vec![vec![Z::new_unchecked(1)]],
        }
    }

    pub fn with_max(n: u32) -> Self {
        let mut this = Self::new();
        this.prepare(n);
        this
    }

    pub fn get(&mut self, n: u32, r: u32) -> Z {
        if n < r {
            return Z::new_unchecked(0);
        }

        self.prepare(n);
        self.binoms[n as usize][r as usize]
    }

    fn prepare(&mut self, n: u32) {
        let n = n as usize;

        let len_pre = self.binoms.len();
        if n < len_pre {
            return;
        }

        self.binoms.reserve(n + 1);

        for i in len_pre..=n {
            self.binoms.push(
                std::iter::once(Z::new_unchecked(1))
                    .chain((1..i).map(|j| self.binoms[i - 1][j - 1] + self.binoms[i - 1][j]))
                    .chain(std::iter::once(Z::new_unchecked(1)))
                    .collect(),
            );
        }
    }
}

impl<Z: ModIntBase> Default for BinomialTable<Z> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type ModInt = procon_rs_modint::ModInt1000000007;

    #[test]
    fn test_factorial() {
        fn fac(n: u32) -> u32 {
            factorial::<ModInt>(n).value()
        }

        assert_eq!(fac(0), 1);
        assert_eq!(fac(1), 1);
        assert_eq!(fac(2), 2);
        assert_eq!(fac(5), 120);
        assert_eq!(fac(20), 146_326_063);
    }

    #[test]
    fn test_permutation() {
        fn perm(n: u32, r: u32) -> u32 {
            permutation::<ModInt>(n, r).value()
        }

        assert_eq!(perm(0, 0), 1);
        assert_eq!(perm(1, 0), 1);
        assert_eq!(perm(0, 1), 0);
        assert_eq!(perm(1, 1), 1);
        assert_eq!(perm(5, 5), 120);
        assert_eq!(perm(10, 6), 151_200);
        assert_eq!(perm(20, 10), 442_568_110);
    }

    #[test]
    fn test_binomial() {
        fn binom(n: u32, r: u32) -> u32 {
            binomial::<ModInt>(n, r).value()
        }

        assert_eq!(binom(0, 0), 1);
        assert_eq!(binom(1, 0), 1);
        assert_eq!(binom(0, 1), 0);
        assert_eq!(binom(1, 1), 1);
        assert_eq!(binom(5, 2), 10);
        assert_eq!(binom(5, 5), 1);
        assert_eq!(binom(10, 6), 210);
        assert_eq!(binom(50, 25), 605_552_882);
    }

    #[test]
    fn factorial_table_factorial() {
        let mut ft = FactorialTable::<ModInt>::new();

        assert_eq!(ft.factorial(0).value(), 1);
        assert_eq!(ft.factorial(1).value(), 1);
        assert_eq!(ft.factorial(5).value(), 120);
        assert_eq!(ft.factorial(20).value(), 146_326_063);
    }

    #[test]
    fn factorial_table_factorial_inv() {
        let mut ft = FactorialTable::<ModInt>::new();

        assert_eq!(ft.factorial_inv(0).value(), 1);
        assert_eq!(ft.factorial_inv(1).value(), 1);
        assert_eq!(ft.factorial_inv(5).value(), 808_333_339);
        assert_eq!(ft.factorial_inv(20).value(), 120_104_394);
    }

    #[test]
    fn factorial_table_permutation() {
        let mut ft = FactorialTable::<ModInt>::new();

        assert_eq!(ft.permutation(0, 0).value(), 1);
        assert_eq!(ft.permutation(1, 0).value(), 1);
        assert_eq!(ft.permutation(0, 1).value(), 0);
        assert_eq!(ft.permutation(1, 1).value(), 1);
        assert_eq!(ft.permutation(5, 5).value(), 120);
        assert_eq!(ft.permutation(10, 6).value(), 151_200);
        assert_eq!(ft.permutation(20, 10).value(), 442_568_110);
    }

    #[test]
    fn factorial_table_binomial() {
        let mut ft = FactorialTable::<ModInt>::new();

        assert_eq!(ft.binomial(0, 0).value(), 1);
        assert_eq!(ft.binomial(1, 0).value(), 1);
        assert_eq!(ft.binomial(0, 1).value(), 0);
        assert_eq!(ft.binomial(1, 1).value(), 1);
        assert_eq!(ft.binomial(5, 2).value(), 10);
        assert_eq!(ft.binomial(5, 5).value(), 1);
        assert_eq!(ft.binomial(10, 6).value(), 210);
        assert_eq!(ft.binomial(50, 25).value(), 605_552_882);
    }

    #[test]
    fn permutation_table_get() {
        let mut pt = PermutationTable::<ModInt>::new();

        assert_eq!(pt.get(0, 0).value(), 1);
        assert_eq!(pt.get(1, 0).value(), 1);
        assert_eq!(pt.get(0, 1).value(), 0);
        assert_eq!(pt.get(1, 1).value(), 1);
        assert_eq!(pt.get(5, 5).value(), 120);
        assert_eq!(pt.get(10, 6).value(), 151_200);
        assert_eq!(pt.get(20, 10).value(), 442_568_110);
    }

    #[test]
    fn binomial_table_get() {
        let mut bt = BinomialTable::<ModInt>::new();

        assert_eq!(bt.get(0, 0).value(), 1);
        assert_eq!(bt.get(1, 0).value(), 1);
        assert_eq!(bt.get(0, 1).value(), 0);
        assert_eq!(bt.get(1, 1).value(), 1);
        assert_eq!(bt.get(5, 2).value(), 10);
        assert_eq!(bt.get(5, 5).value(), 1);
        assert_eq!(bt.get(10, 6).value(), 210);
        assert_eq!(bt.get(50, 25).value(), 605_552_882);
    }
}
