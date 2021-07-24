use std::marker::PhantomData;

use crate::modint_base::{ModIntBase, ModIntBaseImpl};

pub type ModInt1000000007 = StaticModInt<Mod1000000007>;
pub type ModInt1000000009 = StaticModInt<Mod1000000009>;
pub type ModInt998244353 = StaticModInt<Mod998244353>;

pub struct StaticModInt<M> {
    value: u32,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: StaticModulus> ModIntBase for StaticModInt<M> {
    fn modulus() -> u32 {
        M::VALUE
    }

    fn new_unchecked(value: u32) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    fn value(self) -> u32 {
        self.value
    }
}

impl<M: StaticModulus> ModIntBaseImpl for StaticModInt<M> {}

impl_traits!(<M: StaticModulus>, StaticModInt<M>);

pub trait StaticModulus: 'static {
    const VALUE: u32;
}

pub enum Mod1000000007 {}
impl StaticModulus for Mod1000000007 {
    const VALUE: u32 = 1_000_000_007;
}

pub enum Mod1000000009 {}
impl StaticModulus for Mod1000000009 {
    const VALUE: u32 = 1_000_000_009;
}

pub enum Mod998244353 {}
impl StaticModulus for Mod998244353 {
    const VALUE: u32 = 998_244_353;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_modint_new() {
        fn f<V: crate::modint_base::RemEuclidU32>(value: V) -> u32 {
            ModInt1000000007::new(value).value()
        }

        assert_eq!(f(0_u32), 0);
        assert_eq!(f(1_u32), 1);
        assert_eq!(f(1_000_000_008_u32), 1);

        assert_eq!(f(0_u64), 0);
        assert_eq!(f(1_u64), 1);
        assert_eq!(f(1_000_000_008_u64), 1);
        assert_eq!(f((1_000_000_007_u64 << 24) + 1), 1);

        assert_eq!(f(0_usize), 0);
        assert_eq!(f(1_usize), 1);
        assert_eq!(f(1_000_000_008_usize), 1);

        assert_eq!(f(0_i64), 0);
        assert_eq!(f(1_i64), 1);
        assert_eq!(f(1_000_000_008_i64), 1);
        assert_eq!(f((1_000_000_007_i64 << 24) + 1), 1);
        assert_eq!(f(-1_i64), 1_000_000_006);
    }

    #[test]
    fn static_modint_pow() {
        fn pow(value: u32, e: u64) -> u32 {
            ModInt1000000007::new(value).pow(e).value()
        }

        assert_eq!(pow(0, 0), 1);
        assert_eq!(pow(1, 0), 1);
        assert_eq!(pow(1, 1), 1);
        assert_eq!(pow(2, 0), 1);
        assert_eq!(pow(2, 1), 2);
        assert_eq!(pow(2, 2), 4);
        assert_eq!(pow(2, 10), 1024);
        assert_eq!(pow(2, 32), 294_967_268);
        assert_eq!(pow(2, 1_000_000_006), 1);
    }

    #[test]
    fn static_modint_inv() {
        fn inv(value: u32) -> u32 {
            ModInt1000000007::new(value).inv().value()
        }

        assert_eq!(inv(1), 1);
        assert_eq!(inv(2), 500_000_004);
        assert_eq!(inv(3), 333_333_336);
        assert_eq!(inv(42), 23_809_524);
        assert_eq!(inv(1_000_000_006), 1_000_000_006);
    }

    #[test]
    fn static_modint_default() {
        assert_eq!(ModInt1000000007::default().value(), 0);
    }

    #[test]
    fn static_modint_from_str() {
        fn parse(s: &str) -> u32 {
            s.parse::<ModInt1000000007>().unwrap().value()
        }

        assert_eq!(parse("0"), 0);
        assert_eq!(parse("1"), 1);
        assert_eq!(parse("1000000008"), 1);
        assert_eq!(parse("-1"), 1_000_000_006);
    }

    #[test]
    fn static_modint_neg() {
        fn neg(value: u32) -> u32 {
            (-ModInt1000000007::new(value)).value()
        }

        assert_eq!(neg(0), 0);
        assert_eq!(neg(1), 1_000_000_006);
        assert_eq!(neg(1_000_000_006), 1);
    }

    #[test]
    fn static_modint_add() {
        fn add(lhs: u32, rhs: u32) -> u32 {
            (ModInt1000000007::new(lhs) + ModInt1000000007::new(rhs)).value()
        }

        assert_eq!(add(1, 1), 2);
        assert_eq!(add(1_000_000_006, 2), 1);
    }

    #[test]
    fn static_modint_sub() {
        fn sub(lhs: u32, rhs: u32) -> u32 {
            (ModInt1000000007::new(lhs) - ModInt1000000007::new(rhs)).value()
        }

        assert_eq!(sub(2, 1), 1);
        assert_eq!(sub(0, 1), 1_000_000_006);
    }

    #[test]
    fn static_modint_mul() {
        fn mul(lhs: u32, rhs: u32) -> u32 {
            (ModInt1000000007::new(lhs) * ModInt1000000007::new(rhs)).value()
        }

        assert_eq!(mul(1, 1), 1);
        assert_eq!(mul(2, 3), 6);
        assert_eq!(mul(100_000, 100_000), 999_999_937);
    }

    #[test]
    fn static_modint_add_assign() {
        let mut a = ModInt1000000007::new(0);
        let mut add_assign = move |b: u32| {
            a += ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(add_assign(1), 1);
        assert_eq!(add_assign(2), 3);
        assert_eq!(add_assign(1_000_000_006), 2);
    }

    #[test]
    fn static_modint_sub_assign() {
        let mut a = ModInt1000000007::new(3);
        let mut sub_assign = move |b: u32| {
            a -= ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(sub_assign(1), 2);
        assert_eq!(sub_assign(2), 0);
        assert_eq!(sub_assign(1_000_000_006), 1);
    }

    #[test]
    fn static_modint_mul_assign() {
        let mut a = ModInt1000000007::new(1);
        let mut mul_assign = move |b: u32| {
            a *= ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(mul_assign(1), 1);
        assert_eq!(mul_assign(2), 2);
        assert_eq!(mul_assign(3), 6);
        assert_eq!(mul_assign(1_000_000_006), 1_000_000_001);
    }

    #[test]
    fn static_modint_unary_op_ergonomics() {
        let a = ModInt1000000007::new(1);

        assert_eq!(-a, -(&a));
    }

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn static_modint_binary_op_ergonomics() {
        fn f(value: u32) -> ModInt1000000007 {
            ModInt1000000007::new(value)
        }

        #[allow(clippy::op_ref)]
        {
            assert_eq!(f(2) + f(2), f(2) + &f(2));
            assert_eq!(f(2) + f(2), &f(2) + f(2));
            assert_eq!(f(2) + f(2), &f(2) + &f(2));

            assert_eq!(f(2) + f(2), f(2) + 2);
            assert_eq!(f(2) + f(2), f(2) + &2);
            assert_eq!(f(2) + f(2), &f(2) + 2);
            assert_eq!(f(2) + f(2), &f(2) + &2);

            assert_eq!(f(2) + f(2), 2 + f(2));
            assert_eq!(f(2) + f(2), 2 + &f(2));
            assert_eq!(f(2) + f(2), &2 + f(2));
            assert_eq!(f(2) + f(2), &2 + &f(2));

            assert_eq!(f(2) - f(2), f(2) - &f(2));
            assert_eq!(f(2) - f(2), &f(2) - f(2));
            assert_eq!(f(2) - f(2), &f(2) - &f(2));

            assert_eq!(f(2) - f(2), f(2) - 2);
            assert_eq!(f(2) - f(2), f(2) - &2);
            assert_eq!(f(2) - f(2), &f(2) - 2);
            assert_eq!(f(2) - f(2), &f(2) - &2);

            assert_eq!(f(2) - f(2), 2 - f(2));
            assert_eq!(f(2) - f(2), 2 - &f(2));
            assert_eq!(f(2) - f(2), &2 - f(2));
            assert_eq!(f(2) - f(2), &2 - &f(2));

            assert_eq!(f(2) * f(2), f(2) * &f(2));
            assert_eq!(f(2) * f(2), &f(2) * f(2));
            assert_eq!(f(2) * f(2), &f(2) * &f(2));

            assert_eq!(f(2) * f(2), f(2) * 2);
            assert_eq!(f(2) * f(2), f(2) * &2);
            assert_eq!(f(2) * f(2), &f(2) * 2);
            assert_eq!(f(2) * f(2), &f(2) * &2);

            assert_eq!(f(2) * f(2), 2 * f(2));
            assert_eq!(f(2) * f(2), 2 * &f(2));
            assert_eq!(f(2) * f(2), &2 * f(2));
            assert_eq!(f(2) * f(2), &2 * &f(2));
        }
    }

    #[test]
    fn static_modint_assign_op_ergonomics() {
        {
            let mut a = ModInt1000000007::new(0);
            a += &ModInt1000000007::new(1);
            assert_eq!(a.value(), 1);
            a += 1;
            assert_eq!(a.value(), 2);
            a += &1;
            assert_eq!(a.value(), 3);
        }
        {
            let mut a = ModInt1000000007::new(3);
            a -= &ModInt1000000007::new(1);
            assert_eq!(a.value(), 2);
            a -= 1;
            assert_eq!(a.value(), 1);
            a -= &1;
            assert_eq!(a.value(), 0);
        }
        {
            let mut a = ModInt1000000007::new(1);
            a *= &ModInt1000000007::new(2);
            assert_eq!(a.value(), 2);
            a *= 2;
            assert_eq!(a.value(), 4);
            a *= &2;
            assert_eq!(a.value(), 8);
        }
    }

    #[test]
    fn static_modint_sum() {
        fn sum(values: impl AsRef<[i32]>) -> ModInt1000000007 {
            values
                .as_ref()
                .iter()
                .copied()
                .map(ModInt1000000007::new)
                .sum()
        }

        assert_eq!(sum([-1, 2, -3, 4, -5]), ModInt1000000007::new(-3));
    }

    #[test]
    fn static_modint_product() {
        fn product(values: impl AsRef<[i32]>) -> ModInt1000000007 {
            values
                .as_ref()
                .iter()
                .copied()
                .map(ModInt1000000007::new)
                .product()
        }

        assert_eq!(product([-1, 2, -3, 4, -5]), ModInt1000000007::new(-120));
    }
}
