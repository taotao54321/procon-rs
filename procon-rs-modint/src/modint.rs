//! 法は 2^31 以下であることを仮定している。そうでない場合の挙動は未定義。

use std::marker::PhantomData;

pub type ModInt1000000007 = StaticModInt<Mod1000000007>;
pub type ModInt1000000009 = StaticModInt<Mod1000000009>;
pub type ModInt998244353 = StaticModInt<Mod998244353>;

pub struct StaticModInt<M> {
    value: u32,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: StaticModulus> StaticModInt<M> {
    pub fn modulus() -> u32 {
        M::VALUE
    }

    pub fn new_unchecked(value: u32) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    pub fn new<V: RemEuclidU32>(value: V) -> Self {
        Self::new_unchecked(value.rem_euclid_u32(M::VALUE))
    }

    pub fn value(self) -> u32 {
        self.value
    }

    /// 0^0 は 1 を返す。
    pub fn pow(self, mut e: u64) -> Self {
        let mut res = Self::new_unchecked(1);

        let mut x = self;
        loop {
            if e & 1 != 0 {
                res *= x;
            }
            e >>= 1;
            if e == 0 {
                break;
            }
            x *= x;
        }

        res
    }
}

pub trait StaticModulus {
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

pub trait RemEuclidU32 {
    fn rem_euclid_u32(self, modulus: u32) -> u32;
}

macro_rules! impl_rem_euclid_u32_for_into_i64 {
    ($($ty:ty),*) => {
        $(
            impl RemEuclidU32 for $ty {
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    i64::from(self).rem_euclid(i64::from(modulus)) as u32
                }
            }
        )*
    };
}

impl_rem_euclid_u32_for_into_i64!(i8, i16, i32, i64);

impl RemEuclidU32 for i128 {
    fn rem_euclid_u32(self, modulus: u32) -> u32 {
        self.rem_euclid(i128::from(modulus)) as u32
    }
}

impl RemEuclidU32 for isize {
    fn rem_euclid_u32(self, modulus: u32) -> u32 {
        (self as i64).rem_euclid(i64::from(modulus)) as u32
    }
}

macro_rules! impl_rem_euclid_u32_for_into_u32 {
    ($($ty:ty),*) => {
        $(
            impl RemEuclidU32 for $ty {
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    u32::from(self) % modulus
                }
            }
        )*
    };
}

macro_rules! impl_rem_euclid_u32_for_from_u32 {
    ($($ty:ty),*) => {
        $(
            impl RemEuclidU32 for $ty {
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    (self % <$ty>::from(modulus)) as u32
                }
            }
        )*
    };
}

impl_rem_euclid_u32_for_into_u32!(u8, u16, u32);
impl_rem_euclid_u32_for_from_u32!(u64, u128);

impl RemEuclidU32 for usize {
    fn rem_euclid_u32(self, modulus: u32) -> u32 {
        ((self as u64) % u64::from(modulus)) as u32
    }
}

impl<M: StaticModulus> Clone for StaticModInt<M> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<M: StaticModulus> Copy for StaticModInt<M> {}

impl<M: StaticModulus> PartialEq for StaticModInt<M> {
    fn eq(&self, rhs: &Self) -> bool {
        self.value == rhs.value
    }
}

impl<M: StaticModulus> Eq for StaticModInt<M> {}

impl<M: StaticModulus> std::hash::Hash for StaticModInt<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<M: StaticModulus> Default for StaticModInt<M> {
    fn default() -> Self {
        Self::new_unchecked(0)
    }
}

impl<M: StaticModulus, V: RemEuclidU32> From<V> for StaticModInt<M> {
    fn from(value: V) -> Self {
        Self::new(value)
    }
}

impl<M: StaticModulus> std::str::FromStr for StaticModInt<M> {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<i64>().map(Self::new)
    }
}

impl<M: StaticModulus> std::fmt::Debug for StaticModInt<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Debug::fmt(&self.value, f)
    }
}

impl<M: StaticModulus> std::fmt::Display for StaticModInt<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        std::fmt::Display::fmt(&self.value, f)
    }
}

macro_rules! impl_unary_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$this:ident : &$this_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait for $this_ty {
            type Output = $out_ty;
            fn $method(self) -> Self::Output {
                let $this = &self;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait for &$this_ty {
            type Output = $out_ty;
            fn $method(self) -> Self::Output {
                let $this = self;
                $body
            }
        }
    };
}

macro_rules! impl_binary_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = &self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: &$rhs_ty) -> Self::Output {
                let $lhs = &self;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for &$lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for &$lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: &$rhs_ty) -> Self::Output {
                let $lhs = self;
                $body
            }
        }
    };
}

macro_rules! impl_binary_op_commutative {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl_binary_op!(
            <$($param: $bound),*>, $trait, $method,
            |$lhs: &$lhs_ty, $rhs: &$rhs_ty| -> $out_ty $body
        );
        impl_binary_op!(
            <$($param: $bound),*>, $trait, $method,
            |$rhs: &$rhs_ty, $lhs: &$lhs_ty| -> $out_ty $body
        );
    };
}

macro_rules! impl_binary_op_lhs_rem_euclid_u32 {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i8,    $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i16,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i32,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i64,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i128,  $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &isize, $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u8,    $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u16,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u32,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u64,   $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u128,  $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &usize, $rhs: &$rhs_ty| -> $out_ty $body);
    };
}

macro_rules! impl_binary_op_rhs_rem_euclid_u32 {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident| -> $out_ty:ty $body:block
    ) => {
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i8   | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i16  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i32  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i64  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i128 | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &isize| -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u8   | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u16  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u32  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u64  | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u128 | -> $out_ty $body);
        impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &usize| -> $out_ty $body);
    };
}

macro_rules! impl_binary_op_commutative_rhs_rem_euclid_u32 {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident| -> $out_ty:ty $body:block
    ) => {
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i8   | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i16  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i32  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i64  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i128 | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &isize| -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u8   | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u16  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u32  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u64  | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u128 | -> $out_ty $body);
        impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &usize| -> $out_ty $body);
    };
}

macro_rules! impl_assign_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &mut $lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: $rhs_ty) {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: &$rhs_ty) {
                let $lhs = self;
                $body
            }
        }
    };
}

macro_rules! impl_assign_op_rhs_rem_euclid_u32 {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &mut $lhs_ty:ty, $rhs:ident| $body:block
    ) => {
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i8   | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i16  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i32  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i64  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i128 | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &isize| $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u8   | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u16  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u32  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u64  | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u128 | $body);
        impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &usize| $body);
    };
}

// Neg
impl_unary_op!(<M: StaticModulus>, Neg, neg, |this: &StaticModInt<M>| -> StaticModInt<M> {
    StaticModInt::<M>::new_unchecked(0) - this
});

// Add
impl_binary_op!(<M: StaticModulus>, Add, add, |lhs: &StaticModInt<M>, rhs: &StaticModInt<M>| -> StaticModInt<M> {
    let modulus = M::VALUE;
    let mut value = lhs.value + rhs.value;
    if value >= modulus {
        value -= modulus;
    }
    StaticModInt::<M>::new_unchecked(value)
});
impl_binary_op_commutative_rhs_rem_euclid_u32!(<M: StaticModulus>, Add, add, |lhs: &StaticModInt<M>, rhs| -> StaticModInt<M> {
    lhs + StaticModInt::<M>::new(*rhs)
});

// Sub
impl_binary_op!(<M: StaticModulus>, Sub, sub, |lhs: &StaticModInt<M>, rhs: &StaticModInt<M>| -> StaticModInt<M> {
    let modulus = M::VALUE;
    let mut value = lhs.value.wrapping_sub(rhs.value);
    if value >= modulus {
        value = value.wrapping_add(modulus);
    }
    StaticModInt::<M>::new_unchecked(value)
});
impl_binary_op_lhs_rem_euclid_u32!(<M: StaticModulus>, Sub, sub, |lhs, rhs: &StaticModInt<M>| -> StaticModInt<M> {
    StaticModInt::<M>::new(*lhs) - rhs
});
impl_binary_op_rhs_rem_euclid_u32!(<M: StaticModulus>, Sub, sub, |lhs: &StaticModInt<M>, rhs| -> StaticModInt<M> {
    lhs - StaticModInt::<M>::new(*rhs)
});

// Mul
impl_binary_op!(<M: StaticModulus>, Mul, mul, |lhs: &StaticModInt<M>, rhs: &StaticModInt<M>| -> StaticModInt<M> {
    let value = (u64::from(lhs.value) * u64::from(rhs.value) % u64::from(M::VALUE)) as u32;
    StaticModInt::<M>::new_unchecked(value)
});
impl_binary_op_commutative_rhs_rem_euclid_u32!(<M: StaticModulus>, Mul, mul, |lhs: &StaticModInt<M>, rhs| -> StaticModInt<M> {
    lhs * StaticModInt::<M>::new(*rhs)
});

// AddAssign
impl_assign_op!(<M: StaticModulus>, AddAssign, add_assign, |lhs: &mut StaticModInt<M>, rhs: &StaticModInt<M>| {
    *lhs = *lhs + rhs;
});
impl_assign_op_rhs_rem_euclid_u32!(<M: StaticModulus>, AddAssign, add_assign, |lhs: &mut StaticModInt<M>, rhs| {
    *lhs = *lhs + rhs;
});

// SubAssign
impl_assign_op!(<M: StaticModulus>, SubAssign, sub_assign, |lhs: &mut StaticModInt<M>, rhs: &StaticModInt<M>| {
    *lhs = *lhs - rhs;
});
impl_assign_op_rhs_rem_euclid_u32!(<M: StaticModulus>, SubAssign, sub_assign, |lhs: &mut StaticModInt<M>, rhs| {
    *lhs = *lhs - rhs;
});

// MulAssign
impl_assign_op!(<M: StaticModulus>, MulAssign, mul_assign, |lhs: &mut StaticModInt<M>, rhs: &StaticModInt<M>| {
    *lhs = *lhs * rhs;
});
impl_assign_op_rhs_rem_euclid_u32!(<M: StaticModulus>, MulAssign, mul_assign, |lhs: &mut StaticModInt<M>, rhs| {
    *lhs = *lhs * rhs;
});

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_modint_new() {
        fn f<V: RemEuclidU32>(value: V) -> u32 {
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
        let mut f = move |b: u32| {
            a += ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(f(1), 1);
        assert_eq!(f(2), 3);
        assert_eq!(f(1_000_000_006), 2);
    }

    #[test]
    fn static_modint_sub_assign() {
        let mut a = ModInt1000000007::new(3);
        let mut f = move |b: u32| {
            a -= ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(f(1), 2);
        assert_eq!(f(2), 0);
        assert_eq!(f(1_000_000_006), 1);
    }

    #[test]
    fn static_modint_mul_assign() {
        let mut a = ModInt1000000007::new(1);
        let mut f = move |b: u32| {
            a *= ModInt1000000007::new(b);
            a.value()
        };

        assert_eq!(f(1), 1);
        assert_eq!(f(2), 2);
        assert_eq!(f(3), 6);
        assert_eq!(f(1_000_000_006), 1_000_000_001);
    }

    #[test]
    fn static_modint_unary_op_ergonomics() {
        let a = ModInt1000000007::new(1);

        assert_eq!(-a, -(&a));
    }

    #[test]
    fn static_modint_binary_op_ergonomics() {
        fn f<V: RemEuclidU32>(value: V) -> ModInt1000000007 {
            ModInt1000000007::new(value)
        }

        assert_eq!(f(1) + f(1), f(1) + &f(1));
        assert_eq!(f(1) + f(1), &f(1) + f(1));
        assert_eq!(f(1) + f(1), &f(1) + &f(1));

        assert_eq!(f(1) + f(1), f(1) + 1);
        assert_eq!(f(1) + f(1), f(1) + &1);
        assert_eq!(f(1) + f(1), &f(1) + 1);
        assert_eq!(f(1) + f(1), &f(1) + &1);

        assert_eq!(f(1) + f(1), 1 + f(1));
        assert_eq!(f(1) + f(1), 1 + &f(1));
        assert_eq!(f(1) + f(1), &1 + f(1));
        assert_eq!(f(1) + f(1), &1 + &f(1));

        assert_eq!(f(1) - f(1), f(1) - &f(1));
        assert_eq!(f(1) - f(1), &f(1) - f(1));
        assert_eq!(f(1) - f(1), &f(1) - &f(1));

        assert_eq!(f(1) - f(1), f(1) - 1);
        assert_eq!(f(1) - f(1), f(1) - &1);
        assert_eq!(f(1) - f(1), &f(1) - 1);
        assert_eq!(f(1) - f(1), &f(1) - &1);

        assert_eq!(f(1) - f(1), 1 - f(1));
        assert_eq!(f(1) - f(1), 1 - &f(1));
        assert_eq!(f(1) - f(1), &1 - f(1));
        assert_eq!(f(1) - f(1), &1 - &f(1));

        assert_eq!(f(1) * f(1), f(1) * &f(1));
        assert_eq!(f(1) * f(1), &f(1) * f(1));
        assert_eq!(f(1) * f(1), &f(1) * &f(1));

        assert_eq!(f(1) * f(1), f(1) * 1);
        assert_eq!(f(1) * f(1), f(1) * &1);
        assert_eq!(f(1) * f(1), &f(1) * 1);
        assert_eq!(f(1) * f(1), &f(1) * &1);

        assert_eq!(f(1) * f(1), 1 * f(1));
        assert_eq!(f(1) * f(1), 1 * &f(1));
        assert_eq!(f(1) * f(1), &1 * f(1));
        assert_eq!(f(1) * f(1), &1 * &f(1));
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
}
