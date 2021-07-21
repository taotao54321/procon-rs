use std::marker::PhantomData;
use std::sync::atomic;

use crate::modint_base::{ModIntBase, ModIntBaseImpl};

pub type ModIntDynamicDefault = DynamicModInt<ModDynamicDefault>;

pub struct DynamicModInt<M> {
    value: u32,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: DynamicModulus> DynamicModInt<M> {
    pub fn set_modulus(m: u32) {
        M::value().set(m);
    }
}

impl<M: DynamicModulus> ModIntBase for DynamicModInt<M> {
    fn modulus() -> u32 {
        M::value().get()
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

impl<M: DynamicModulus> ModIntBaseImpl for DynamicModInt<M> {}

impl_basic_traits!(<M: DynamicModulus>, DynamicModInt<M>);
impl_ops!(<M: DynamicModulus>, DynamicModInt<M>);
impl_iter_traits!(<M: DynamicModulus>, DynamicModInt<M>);
impl_num_traits!(<M: DynamicModulus>, DynamicModInt<M>);

pub trait DynamicModulus: 'static {
    fn value() -> &'static DynamicModulusValue;
}

pub enum ModDynamicDefault {}
impl DynamicModulus for ModDynamicDefault {
    fn value() -> &'static DynamicModulusValue {
        static VALUE: DynamicModulusValue = DynamicModulusValue::default();
        &VALUE
    }
}

pub struct DynamicModulusValue {
    modulus: atomic::AtomicU32,
}

impl DynamicModulusValue {
    pub const fn new(m: u32) -> Self {
        Self {
            modulus: atomic::AtomicU32::new(m),
        }
    }

    pub const fn default() -> Self {
        Self::new(998_244_353)
    }

    pub fn get(&self) -> u32 {
        self.modulus.load(atomic::Ordering::SeqCst)
    }

    pub fn set(&self, m: u32) {
        self.modulus.store(m, atomic::Ordering::SeqCst);
    }
}

#[cfg(test)]
mod tests {
    use serial_test::serial;

    use super::*;

    type ModInt = ModIntDynamicDefault;

    struct ScopedMod {
        m_orig: u32,
    }
    impl ScopedMod {
        pub fn new(m: u32) -> Self {
            let m_orig = ModInt::modulus();
            ModInt::set_modulus(m);
            Self { m_orig }
        }
    }
    impl Drop for ScopedMod {
        fn drop(&mut self) {
            ModInt::set_modulus(self.m_orig);
        }
    }

    #[test]
    #[serial]
    fn dynamic_modint_new() {
        fn f<V: crate::modint_base::RemEuclidU32>(value: V) -> u32 {
            ModInt::new(value).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(f(0_u32), 0);
        assert_eq!(f(1_u32), 1);
        assert_eq!(f(10008_u32), 1);

        assert_eq!(f(0_u64), 0);
        assert_eq!(f(1_u64), 1);
        assert_eq!(f(10008_u64), 1);
        assert_eq!(f((10007_u64 << 24) + 1), 1);

        assert_eq!(f(0_usize), 0);
        assert_eq!(f(1_usize), 1);
        assert_eq!(f(10008_usize), 1);

        assert_eq!(f(0_i64), 0);
        assert_eq!(f(1_i64), 1);
        assert_eq!(f(10008_i64), 1);
        assert_eq!(f((10007_i64 << 24) + 1), 1);
        assert_eq!(f(-1_i64), 10006);
    }

    #[test]
    #[serial]
    fn dynamic_modint_pow() {
        fn pow(value: u32, e: u64) -> u32 {
            ModInt::new(value).pow(e).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(pow(0, 0), 1);
        assert_eq!(pow(1, 0), 1);
        assert_eq!(pow(1, 1), 1);
        assert_eq!(pow(2, 0), 1);
        assert_eq!(pow(2, 1), 2);
        assert_eq!(pow(2, 2), 4);
        assert_eq!(pow(2, 10), 1024);
        assert_eq!(pow(2, 32), 2924);
        assert_eq!(pow(2, 10006), 1);
    }

    #[test]
    #[serial]
    fn dynamic_modint_inv() {
        fn inv(value: u32) -> u32 {
            ModInt::new(value).inv().value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(inv(1), 1);
        assert_eq!(inv(2), 5004);
        assert_eq!(inv(3), 3336);
        assert_eq!(inv(42), 4527);
        assert_eq!(inv(10006), 10006);
    }

    #[test]
    #[serial]
    fn dynamic_modint_default() {
        let _mod = ScopedMod::new(10007);

        assert_eq!(ModInt::default().value(), 0);
    }

    #[test]
    #[serial]
    fn dynamic_modint_from_str() {
        fn parse(s: &str) -> u32 {
            s.parse::<ModInt>().unwrap().value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(parse("0"), 0);
        assert_eq!(parse("1"), 1);
        assert_eq!(parse("10008"), 1);
        assert_eq!(parse("-1"), 10006);
    }

    #[test]
    #[serial]
    fn dynamic_modint_neg() {
        fn neg(value: u32) -> u32 {
            (-ModInt::new(value)).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(neg(0), 0);
        assert_eq!(neg(1), 10006);
        assert_eq!(neg(10006), 1);
    }

    #[test]
    #[serial]
    fn dynamic_modint_add() {
        fn add(lhs: u32, rhs: u32) -> u32 {
            (ModInt::new(lhs) + ModInt::new(rhs)).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(add(1, 1), 2);
        assert_eq!(add(10006, 2), 1);
    }

    #[test]
    #[serial]
    fn dynamic_modint_sub() {
        fn sub(lhs: u32, rhs: u32) -> u32 {
            (ModInt::new(lhs) - ModInt::new(rhs)).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(sub(2, 1), 1);
        assert_eq!(sub(0, 1), 10006);
    }

    #[test]
    #[serial]
    fn dynamic_modint_mul() {
        fn mul(lhs: u32, rhs: u32) -> u32 {
            (ModInt::new(lhs) * ModInt::new(rhs)).value()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(mul(1, 1), 1);
        assert_eq!(mul(2, 3), 6);
        assert_eq!(mul(1000, 1000), 9307);
    }

    #[test]
    #[serial]
    fn dynamic_modint_add_assign() {
        let _mod = ScopedMod::new(10007);

        let mut a = ModInt::new(0);
        let mut add_assign = move |b: u32| {
            a += ModInt::new(b);
            a.value()
        };

        assert_eq!(add_assign(1), 1);
        assert_eq!(add_assign(2), 3);
        assert_eq!(add_assign(10006), 2);
    }

    #[test]
    #[serial]
    fn dynamic_modint_sub_assign() {
        let _mod = ScopedMod::new(10007);

        let mut a = ModInt::new(3);
        let mut sub_assign = move |b: u32| {
            a -= ModInt::new(b);
            a.value()
        };

        assert_eq!(sub_assign(1), 2);
        assert_eq!(sub_assign(2), 0);
        assert_eq!(sub_assign(10006), 1);
    }

    #[test]
    #[serial]
    fn dynamic_modint_mul_assign() {
        let _mod = ScopedMod::new(10007);

        let mut a = ModInt::new(1);
        let mut mul_assign = move |b: u32| {
            a *= ModInt::new(b);
            a.value()
        };

        assert_eq!(mul_assign(1), 1);
        assert_eq!(mul_assign(2), 2);
        assert_eq!(mul_assign(3), 6);
        assert_eq!(mul_assign(10006), 10001);
    }

    #[test]
    #[serial]
    fn dynamic_modint_unary_op_ergonomics() {
        let _mod = ScopedMod::new(10007);

        let a = ModInt::new(1);

        assert_eq!(-a, -(&a));
    }

    #[test]
    #[serial]
    fn dynamic_modint_binary_op_ergonomics() {
        let _mod = ScopedMod::new(10007);

        fn f(value: u32) -> ModInt {
            ModInt::new(value)
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
    #[serial]
    fn dynamic_modint_assign_op_ergonomics() {
        let _mod = ScopedMod::new(10007);

        {
            let mut a = ModInt::new(0);
            a += &ModInt::new(1);
            assert_eq!(a.value(), 1);
            a += 1;
            assert_eq!(a.value(), 2);
            a += &1;
            assert_eq!(a.value(), 3);
        }
        {
            let mut a = ModInt::new(3);
            a -= &ModInt::new(1);
            assert_eq!(a.value(), 2);
            a -= 1;
            assert_eq!(a.value(), 1);
            a -= &1;
            assert_eq!(a.value(), 0);
        }
        {
            let mut a = ModInt::new(1);
            a *= &ModInt::new(2);
            assert_eq!(a.value(), 2);
            a *= 2;
            assert_eq!(a.value(), 4);
            a *= &2;
            assert_eq!(a.value(), 8);
        }
    }

    #[test]
    #[serial]
    fn dynamic_modint_sum() {
        fn sum(values: impl AsRef<[i32]>) -> ModInt {
            values.as_ref().iter().copied().map(ModInt::new).sum()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(sum([-1, 2, -3, 4, -5]), ModInt::new(-3));
    }

    #[test]
    #[serial]
    fn dynamic_modint_product() {
        fn product(values: impl AsRef<[i32]>) -> ModInt {
            values.as_ref().iter().copied().map(ModInt::new).product()
        }

        let _mod = ScopedMod::new(10007);

        assert_eq!(product([-1, 2, -3, 4, -5]), ModInt::new(-120));
    }
}
