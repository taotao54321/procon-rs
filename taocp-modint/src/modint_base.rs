pub trait ModIntBase:
    Copy
    + Eq
    + std::hash::Hash
    + Default
    + From<i8>
    + From<i16>
    + From<i32>
    + From<i64>
    + From<i128>
    + From<isize>
    + From<u8>
    + From<u16>
    + From<u32>
    + From<u64>
    + From<u128>
    + From<usize>
    + std::str::FromStr
    + std::fmt::Debug
    + std::fmt::Display
    + std::ops::Neg<Output = Self>
    + std::ops::Add<Self, Output = Self>
    + std::ops::Add<i8, Output = Self>
    + std::ops::Add<i16, Output = Self>
    + std::ops::Add<i32, Output = Self>
    + std::ops::Add<i64, Output = Self>
    + std::ops::Add<i128, Output = Self>
    + std::ops::Add<isize, Output = Self>
    + std::ops::Add<u8, Output = Self>
    + std::ops::Add<u16, Output = Self>
    + std::ops::Add<u32, Output = Self>
    + std::ops::Add<u64, Output = Self>
    + std::ops::Add<u128, Output = Self>
    + std::ops::Add<usize, Output = Self>
    + std::ops::Sub<Self, Output = Self>
    + std::ops::Sub<i8, Output = Self>
    + std::ops::Sub<i16, Output = Self>
    + std::ops::Sub<i32, Output = Self>
    + std::ops::Sub<i64, Output = Self>
    + std::ops::Sub<i128, Output = Self>
    + std::ops::Sub<isize, Output = Self>
    + std::ops::Sub<u8, Output = Self>
    + std::ops::Sub<u16, Output = Self>
    + std::ops::Sub<u32, Output = Self>
    + std::ops::Sub<u64, Output = Self>
    + std::ops::Sub<u128, Output = Self>
    + std::ops::Sub<usize, Output = Self>
    + std::ops::Mul<Self, Output = Self>
    + std::ops::Mul<i8, Output = Self>
    + std::ops::Mul<i16, Output = Self>
    + std::ops::Mul<i32, Output = Self>
    + std::ops::Mul<i64, Output = Self>
    + std::ops::Mul<i128, Output = Self>
    + std::ops::Mul<isize, Output = Self>
    + std::ops::Mul<u8, Output = Self>
    + std::ops::Mul<u16, Output = Self>
    + std::ops::Mul<u32, Output = Self>
    + std::ops::Mul<u64, Output = Self>
    + std::ops::Mul<u128, Output = Self>
    + std::ops::Mul<usize, Output = Self>
    + std::ops::AddAssign<Self>
    + std::ops::AddAssign<i8>
    + std::ops::AddAssign<i16>
    + std::ops::AddAssign<i32>
    + std::ops::AddAssign<i64>
    + std::ops::AddAssign<i128>
    + std::ops::AddAssign<isize>
    + std::ops::AddAssign<u8>
    + std::ops::AddAssign<u16>
    + std::ops::AddAssign<u32>
    + std::ops::AddAssign<u64>
    + std::ops::AddAssign<u128>
    + std::ops::AddAssign<usize>
    + std::ops::SubAssign<Self>
    + std::ops::SubAssign<i8>
    + std::ops::SubAssign<i16>
    + std::ops::SubAssign<i32>
    + std::ops::SubAssign<i64>
    + std::ops::SubAssign<i128>
    + std::ops::SubAssign<isize>
    + std::ops::SubAssign<u8>
    + std::ops::SubAssign<u16>
    + std::ops::SubAssign<u32>
    + std::ops::SubAssign<u64>
    + std::ops::SubAssign<u128>
    + std::ops::SubAssign<usize>
    + std::ops::MulAssign<Self>
    + std::ops::MulAssign<i8>
    + std::ops::MulAssign<i16>
    + std::ops::MulAssign<i32>
    + std::ops::MulAssign<i64>
    + std::ops::MulAssign<i128>
    + std::ops::MulAssign<isize>
    + std::ops::MulAssign<u8>
    + std::ops::MulAssign<u16>
    + std::ops::MulAssign<u32>
    + std::ops::MulAssign<u64>
    + std::ops::MulAssign<u128>
    + std::ops::MulAssign<usize>
    + std::iter::Sum
    + std::iter::Product
    + num_traits::Zero
    + num_traits::One
{
    fn modulus() -> u32;

    fn new_unchecked(value: u32) -> Self;

    fn new<V: RemEuclidU32>(value: V) -> Self {
        let value = value.rem_euclid_u32(Self::modulus());
        Self::new_unchecked(value)
    }

    fn value(self) -> u32;

    /// 0^0 は 1 を返す。
    fn pow(self, mut e: u64) -> Self {
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

    /// self.value() == 0 の場合、panic する。
    /// gcd(self.value(), Self::modulus()) != 1 の場合、panic する。
    fn inv(self) -> Self {
        fn extgcd(a: i32, b: i32) -> (i32, i32) {
            if b == 0 {
                assert_eq!(a, 1);
                return (1, 0);
            }
            let (q, r) = (a / b, a % b);
            let (xx, yy) = extgcd(b, r);
            (yy, xx - q * yy)
        }

        assert_ne!(self.value(), 0);

        let modulus = Self::modulus();
        let x = extgcd(self.value() as i32, modulus as i32).0;
        let value = (if x >= 0 { x } else { x + modulus as i32 }) as u32;
        Self::new_unchecked(value)
    }
}

pub(crate) trait ModIntBaseImpl: ModIntBase {
    fn add_impl(self, rhs: Self) -> Self {
        let modulus = Self::modulus();
        let mut value = self.value() + rhs.value();
        if value >= modulus {
            value -= modulus;
        }
        Self::new_unchecked(value)
    }

    fn sub_impl(self, rhs: Self) -> Self {
        let modulus = Self::modulus();
        let mut value = self.value().wrapping_sub(rhs.value());
        if value >= modulus {
            value = value.wrapping_add(modulus);
        }
        Self::new_unchecked(value)
    }

    fn mul_impl(self, rhs: Self) -> Self {
        let value =
            (u64::from(self.value()) * u64::from(rhs.value()) % u64::from(Self::modulus())) as u32;
        Self::new_unchecked(value)
    }
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
