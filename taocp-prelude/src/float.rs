use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{Debug, Display};
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

use num_traits::{
    Bounded, Float, FloatConst, FromPrimitive, Num, NumCast, One, Signed, ToPrimitive, Zero,
};

/// 浮動小数点数に Ord を実装するラッパー。
///
/// FromStr トレイトは NaN をパースしない仕様とする。
#[derive(Clone, Copy, Default)]
pub struct OrdFloat<T>(pub T);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseOrdFloatError {
    ParseFloatError(std::num::ParseFloatError),
    Nan,
}

impl Display for ParseOrdFloatError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ParseFloatError(e) => Display::fmt(e, f),
            Self::Nan => write!(f, "NaN is not permitted"),
        }
    }
}

impl Error for ParseOrdFloatError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::ParseFloatError(e) => Some(e),
            Self::Nan => None,
        }
    }
}

macro_rules! impl_basic_traits {
    ($($ty:ty),*) => {
        $(
            impl Eq for OrdFloat<$ty> {}

            impl PartialEq for OrdFloat<$ty> {
                fn eq(&self, other: &Self) -> bool {
                    if self.0.is_nan() {
                        other.0.is_nan()
                    } else {
                        self.0 == other.0
                    }
                }
            }

            impl PartialEq<$ty> for OrdFloat<$ty> {
                fn eq(&self, other: &$ty) -> bool {
                    self.0 == *other
                }
            }

            impl PartialEq<OrdFloat<$ty>> for $ty {
                fn eq(&self, other: &OrdFloat<$ty>) -> bool {
                    *self == other.0
                }
            }

            impl Ord for OrdFloat<$ty> {
                fn cmp(&self, other: &Self) -> Ordering {
                    let lhs = &self.0;
                    let rhs = &other.0;

                    if let Some(ord) = lhs.partial_cmp(rhs) {
                        ord
                    } else if lhs.is_nan() {
                        if rhs.is_nan() {
                            Ordering::Equal
                        } else {
                            Ordering::Greater
                        }
                    } else {
                        Ordering::Less
                    }
                }
            }

            impl PartialOrd for OrdFloat<$ty> {
                fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                    Some(self.cmp(other))
                }
            }

            impl PartialOrd<$ty> for OrdFloat<$ty> {
                fn partial_cmp(&self, other: &$ty) -> Option<Ordering> {
                    self.0.partial_cmp(other)
                }
            }

            impl PartialOrd<OrdFloat<$ty>> for $ty {
                fn partial_cmp(&self, other: &OrdFloat<$ty>) -> Option<Ordering> {
                    self.partial_cmp(&other.0)
                }
            }

            impl From<$ty> for OrdFloat<$ty> {
                fn from(x: $ty) -> Self {
                    Self(x)
                }
            }

            impl From<OrdFloat<$ty>> for $ty {
                fn from(x: OrdFloat<$ty>) -> Self {
                    x.0
                }
            }

            impl FromStr for OrdFloat<$ty> {
                type Err = ParseOrdFloatError;
                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    match <$ty as FromStr>::from_str(s) {
                        Ok(x) => {
                            if !x.is_nan() {
                                Ok(Self(x))
                            } else {
                                Err(ParseOrdFloatError::Nan)
                            }
                        }
                        Err(e) => Err(ParseOrdFloatError::ParseFloatError(e)),
                    }
                }
            }

            impl Debug for OrdFloat<$ty> {
                fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                    Debug::fmt(&self.0, f)
                }
            }

            impl Display for OrdFloat<$ty> {
                fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                    Display::fmt(&self.0, f)
                }
            }
        )*
    };
}

impl_basic_traits!(f32, f64);

macro_rules! impl_neg {
    ($($ty:ty),*) => {
        $(
            impl Neg for OrdFloat<$ty> {
                type Output = OrdFloat<<$ty as Neg>::Output>;
                fn neg(self) -> Self::Output {
                    OrdFloat(-self.0)
                }
            }
            impl Neg for &OrdFloat<$ty> {
                type Output = OrdFloat<<$ty as Neg>::Output>;
                fn neg(self) -> Self::Output {
                    OrdFloat(-self.0)
                }
            }
        )*
    };
}

impl_neg!(f32, f64);

macro_rules! impl_binary_op {
    (
        $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl $trait<$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = &self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl $trait<&$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: &$rhs_ty) -> Self::Output {
                let $lhs = &self;
                $body
            }
        }
        impl $trait<$rhs_ty> for &$lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl $trait<&$rhs_ty> for &$lhs_ty {
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
        $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl_binary_op!($trait, $method, |$lhs: &$lhs_ty, $rhs: &$rhs_ty| -> $out_ty $body);
        impl_binary_op!($trait, $method, |$rhs: &$rhs_ty, $lhs: &$lhs_ty| -> $out_ty $body);
    };
}

macro_rules! impl_binary_ops {
    ($($ty:ty),*) => {
        $(
            // Add
            impl_binary_op!(Add, add, |lhs: &OrdFloat<$ty>, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 + rhs.0)
            });
            impl_binary_op_commutative!(Add, add, |lhs: &OrdFloat<$ty>, rhs: &$ty| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 + rhs)
            });

            // Sub
            impl_binary_op!(Sub, sub, |lhs: &OrdFloat<$ty>, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 - rhs.0)
            });
            impl_binary_op!(Sub, sub, |lhs: &OrdFloat<$ty>, rhs: &$ty| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 - rhs)
            });
            impl_binary_op!(Sub, sub, |lhs: &$ty, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs - rhs.0)
            });

            // Mul
            impl_binary_op!(Mul, mul, |lhs: &OrdFloat<$ty>, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 * rhs.0)
            });
            impl_binary_op_commutative!(Mul, mul, |lhs: &OrdFloat<$ty>, rhs: &$ty| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 * rhs)
            });

            // Div
            impl_binary_op!(Div, div, |lhs: &OrdFloat<$ty>, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 / rhs.0)
            });
            impl_binary_op!(Div, div, |lhs: &OrdFloat<$ty>, rhs: &$ty| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 / rhs)
            });
            impl_binary_op!(Div, div, |lhs: &$ty, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs / rhs.0)
            });

            // Rem
            impl_binary_op!(Rem, rem, |lhs: &OrdFloat<$ty>, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 % rhs.0)
            });
            impl_binary_op!(Rem, rem, |lhs: &OrdFloat<$ty>, rhs: &$ty| -> OrdFloat<$ty> {
                OrdFloat(lhs.0 % rhs)
            });
            impl_binary_op!(Rem, rem, |lhs: &$ty, rhs: &OrdFloat<$ty>| -> OrdFloat<$ty> {
                OrdFloat(lhs % rhs.0)
            });
        )*
    };
}

impl_binary_ops!(f32, f64);

macro_rules! impl_assign_op {
    (
        $trait:ident, $method:ident,
        |$lhs:ident : &mut $lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| $body:block
    ) => {
        impl $trait<$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: $rhs_ty) {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl $trait<&$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: &$rhs_ty) {
                let $lhs = self;
                $body
            }
        }
    };
}

macro_rules! impl_assign_ops {
    ($($ty:ty),*) => {
        $(
            // AddAssign
            impl_assign_op!(AddAssign, add_assign, |lhs: &mut OrdFloat<$ty>, rhs: &OrdFloat<$ty>| {
                *lhs = *lhs + rhs;
            });
            impl_assign_op!(AddAssign, add_assign, |lhs: &mut OrdFloat<$ty>, rhs: &$ty| {
                *lhs = *lhs + rhs;
            });

            // SubAssign
            impl_assign_op!(SubAssign, sub_assign, |lhs: &mut OrdFloat<$ty>, rhs: &OrdFloat<$ty>| {
                *lhs = *lhs - rhs;
            });
            impl_assign_op!(SubAssign, sub_assign, |lhs: &mut OrdFloat<$ty>, rhs: &$ty| {
                *lhs = *lhs - rhs;
            });

            // MulAssign
            impl_assign_op!(MulAssign, mul_assign, |lhs: &mut OrdFloat<$ty>, rhs: &OrdFloat<$ty>| {
                *lhs = *lhs * rhs;
            });
            impl_assign_op!(MulAssign, mul_assign, |lhs: &mut OrdFloat<$ty>, rhs: &$ty| {
                *lhs = *lhs * rhs;
            });

            // DivAssign
            impl_assign_op!(DivAssign, div_assign, |lhs: &mut OrdFloat<$ty>, rhs: &OrdFloat<$ty>| {
                *lhs = *lhs / rhs;
            });
            impl_assign_op!(DivAssign, div_assign, |lhs: &mut OrdFloat<$ty>, rhs: &$ty| {
                *lhs = *lhs / rhs;
            });

            // RemAssign
            impl_assign_op!(RemAssign, rem_assign, |lhs: &mut OrdFloat<$ty>, rhs: &OrdFloat<$ty>| {
                *lhs = *lhs % rhs;
            });
            impl_assign_op!(RemAssign, rem_assign, |lhs: &mut OrdFloat<$ty>, rhs: &$ty| {
                *lhs = *lhs % rhs;
            });
        )*
    };
}

impl_assign_ops!(f32, f64);

macro_rules! impl_iter_traits {
    ($($ty:ty),*) => {
        $(
            // Sum
            impl Sum for OrdFloat<$ty> {
                fn sum<I>(it: I) -> Self
                where
                    I: Iterator<Item = Self>,
                {
                    Self(it.map(|x| x.0).sum())
                }
            }
            impl<'a> Sum<&'a Self> for OrdFloat<$ty> {
                fn sum<I>(it: I) -> Self
                where
                    I: Iterator<Item = &'a Self>,
                {
                    it.copied().sum()
                }
            }

            // Product
            impl Product for OrdFloat<$ty> {
                fn product<I>(it: I) -> Self
                where
                    I: Iterator<Item = Self>,
                {
                    Self(it.map(|x| x.0).product())
                }
            }
            impl<'a> Product<&'a Self> for OrdFloat<$ty> {
                fn product<I>(it: I) -> Self
                where
                    I: Iterator<Item = &'a Self>,
                {
                    it.copied().product()
                }
            }
        )*
    };
}

impl_iter_traits!(f32, f64);

macro_rules! impl_num_traits {
    ($($ty:ty),*) => {
        $(
            impl Zero for OrdFloat<$ty> {
                fn zero() -> Self {
                    Self(<$ty as Zero>::zero())
                }
                fn is_zero(&self) -> bool {
                    Zero::is_zero(&self.0)
                }
            }

            impl One for OrdFloat<$ty> {
                fn one() -> Self {
                    Self(<$ty as One>::one())
                }
                fn is_one(&self) -> bool {
                    One::is_one(&self.0)
                }
            }

            impl Bounded for OrdFloat<$ty> {
                fn min_value() -> Self {
                    Self(<$ty as Bounded>::min_value())
                }
                fn max_value() -> Self {
                    Self(<$ty as Bounded>::max_value())
                }
            }

            impl FromPrimitive for OrdFloat<$ty> {
                fn from_i8(n:    i8)    -> Option<Self> { <$ty as FromPrimitive>::from_i8(n).map(Self)    }
                fn from_i16(n:   i16)   -> Option<Self> { <$ty as FromPrimitive>::from_i16(n).map(Self)   }
                fn from_i32(n:   i32)   -> Option<Self> { <$ty as FromPrimitive>::from_i32(n).map(Self)   }
                fn from_i64(n:   i64)   -> Option<Self> { <$ty as FromPrimitive>::from_i64(n).map(Self)   }
                fn from_i128(n:  i128)  -> Option<Self> { <$ty as FromPrimitive>::from_i128(n).map(Self)  }
                fn from_isize(n: isize) -> Option<Self> { <$ty as FromPrimitive>::from_isize(n).map(Self) }
                fn from_u8(n:    u8)    -> Option<Self> { <$ty as FromPrimitive>::from_u8(n).map(Self)    }
                fn from_u16(n:   u16)   -> Option<Self> { <$ty as FromPrimitive>::from_u16(n).map(Self)   }
                fn from_u32(n:   u32)   -> Option<Self> { <$ty as FromPrimitive>::from_u32(n).map(Self)   }
                fn from_u64(n:   u64)   -> Option<Self> { <$ty as FromPrimitive>::from_u64(n).map(Self)   }
                fn from_u128(n:  u128)  -> Option<Self> { <$ty as FromPrimitive>::from_u128(n).map(Self)  }
                fn from_usize(n: usize) -> Option<Self> { <$ty as FromPrimitive>::from_usize(n).map(Self) }
            }

            impl ToPrimitive for OrdFloat<$ty> {
                fn to_i8(&self)    -> Option<i8>    { ToPrimitive::to_i8(&self.0)    }
                fn to_i16(&self)   -> Option<i16>   { ToPrimitive::to_i16(&self.0)   }
                fn to_i32(&self)   -> Option<i32>   { ToPrimitive::to_i32(&self.0)   }
                fn to_i64(&self)   -> Option<i64>   { ToPrimitive::to_i64(&self.0)   }
                fn to_i128(&self)  -> Option<i128>  { ToPrimitive::to_i128(&self.0)  }
                fn to_isize(&self) -> Option<isize> { ToPrimitive::to_isize(&self.0) }
                fn to_u8(&self)    -> Option<u8>    { ToPrimitive::to_u8(&self.0)    }
                fn to_u16(&self)   -> Option<u16>   { ToPrimitive::to_u16(&self.0)   }
                fn to_u32(&self)   -> Option<u32>   { ToPrimitive::to_u32(&self.0)   }
                fn to_u64(&self)   -> Option<u64>   { ToPrimitive::to_u64(&self.0)   }
                fn to_u128(&self)  -> Option<u128>  { ToPrimitive::to_u128(&self.0)  }
                fn to_usize(&self) -> Option<usize> { ToPrimitive::to_usize(&self.0) }
            }

            impl Num for OrdFloat<$ty> {
                type FromStrRadixErr = <$ty as num_traits::Num>::FromStrRadixErr;
                fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                    <$ty as Num>::from_str_radix(s, radix).map(Self)
                }
            }

            impl NumCast for OrdFloat<$ty> {
                fn from<T: ToPrimitive>(n: T) -> Option<Self> {
                    <$ty as NumCast>::from(n).map(Self)
                }
            }

            impl Signed for OrdFloat<$ty> {
                fn abs(&self) -> Self {
                    Self(Signed::abs(&self.0))
                }
                fn abs_sub(&self, other: &Self) -> Self {
                    Self(Signed::abs_sub(&self.0, &other.0))
                }
                fn signum(&self) -> Self {
                    Self(Signed::signum(&self.0))
                }
                fn is_positive(&self) -> bool {
                    Signed::is_positive(&self.0)
                }
                fn is_negative(&self) -> bool {
                    Signed::is_negative(&self.0)
                }
            }

            impl Float for OrdFloat<$ty> {
                fn nan() -> Self {
                    Self(<$ty as Float>::nan())
                }
                fn infinity() -> Self {
                    Self(<$ty as Float>::infinity())
                }
                fn neg_infinity() -> Self {
                    Self(<$ty as Float>::neg_infinity())
                }
                fn neg_zero() -> Self {
                    Self(<$ty as Float>::neg_zero())
                }
                fn min_value() -> Self {
                    Self(<$ty as Float>::min_value())
                }
                fn min_positive_value() -> Self {
                    Self(<$ty as Float>::min_positive_value())
                }
                fn max_value() -> Self {
                    Self(<$ty as Float>::max_value())
                }
                fn is_nan(self) -> bool {
                    Float::is_nan(self.0)
                }
                fn is_infinite(self) -> bool {
                    Float::is_infinite(self.0)
                }
                fn is_finite(self) -> bool {
                    Float::is_finite(self.0)
                }
                fn is_normal(self) -> bool {
                    Float::is_normal(self.0)
                }
                fn classify(self) -> std::num::FpCategory {
                    Float::classify(self.0)
                }
                fn floor(self) -> Self {
                    Self(Float::floor(self.0))
                }
                fn ceil(self) -> Self {
                    Self(Float::ceil(self.0))
                }
                fn round(self) -> Self {
                    Self(Float::round(self.0))
                }
                fn trunc(self) -> Self {
                    Self(Float::trunc(self.0))
                }
                fn fract(self) -> Self {
                    Self(Float::fract(self.0))
                }
                fn abs(self) -> Self {
                    Self(Float::abs(self.0))
                }
                fn signum(self) -> Self {
                    Self(Float::signum(self.0))
                }
                fn is_sign_positive(self) -> bool {
                    Float::is_sign_positive(self.0)
                }
                fn is_sign_negative(self) -> bool {
                    Float::is_sign_negative(self.0)
                }
                fn mul_add(self, a: Self, b: Self) -> Self {
                    Self(Float::mul_add(self.0, a.0, b.0))
                }
                fn recip(self) -> Self {
                    Self(Float::recip(self.0))
                }
                fn powi(self, n: i32) -> Self {
                    Self(Float::powi(self.0, n))
                }
                fn powf(self, n: Self) -> Self {
                    Self(Float::powf(self.0, n.0))
                }
                fn sqrt(self) -> Self {
                    Self(Float::sqrt(self.0))
                }
                fn exp(self) -> Self {
                    Self(Float::exp(self.0))
                }
                fn exp2(self) -> Self {
                    Self(Float::exp2(self.0))
                }
                fn ln(self) -> Self {
                    Self(Float::ln(self.0))
                }
                fn log(self, base: Self) -> Self {
                    Self(Float::log(self.0, base.0))
                }
                fn log2(self) -> Self {
                    Self(Float::log2(self.0))
                }
                fn log10(self) -> Self {
                    Self(Float::log10(self.0))
                }
                fn max(self, other: Self) -> Self {
                    Self(Float::max(self.0, other.0))
                }
                fn min(self, other: Self) -> Self {
                    Self(Float::min(self.0, other.0))
                }
                fn abs_sub(self, other: Self) -> Self {
                    Self(Float::abs_sub(self.0, other.0))
                }
                fn cbrt(self) -> Self {
                    Self(Float::cbrt(self.0))
                }
                fn hypot(self, other: Self) -> Self {
                    Self(Float::hypot(self.0, other.0))
                }
                fn sin(self) -> Self {
                    Self(Float::sin(self.0))
                }
                fn cos(self) -> Self {
                    Self(Float::cos(self.0))
                }
                fn tan(self) -> Self {
                    Self(Float::tan(self.0))
                }
                fn asin(self) -> Self {
                    Self(Float::asin(self.0))
                }
                fn acos(self) -> Self {
                    Self(Float::acos(self.0))
                }
                fn atan(self) -> Self {
                    Self(Float::atan(self.0))
                }
                fn atan2(self, other: Self) -> Self {
                    Self(Float::atan2(self.0, other.0))
                }
                fn sin_cos(self) -> (Self, Self) {
                    let (a, b) = Float::sin_cos(self.0);
                    (Self(a), Self(b))
                }
                fn exp_m1(self) -> Self {
                    Self(Float::exp_m1(self.0))
                }
                fn ln_1p(self) -> Self {
                    Self(Float::ln_1p(self.0))
                }
                fn sinh(self) -> Self {
                    Self(Float::sinh(self.0))
                }
                fn cosh(self) -> Self {
                    Self(Float::cosh(self.0))
                }
                fn tanh(self) -> Self {
                    Self(Float::tanh(self.0))
                }
                fn asinh(self) -> Self {
                    Self(Float::asinh(self.0))
                }
                fn acosh(self) -> Self {
                    Self(Float::acosh(self.0))
                }
                fn atanh(self) -> Self {
                    Self(Float::atanh(self.0))
                }
                fn integer_decode(self) -> (u64, i16, i8) {
                    Float::integer_decode(self.0)
                }
                fn epsilon() -> Self {
                    Self(<$ty as Float>::epsilon())
                }
                fn to_degrees(self) -> Self {
                    Self(Float::to_degrees(self.0))
                }
                fn to_radians(self) -> Self {
                    Self(Float::to_radians(self.0))
                }
            }

            impl FloatConst for OrdFloat<$ty> {
                fn E() -> Self {
                    Self(<$ty as FloatConst>::E())
                }
                fn FRAC_1_PI() -> Self {
                    Self(<$ty as FloatConst>::FRAC_1_PI())
                }
                fn FRAC_1_SQRT_2() -> Self {
                    Self(<$ty as FloatConst>::FRAC_1_SQRT_2())
                }
                fn FRAC_2_PI() -> Self {
                    Self(<$ty as FloatConst>::FRAC_2_PI())
                }
                fn FRAC_2_SQRT_PI() -> Self {
                    Self(<$ty as FloatConst>::FRAC_2_SQRT_PI())
                }
                fn FRAC_PI_2() -> Self {
                    Self(<$ty as FloatConst>::FRAC_PI_2())
                }
                fn FRAC_PI_3() -> Self {
                    Self(<$ty as FloatConst>::FRAC_PI_3())
                }
                fn FRAC_PI_4() -> Self {
                    Self(<$ty as FloatConst>::FRAC_PI_4())
                }
                fn FRAC_PI_6() -> Self {
                    Self(<$ty as FloatConst>::FRAC_PI_6())
                }
                fn FRAC_PI_8() -> Self {
                    Self(<$ty as FloatConst>::FRAC_PI_8())
                }
                fn LN_10() -> Self {
                    Self(<$ty as FloatConst>::LN_10())
                }
                fn LN_2() -> Self {
                    Self(<$ty as FloatConst>::LN_2())
                }
                fn LOG10_E() -> Self {
                    Self(<$ty as FloatConst>::LOG10_E())
                }
                fn LOG2_E() -> Self {
                    Self(<$ty as FloatConst>::LOG2_E())
                }
                fn PI() -> Self {
                    Self(<$ty as FloatConst>::PI())
                }
                fn SQRT_2() -> Self {
                    Self(<$ty as FloatConst>::SQRT_2())
                }
            }
        )*
    };
}

impl_num_traits!(f32, f64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ord_float_eq() {
        assert_eq!(OrdFloat(0.), OrdFloat(0.));
        assert_ne!(OrdFloat(0.), OrdFloat(1.));
        assert_ne!(OrdFloat(0.), OrdFloat::nan());
        assert_ne!(OrdFloat::nan(), OrdFloat(0.));
        assert_eq!(OrdFloat::<f32>::nan(), OrdFloat::<f32>::nan());

        assert_eq!(OrdFloat(0.), 0.);
        assert_eq!(0., OrdFloat(0.));
        assert_ne!(OrdFloat(0.), 1.);
        assert_ne!(1., OrdFloat(0.));
        assert_ne!(OrdFloat(0.), f32::nan());
        assert_ne!(f32::nan(), OrdFloat(0.));
        assert_ne!(OrdFloat::nan(), 0.);
        assert_ne!(0., OrdFloat::nan());
        assert_ne!(OrdFloat::nan(), f32::nan());
        assert_ne!(f32::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_ord() {
        assert!(OrdFloat(0.) < OrdFloat(1.));
        assert!(OrdFloat(0.) < OrdFloat::nan());

        assert!(OrdFloat(0.) < 1.);
        assert!(0. < OrdFloat(1.));
        assert!(!(OrdFloat(0.) < f32::nan()));
        assert!(!(OrdFloat(0.) > f32::nan()));
        assert!(!(f32::nan() < OrdFloat(0.)));
        assert!(!(f32::nan() > OrdFloat(0.)));
        assert!(!(OrdFloat::nan() < f32::nan()));
        assert!(!(OrdFloat::nan() > f32::nan()));
        assert!(!(f32::nan() < OrdFloat::nan()));
        assert!(!(f32::nan() > OrdFloat::nan()));
    }

    #[test]
    fn ord_float_from_str() {
        assert_eq!("0.".parse(), Ok(OrdFloat(0.)));
        assert_eq!("1.".parse(), Ok(OrdFloat(1.)));
        assert_eq!("NaN".parse::<OrdFloat<f32>>(), Err(ParseOrdFloatError::Nan));
        assert!(matches!(
            "abc".parse::<OrdFloat<f32>>(),
            Err(ParseOrdFloatError::ParseFloatError(_))
        ));
    }

    #[test]
    fn ord_float_neg() {
        assert_eq!(-OrdFloat(1.), OrdFloat(-1.));
        assert_eq!(-OrdFloat::<f32>::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_add() {
        assert_eq!(OrdFloat(1.) + OrdFloat(2.), OrdFloat(3.));
        assert_eq!(OrdFloat(1.) + OrdFloat::nan(), OrdFloat::nan());
        assert_eq!(OrdFloat::nan() + OrdFloat(1.), OrdFloat::nan());
        assert_eq!(OrdFloat::<f32>::nan() + OrdFloat::nan(), OrdFloat::nan());

        #[allow(clippy::op_ref)]
        {
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), OrdFloat(1.) + &OrdFloat(2.));
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &OrdFloat(1.) + OrdFloat(2.));
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &OrdFloat(1.) + &OrdFloat(2.));

            assert_eq!(OrdFloat(1.) + OrdFloat(2.), OrdFloat(1.) + 2.);
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), OrdFloat(1.) + &2.);
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &OrdFloat(1.) + 2.);
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &OrdFloat(1.) + &2.);

            assert_eq!(OrdFloat(1.) + OrdFloat(2.), 1. + OrdFloat(2.));
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), 1. + &OrdFloat(2.));
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &1. + OrdFloat(2.));
            assert_eq!(OrdFloat(1.) + OrdFloat(2.), &1. + &OrdFloat(2.));
        }
    }

    #[test]
    fn ord_float_sub() {
        assert_eq!(OrdFloat(3.) - OrdFloat(1.), OrdFloat(2.));
        assert_eq!(OrdFloat(1.) - OrdFloat::nan(), OrdFloat::nan());
        assert_eq!(OrdFloat::nan() - OrdFloat(1.), OrdFloat::nan());
        assert_eq!(OrdFloat::<f32>::nan() - OrdFloat::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_mul() {
        assert_eq!(OrdFloat(2.) * OrdFloat(3.), OrdFloat(6.));
        assert_eq!(OrdFloat(1.) * OrdFloat::nan(), OrdFloat::nan());
        assert_eq!(OrdFloat::nan() * OrdFloat(1.), OrdFloat::nan());
        assert_eq!(OrdFloat::<f32>::nan() * OrdFloat::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_div() {
        assert_eq!(OrdFloat(6.) / OrdFloat(2.), OrdFloat(3.));
        assert_eq!(OrdFloat(1.) / OrdFloat::nan(), OrdFloat::nan());
        assert_eq!(OrdFloat::nan() / OrdFloat(1.), OrdFloat::nan());
        assert_eq!(OrdFloat::<f32>::nan() / OrdFloat::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_rem() {
        assert_eq!(OrdFloat(5.) % OrdFloat(2.), OrdFloat(1.));
        assert_eq!(OrdFloat(1.) % OrdFloat::nan(), OrdFloat::nan());
        assert_eq!(OrdFloat::nan() % OrdFloat(1.), OrdFloat::nan());
        assert_eq!(OrdFloat::<f32>::nan() % OrdFloat::nan(), OrdFloat::nan());
    }

    #[test]
    fn ord_float_add_assign() {
        let mut x = OrdFloat(1.);
        x += OrdFloat(2.);
        assert_eq!(x, OrdFloat(3.));
    }

    #[test]
    fn ord_float_sub_assign() {
        let mut x = OrdFloat(3.);
        x -= OrdFloat(1.);
        assert_eq!(x, OrdFloat(2.));
    }

    #[test]
    fn ord_float_mul_assign() {
        let mut x = OrdFloat(2.);
        x *= OrdFloat(3.);
        assert_eq!(x, OrdFloat(6.));
    }

    #[test]
    fn ord_float_div_assign() {
        let mut x = OrdFloat(6.);
        x /= OrdFloat(2.);
        assert_eq!(x, OrdFloat(3.));
    }

    #[test]
    fn ord_float_rem_assign() {
        let mut x = OrdFloat(5.);
        x %= OrdFloat(2.);
        assert_eq!(x, OrdFloat(1.));
    }

    #[test]
    fn ord_float_sum() {
        assert_eq!(
            vec![1., 2., 3., 4., 5.]
                .into_iter()
                .map(OrdFloat)
                .sum::<OrdFloat<_>>(),
            OrdFloat(15.)
        );
    }

    #[test]
    fn ord_float_product() {
        assert_eq!(
            vec![1., 2., 3., 4., 5.]
                .into_iter()
                .map(OrdFloat)
                .product::<OrdFloat<_>>(),
            OrdFloat(120.)
        );
    }
}
