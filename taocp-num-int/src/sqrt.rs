/// 負数が渡された場合、panic する。
pub trait Sqrt {
    fn sqrt_floor(&self) -> Self;
    fn sqrt_ceil(&self) -> Self;
}

macro_rules! impl_sqrt_for_signed {
    ($($ty:ty),*) => {
        $(
            impl Sqrt for $ty {
                fn sqrt_floor(&self) -> Self {
                    assert!(*self >= 0);
                    self.sqrt_floor_impl()
                }
                fn sqrt_ceil(&self) -> Self {
                    assert!(*self >= 0);
                    self.sqrt_ceil_impl()
                }
            }
        )*
    };
}

macro_rules! impl_sqrt_for_unsigned {
    ($($ty:ty),*) => {
        $(
            impl Sqrt for $ty {
                fn sqrt_floor(&self) -> Self {
                    self.sqrt_floor_impl()
                }
                fn sqrt_ceil(&self) -> Self {
                    self.sqrt_ceil_impl()
                }
            }
        )*
    };
}

impl_sqrt_for_signed!(i8, i16, i32, i64, i128, isize);
impl_sqrt_for_unsigned!(u8, u16, u32, u64, u128, usize);

/// 負数チェックを済ませた後の実装。
trait SqrtImpl {
    fn sqrt_floor_impl(&self) -> Self;
    fn sqrt_ceil_impl(&self) -> Self;
}

macro_rules! impl_sqrt_impl_f64_sqrt {
    ($($ty:ty),*) => {
        $(
            impl SqrtImpl for $ty {
                fn sqrt_floor_impl(&self) -> Self {
                    f64::from(*self).sqrt().floor() as $ty
                }
                fn sqrt_ceil_impl(&self) -> Self {
                    f64::from(*self).sqrt().ceil() as $ty
                }
            }
        )*
    };
}

impl_sqrt_impl_f64_sqrt!(i8, i16, i32, u8, u16, u32);

macro_rules! impl_sqrt_impl_newton {
    ($($ty:ty),*) => {
        $(
            impl SqrtImpl for $ty {
                fn sqrt_floor_impl(&self) -> Self {
                    if *self <= 1 {
                        return *self;
                    }

                    let s = expo2_ge_sqrt(*self);
                    let mut g0 = 1 << s;
                    let mut g1 = (g0 + (self >> s)) >> 1;

                    while g1 < g0 {
                        g0 = g1;
                        g1 = (g0 + self / g0) >> 1;
                    }

                    g0
                }

                fn sqrt_ceil_impl(&self) -> Self {
                    let r = self.sqrt_floor_impl();

                    if r * r == *self {
                        r
                    } else {
                        r + 1
                    }
                }
            }
        )*
    }
}

impl_sqrt_impl_newton!(i64, i128, isize, u64, u128, usize);

/// sqrt(x) 以上の最小の2の冪の指数を返す。
/// x >= 1 を仮定する。
fn expo2_ge_sqrt<T: num_traits::PrimInt>(x: T) -> u32 {
    8 * std::mem::size_of::<T>() as u32 / 2 - ((x - T::one()).leading_zeros() / 2)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cases_floor_basic<T: From<u8>>() -> impl Iterator<Item = (T, T)> {
        const CASES: &[(u8, u8)] = &[
            (0, 0),
            (1, 1),
            (2, 1),
            (3, 1),
            (4, 2),
            (5, 2),
            (8, 2),
            (9, 3),
            (10, 3),
            (15, 3),
            (16, 4),
            (17, 4),
        ];

        CASES
            .iter()
            .copied()
            .map(|(x, expect)| (T::from(x), T::from(expect)))
    }

    fn cases_ceil_basic<T: From<u8>>() -> impl Iterator<Item = (T, T)> {
        const CASES: &[(u8, u8)] = &[
            (0, 0),
            (1, 1),
            (2, 2),
            (3, 2),
            (4, 2),
            (5, 3),
            (8, 3),
            (9, 3),
            (10, 4),
            (15, 4),
            (16, 4),
            (17, 5),
        ];

        CASES
            .iter()
            .copied()
            .map(|(x, expect)| (T::from(x), T::from(expect)))
    }

    #[test]
    fn sqrt_floor_i32() {
        for (x, expect) in cases_floor_basic::<i32>() {
            assert_eq!(x.sqrt_floor(), expect);
        }

        assert_eq!(((1_i32 << 30) - 1).sqrt_floor(), (1 << 15) - 1);
        assert_eq!((1_i32 << 30).sqrt_floor(), 1 << 15);
        assert_eq!(((1_i32 << 30) + 1).sqrt_floor(), 1 << 15);

        assert_eq!(i32::max_value().sqrt_floor(), 46340);
    }

    #[test]
    fn sqrt_ceil_i32() {
        for (x, expect) in cases_ceil_basic::<i32>() {
            assert_eq!(x.sqrt_ceil(), expect);
        }

        assert_eq!(((1_i32 << 30) - 1).sqrt_ceil(), 1 << 15);
        assert_eq!((1_i32 << 30).sqrt_ceil(), 1 << 15);
        assert_eq!(((1_i32 << 30) + 1).sqrt_ceil(), (1 << 15) + 1);

        assert_eq!(i32::max_value().sqrt_ceil(), 46341);
    }

    #[test]
    fn sqrt_floor_u32() {
        for (x, expect) in cases_floor_basic::<u32>() {
            assert_eq!(x.sqrt_floor(), expect);
        }

        assert_eq!(((1_u32 << 30) - 1).sqrt_floor(), (1 << 15) - 1);
        assert_eq!((1_u32 << 30).sqrt_floor(), 1 << 15);
        assert_eq!(((1_u32 << 30) + 1).sqrt_floor(), 1 << 15);

        assert_eq!(u32::max_value().sqrt_floor(), 65535);
    }

    #[test]
    fn sqrt_ceil_u32() {
        for (x, expect) in cases_ceil_basic::<u32>() {
            assert_eq!(x.sqrt_ceil(), expect);
        }

        assert_eq!(((1_u32 << 30) - 1).sqrt_ceil(), 1 << 15);
        assert_eq!((1_u32 << 30).sqrt_ceil(), 1 << 15);
        assert_eq!(((1_u32 << 30) + 1).sqrt_ceil(), (1 << 15) + 1);

        assert_eq!(u32::max_value().sqrt_ceil(), 65536);
    }

    #[test]
    fn sqrt_floor_i64() {
        for (x, expect) in cases_floor_basic::<i64>() {
            assert_eq!(x.sqrt_floor(), expect);
        }

        assert_eq!(((1_i64 << 62) - 1).sqrt_floor(), (1 << 31) - 1);
        assert_eq!((1_i64 << 62).sqrt_floor(), 1 << 31);
        assert_eq!(((1_i64 << 62) + 1).sqrt_floor(), 1 << 31);

        assert_eq!(i64::max_value().sqrt_floor(), 3_037_000_499);
    }

    #[test]
    fn sqrt_ceil_i64() {
        for (x, expect) in cases_ceil_basic::<i64>() {
            assert_eq!(x.sqrt_ceil(), expect);
        }

        assert_eq!(((1_i64 << 62) - 1).sqrt_ceil(), 1 << 31);
        assert_eq!((1_i64 << 62).sqrt_ceil(), 1 << 31);
        assert_eq!(((1_i64 << 62) + 1).sqrt_ceil(), (1 << 31) + 1);

        assert_eq!(i64::max_value().sqrt_ceil(), 3_037_000_500);
    }

    #[test]
    fn sqrt_floor_u64() {
        for (x, expect) in cases_floor_basic::<u64>() {
            assert_eq!(x.sqrt_floor(), expect);
        }

        assert_eq!(((1_u64 << 62) - 1).sqrt_floor(), (1 << 31) - 1);
        assert_eq!((1_u64 << 62).sqrt_floor(), 1 << 31);
        assert_eq!(((1_u64 << 62) + 1).sqrt_floor(), 1 << 31);

        assert_eq!(u64::max_value().sqrt_floor(), 4_294_967_295);
    }

    #[test]
    fn sqrt_ceil_u64() {
        for (x, expect) in cases_ceil_basic::<u64>() {
            assert_eq!(x.sqrt_ceil(), expect);
        }

        assert_eq!(((1_u64 << 62) - 1).sqrt_ceil(), 1 << 31);
        assert_eq!((1_u64 << 62).sqrt_ceil(), 1 << 31);
        assert_eq!(((1_u64 << 62) + 1).sqrt_ceil(), (1 << 31) + 1);

        assert_eq!(u64::max_value().sqrt_ceil(), 4_294_967_296);
    }
}
