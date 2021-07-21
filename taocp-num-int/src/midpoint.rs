/// とりあえず値型のみ受け入れる。
/// 値と参照どちらもとれるのが理想だが実装できなかった。
pub fn midpoint_floor<T: Midpoint>(x: T, y: T) -> T {
    x.midpoint_floor(&y)
}

pub trait Midpoint {
    fn midpoint_floor(&self, other: &Self) -> Self;
}

macro_rules! impl_midpoint_for_prims {
    ($($ty:ty),*) => {
        $(
            impl Midpoint for $ty {
                fn midpoint_floor(&self, other: &Self) -> Self {
                    (self & other) + ((self ^ other) >> 1)
                }
            }
        )*
    };
}

impl_midpoint_for_prims!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_midpoint_floor() {
        assert_eq!(midpoint_floor(0, 0), 0);
        assert_eq!(midpoint_floor(0, 1), 0);
        assert_eq!(midpoint_floor(0, 2), 1);
        assert_eq!(midpoint_floor(1, 2), 1);
        assert_eq!(midpoint_floor(12, 18), 15);
        assert_eq!(midpoint_floor(12, 19), 15);
        assert_eq!(midpoint_floor(-1, 0), -1);
        assert_eq!(midpoint_floor(-2, 0), -1);
        assert_eq!(midpoint_floor(-2, -1), -2);
        assert_eq!(midpoint_floor(3, -1), 1);
        assert_eq!(midpoint_floor(4, -1), 1);
        assert_eq!(midpoint_floor(-18, -12), -15);
        assert_eq!(midpoint_floor(-19, -12), -16);

        macro_rules! ty_min {
            ($ty:ty) => {{
                <$ty>::min_value()
            }};
        }
        macro_rules! ty_max {
            ($ty:ty) => {{
                <$ty>::max_value()
            }};
        }

        assert_eq!(midpoint_floor(ty_min!(i32), ty_min!(i32)), ty_min!(i32));
        assert_eq!(midpoint_floor(ty_max!(i32), ty_max!(i32)), ty_max!(i32));
        assert_eq!(midpoint_floor(ty_min!(i32), ty_max!(i32)), -1_i32);

        assert_eq!(midpoint_floor(ty_max!(u32), ty_max!(u32)), ty_max!(u32));
        assert_eq!(midpoint_floor(ty_min!(u32), ty_max!(u32)), ty_max!(u32) / 2);

        assert_eq!(midpoint_floor(ty_min!(i64), ty_min!(i64)), ty_min!(i64));
        assert_eq!(midpoint_floor(ty_max!(i64), ty_max!(i64)), ty_max!(i64));
        assert_eq!(midpoint_floor(ty_min!(i64), ty_max!(i64)), -1_i64);

        assert_eq!(midpoint_floor(ty_max!(u64), ty_max!(u64)), ty_max!(u64));
        assert_eq!(midpoint_floor(ty_min!(u64), ty_max!(u64)), ty_max!(u64) / 2);
    }
}
