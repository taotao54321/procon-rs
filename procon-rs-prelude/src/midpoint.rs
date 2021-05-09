use num_traits::PrimInt;

/// floor((x+y)/2) を求める。オーバーフローしない。
pub fn midpoint_floor<T>(x: T, y: T) -> T
where
    T: PrimInt,
{
    (x & y) + ((x ^ y) >> 1)
}

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
