use num_traits::{One, PrimInt};

use crate::midpoint::midpoint_floor;

/// lo..hi で定義された広義単調減少する述語関数 pred に対し、pred(x) が偽となる最小の x を返す。
/// lo..hi の全てで pred が真となるなら hi を返す。
///
/// lo > hi であってはならない。
pub fn bisect_int<T, F>(mut lo: T, mut hi: T, mut pred: F) -> T
where
    T: PrimInt,
    F: FnMut(T) -> bool,
{
    assert!(lo <= hi);

    while lo != hi {
        let mid = midpoint_floor(lo, hi);

        if pred(mid) {
            lo = mid + One::one();
        } else {
            hi = mid;
        }
    }

    lo
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bisect_int() {
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

        assert_eq!(bisect_int(0, 0, |_| true), 0);
        assert_eq!(bisect_int(0, 0, |_| false), 0);
        assert_eq!(bisect_int(0, 1, |_| true), 1);
        assert_eq!(bisect_int(0, 1, |_| false), 0);
        assert_eq!(
            bisect_int(ty_min!(i32), ty_max!(i32), |_| true),
            ty_max!(i32)
        );
        assert_eq!(
            bisect_int(ty_min!(i32), ty_max!(i32), |_| false),
            ty_min!(i32)
        );
        assert_eq!(bisect_int(ty_min!(i32), ty_max!(i32), |x| x < 10000), 10000);
    }
}
