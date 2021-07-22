// 事故防止のため、符号なし型のみに対応する。

pub trait BitExt {
    fn bit_new_single(i: u32) -> Self;
    fn bit_new_repunit(i: u32) -> Self;

    fn bit_test(&self, i: u32) -> bool;
    fn bit_set_one(&mut self, i: u32) -> bool;
    fn bit_set_zero(&mut self, i: u32) -> bool;
    fn bit_set(&mut self, i: u32, bit: bool) -> bool;
    fn bit_flip(&mut self, i: u32) -> bool;

    fn bit_is_subset_of(&self, other: &Self) -> bool;
    fn bit_is_superset_of(&self, other: &Self) -> bool;
}

macro_rules! impl_bit_ext_for_prims {
    ($($ty:ty),*) => {
        $(
            impl BitExt for $ty {
                fn bit_new_single(i: u32) -> Self {
                    assert!(i < bits_of::<$ty>());
                    1 << i
                }
                fn bit_new_repunit(k: u32) -> Self {
                    assert!(k <= bits_of::<$ty>());
                    if k == 0 { 0 } else { !0 >> (bits_of::<$ty>() - k) }
                }

                fn bit_test(&self, i: u32) -> bool {
                    assert!(i < bits_of::<$ty>());
                    (self & (1 << i)) != 0
                }
                fn bit_set_one(&mut self, i: u32) -> bool {
                    assert!(i < bits_of::<$ty>());
                    let bit_pre = (*self & (1 << i)) != 0;
                    *self |= 1 << i;
                    bit_pre
                }
                fn bit_set_zero(&mut self, i: u32) -> bool {
                    assert!(i < bits_of::<$ty>());
                    let bit_pre = (*self & (1 << i)) != 0;
                    *self &= !(1 << i);
                    bit_pre
                }
                fn bit_set(&mut self, i: u32, bit: bool) -> bool {
                    assert!(i < bits_of::<$ty>());
                    if bit { self.bit_set_one(i) } else { self.bit_set_zero(i) }
                }
                fn bit_flip(&mut self, i: u32) -> bool {
                    assert!(i < bits_of::<$ty>());
                    let bit_pre = (*self & (1 << i)) != 0;
                    *self ^= 1 << i;
                    bit_pre
                }

                fn bit_is_subset_of(&self, other: &Self) -> bool {
                    (self & other) == *self
                }
                fn bit_is_superset_of(&self, other: &Self) -> bool {
                    (self & other) == *other
                }
            }
        )*
    };
}

impl_bit_ext_for_prims!(u8, u16, u32, u64, u128, usize);

/// x 内で 1 が立っているビット位置を昇順に列挙する。
pub fn bit_positions_one<T>(mut x: T) -> impl Iterator<Item = u32>
where
    T: num_traits::PrimInt + num_traits::Unsigned,
{
    std::iter::from_fn(move || {
        if x.is_zero() {
            return None;
        }

        let res = Some(x.trailing_zeros());
        x = x & (x - T::one());
        res
    })
}

/// x の部分集合を昇順に列挙する。
pub fn bit_subsets<T>(x: T) -> impl Iterator<Item = T>
where
    T: num_traits::PrimInt + num_traits::Unsigned + num_traits::WrappingSub,
{
    std::iter::successors(Some(T::zero()), move |&cur| {
        if cur == x {
            None
        } else {
            Some(cur.wrapping_sub(&x) & x)
        }
    })
}

/// x の部分集合を降順に列挙する。
pub fn bit_subsets_rev<T>(x: T) -> impl Iterator<Item = T>
where
    T: num_traits::PrimInt + num_traits::Unsigned,
{
    std::iter::successors(Some(x), move |&cur| {
        if cur.is_zero() {
            None
        } else {
            Some((cur - T::one()) & x)
        }
    })
}

/// univ の部分集合のうち x を包含する集合を昇順に列挙する。
/// x は univ の部分集合でなければならない。
pub fn bit_supersets<T>(univ: T, x: T) -> impl Iterator<Item = T>
where
    T: num_traits::PrimInt + num_traits::Unsigned + num_traits::WrappingSub,
{
    assert!(univ & x == x);

    bit_subsets(univ & !x).map(move |y| y | x)
}

/// univ の部分集合のうち x を包含する集合を降順に列挙する。
/// x は univ の部分集合でなければならない。
pub fn bit_supersets_rev<T>(univ: T, x: T) -> impl Iterator<Item = T>
where
    T: num_traits::PrimInt + num_traits::Unsigned + num_traits::WrappingSub,
{
    assert!(univ & x == x);

    bit_subsets_rev(univ & !x).map(move |y| y | x)
}

/// n ビット中 k 個が 1 である数を昇順に列挙する。
/// n >= k でなければならない。
pub fn bit_combinations<T>(n: u32, k: u32) -> impl Iterator<Item = T>
where
    T: num_traits::PrimInt + num_traits::Unsigned,
{
    assert!(n <= bits_of::<T>());
    assert!(n >= k);

    let (first, last) = if k == 0 {
        (T::zero(), T::zero())
    } else {
        let first = !T::zero() >> ((bits_of::<T>() - k) as usize);
        (first, first << ((n - k) as usize))
    };

    std::iter::successors(Some(first), move |&cur| {
        if cur == last {
            None
        } else {
            let t = cur | (cur - T::one());
            let ctz = cur.trailing_zeros() as usize;
            Some((t + T::one()) | (((!t & (t + T::one())) - T::one()) >> 1 >> ctz))
        }
    })
}

const fn bits_of<T>() -> u32 {
    8 * std::mem::size_of::<T>() as u32
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use super::*;

    #[test]
    fn test_bit_new_single() {
        assert_eq!(u32::bit_new_single(0), 1 << 0);
        assert_eq!(u32::bit_new_single(1), 1 << 1);
        assert_eq!(u32::bit_new_single(2), 1 << 2);
        assert_eq!(u32::bit_new_single(10), 1 << 10);
        assert_eq!(u32::bit_new_single(31), 1 << 31);
    }

    #[test]
    fn test_bit_new_repunit() {
        assert_eq!(u32::bit_new_repunit(0), 0);
        assert_eq!(u32::bit_new_repunit(1), 0b1);
        assert_eq!(u32::bit_new_repunit(2), 0b11);
        assert_eq!(u32::bit_new_repunit(10), (1 << 10) - 1);
        assert_eq!(u32::bit_new_repunit(31), (1 << 31) - 1);
        assert_eq!(u32::bit_new_repunit(32), !0);
    }

    #[test]
    fn test_bit_ext_index_access() {
        let mut x = 0b010_u32;

        assert!(!x.bit_test(0));
        assert!(x.bit_test(1));
        assert!(!x.bit_test(2));

        assert!(!x.bit_set_one(2));
        assert_eq!(x, 0b110);

        assert!(x.bit_set_zero(2));
        assert_eq!(x, 0b010);

        assert!(!x.bit_set(2, true));
        assert_eq!(x, 0b110);
        assert!(x.bit_set(2, false));
        assert_eq!(x, 0b010);

        assert!(!x.bit_flip(2));
        assert_eq!(x, 0b110);
        assert!(x.bit_flip(2));
        assert_eq!(x, 0b010);
    }

    #[test]
    fn test_bit_ext_set_operation() {
        assert!(0_u32.bit_is_subset_of(&0));
        assert!(0_u32.bit_is_subset_of(&1));
        assert!(!1_u32.bit_is_subset_of(&0));
        assert!(1_u32.bit_is_subset_of(&1));
        assert!(0b1001_u32.bit_is_subset_of(&0b11001));
        assert!(!0b1001_u32.bit_is_subset_of(&0b1000));

        assert!(0_u32.bit_is_superset_of(&0));
        assert!(!0_u32.bit_is_superset_of(&1));
        assert!(1_u32.bit_is_superset_of(&0));
        assert!(1_u32.bit_is_superset_of(&1));
        assert!(!0b1001_u32.bit_is_superset_of(&0b11001));
        assert!(0b1001_u32.bit_is_superset_of(&0b1000));
    }

    #[test]
    fn test_bit_positions_one() {
        let x = 0b101101_u32;

        assert_equal(bit_positions_one(x), vec![0, 2, 3, 5]);
    }

    #[test]
    fn test_bit_subsets() {
        assert_equal(bit_subsets(0_u32), vec![0]);
        assert_equal(bit_subsets(1_u32), vec![0, 1]);
        assert_equal(
            bit_subsets(0b11010_u32),
            vec![
                0b00000, 0b00010, 0b01000, 0b01010, 0b10000, 0b10010, 0b11000, 0b11010,
            ],
        );
    }

    #[test]
    fn test_bit_subsets_rev() {
        assert_equal(bit_subsets_rev(0_u32), vec![0]);
        assert_equal(bit_subsets_rev(1_u32), vec![1, 0]);
        assert_equal(
            bit_subsets_rev(0b11010_u32),
            vec![
                0b11010, 0b11000, 0b10010, 0b10000, 0b01010, 0b01000, 0b00010, 0b00000,
            ],
        );
    }

    #[test]
    fn test_bit_supersets() {
        assert_equal(bit_supersets(0_u32, 0_u32), vec![0]);
        assert_equal(bit_supersets(1_u32, 0_u32), vec![0, 1]);
        assert_equal(bit_supersets(1_u32, 1_u32), vec![1]);
        assert_equal(
            bit_supersets(0b11010_u32, 0b01000_u32),
            vec![0b01000, 0b01010, 0b11000, 0b11010],
        );
        assert_equal(bit_supersets(!0_u32, !0_u32 - 1), vec![!0 - 1, !0]);
    }

    #[test]
    fn test_bit_supersets_rev() {
        assert_equal(bit_supersets_rev(0_u32, 0_u32), vec![0]);
        assert_equal(bit_supersets_rev(1_u32, 0_u32), vec![1, 0]);
        assert_equal(bit_supersets_rev(1_u32, 1_u32), vec![1]);
        assert_equal(
            bit_supersets_rev(0b11010_u32, 0b01000_u32),
            vec![0b11010, 0b11000, 0b01010, 0b01000],
        );
        assert_equal(bit_supersets_rev(!0_u32, !0_u32 - 1), vec![!0, !0 - 1]);
    }

    #[test]
    fn test_bit_combinations() {
        assert_equal(bit_combinations::<u32>(0, 0), vec![0]);
        assert_equal(bit_combinations::<u32>(1, 0), vec![0]);
        assert_equal(bit_combinations::<u32>(1, 1), vec![1]);
        assert_equal(bit_combinations::<u32>(2, 1), vec![0b01, 0b10]);
        assert_equal(
            bit_combinations::<u32>(5, 2),
            vec![
                0b00011, 0b00101, 0b00110, 0b01001, 0b01010, 0b01100, 0b10001, 0b10010, 0b10100,
                0b11000,
            ],
        );
        assert_equal(bit_combinations::<u32>(32, 32), vec![!0]);
    }
}
