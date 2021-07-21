/// Rust 1.52 で導入されたものと同じ。
pub trait PartitionPointExt {
    type Item;

    fn partition_point<P>(&self, pred: P) -> usize
    where
        P: FnMut(&Self::Item) -> bool;
}

impl<T> PartitionPointExt for [T] {
    type Item = T;

    fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        let mut lo = 0;
        let mut hi = self.len();

        while lo != hi {
            let mid = lo + (hi - lo) / 2;

            let value = unsafe { self.get_unchecked(mid) };
            if pred(value) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        lo
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partition_point_ext() {
        let xs = (0..10).collect::<Vec<_>>();

        assert_eq!(xs.partition_point(|&x| x < 4), 4);
        assert_eq!(xs.partition_point(|&x| x <= 4), 5);
    }
}
