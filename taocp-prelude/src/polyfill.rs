/// https://doc.rust-lang.org/std/primitive.slice.html#method.partition_point
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

/// https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.reduce
pub trait ReduceExt {
    type Item;

    fn reduce<F>(self, f: F) -> Option<Self::Item>
    where
        F: FnMut(Self::Item, Self::Item) -> Self::Item;
}

impl<T> ReduceExt for T
where
    T: Iterator,
{
    type Item = T::Item;

    fn reduce<F>(mut self, f: F) -> Option<Self::Item>
    where
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
    {
        let ini = self.next()?;
        Some(self.fold(ini, f))
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

    #[test]
    fn reduce_ext() {
        assert_eq!((0..0).reduce(std::ops::Add::add), None);
        assert_eq!((0..=0).reduce(std::ops::Add::add), Some(0));
        assert_eq!((1..=10).reduce(std::ops::Add::add), Some(55));
    }
}
