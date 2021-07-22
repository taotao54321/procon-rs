pub trait IterExt: Iterator {
    fn scanl<Lhs, F>(self, ini: Lhs, f: F) -> Scanl<Self, Lhs, F>
    where
        Self: Sized,
        F: FnMut(&Lhs, &Self::Item) -> Lhs,
    {
        Scanl::new(self, ini, f)
    }

    fn scanl1<F>(self, f: F) -> Scanl1<Self, Self::Item, F>
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Self::Item,
    {
        Scanl1::new(self, f)
    }
}

impl<T: ?Sized> IterExt for T where T: Iterator {}

#[derive(Clone)]
pub struct Scanl<I, Lhs, F> {
    it: I,
    f: F,
    lhs: Option<Lhs>,
}

impl<I, Lhs, F> Scanl<I, Lhs, F> {
    fn new(it: I, ini: Lhs, f: F) -> Self {
        Self {
            it,
            f,
            lhs: Some(ini),
        }
    }
}

impl<I, Lhs, F> Iterator for Scanl<I, Lhs, F>
where
    I: Iterator,
    F: FnMut(&Lhs, &I::Item) -> Lhs,
{
    type Item = Lhs;

    fn next(&mut self) -> Option<Self::Item> {
        let lhs = self.lhs.take()?;

        if let Some(rhs) = self.it.next() {
            let lhs_new = (self.f)(&lhs, &rhs);
            self.lhs = Some(lhs_new);
        }

        Some(lhs)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lb, ub) = self.it.size_hint();
        (lb + 1, ub.map(|ub| ub + 1))
    }
}

#[derive(Clone)]
pub struct Scanl1<I, T, F> {
    it: I,
    f: F,
    lhs: Option<T>,
    is_first: bool,
}

impl<I, T, F> Scanl1<I, T, F>
where
    I: Iterator<Item = T>,
{
    fn new(it: I, f: F) -> Self {
        Self {
            it,
            f,
            lhs: None,
            is_first: true,
        }
    }
}

impl<I, T, F> Iterator for Scanl1<I, T, F>
where
    I: Iterator<Item = T>,
    F: FnMut(&T, &T) -> T,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.lhs = Some(self.it.next())?;
            self.is_first = false;
        }

        let lhs = self.lhs.take()?;

        if let Some(rhs) = self.it.next() {
            let lhs_new = (self.f)(&lhs, &rhs);
            self.lhs = Some(lhs_new);
        }

        Some(lhs)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use super::*;

    #[derive(Debug, Eq, PartialEq)]
    struct X(i32);
    impl X {
        fn add(lhs: &X, rhs: &X) -> X {
            X(lhs.0 + rhs.0)
        }
    }

    #[test]
    fn test_scanl() {
        assert_equal(std::iter::empty().scanl(0, |x, y| x + y), vec![0]);
        assert_equal(std::iter::once(1).scanl(0, |x, y| x + y), vec![0, 1]);

        assert_equal(
            (1..=10).scanl(0, |x, y| x + y),
            vec![0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55],
        );

        assert_equal(
            vec![X(1), X(2), X(3)].into_iter().scanl(X(0), X::add),
            vec![X(0), X(1), X(3), X(6)],
        );
    }

    #[test]
    fn test_scanl1() {
        assert_equal(std::iter::empty::<i32>().scanl1(|x, y| x + y), vec![]);
        assert_equal(std::iter::once(0).scanl1(|x, y| x + y), vec![0]);

        assert_equal(
            (1..=10).scanl1(|x, y| x + y),
            vec![1, 3, 6, 10, 15, 21, 28, 36, 45, 55],
        );

        assert_equal(
            vec![X(1), X(2), X(3)].into_iter().scanl1(X::add),
            vec![X(1), X(3), X(6)],
        );
    }
}
