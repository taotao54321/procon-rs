macro_rules! impl_basic_traits {
    (<$($param:ident : $bound:tt),*>, $modint:ty) => {
        impl<$($param: $bound),*> ::std::clone::Clone for $modint {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<$($param: $bound),*> ::std::marker::Copy for $modint {}

        impl<$($param: $bound),*> ::std::cmp::PartialEq for $modint {
            fn eq(&self, rhs: &Self) -> bool {
                self.value() == rhs.value()
            }
        }

        impl<$($param: $bound),*> ::std::cmp::Eq for $modint {}

        impl<$($param: $bound),*> ::std::hash::Hash for $modint {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                self.value().hash(state);
            }
        }

        impl<$($param: $bound),*> ::std::default::Default for $modint {
            fn default() -> Self {
                Self::new_unchecked(0)
            }
        }

        impl<$($param: $bound),*, V: $crate::modint_base::RemEuclidU32> ::std::convert::From<V> for $modint {
            fn from(value: V) -> Self {
                Self::new(value)
            }
        }

        impl<$($param: $bound),*> ::std::str::FromStr for $modint {
            type Err = ::std::num::ParseIntError;

            fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
                s.parse::<i64>().map(Self::new)
            }
        }

        impl<$($param: $bound),*> ::std::fmt::Debug for $modint {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::result::Result<(), ::std::fmt::Error> {
                ::std::fmt::Debug::fmt(&self.value(), f)
            }
        }

        impl<$($param: $bound),*> ::std::fmt::Display for $modint {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::result::Result<(), ::std::fmt::Error> {
                ::std::fmt::Display::fmt(&self.value(), f)
            }
        }
    };
}

macro_rules! detail_impl_unary_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$this:ident : &$this_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait for $this_ty {
            type Output = $out_ty;
            fn $method(self) -> Self::Output {
                let $this = &self;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait for &$this_ty {
            type Output = $out_ty;
            fn $method(self) -> Self::Output {
                let $this = self;
                $body
            }
        }
    };
}

macro_rules! detail_impl_binary_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = &self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for $lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: &$rhs_ty) -> Self::Output {
                let $lhs = &self;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for &$lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: $rhs_ty) -> Self::Output {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for &$lhs_ty {
            type Output = $out_ty;
            fn $method(self, $rhs: &$rhs_ty) -> Self::Output {
                let $lhs = self;
                $body
            }
        }
    };
}

macro_rules! detail_impl_binary_op_commutative {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        detail_impl_binary_op!(
            <$($param: $bound),*>, $trait, $method,
            |$lhs: &$lhs_ty, $rhs: &$rhs_ty| -> $out_ty $body
        );
        detail_impl_binary_op!(
            <$($param: $bound),*>, $trait, $method,
            |$rhs: &$rhs_ty, $lhs: &$lhs_ty| -> $out_ty $body
        );
    };
}

macro_rules! detail_impl_binary_op_lhs_prim {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident, $rhs:ident : &$rhs_ty:ty| -> $out_ty:ty $body:block
    ) => {
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i8,    $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i16,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i32,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i64,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &i128,  $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &isize, $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u8,    $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u16,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u32,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u64,   $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &u128,  $rhs: &$rhs_ty| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &usize, $rhs: &$rhs_ty| -> $out_ty $body);
    };
}

macro_rules! detail_impl_binary_op_rhs_prim {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident| -> $out_ty:ty $body:block
    ) => {
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i8   | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i16  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i32  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i64  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i128 | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &isize| -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u8   | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u16  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u32  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u64  | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u128 | -> $out_ty $body);
        detail_impl_binary_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &usize| -> $out_ty $body);
    };
}

macro_rules! detail_impl_binary_op_commutative_rhs_prim {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &$lhs_ty:ty, $rhs:ident| -> $out_ty:ty $body:block
    ) => {
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i8   | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i16  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i32  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i64  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &i128 | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &isize| -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u8   | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u16  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u32  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u64  | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &u128 | -> $out_ty $body);
        detail_impl_binary_op_commutative!(<$($param: $bound),*>, $trait, $method, |$lhs: &$lhs_ty, $rhs: &usize| -> $out_ty $body);
    };
}

macro_rules! detail_impl_assign_op {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &mut $lhs_ty:ty, $rhs:ident : &$rhs_ty:ty| $body:block
    ) => {
        impl<$($param: $bound),*> ::std::ops::$trait<$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: $rhs_ty) {
                let $lhs = self;
                let $rhs = &$rhs;
                $body
            }
        }
        impl<$($param: $bound),*> ::std::ops::$trait<&$rhs_ty> for $lhs_ty {
            fn $method(&mut self, $rhs: &$rhs_ty) {
                let $lhs = self;
                $body
            }
        }
    };
}

macro_rules! detail_impl_assign_op_rhs_prim {
    (
        <$($param:ident : $bound:tt),*>, $trait:ident, $method:ident,
        |$lhs:ident : &mut $lhs_ty:ty, $rhs:ident| $body:block
    ) => {
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i8   | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i16  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i32  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i64  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &i128 | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &isize| $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u8   | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u16  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u32  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u64  | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &u128 | $body);
        detail_impl_assign_op!(<$($param: $bound),*>, $trait, $method, |$lhs: &mut $lhs_ty, $rhs: &usize| $body);
    };
}

macro_rules! impl_ops {
    (<$($param:ident : $bound:tt),*>, $modint:ty) => {
        // Neg
        detail_impl_unary_op!(<$($param: $bound),*>, Neg, neg, |this: &$modint| -> $modint {
            <$modint>::new_unchecked(0) - this
        });

        // Add
        detail_impl_binary_op!(<$($param: $bound),*>, Add, add, |lhs: &$modint, rhs: &$modint| -> $modint {
            <$modint>::add_impl(*lhs, *rhs)
        });
        detail_impl_binary_op_commutative_rhs_prim!(<$($param: $bound),*>, Add, add, |lhs: &$modint, rhs| -> $modint {
            lhs + <$modint>::new(*rhs)
        });

        // Sub
        detail_impl_binary_op!(<$($param: $bound),*>, Sub, sub, |lhs: &$modint, rhs: &$modint| -> $modint {
            <$modint>::sub_impl(*lhs, *rhs)
        });
        detail_impl_binary_op_lhs_prim!(<$($param: $bound),*>, Sub, sub, |lhs, rhs: &$modint| -> $modint {
            <$modint>::new(*lhs) - rhs
        });
        detail_impl_binary_op_rhs_prim!(<$($param: $bound),*>, Sub, sub, |lhs: &$modint, rhs| -> $modint {
            lhs - <$modint>::new(*rhs)
        });

        // Mul
        detail_impl_binary_op!(<$($param: $bound),*>, Mul, mul, |lhs: &$modint, rhs: &$modint| -> $modint {
            <$modint>::mul_impl(*lhs, *rhs)
        });
        detail_impl_binary_op_commutative_rhs_prim!(<$($param: $bound),*>, Mul, mul, |lhs: &$modint, rhs| -> $modint {
            lhs * <$modint>::new(*rhs)
        });

        // AddAssign
        detail_impl_assign_op!(<$($param: $bound),*>, AddAssign, add_assign, |lhs: &mut $modint, rhs: &$modint| {
            *lhs = *lhs + rhs;
        });
        detail_impl_assign_op_rhs_prim!(<$($param: $bound),*>, AddAssign, add_assign, |lhs: &mut $modint, rhs| {
            *lhs = *lhs + rhs;
        });

        // SubAssign
        detail_impl_assign_op!(<$($param: $bound),*>, SubAssign, sub_assign, |lhs: &mut $modint, rhs: &$modint| {
            *lhs = *lhs - rhs;
        });
        detail_impl_assign_op_rhs_prim!(<$($param: $bound),*>, SubAssign, sub_assign, |lhs: &mut $modint, rhs| {
            *lhs = *lhs - rhs;
        });

        // MulAssign
        detail_impl_assign_op!(<$($param: $bound),*>, MulAssign, mul_assign, |lhs: &mut $modint, rhs: &$modint| {
            *lhs = *lhs * rhs;
        });
        detail_impl_assign_op_rhs_prim!(<$($param: $bound),*>, MulAssign, mul_assign, |lhs: &mut $modint, rhs| {
            *lhs = *lhs * rhs;
        });
    };
}

macro_rules! impl_iter_traits {
    (<$($param:ident : $bound:tt),*>, $modint:ty) => {
        // Sum
        impl<$($param: $bound),*> ::std::iter::Sum<Self> for $modint {
            fn sum<I>(it: I) -> Self
            where I: ::std::iter::Iterator<Item=Self>,
            {
                it.fold(Self::new_unchecked(0), ::std::ops::Add::add)
            }
        }
        impl<'a, $($param: $bound),*> ::std::iter::Sum<&'a Self> for $modint {
            fn sum<I>(it: I) -> Self
            where I: ::std::iter::Iterator<Item=&'a Self>,
            {
                it.fold(Self::new_unchecked(0), ::std::ops::Add::add)
            }
        }

        // Product
        impl<$($param: $bound),*> ::std::iter::Product<Self> for $modint {
            fn product<I>(it: I) -> Self
            where I: ::std::iter::Iterator<Item=Self>,
            {
                it.fold(Self::new_unchecked(1), ::std::ops::Mul::mul)
            }
        }
        impl<'a, $($param: $bound),*> ::std::iter::Product<&'a Self> for $modint {
            fn product<I>(it: I) -> Self
            where I: ::std::iter::Iterator<Item=&'a Self>,
            {
                it.fold(Self::new_unchecked(1), ::std::ops::Mul::mul)
            }
        }
    };
}

macro_rules! impl_num_traits {
    (<$($param:ident : $bound:tt),*>, $modint:ty) => {
        impl<$($param: $bound),*> ::num_traits::Zero for $modint {
            fn zero() -> Self {
                Self::new_unchecked(0)
            }
            fn is_zero(&self) -> bool {
                self.value() == 0
            }
        }

        impl<$($param: $bound),*> ::num_traits::One for $modint {
            fn one() -> Self {
                Self::new_unchecked(1)
            }
            fn is_one(&self) -> bool {
                self.value() == 1
            }
        }
    };
}
