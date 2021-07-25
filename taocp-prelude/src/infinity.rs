use crate::float::OrdFloat;

pub trait Inf:
    Copy
    + PartialEq
    + PartialOrd
    + std::fmt::Debug
    + std::fmt::Display
    + std::ops::Neg<Output = Self>
    + num_traits::Signed
{
    const INF: Self;
}

impl Inf for i32 {
    const INF: Self = 1_010_000_011;
}

impl Inf for i64 {
    const INF: Self = 1_010_000_000_000_000_017;
}

impl Inf for f32 {
    const INF: Self = 1e19;
}

impl Inf for f64 {
    const INF: Self = 1e100;
}

impl Inf for OrdFloat<f32> {
    const INF: Self = Self(f32::INF);
}

impl Inf for OrdFloat<f64> {
    const INF: Self = Self(f64::INF);
}
