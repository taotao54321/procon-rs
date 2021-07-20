//! 法は 2 以上 2^31 以下であることを仮定している。そうでない場合の挙動は未定義。

#[macro_use]
mod macros;

mod modint_base;
mod modint_static;

pub use modint_base::*;
pub use modint_static::*;
