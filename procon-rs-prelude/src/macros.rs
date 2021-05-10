#[macro_export]
macro_rules! chmin {
    ($xmin:expr, $x:expr) => {{
        if $x < $xmin {
            $xmin = $x;
            true
        } else {
            false
        }
    }};
}

#[macro_export]
macro_rules! chmax {
    ($xmax:expr, $x:expr) => {{
        if $xmax < $x {
            $xmax = $x;
            true
        } else {
            false
        }
    }};
}

/// 多次元 Vec を作る。
///
/// ```
/// # use procon_rs_prelude::ndvec;
/// let dp = ndvec![0; 2, 3, 4];
/// assert_eq!(dp, vec![vec![vec![0; 4]; 3]; 2]);
/// ```
#[macro_export]
macro_rules! ndvec {
    ($elem:expr; $n:expr) => {{
        ::std::vec![$elem; $n]
    }};
    ($elem:expr; $n:expr, $($ns:expr),+ $(,)?) => {{
        ::std::vec![$crate::ndvec![$elem; $($ns),+]; $n]
    }};
}

/// 競プロ向けデバッグマクロ。std::dbg! の代替品。
///
/// * リリースビルドでは何もしない。
/// * 引数の所有権を奪わない。
/// * 引数が複数あっても1行で出力する。
#[macro_export]
macro_rules! debug {
    ($($x:expr),+ $(,)?) => {{
        #[cfg(debug_assertions)]
        ::std::eprintln!(
            ::std::concat!(
                "[{}:{}]",
                $(" ", ::std::stringify!($x), "={:?}"),+
            ),
            ::std::path::Path::new(::std::file!()).file_name().unwrap().to_str().unwrap(), ::std::line!(), $($x),+
        );
    }};
}

/// 誤って std::dbg! を使うのを防ぐ。
#[macro_export]
macro_rules! dbg {
    ($($_:expr),* $(,)*) => {{
        ::std::compile_error!("DO NOT USE std::dbg! for procon!");
    }};
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_chmin() {
        {
            let mut x = 5;
            assert!(chmin!(x, 3));
            assert_eq!(x, 3);
        }
        {
            let mut x = 5;
            assert!(!chmin!(x, 5));
            assert_eq!(x, 5);
        }
        {
            let mut x = 5;
            assert!(!chmin!(x, 7));
            assert_eq!(x, 5);
        }
    }

    #[test]
    fn test_chmax() {
        {
            let mut x = 5;
            assert!(!chmax!(x, 3));
            assert_eq!(x, 5);
        }
        {
            let mut x = 5;
            assert!(!chmax!(x, 5));
            assert_eq!(x, 5);
        }
        {
            let mut x = 5;
            assert!(chmax!(x, 7));
            assert_eq!(x, 7);
        }
    }

    #[test]
    fn test_ndvec() {
        assert_eq!(ndvec![0; 3], vec![0; 3]);
        assert_eq!(ndvec![0; 2, 3, 4], vec![vec![vec![0; 4]; 3]; 2]);
        assert_eq!(ndvec![0; 2, 3, 4,], vec![vec![vec![0; 4]; 3]; 2]);
    }
}
