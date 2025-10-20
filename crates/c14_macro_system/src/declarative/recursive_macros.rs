//! 递归宏实现示例

/// 计数宏 - 递归计算参数个数
///
/// # 示例
///
/// ```
/// # use c14_macro_system::count;
/// assert_eq!(count!(), 0);
/// assert_eq!(count!(1), 1);
/// assert_eq!(count!(1, 2, 3), 3);
/// ```
#[macro_export]
macro_rules! count {
    () => { 0 };
    ($x:expr) => { 1 };
    ($x:expr, $($rest:expr),+ $(,)?) => {
        1 + count!($($rest),+)
    };
}

/// 查找最大值宏
///
/// # 示例
///
/// ```
/// # use c14_macro_system::max;
/// assert_eq!(max!(1, 2, 3), 3);
/// ```
#[macro_export]
macro_rules! max {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+ $(,)?) => {
        {
            let rest_max = max!($($rest),+);
            if $x > rest_max { $x } else { rest_max }
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_count() {
        assert_eq!(count!(), 0);
        assert_eq!(count!(1), 1);
        assert_eq!(count!(1, 2), 2);
        assert_eq!(count!(1, 2, 3, 4, 5), 5);
    }

    #[test]
    fn test_max() {
        assert_eq!(max!(1), 1);
        assert_eq!(max!(1, 5, 3), 5);
        assert_eq!(max!(10, 5, 20, 15), 20);
    }
}

