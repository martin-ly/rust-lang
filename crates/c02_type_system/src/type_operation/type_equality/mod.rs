//! 类型相等：类型别名在 Rust 类型系统中与原名完全等价。

use std::mem::size_of;

/// [`Alias`] 与 [`i32`] 是同一类型。
pub type Alias = i32;

/// 验证别名与原名大小相同。
pub fn alias_same_size() -> bool {
    size_of::<Alias>() == size_of::<i32>()
}

/// 接受实现 `Add` 的泛型值，展示别名可替换原名使用。
pub fn double<T>(x: T) -> T
where
    T: std::ops::Add<Output = T> + Copy,
{
    x + x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alias_replaces_original() {
        let v: Alias = 21;
        assert_eq!(double(v), 42);
        assert!(alias_same_size());
    }
}
