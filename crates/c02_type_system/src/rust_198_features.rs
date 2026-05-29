//! Rust 1.98 Nightly 前瞻 —— 类型系统实验特性
#![allow(clippy::incompatible_msrv)]

use std::marker::CoercePointee;
use std::ops::Deref;

/// # Rust 1.98 Nightly 类型系统前瞻
///
/// 本模块展示 nightly 1.98 中可用的前沿类型系统特性：
/// - `derive(CoercePointee)` — 自动生成智能指针的强制转换逻辑
/// - `!` (never type) 显式标注 — 在更多上下文中的类型推导应用
///
/// **⚠️ 所有代码需要 nightly Rust 编译器。**
pub struct Rust198TypeFeatures;

// ============================================================================
// derive(CoercePointee) 演示
// ============================================================================

/// 使用 `#[derive(CoercePointee)]` 创建的自定义智能指针
///
/// `CoercePointee` 自动为智能指针实现 `CoerceUnsized`，
/// 使得 `MyBox<T>` 可以像 `Box<T>` 一样自动从 `T` 协变到 `dyn Trait`。
#[derive(CoercePointee)]
#[repr(transparent)]
pub struct MyBox<'a, #[pointee] T: ?Sized>(&'a T);

impl<'a, T: ?Sized> MyBox<'a, T> {
    /// 创建新的 MyBox
    pub fn new(value: &'a T) -> Self {
        Self(value)
    }
}

impl<'a, T: ?Sized> Deref for MyBox<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.0
    }
}

impl Rust198TypeFeatures {
    /// 使用 `derive(CoercePointee)` 创建自定义智能指针
    ///
    /// `MyBox<T>` 可以像标准库智能指针一样工作，且支持自动 CoerceUnsized。
    pub fn create_smart_pointer(s: &str) -> MyBox<'_, str> {
        MyBox(s)
    }

    /// 使用 never type 显式标注不可达分支
    ///
    /// `Result<T, !>` 表示该操作永远不会失败，match 时不需要处理 Err 分支。
    pub fn infallible_operation() -> Result<i32, !> {
        Ok(42)
    }

    /// 使用 never type 进行穷尽性检查优化
    ///
    /// 当错误类型为 `!` 时，编译器知道 match 的 `Ok` 分支是唯一的，
    /// 可以省略 `_` 通配分支。
    pub fn exhaustive_match(r: Result<i32, !>) -> i32 {
        match r {
            Ok(v) => v,
            // Err(e) => match e {}, // never type 不需要处理，或编译器已知晓
        }
    }

    /// 发散函数返回 never type
    ///
    /// `-> !` 明确表示函数永不返回（panic/exit/loop）。
    pub fn diverging_function() -> ! {
        panic!("This function never returns normally")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_smart_pointer() {
        let s = "world";
        let boxed = Rust198TypeFeatures::create_smart_pointer(s);
        assert_eq!(&*boxed, "world");
    }

    #[test]
    fn test_coerce_pointee_deref() {
        let s = "hello";
        let ptr = MyBox::new(s);
        assert_eq!(&*ptr, "hello");
    }

    #[test]
    fn test_infallible_operation() {
        let result = Rust198TypeFeatures::infallible_operation();
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn test_exhaustive_match() {
        let r: Result<i32, !> = Ok(100);
        assert_eq!(Rust198TypeFeatures::exhaustive_match(r), 100);
    }
}
