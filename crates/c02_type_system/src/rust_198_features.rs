//! Rust 1.98 Nightly 前瞻 —— 类型系统实验特性
//! Rust 1.98 Nightly before —— type system feature
#![allow(clippy::incompatible_msrv)]

use std::marker::CoercePointee;
use std::ops::Deref;

/// # Rust 1.98 Nightly 类型系统前瞻
/// # Rust 1.98 Nightly type system before
/// **⚠️ 所有代码需要 nightly Rust 编译器。**
/// **⚠️ all nightly Rust 。**
/// **⚠️ 所有代码Requires nightly Rust 编译器。**
pub struct Rust198TypeFeatures;

// ============================================================================
// derive(CoercePointee) 演示
// ============================================================================

#[derive(CoercePointee)]
#[repr(transparent)]
pub struct MyBox<'a, #[pointee] T: ?Sized>(&'a T);

impl<'a, T: ?Sized> MyBox<'a, T> {
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
    pub fn create_smart_pointer(s: &str) -> MyBox<'_, str> {
        MyBox(s)
    }

    /// 使用 never type 显式标注不可达分支
    /// never type
    /// `Result<T, !>` 表示该操作永远不会失败，match 时不需要处理 Err 分支。
    /// `Result<T,!>` represent this ，match Err 。
    pub fn infallible_operation() -> Result<i32, !> {
        Ok(42)
    }

    /// 使用 never type 进行穷尽性检查优化
    /// never type optimization
    /// Use never type 进行穷尽性Checkoptimization
    /// 可以省略 `_` 通配分支。
    /// can `_` 。
    pub fn exhaustive_match(r: Result<i32, !>) -> i32 {
        match r {
            Ok(v) => v,
            // Err(e) => match e {}, // never type 不需要处理，或编译器已知晓
        }
    }

    /// 发散函数返回 never type
    /// function never type
    /// `-> !` 明确表示函数永不返回（panic/exit/loop）。
    /// `->!` explicit represent function （panic/exit/loop）。
    pub fn diverging_function() -> ! {
        panic!("This function never returns normally")
    }
}

// ============================================================================
// 1.98+ Nightly-only 特性占位模块
// 这些特性需要 nightly Rust 编译器；默认 feature 关闭，不影响稳定版构建。
// 当对应特性稳定后，再将其迁移到稳定模块并补充可编译示例与单元测试。
// ============================================================================

#[cfg(nightly)]
pub mod nightly_placeholders {
    /// Pin ergonomics: `&pin mut T` / `&pin const T`（lang experiment）
    /// Tracking: rust-lang/rust#130494
    pub fn pin_ergonomics_demo(_node: &mut ()) {
        // 假设 nightly 特性启用后，签名可写为 `fn(&pin mut Node)`
        // 自动 pin projection，无需 unsafe
    }

    /// Reborrow traits: 统一 `&mut T`、`Pin<&mut T>`、`&Cell<T>` 的 reborrow
    pub fn reborrow_traits_demo() {
        // 等待 `Reborrow` / `ReborrowMut` trait 设计稳定
    }

    /// Field projections: trait 中表达字段投影
    pub fn field_projection_demo() {
        // 等待 field projection trait / 语言支持
    }

    /// Return Type Notation (RTN): 约束 `impl Trait` 返回类型的关联属性
    pub fn return_type_notation_demo() {
        // `P::process(): Send`
    }

    /// Async Drop: `async fn drop(&mut self)`
    pub fn async_drop_demo() {
        // `impl AsyncDrop for T { async fn drop(&mut self) { ... } }`
    }

    /// Cranelift backend 启用占位
    pub fn cranelift_backend_demo() {
        // `-Zcodegen-backend=cranelift`
    }

    /// Parallel frontend / `-Zthreads=N`
    pub fn parallel_frontend_demo() {
        // `rustc -Zthreads=8`
    }

    /// Public/private dependencies: `serde = { public = true }`
    pub fn public_dependency_demo() {
        // Cargo.toml 中声明 public 依赖
    }

    /// Sized hierarchy / const Sized / SVE 占位
    pub fn sized_hierarchy_demo() {
        // 细化 `Sized` trait 层级、支持 `const Sized`
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
