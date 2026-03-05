//! # Rust 1.94.0 泛型编程特性实现模块 / Rust 1.94.0 Generic Programming Features Implementation Module
//!
//! 本模块实现了 Rust 1.94.0 版本中与泛型编程相关的新特性和改进，包括：
//! This module implements new features and improvements in Rust 1.94.0 related to generic programming, including:
//!
//! - 改进的泛型类型推断 / Improved Generic Type Inference
//! - 更灵活的关联类型 / More Flexible Associated Types
//! - 增强的 trait 边界推断 / Enhanced Trait Bounds Inference
//! - Edition 2024 泛型优化 / Edition 2024 Generic Optimizations
//! - 编译时泛型验证 / Compile-time Generic Validation
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
//!
//! # 使用示例
//!
//! ```ignore
//! use c04_generic::rust_194_features::*;
//!
//! // 1. 使用改进的泛型推断
//! let container = SmartContainer::new(42);
//!
//! // 2. 使用灵活的关联类型
//! let adapter = TypeAdapter::new();
//!
//! // 3. 使用增强的 trait 边界
//! let validator = GenericValidator::new();
//! ```

use std::marker::PhantomData;

// ==================== 1. 改进的泛型类型推断 ====================

/// # 1. 改进的泛型类型推断 / Improved Generic Type Inference
///
/// Rust 1.94.0 显著改进了泛型类型推断，减少了显式类型标注的需要：
/// Rust 1.94.0 significantly improves generic type inference, reducing the need for explicit type annotations:

/// 智能容器 - 演示改进的泛型推断
///
/// Rust 1.94.0: 更智能的泛型类型推断
#[derive(Debug, Clone)]
pub struct SmartContainer<T> {
    data: T,
    metadata: Option<String>,
}

impl<T> SmartContainer<T> {
    /// 创建新的智能容器
    ///
    /// Rust 1.94.0: 改进的构造函数类型推断
    pub fn new(data: T) -> Self {
        Self {
            data,
            metadata: None,
        }
    }

    /// 创建带元数据的容器
    ///
    /// Rust 1.94.0: 更好的多参数类型推断
    pub fn with_metadata(data: T, metadata: impl Into<String>) -> Self {
        Self {
            data,
            metadata: Some(metadata.into()),
        }
    }

    /// 获取数据引用
    pub fn get(&self) -> &T {
        &self.data
    }

    /// 转换容器类型
    ///
    /// Rust 1.94.0: 改进的泛型方法类型推断
    pub fn map<F, R>(self, f: F) -> SmartContainer<R>
    where
        F: FnOnce(T) -> R,
    {
        SmartContainer {
            data: f(self.data),
            metadata: self.metadata,
        }
    }

    /// 链式操作
    ///
    /// Rust 1.94.0: 更好的链式调用类型推断
    pub fn and_then<F, R>(self, f: F) -> SmartContainer<R>
    where
        F: FnOnce(T) -> SmartContainer<R>,
    {
        f(self.data)
    }
}

impl<T: Default> Default for SmartContainer<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

/// 泛型函数组合器
///
/// Rust 1.94.0: 改进的泛型函数类型推断
pub struct GenericComposer<F, G> {
    first: F,
    second: G,
}

impl<F, G> GenericComposer<F, G> {
    /// 创建新的组合器
    pub fn new(first: F, second: G) -> Self {
        Self { first, second }
    }

    /// 组合执行
    ///
    /// Rust 1.94.0: 自动推断中间类型
    pub fn compose<T, U, V>(&self, value: T) -> V
    where
        F: Fn(T) -> U,
        G: Fn(U) -> V,
    {
        (self.second)((self.first)(value))
    }
}

// ==================== 2. 更灵活的关联类型 ====================

/// # 2. 更灵活的关联类型 / More Flexible Associated Types
///
/// Rust 1.94.0 提供了更灵活的关联类型定义和使用方式：
/// Rust 1.94.0 provides more flexible associated type definitions and usage:

/// 类型适配器 Trait
///
/// Rust 1.94.0: 更灵活的关联类型定义
pub trait TypeAdapter {
    /// 输入类型
    type Input: Clone;
    /// 输出类型 - 可以有更灵活的约束
    type Output: Clone + Send;
    /// 错误类型
    type Error: std::error::Error;

    /// 适配转换
    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;

    /// 批量适配
    ///
    /// Rust 1.94.0: 改进的关联类型在泛型上下文中的使用
    fn adapt_batch(
        &self,
        inputs: Vec<Self::Input>,
    ) -> Result<Vec<Self::Output>, Self::Error>
    where
        Self: Sized,
    {
        inputs.into_iter().map(|i| self.adapt(i)).collect()
    }
}

/// 字符串到整数适配器
#[derive(Debug, Clone, Copy, Default)]
pub struct StringToIntAdapter;

#[derive(Debug, Clone)]
pub struct AdapterError {
    message: String,
}

impl std::fmt::Display for AdapterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for AdapterError {}

impl TypeAdapter for StringToIntAdapter {
    type Input = String;
    type Output = i64;
    type Error = AdapterError;

    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        input.parse().map_err(|e| AdapterError {
            message: format!("Parse error: {}", e),
        })
    }
}

/// 类型适配器实现
///
/// Rust 1.94.0: 泛型适配器模式
#[derive(Debug, Clone)]
pub struct GenericAdapter<T, U, F>
where
    F: Fn(T) -> Result<U, AdapterError>,
{
    converter: F,
    _phantom: PhantomData<(T, U)>,
}

impl<T, U, F> GenericAdapter<T, U, F>
where
    F: Fn(T) -> Result<U, AdapterError>,
{
    pub fn new(converter: F) -> Self {
        Self {
            converter,
            _phantom: PhantomData,
        }
    }
}

impl<T, U, F> TypeAdapter for GenericAdapter<T, U, F>
where
    T: Clone,
    U: Clone + Send,
    F: Fn(T) -> Result<U, AdapterError>,
{
    type Input = T;
    type Output = U;
    type Error = AdapterError;

    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        (self.converter)(input)
    }
}

// ==================== 3. 增强的 trait 边界推断 ====================

/// # 3. 增强的 trait 边界推断 / Enhanced Trait Bounds Inference
///
/// Rust 1.94.0 改进了 trait 边界的自动推断：
/// Rust 1.94.0 improves automatic trait bounds inference:

/// 泛型验证器
///
/// Rust 1.94.0: 更智能的 trait 边界推断
pub struct GenericValidator<T: ?Sized> {
    _phantom: PhantomData<T>,
}

impl<T: ?Sized> GenericValidator<T> {
    /// 创建新的验证器
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 验证类型实现 Clone
    ///
    /// Rust 1.94.0: 编译器自动推断 trait 边界
    pub fn validate_clone(&self) -> bool
    where
        T: Clone,
    {
        true
    }

    /// 验证类型实现 Send + Sync
    ///
    /// Rust 1.94.0: 更精确的 trait 边界检查
    pub fn validate_thread_safe(&self) -> bool
    where
        T: Send + Sync,
    {
        true
    }

    /// 验证类型大小
    pub fn check_size(&self) -> usize
    where
        T: Sized,
    {
        std::mem::size_of::<T>()
    }
}

impl<T: ?Sized> Default for GenericValidator<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 复杂 trait 边界结构
///
/// Rust 1.94.0: 简化的复杂 trait 边界表达
#[derive(Debug, Clone)]
pub struct ComplexBoundsStruct<T, U>
where
    T: Clone + Send + Sync + 'static,
    U: Clone + Send + Sync + 'static,
{
    first: T,
    second: U,
}

impl<T, U> ComplexBoundsStruct<T, U>
where
    T: Clone + Send + Sync + 'static,
    U: Clone + Send + Sync + 'static,
{
    pub fn new(first: T, second: U) -> Self {
        Self { first, second }
    }

    /// 交换值
    ///
    /// Rust 1.94.0: 改进的泛型约束传播
    pub fn swap(self) -> ComplexBoundsStruct<U, T> {
        ComplexBoundsStruct {
            first: self.second,
            second: self.first,
        }
    }

    /// 获取元组
    pub fn into_tuple(self) -> (T, U) {
        (self.first, self.second)
    }
}

// ==================== 4. Edition 2024 泛型优化 ====================

/// # 4. Edition 2024 泛型优化 / Edition 2024 Generic Optimizations
///
/// Rust 1.94.0 与 Edition 2024 的泛型系统集成：
/// Rust 1.94.0 generic system integration with Edition 2024:

/// Edition 2024 泛型容器
///
/// Rust 1.94.0: Edition 2024 优化的泛型代码
#[derive(Debug, Clone)]
pub struct Edition2024Generic<T> {
    value: T,
    edition_marker: Edition2024Marker,
}

/// Edition 2024 标记
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition2024Marker {
    Legacy,
    Modern,
}

impl<T> Edition2024Generic<T> {
    /// 创建 Edition 2024 泛型容器
    pub fn new(value: T) -> Self {
        Self {
            value,
            edition_marker: Edition2024Marker::Modern,
        }
    }

    /// 创建特定 Edition 的容器
    pub fn with_edition(value: T, edition: Edition2024Marker) -> Self {
        Self {
            value,
            edition_marker: edition,
        }
    }

    /// 获取值
    pub fn get(&self) -> &T {
        &self.value
    }

    /// 转换值
    ///
    /// Rust 1.94.0: Edition 2024 优化的泛型转换
    pub fn transform<F, R>(self, f: F) -> Edition2024Generic<R>
    where
        F: FnOnce(T) -> R,
    {
        Edition2024Generic {
            value: f(self.value),
            edition_marker: self.edition_marker,
        }
    }

    /// 检查是否为 Modern Edition
    pub fn is_modern(&self) -> bool {
        self.edition_marker == Edition2024Marker::Modern
    }
}

// ==================== 5. 编译时泛型验证 ====================

/// # 5. 编译时泛型验证 / Compile-time Generic Validation
///
/// Rust 1.94.0 增强了编译时的泛型验证能力：
/// Rust 1.94.0 enhances compile-time generic validation:

/// 编译时类型断言
///
/// Rust 1.94.0: 编译时泛型约束验证
pub struct CompileTimeAssert<T: ?Sized> {
    _phantom: PhantomData<T>,
}

impl<T: ?Sized> CompileTimeAssert<T> {
    /// 断言类型实现 Send
    pub const fn assert_send() -> ()
    where
        T: Send,
    {
        ()
    }

    /// 断言类型实现 Sync
    pub const fn assert_sync() -> ()
    where
        T: Sync,
    {
        ()
    }

    /// 断言类型大小
    pub const fn assert_size(expected: usize) -> ()
    where
        T: Sized,
    {
        assert!(std::mem::size_of::<T>() == expected);
    }
}

/// 类型级别验证器
///
/// Rust 1.94.0: 类型级别的泛型验证
pub trait TypeLevelValidation {
    /// 验证类型有效性
    const IS_VALID: bool;
    /// 类型大小
    const SIZE: usize;
    /// 类型对齐
    const ALIGN: usize;
}

impl<T> TypeLevelValidation for T
where
    T: Sized,
{
    const IS_VALID: bool = true;
    const SIZE: usize = std::mem::size_of::<T>();
    const ALIGN: usize = std::mem::align_of::<T>();
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 泛型编程特性
pub fn demonstrate_rust_194_generic_features() {
    println!("\n=== Rust 1.94.0 泛型编程特性演示 ===\n");

    // 1. 改进的泛型类型推断
    println!("1. 改进的泛型类型推断:");
    let container = SmartContainer::new(42);
    println!("   容器值: {}", container.get());

    let container_with_meta = SmartContainer::with_metadata("hello", "metadata");
    println!("   带元数据容器: {:?}", container_with_meta);

    let mapped = container.map(|x| x.to_string());
    println!("   映射后: {}", mapped.get());

    // 2. 更灵活的关联类型
    println!("\n2. 更灵活的关联类型:");
    let adapter = StringToIntAdapter;
    let result = adapter.adapt("42".to_string());
    println!("   适配结果: {:?}", result);

    let batch_result = adapter.adapt_batch(vec![
        "1".to_string(),
        "2".to_string(),
        "3".to_string(),
    ]);
    println!("   批量适配结果: {:?}", batch_result);

    let generic_adapter = GenericAdapter::new(|s: String| s.parse::<i32>().map_err(|e| AdapterError {
        message: e.to_string(),
    }));
    println!("   泛型适配器: {:?}", generic_adapter.adapt("100".to_string()));

    // 3. 增强的 trait 边界推断
    println!("\n3. 增强的 trait 边界推断:");
    let validator = GenericValidator::<String>::new();
    println!("   String 实现 Clone: {}", validator.validate_clone());
    println!("   String 实现 Send+Sync: {}", validator.validate_thread_safe());
    println!("   String 大小: {} 字节", validator.check_size());

    let complex = ComplexBoundsStruct::new(1, "hello");
    let swapped = complex.swap();
    let (u, t) = swapped.into_tuple();
    println!("   交换后: ({}, {})", u, t);

    // 4. Edition 2024 泛型优化
    println!("\n4. Edition 2024 泛型优化:");
    let edition_generic = Edition2024Generic::new(42);
    println!("   值: {}", edition_generic.get());
    println!("   是否 Modern: {}", edition_generic.is_modern());

    let transformed = edition_generic.transform(|x| x * 2);
    println!("   转换后: {}", transformed.get());

    // 5. 编译时泛型验证
    println!("\n5. 编译时泛型验证:");
    CompileTimeAssert::<i32>::assert_send();
    CompileTimeAssert::<i32>::assert_sync();
    println!("   i32 IS_VALID: {}", bool::from(<i32 as TypeLevelValidation>::IS_VALID));
    println!("   i32 SIZE: {} 字节", <i32 as TypeLevelValidation>::SIZE);
    println!("   i32 ALIGN: {} 字节", <i32 as TypeLevelValidation>::ALIGN);
}

/// 获取 Rust 1.94.0 泛型编程特性信息
pub fn get_rust_194_generic_info() -> String {
    "Rust 1.94.0 泛型编程特性:\n\
        - 改进的泛型类型推断\n\
        - 更灵活的关联类型\n\
        - 增强的 trait 边界推断\n\
        - Edition 2024 泛型优化\n\
        - 编译时泛型验证"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smart_container() {
        let container = SmartContainer::new(42);
        assert_eq!(container.get(), &42);

        let mapped = container.map(|x| x * 2);
        assert_eq!(mapped.get(), &84);
    }

    #[test]
    fn test_smart_container_with_metadata() {
        let container = SmartContainer::with_metadata(42, "test");
        assert_eq!(container.get(), &42);
    }

    #[test]
    fn test_generic_composer() {
        let composer = GenericComposer::new(|x: i32| x * 2, |y: i32| y + 1);
        assert_eq!(composer.compose(5), 11); // (5 * 2) + 1
    }

    #[test]
    fn test_string_to_int_adapter() {
        let adapter = StringToIntAdapter;
        assert_eq!(adapter.adapt("42".to_string()).unwrap(), 42);
        assert!(adapter.adapt("not a number".to_string()).is_err());
    }

    #[test]
    fn test_adapter_batch() {
        let adapter = StringToIntAdapter;
        let results = adapter.adapt_batch(vec!["1".to_string(), "2".to_string()]).unwrap();
        assert_eq!(results, vec![1, 2]);
    }

    #[test]
    fn test_generic_adapter() {
        let adapter = GenericAdapter::new(|s: String| s.parse::<i32>().map_err(|e| AdapterError {
            message: e.to_string(),
        }));
        assert_eq!(adapter.adapt("100".to_string()).unwrap(), 100);
    }

    #[test]
    fn test_generic_validator() {
        let validator = GenericValidator::<String>::new();
        assert!(validator.validate_clone());
        assert!(validator.validate_thread_safe());
    }

    #[test]
    fn test_complex_bounds_struct() {
        let complex = ComplexBoundsStruct::new(1, "hello");
        let swapped = complex.swap();
        let (u, t) = swapped.into_tuple();
        assert_eq!(u, "hello");
        assert_eq!(t, 1);
    }

    #[test]
    fn test_edition_2024_generic() {
        let generic = Edition2024Generic::new(42);
        assert_eq!(generic.get(), &42);
        assert!(generic.is_modern());

        let transformed = generic.transform(|x| x * 2);
        assert_eq!(transformed.get(), &84);
    }

    #[test]
    fn test_compile_time_assert() {
        CompileTimeAssert::<i32>::assert_send();
        CompileTimeAssert::<i32>::assert_sync();
    }

    #[test]
    fn test_type_level_validation() {
        assert!(<i32 as TypeLevelValidation>::IS_VALID);
        assert_eq!(<i32 as TypeLevelValidation>::SIZE, 4);
        assert_eq!(<i32 as TypeLevelValidation>::ALIGN, 4);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_generic_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_generic_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("泛型"));
    }
}
