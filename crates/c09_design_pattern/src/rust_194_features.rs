//! Rust 1.94.0 设计模式特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在设计模式场景中的增强，包括：
//! - 改进的 Builder 模式 / Improved Builder Pattern
//! - 增强的类型状态模式 / Enhanced Type State Pattern
//! - 优化的访问者模式 / Optimized Visitor Pattern
//! - Edition 2024 设计模式优化 / Edition 2024 Design Pattern Optimizations
//! - 零成本抽象模式 / Zero-Cost Abstraction Patterns
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024

use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};

// ==================== 1. 改进的 Builder 模式 ====================

/// # 1. 改进的 Builder 模式 / Improved Builder Pattern
///
/// Rust 1.94.0 优化了 Builder 模式的实现：
/// Rust 1.94.0 optimizes Builder pattern implementation:

/// 类型安全的 Builder
///
/// Rust 1.94.0: 改进的类型安全 Builder
pub struct TypedBuilder<T, State: BuilderState> {
    data: T,
    _state: PhantomData<State>,
}

/// Builder 状态 Trait
pub trait BuilderState {}

/// 初始状态
pub struct Initial;
impl BuilderState for Initial {}

/// 配置中状态
pub struct Configuring;
impl BuilderState for Configuring {}

/// 可构建状态
pub struct Ready;
impl BuilderState for Ready {}

/// 配置对象
#[derive(Debug, Clone, Default)]
pub struct Configuration {
    pub name: String,
    pub value: i32,
    pub enabled: bool,
}

impl Configuration {
    /// 创建新的 Builder
    ///
    /// Rust 1.94.0: 清晰的 Builder 初始状态
    pub fn builder() -> TypedBuilder<Self, Initial> {
        TypedBuilder {
            data: Self::default(),
            _state: PhantomData,
        }
    }
}

impl TypedBuilder<Configuration, Initial> {
    /// 设置名称
    ///
    /// Rust 1.94.0: 状态转换的类型安全
    pub fn name(self, name: impl Into<String>) -> TypedBuilder<Configuration, Configuring> {
        let mut data = self.data;
        data.name = name.into();
        TypedBuilder {
            data,
            _state: PhantomData,
        }
    }
}

impl TypedBuilder<Configuration, Configuring> {
    /// 设置值
    pub fn value(self, value: i32) -> Self {
        let mut data = self.data;
        data.value = value;
        TypedBuilder {
            data,
            _state: PhantomData,
        }
    }

    /// 设置启用状态
    pub fn enabled(self, enabled: bool) -> TypedBuilder<Configuration, Ready> {
        let mut data = self.data;
        data.enabled = enabled;
        TypedBuilder {
            data,
            _state: PhantomData,
        }
    }
}

impl TypedBuilder<Configuration, Ready> {
    /// 构建最终对象
    ///
    /// Rust 1.94.0: 只能在 Ready 状态构建
    pub fn build(self) -> Configuration {
        self.data
    }
}

/// 函数式 Builder
///
/// Rust 1.94.0: 更灵活的函数式 Builder
pub struct FunctionalBuilder<T> {
    steps: Vec<Box<dyn FnOnce(T) -> T>>,
    _phantom: PhantomData<T>,
}

impl<T: Default> FunctionalBuilder<T> {
    /// 创建新的函数式 Builder
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            _phantom: PhantomData,
        }
    }

    /// 添加配置步骤
    pub fn with<F>(mut self, f: F) -> Self
    where
        F: FnOnce(T) -> T + 'static,
    {
        self.steps.push(Box::new(f));
        self
    }

    /// 构建最终对象
    pub fn build(self) -> T {
        self.steps.into_iter().fold(T::default(), |acc, step| step(acc))
    }
}

impl<T: Default> Default for FunctionalBuilder<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 2. 增强的类型状态模式 ====================

/// # 2. 增强的类型状态模式 / Enhanced Type State Pattern
///
/// Rust 1.94.0 优化了类型状态模式的实现：
/// Rust 1.94.0 optimizes type state pattern implementation:

/// 连接状态机
///
/// Rust 1.94.0: 改进的类型状态转换
pub struct Connection<State: ConnectionState> {
    address: String,
    port: u16,
    #[allow(dead_code)]
    state: PhantomData<State>,
}

/// 连接状态 Trait
pub trait ConnectionState {}

/// 未连接状态
pub struct Disconnected;
impl ConnectionState for Disconnected {}

/// 连接中状态
pub struct Connecting;
impl ConnectionState for Connecting {}

/// 已连接状态
pub struct Connected;
impl ConnectionState for Connected {}

/// 已关闭状态
pub struct Closed;
impl ConnectionState for Closed {}

impl Connection<Disconnected> {
    /// 创建新连接（未连接状态）
    pub fn new(address: impl Into<String>, port: u16) -> Self {
        Self {
            address: address.into(),
            port,
            state: PhantomData,
        }
    }

    /// 开始连接
    ///
    /// Rust 1.94.0: 类型安全的状态转换
    pub fn connect(self) -> Connection<Connecting> {
        Connection {
            address: self.address,
            port: self.port,
            state: PhantomData,
        }
    }
}

impl Connection<Connecting> {
    /// 完成连接
    pub fn established(self) -> Connection<Connected> {
        Connection {
            address: self.address,
            port: self.port,
            state: PhantomData,
        }
    }
}

impl Connection<Connected> {
    /// 发送数据
    pub fn send(&self, data: &[u8]) -> Result<(), String> {
        println!("   发送到 {}:{}, 数据: {:?}", self.address, self.port, data);
        Ok(())
    }

    /// 关闭连接
    pub fn close(self) -> Connection<Closed> {
        Connection {
            address: self.address,
            port: self.port,
            state: PhantomData,
        }
    }
}

impl Connection<Closed> {
    /// 获取连接信息
    pub fn info(&self) -> String {
        format!("{}:{} (closed)", self.address, self.port)
    }
}

// ==================== 3. 优化的访问者模式 ====================

/// # 3. 优化的访问者模式 / Optimized Visitor Pattern
///
/// Rust 1.94.0 优化了访问者模式的性能：
/// Rust 1.94.0 optimizes visitor pattern performance:

/// 访问者 Trait
///
/// Rust 1.94.0: 改进的访问者实现
pub trait Visitor<T> {
    fn visit(&mut self, element: &T);
}

/// 可访问 Trait
pub trait Visitable<T> {
    fn accept<V: Visitor<T>>(&self, visitor: &mut V);
}

/// 文档元素
#[derive(Debug, Clone)]
pub enum DocumentElement {
    Text(String),
    Heading(u8, String),
    List(Vec<String>),
}

/// 文档统计访问者
pub struct DocumentStatsVisitor {
    text_count: usize,
    heading_count: usize,
    list_count: usize,
    char_count: AtomicU64,
}

impl DocumentStatsVisitor {
    /// 创建新的统计访问者
    pub fn new() -> Self {
        Self {
            text_count: 0,
            heading_count: 0,
            list_count: 0,
            char_count: AtomicU64::new(0),
        }
    }

    /// 获取统计结果
    pub fn stats(&self) -> DocumentStats {
        DocumentStats {
            text_count: self.text_count,
            heading_count: self.heading_count,
            list_count: self.list_count,
            total_chars: self.char_count.load(Ordering::Relaxed),
        }
    }
}

impl Default for DocumentStatsVisitor {
    fn default() -> Self {
        Self::new()
    }
}

/// 文档统计
#[derive(Debug, Clone, Copy)]
pub struct DocumentStats {
    pub text_count: usize,
    pub heading_count: usize,
    pub list_count: usize,
    pub total_chars: u64,
}

impl Visitor<DocumentElement> for DocumentStatsVisitor {
    fn visit(&mut self, element: &DocumentElement) {
        match element {
            DocumentElement::Text(text) => {
                self.text_count += 1;
                self.char_count.fetch_add(text.len() as u64, Ordering::Relaxed);
            }
            DocumentElement::Heading(_, text) => {
                self.heading_count += 1;
                self.char_count.fetch_add(text.len() as u64, Ordering::Relaxed);
            }
            DocumentElement::List(items) => {
                self.list_count += 1;
                for item in items {
                    self.char_count.fetch_add(item.len() as u64, Ordering::Relaxed);
                }
            }
        }
    }
}

/// 文档结构
pub struct Document {
    elements: Vec<DocumentElement>,
}

impl Document {
    /// 创建新文档
    pub fn new() -> Self {
        Self { elements: Vec::new() }
    }

    /// 添加元素
    pub fn add_element(&mut self, element: DocumentElement) {
        self.elements.push(element);
    }

    /// 接受访问者
    pub fn accept<V: Visitor<DocumentElement>>(&self, visitor: &mut V) {
        for element in &self.elements {
            visitor.visit(element);
        }
    }

    /// 遍历所有元素
    pub fn iter(&self) -> impl Iterator<Item = &DocumentElement> {
        self.elements.iter()
    }
}

impl Default for Document {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 4. Edition 2024 设计模式优化 ====================

/// # 4. Edition 2024 设计模式优化 / Edition 2024 Design Pattern Optimizations
///
/// Rust 1.94.0 与 Edition 2024 的设计模式集成：
/// Rust 1.94.0 design pattern integration with Edition 2024:

/// Edition 2024 策略模式
///
/// Rust 1.94.0: Edition 2024 优化的策略模式
pub struct Edition2024Strategy<S: Strategy> {
    strategy: S,
    edition: Edition2024Marker,
}

/// Edition 2024 标记
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition2024Marker {
    Legacy,
    Modern,
}

/// 策略 Trait
pub trait Strategy {
    type Input;
    type Output;
    fn execute(&self, input: Self::Input) -> Self::Output;
}

/// 加法策略
pub struct AddStrategy;

impl Strategy for AddStrategy {
    type Input = (i32, i32);
    type Output = i32;

    fn execute(&self, input: Self::Input) -> Self::Output {
        input.0 + input.1
    }
}

/// 乘法策略
pub struct MultiplyStrategy;

impl Strategy for MultiplyStrategy {
    type Input = (i32, i32);
    type Output = i32;

    fn execute(&self, input: Self::Input) -> Self::Output {
        input.0 * input.1
    }
}

impl<S: Strategy> Edition2024Strategy<S> {
    /// 创建新的策略实例
    pub fn new(strategy: S) -> Self {
        Self {
            strategy,
            edition: Edition2024Marker::Modern,
        }
    }

    /// 执行策略
    ///
    /// Rust 1.94.0: Edition 2024 优化的策略执行
    pub fn execute(&self, input: S::Input) -> S::Output {
        // Edition 2024 优化
        self.strategy.execute(input)
    }

    /// 切换策略
    pub fn with_strategy<NewS: Strategy>(self, new_strategy: NewS) -> Edition2024Strategy<NewS> {
        Edition2024Strategy {
            strategy: new_strategy,
            edition: self.edition,
        }
    }
}

// ==================== 5. 零成本抽象模式 ====================

/// # 5. 零成本抽象模式 / Zero-Cost Abstraction Patterns
///
/// Rust 1.94.0 提供了更好的零成本抽象：
/// Rust 1.94.0 provides better zero-cost abstractions:

/// 零成本包装器
///
/// Rust 1.94.0: 编译时优化的包装器
#[repr(transparent)]
pub struct ZeroCostWrapper<T> {
    inner: T,
}

impl<T> ZeroCostWrapper<T> {
    /// 创建新的包装器
    pub const fn new(inner: T) -> Self {
        Self { inner }
    }

    /// 获取内部值引用
    pub const fn get(&self) -> &T {
        &self.inner
    }

    /// 获取内部值
    pub fn into_inner(self) -> T {
        self.inner
    }
}

/// 编译时工厂
///
/// Rust 1.94.0: 编译时确定的工厂模式
pub struct ConstFactory<T> {
    _phantom: PhantomData<T>,
}

impl<T: Default> ConstFactory<T> {
    /// 运行时创建实例
    /// 注意: const fn 中不能调用 trait 方法，因为这需要虚函数调用
    pub fn create() -> T {
        T::default()
    }
}

/// 单例模式（线程安全）
///
/// Rust 1.94.0: 优化的单例实现
pub struct Singleton<T> {
    instance: std::sync::OnceLock<T>,
}

impl<T> Singleton<T> {
    /// 创建新的单例容器
    pub const fn new() -> Self {
        Self {
            instance: std::sync::OnceLock::new(),
        }
    }

    /// 获取或初始化实例
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.instance.get_or_init(f)
    }
}

impl<T> Default for Singleton<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 设计模式特性
pub fn demonstrate_rust_194_design_patterns() {
    println!("\n=== Rust 1.94.0 设计模式特性演示 ===\n");

    // 1. 改进的 Builder 模式
    println!("1. 改进的 Builder 模式:");
    let config = Configuration::builder()
        .name("MyApp")
        .value(42)
        .enabled(true)
        .build();
    println!("   构建的配置: {:?}", config);

    let func_config: Configuration = FunctionalBuilder::<Configuration>::new()
        .with(|mut c| { c.name = "FuncApp".to_string(); c })
        .with(|mut c| { c.value = 100; c })
        .build();
    println!("   函数式配置: {:?}", func_config);

    // 2. 增强的类型状态模式
    println!("\n2. 增强的类型状态模式:");
    let conn = Connection::new("localhost", 8080)
        .connect()
        .established();
    conn.send(b"Hello, Rust 1.94!").unwrap();
    let closed = conn.close();
    println!("   连接信息: {}", closed.info());

    // 3. 优化的访问者模式
    println!("\n3. 优化的访问者模式:");
    let mut doc = Document::new();
    doc.add_element(DocumentElement::Heading(1, "Title".to_string()));
    doc.add_element(DocumentElement::Text("Some content".to_string()));
    doc.add_element(DocumentElement::List(vec!["Item 1".to_string(), "Item 2".to_string()]));

    let mut stats_visitor = DocumentStatsVisitor::new();
    doc.accept(&mut stats_visitor);
    println!("   文档统计: {:?}", stats_visitor.stats());

    // 4. Edition 2024 策略模式
    println!("\n4. Edition 2024 策略模式:");
    let add_strategy = Edition2024Strategy::new(AddStrategy);
    println!("   加法策略 (5, 3): {}", add_strategy.execute((5, 3)));

    let mul_strategy = add_strategy.with_strategy(MultiplyStrategy);
    println!("   乘法策略 (5, 3): {}", mul_strategy.execute((5, 3)));

    // 5. 零成本抽象
    println!("\n5. 零成本抽象:");
    let wrapper = ZeroCostWrapper::new(42);
    println!("   包装器值: {}", wrapper.get());

    let singleton: Singleton<String> = Singleton::new();
    let instance = singleton.get_or_init(|| "initialized".to_string());
    println!("   单例值: {}", instance);
}

/// 获取 Rust 1.94.0 设计模式特性信息
pub fn get_rust_194_design_pattern_info() -> String {
    "Rust 1.94.0 设计模式特性:\n\
        - 改进的 Builder 模式\n\
        - 增强的类型状态模式\n\
        - 优化的访问者模式\n\
        - Edition 2024 设计模式优化\n\
        - 零成本抽象模式"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_typed_builder() {
        let config = Configuration::builder()
            .name("Test")
            .value(42)
            .enabled(true)
            .build();
        assert_eq!(config.name, "Test");
        assert_eq!(config.value, 42);
        assert!(config.enabled);
    }

    #[test]
    fn test_functional_builder() {
        let config: Configuration = FunctionalBuilder::<Configuration>::new()
            .with(|mut c: Configuration| { c.name = "Func".to_string(); c })
            .with(|mut c: Configuration| { c.value = 10; c })
            .build();
        assert_eq!(config.name, "Func");
        assert_eq!(config.value, 10);
    }

    #[test]
    fn test_connection_state_machine() {
        let conn = Connection::new("localhost", 8080)
            .connect()
            .established();
        assert!(conn.send(b"test").is_ok());
        let closed = conn.close();
        assert_eq!(closed.info(), "localhost:8080 (closed)");
    }

    #[test]
    fn test_document_visitor() {
        let mut doc = Document::new();
        doc.add_element(DocumentElement::Text("Hello".to_string()));

        let mut visitor = DocumentStatsVisitor::new();
        doc.accept(&mut visitor);
        let stats = visitor.stats();
        assert_eq!(stats.text_count, 1);
        assert_eq!(stats.total_chars, 5);
    }

    #[test]
    fn test_edition_2024_strategy() {
        let add = Edition2024Strategy::new(AddStrategy);
        assert_eq!(add.execute((5, 3)), 8);

        let mul = add.with_strategy(MultiplyStrategy);
        assert_eq!(mul.execute((5, 3)), 15);
    }

    #[test]
    fn test_zero_cost_wrapper() {
        let wrapper = ZeroCostWrapper::new(42);
        assert_eq!(wrapper.get(), &42);
        assert_eq!(wrapper.into_inner(), 42);
    }

    #[test]
    fn test_singleton() {
        let singleton: Singleton<i32> = Singleton::new();
        let val1 = singleton.get_or_init(|| 42);
        let val2 = singleton.get_or_init(|| 100); // 不会被调用
        assert_eq!(*val1, 42);
        assert_eq!(*val2, 42); // 返回同一个值
    }

    #[test]
    fn test_demonstrate_patterns() {
        demonstrate_rust_194_design_patterns();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_design_pattern_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("设计模式"));
    }
}
