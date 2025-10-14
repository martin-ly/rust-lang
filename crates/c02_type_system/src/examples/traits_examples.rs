//! 特征系统示例代码
//! 
//! 本文件包含了特征系统的各种示例，包括：
//! - 特征定义与实现
//! - 特征对象和动态分发
//! - 对象安全规则
//! - 高级特性（关联类型、GATs、关联常量）
//! - 常见设计模式

use std::fmt::{Debug, Display};

/// 特征基础示例
pub fn trait_basics_examples() {
    println!("=== 特征基础示例 ===");
    
    // 基本特征实现
    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle { width: 3.0, height: 4.0 };
    
    println!("Circle area: {:.2}", circle.area());
    println!("Rectangle area: {:.2}", rectangle.area());
    
    // 特征对象
    let shapes: Vec<Box<dyn Shape>> = vec![
        Box::new(circle),
        Box::new(rectangle),
    ];
    
    for shape in shapes {
        println!("Shape area: {:.2}", shape.area());
    }
}

/// 特征对象示例
pub fn trait_object_examples() {
    println!("\n=== 特征对象示例 ===");
    
    // 动态分发
    let processors: Vec<Box<dyn Processor>> = vec![
        Box::new(Trimmer),
        Box::new(Uppercaser),
    ];
    
    for processor in processors {
        let result = processor.process("hello world");
        println!("Processed: {}", result);
    }
}

/// 高级特征特性示例
pub fn advanced_traits_examples() {
    println!("\n=== 高级特征特性示例 ===");
    
    // 关联类型
    let mut counter = Counter { count: 0 };
    while let Some(item) = counter.next() {
        println!("Counter item: {}", item);
        if item > 5 {
            break;
        }
    }
    
    // 泛型关联类型 (GATs)
    let mut stream = StringStream {
        data: vec!["hello".to_string(), "world".to_string()],
        index: 0,
    };
    
    while let Some(item) = stream.next() {
        println!("Stream item: {}", item);
    }
    
    // 关联常量
    use_constants::<MyType>();
}

/// 标准库特征示例
pub fn std_traits_examples() {
    println!("\n=== 标准库特征示例 ===");
    
    // Clone 和 Copy
    let point1 = Point { x: 1, y: 2 };
    let point2 = point1;  // Copy
    println!("Point1: {:?}, Point2: {:?}", point1, point2);
    
    // Debug 和 Display
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    println!("Debug: {:?}", person);
    println!("Display: {}", person);
    
    // 数值特征
    let complex1 = Complex { real: 1.0, imag: 2.0 };
    let complex2 = Complex { real: 3.0, imag: 4.0 };
    let sum = complex1 + complex2;
    println!("Complex sum: {:?}", sum);
}

/// 设计模式示例
pub fn design_patterns_examples() {
    println!("\n=== 设计模式示例 ===");
    
    // 建造者模式
    let person = PersonBuilder::new()
        .name("Bob".to_string())
        .age(25)
        .email("bob@example.com".to_string())
        .build();
    println!("Built person: {:?}", person);
    
    // 策略模式
    let sorter = Sorter::new(Box::new(QuickSort));
    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
    sorter.sort(&mut data);
    println!("Quick sorted: {:?}", data);
    
    // 适配器模式
    let loggers: Vec<Box<dyn Logger>> = vec![
        Box::new(ConsoleLogger),
        Box::new(FileLogger { filename: "app.log".to_string() }),
        Box::new(LoggerAdapter {
            external_logger: ExternalLogger,
        }),
    ];
    
    for logger in loggers {
        logger.log("Hello, world!");
    }
}

/// 性能考虑示例
pub fn performance_examples() {
    println!("\n=== 性能考虑示例 ===");
    
    // 泛型 vs 特征对象
    let data = vec![1, 2, 3, 4, 5];
    
    // 泛型：编译时多态
    let result1 = process_generic(data.iter().sum::<i32>());
    println!("Generic result: {}", result1);
    
    // 特征对象：运行时多态
    let processor = Box::new(SumProcessor);
    let result2 = process_trait_object(processor, data);
    println!("Trait object result: {}", result2);
}

// ============================================================================
// 特征定义
// ============================================================================

/// 基本形状特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait Shape {
    fn area(&self) -> f64;
    fn perimeter(&self) -> f64;
}

/// 处理器特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait Processor {
    fn process(&self, input: &str) -> String;
}

/// 迭代器特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

/// 流式迭代器特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait StreamingIterator {
    type Item<'a> where Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

/// 常量特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait Constants {
    const MAX_VALUE: u32;
    const MIN_VALUE: u32;
    const DEFAULT_VALUE: u32 = 0;
}

/// 日志器特征
#[allow(dead_code)]
#[allow(unused_variables)]
trait Logger {
    fn log(&self, message: &str);
}

// ============================================================================
// 结构体定义
// ============================================================================

/// 圆形
#[allow(dead_code)]
#[allow(unused_variables)]
struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
    
    fn perimeter(&self) -> f64 {
        2.0 * std::f64::consts::PI * self.radius
    }
}

/// 矩形
#[allow(dead_code)]
#[allow(unused_variables)]
struct Rectangle {
    width: f64,
    height: f64,
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }
    
    fn perimeter(&self) -> f64 {
        2.0 * (self.width + self.height)
    }
}

/// 字符串修剪器
#[allow(dead_code)]
#[allow(unused_variables)]
struct Trimmer;

impl Processor for Trimmer {
    fn process(&self, input: &str) -> String {
        input.trim().to_string()
    }
}

/// 大写转换器
#[allow(dead_code)]
#[allow(unused_variables)]
struct Uppercaser;

impl Processor for Uppercaser {
    fn process(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

/// 计数器
#[allow(dead_code)]
#[allow(unused_variables)]
struct Counter {
    count: u32,
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.count += 1;
        Some(self.count)
    }
}

/// 字符串流
#[allow(dead_code)]
#[allow(unused_variables)]
struct StringStream {
    data: Vec<String>,
    index: usize,
}

impl StreamingIterator for StringStream {
    type Item<'a> = &'a str where Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.index < self.data.len() {
            let result = &self.data[self.index];
            self.index += 1;
            Some(result)
        } else {
            None
        }
    }
}

/// 我的类型
#[allow(dead_code)]
#[allow(unused_variables)]
struct MyType;

impl Constants for MyType {
    const MAX_VALUE: u32 = 1000;
    const MIN_VALUE: u32 = 0;
}

/// 点
#[allow(dead_code)]
#[derive(Debug, Copy, Clone)]
#[allow(unused_variables)]
struct Point {
    x: i32,
    y: i32,
}

/// 人员
#[allow(dead_code)]
#[derive(Debug)]
#[allow(unused_variables)]
struct Person {
    name: String,
    age: u32,
}

impl Display for Person {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({} years old)", self.name, self.age)
    }
}

/// 复数
#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
struct Complex {
    real: f64,
    imag: f64,
}

impl std::ops::Add for Complex {
    type Output = Self;
    
    fn add(self, other: Self) -> Self::Output {
        Complex {
            real: self.real + other.real,
            imag: self.imag + other.imag,
        }
    }
}

// ============================================================================
// 设计模式实现
// ============================================================================

/// 人员建造者
#[allow(dead_code)]
struct PersonBuilder {
    name: Option<String>,
    age: Option<u32>,
    email: Option<String>,
}

impl PersonBuilder {
    fn new() -> Self {
        PersonBuilder {
            name: None,
            age: None,
            email: None,
        }
    }
    
    fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }
    
    fn age(mut self, age: u32) -> Self {
        self.age = Some(age);
        self
    }
    
    fn email(mut self, email: String) -> Self {
        self.email = Some(email);
        self
    }
    
    fn build(self) -> Person {
        Person {
            name: self.name.unwrap_or_else(|| "Unknown".to_string()),
            age: self.age.unwrap_or(0),
        }
    }
}

/// 排序策略特征
#[allow(dead_code)]
trait SortStrategy<T> {
    fn sort(&self, items: &mut [T]);
}

/// 快速排序
#[allow(dead_code)]
struct QuickSort;

impl<T: Ord> SortStrategy<T> for QuickSort {
    fn sort(&self, items: &mut [T]) {
        items.sort();
    }
}

/// 排序器
#[allow(dead_code)]
struct Sorter<T> {
    strategy: Box<dyn SortStrategy<T>>,
}

impl<T> Sorter<T> {
    fn new(strategy: Box<dyn SortStrategy<T>>) -> Self {
        Sorter { strategy }
    }
    
    fn sort(&self, items: &mut [T]) {
        self.strategy.sort(items);
    }
}

/// 控制台日志器
#[allow(dead_code)]
struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        println!("[CONSOLE] {}", message);
    }
}

/// 文件日志器
#[allow(dead_code)]
struct FileLogger {
    filename: String,
}

impl Logger for FileLogger {
    fn log(&self, message: &str) {
        println!("[FILE: {}] {}", self.filename, message);
    }
}

/// 外部日志器
#[allow(dead_code)]
struct ExternalLogger;

impl ExternalLogger {
    fn write_log(&self, level: &str, msg: &str) {
        println!("[{}] {}", level, msg);
    }
}

/// 日志器适配器
#[allow(dead_code)]
struct LoggerAdapter {
    external_logger: ExternalLogger,
}

impl Logger for LoggerAdapter {
    fn log(&self, message: &str) {
        self.external_logger.write_log("INFO", message);
    }
}

// ============================================================================
// 性能示例
// ============================================================================

/// 泛型处理器
fn process_generic<T: std::fmt::Display>(item: T) -> String {
    format!("Processed: {}", item)
}

/// 特征对象处理器
fn process_trait_object(processor: Box<dyn Processor>, data: Vec<i32>) -> String {
    let sum: i32 = data.iter().sum();
    processor.process(&sum.to_string())
}

/// 求和处理器
#[allow(dead_code)]
struct SumProcessor;

impl Processor for SumProcessor {
    fn process(&self, input: &str) -> String {
        format!("Sum: {}", input)
    }
}

/// 使用关联常量
fn use_constants<T: Constants>() {
    println!("Max: {}, Min: {}, Default: {}", 
             T::MAX_VALUE, T::MIN_VALUE, T::DEFAULT_VALUE);
}

/// 运行所有特征示例
pub fn run_all_examples() {
    println!("Rust 特征系统示例");
    println!("==================");
    
    trait_basics_examples();
    trait_object_examples();
    advanced_traits_examples();
    std_traits_examples();
    design_patterns_examples();
    performance_examples();
    
    println!("\n所有示例运行完成！");
}
