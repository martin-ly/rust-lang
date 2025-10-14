//! 泛型系统示例代码
//! 
//! 本文件包含了泛型系统的各种示例，包括：
//! - 泛型函数和结构体
//! - 特征约束和 where 子句
//! - 高级泛型特性（GATs、HRTB、常量泛型）
//! - 变型（Variance）
//! - 性能优化技巧

use std::fmt::Debug;

/// 泛型函数示例
pub fn generic_function_examples() {
    println!("=== 泛型函数示例 ===");
    
    // 基本泛型函数
    let result1 = identity(42);
    let result2 = identity("hello");
    println!("identity(42) = {}", result1);
    println!("identity(\"hello\") = {}", result2);
    
    // 多个类型参数
    let pair = make_pair(42, "world");
    println!("make_pair(42, \"world\") = {:?}", pair);
    
    // 带约束的泛型函数
    let cloned = clone_and_print("hello");
    println!("cloned = {}", cloned);
}

/// 泛型结构体示例
pub fn generic_struct_examples() {
    println!("\n=== 泛型结构体示例 ===");
    
    // 基本泛型结构体
    let point_i32 = Point::new(1, 2);
    let point_f64 = Point::new(1.0, 2.0);
    println!("Point<i32>: {:?}", point_i32);
    println!("Point<f64>: {:?}", point_f64);
    
    // 多个类型参数
    let pair = Pair::new(42, "hello");
    println!("Pair<i32, &str>: {:?}", pair);
    
    // 泛型容器
    let mut container = Container::new(100);
    container.set(200);
    println!("Container value: {}", container.get());
}

/// 特征约束示例
pub fn trait_constraint_examples() {
    println!("\n=== 特征约束示例 ===");
    
    // 基本约束
    print_debug(42);
    print_debug("hello");
    
    // 多个约束
    let cloned = clone_and_debug("world");
    println!("cloned = {}", cloned);
    
    // where 子句
    let result = complex_function(42, "hello");
    println!("complex_function result = {}", result);
}

/// 高级泛型特性示例
pub fn advanced_generics_examples() {
    println!("\n=== 高级泛型特性示例 ===");
    
    // 泛型关联类型 (GATs)
    let mut counter = Counter { count: 0 };
    while let Some(item) = counter.next() {
        println!("Counter item: {}", item);
        if *item > 5 {
            break;
        }
    }
    
    // 高阶生命周期约束 (HRTB)
    fn truncate_string(s: &str) -> &str {
        if s.len() > 5 {
            &s[..5]
        } else {
            s
        }
    }
    higher_ranked_lifetime(&truncate_string);
    
    // 常量泛型
    let array: Array<i32, 5> = Array::new();
    println!("Array length: {}", array.len());
}

/// 变型示例
pub fn variance_examples() {
    println!("\n=== 变型示例 ===");
    
    // 协变示例
    let long_lived = String::from("long lived");
    let short_lived = String::from("short");
    let result = longest(&long_lived, &short_lived);
    println!("Longest string: {}", result);
    
    // 逆变示例
    let handler = StringHandler;
    use_handler(handler);
}

/// 性能优化示例
pub fn performance_examples() {
    println!("\n=== 性能优化示例 ===");
    
    // 单态化示例
    let int_result = generic_function(42);
    let str_result = generic_function("hello");
    println!("int_result = {}", int_result);
    println!("str_result = {}", str_result);
    
    // 零成本抽象
    let items = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = items.iter().map(|x| x * 2).collect();
    println!("Doubled: {:?}", doubled);
}

// ============================================================================
// 辅助函数和结构体定义
// ============================================================================

/// 泛型恒等函数
pub fn identity<T>(x: T) -> T {
    x
}

/// 创建元组的泛型函数
pub fn make_pair<T, U>(first: T, second: U) -> (T, U) {
    (first, second)
}

/// 带约束的泛型函数
pub fn clone_and_print<T: Clone + Debug>(item: T) -> T {
    let cloned = item.clone();
    println!("Cloned item: {:?}", cloned);
    cloned
}

/// 泛型结构体
#[derive(Debug)]
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

impl<T> Point<T> {
    pub fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
}

/// 多个类型参数的泛型结构体
#[derive(Debug)]
pub struct Pair<T, U> {
    pub first: T,
    pub second: U,
}

impl<T, U> Pair<T, U> {
    pub fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }
}

/// 泛型容器
pub struct Container<T> {
    value: T,
}

impl<T> Container<T> {
    pub fn new(value: T) -> Self {
        Container { value }
    }
    
    pub fn get(&self) -> &T {
        &self.value
    }
    
    pub fn set(&mut self, value: T) {
        self.value = value;
    }
}

/// 带约束的泛型函数
pub fn print_debug<T: Debug>(item: T) {
    println!("Debug: {:?}", item);
}

/// 多个约束的泛型函数
pub fn clone_and_debug<T: Clone + Debug>(item: T) -> T {
    let cloned = item.clone();
    println!("Cloned and debug: {:?}", cloned);
    cloned
}

/// 使用 where 子句的复杂函数
pub fn complex_function<T, U>(x: T, y: U) -> String
where
    T: Clone + Debug,
    U: std::fmt::Display,
{
    let cloned = x.clone();
    format!("Complex: {:?} and {}", cloned, y)
}

/// 泛型关联类型 (GATs) 示例
pub trait Iterator {
    type Item<'a> where Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

#[allow(dead_code)]
pub struct Counter {
    pub count: u32,
}

impl Iterator for Counter {
    type Item<'a> = &'a u32;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        self.count += 1;
        Some(&self.count)
    }
}

/// 高阶生命周期约束 (HRTB) 示例
pub fn higher_ranked_lifetime<F>(f: &F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s = "hello world";
    let result = f(s);
    println!("HRTB result: {}", result);
}

/// 常量泛型示例
#[allow(dead_code)]
pub struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> Array<T, N>
where
    T: Default,
{
    pub fn new() -> Self {
        Array {
            data: [(); N].map(|_| T::default()),
        }
    }
    
    pub fn len(&self) -> usize {
        N
    }
}

/// 变型示例 - 协变
pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 变型示例 - 逆变
#[allow(dead_code)]
pub trait Handler<T> {
    fn handle(&self, input: T);
}

#[allow(dead_code)]
pub struct StringHandler;

impl Handler<String> for StringHandler {
    fn handle(&self, input: String) {
        println!("Handling string: {}", input);
    }
}

pub fn use_handler<H>(handler: H)
where
    H: Handler<String>,
{
    handler.handle("hello".to_string());
}

/// 性能优化示例
#[allow(dead_code)]
pub fn generic_function<T>(x: T) -> T {
    x
}

/// 运行所有泛型示例
pub fn run_all_examples() {
    println!("Rust 泛型系统示例");
    println!("==================");
    
    generic_function_examples();
    generic_struct_examples();
    trait_constraint_examples();
    advanced_generics_examples();
    variance_examples();
    performance_examples();
    
    println!("\n所有示例运行完成！");
}
