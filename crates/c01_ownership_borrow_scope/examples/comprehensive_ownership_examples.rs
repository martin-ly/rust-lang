//! # Rust 所有权系统综合示例
//! 
//! 本文件包含了 Rust 所有权系统的综合示例，涵盖了所有权、借用、生命周期等各个方面
//! This file contains comprehensive examples of Rust's ownership system, covering ownership, borrowing, lifetimes, etc.

use std::rc::Rc;
use std::cell::RefCell;
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

/// 所有权基础示例 / Basic Ownership Examples
fn ownership_basics() {
    println!("=== 所有权基础示例 / Basic Ownership Examples ===");
    
    // 示例 1：所有权转移 / Example 1: Ownership Transfer
    let s1 = String::from("hello");
    let s2 = s1; // s1 的所有权转移给 s2 / Ownership of s1 is transferred to s2
    // println!("{}", s1); // 编译错误：s1 不再有效 / Compilation error: s1 is no longer valid
    println!("s2: {}", s2);
    
    // 示例 2：函数参数所有权转移 / Example 2: Function Parameter Ownership Transfer
    let s3 = String::from("world");
    takes_ownership(s3);
    // println!("{}", s3); // 编译错误：s3 不再有效 / Compilation error: s3 is no longer valid
    
    // 示例 3：返回值所有权转移 / Example 3: Return Value Ownership Transfer
    let s4 = gives_ownership();
    println!("s4: {}", s4);
    
    // 示例 4：获取并返回所有权 / Example 4: Take and Return Ownership
    let s5 = String::from("rust");
    let s6 = takes_and_gives_back(s5);
    println!("s6: {}", s6);
}

/// 获取所有权的函数 / Function that takes ownership
fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string 在这里离开作用域并被丢弃 / some_string goes out of scope and is dropped

/// 返回所有权的函数 / Function that returns ownership
fn gives_ownership() -> String {
    
    String::from("yours") // 返回所有权 / return ownership
}

/// 获取并返回所有权的函数 / Function that takes and returns ownership
fn takes_and_gives_back(a_string: String) -> String {
    a_string // 返回所有权 / return ownership
}

/// 借用基础示例 / Basic Borrowing Examples
fn borrowing_basics() {
    println!("\n=== 借用基础示例 / Basic Borrowing Examples ===");
    
    let s1 = String::from("hello");
    
    // 示例 1：不可变借用 / Example 1: Immutable Borrowing
    let len = calculate_length(&s1);
    println!("The length of '{}' is {}.", s1, len);
    
    // 示例 2：可变借用 / Example 2: Mutable Borrowing
    let mut s2 = String::from("hello");
    change(&mut s2);
    println!("Changed string: {}", s2);
    
    // 示例 3：借用规则 / Example 3: Borrowing Rules
    let mut s3 = String::from("hello");
    let r1 = &s3;
    let r2 = &s3;
    println!("r1: {}, r2: {}", r1, r2);
    
    let r3 = &mut s3;
    // println!("r1: {}", r1); // 编译错误：不能同时有可变和不可变借用 / Compilation error: cannot have mutable and immutable borrows at the same time
    println!("r3: {}", r3);
}

/// 计算字符串长度的函数 / Function to calculate string length
fn calculate_length(s: &str) -> usize {
    s.len()
} // s 离开作用域，但因为它不拥有所有权，所以不会丢弃任何内容 / s goes out of scope, but since it doesn't own the value, nothing is dropped

/// 修改字符串的函数 / Function that modifies the string
fn change(some_string: &mut String) {
    some_string.push_str(", world");
}

/// 生命周期基础示例 / Basic Lifetime Examples
fn lifetime_basics() {
    println!("\n=== 生命周期基础示例 / Basic Lifetime Examples ===");
    
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    // 示例 1：生命周期注解 / Example 1: Lifetime Annotations
    let result = longest(&string1, string2);
    println!("The longest string is {}", result);
    
    // 示例 2：结构体生命周期 / Example 2: Struct Lifetimes
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Part: {}", i.part);
    println!("Level: {}", i.level());
    println!("Announcement: {}", i.announce_and_return_part("Hello"));
}

/// 带生命周期注解的函数 / Function with lifetime annotations
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 带生命周期注解的结构体 / Struct with lifetime annotations
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    /// 方法中的生命周期注解 / Lifetime annotations in methods
    fn level(&self) -> i32 {
        3
    }
    
    /// 方法中的生命周期省略 / Lifetime elision in methods
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}

/// 智能指针示例 / Smart Pointer Examples
fn smart_pointer_examples() {
    println!("\n=== 智能指针示例 / Smart Pointer Examples ===");
    
    // 示例 1：Box<T> / Example 1: Box<T>
    let _b = Box::new(5);
    println!("b = {}", _b);
    
    // 示例 2：Rc<T> / Example 2: Rc<T>
    let a = Rc::new(Cons(5, Rc::new(Cons(10, Rc::new(Nil)))));
    println!("count after creating a = {}", Rc::strong_count(&a));
    
    let _b = Cons(3, Rc::clone(&a));
    println!("count after creating b = {}", Rc::strong_count(&a));
    
    {
        let _c = Cons(4, Rc::clone(&a));
        println!("count after creating c = {}", Rc::strong_count(&a));
    }
    
    println!("count after c goes out of scope = {}", Rc::strong_count(&a));
    
    // 示例 3：RefCell<T> / Example 3: RefCell<T>
    let data = RefCell::new(5);
    
    {
        let r1 = data.borrow();
        println!("r1: {}", r1);
    }
    
    {
        let mut r2 = data.borrow_mut();
        *r2 += 1;
    }
    
    let r3 = data.borrow();
    println!("r3: {}", r3);
}

/// 递归枚举 / Recursive Enum
#[allow(dead_code)]
#[derive(Debug)]
enum List {
    Cons(i32, Rc<List>),
    Nil,
}

use List::{Cons, Nil};

/// 并发安全示例 / Concurrency Safety Examples
fn concurrency_safety_examples() {
    println!("\n=== 并发安全示例 / Concurrency Safety Examples ===");
    
    // 示例 1：Arc + Mutex / Example 1: Arc + Mutex
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut data_guard = data_clone.lock().unwrap();
            data_guard.push(i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final data: {:?}", data.lock().unwrap());
    
    // 示例 2：Arc + RwLock / Example 2: Arc + RwLock
    let rw_data: Arc<RwLock<Vec<i32>>> = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程 / Multiple reader threads
    for i in 0..3 {
        let data_clone: Arc<RwLock<Vec<i32>>> = Arc::clone(&rw_data);
        let handle = thread::spawn(move || {
            let data_guard = data_clone.read().unwrap();
            println!("Reader {}: {:?}", i, *data_guard);
        });
        handles.push(handle);
    }
    
    // 一个写线程 / One writer thread
    let data_clone: Arc<RwLock<Vec<i32>>> = Arc::clone(&rw_data);
    let handle = thread::spawn(move || {
        let mut data_guard = data_clone.write().unwrap();
        data_guard.push(4);
        println!("Writer: {:?}", *data_guard);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}

/// 性能优化示例 / Performance Optimization Examples
fn performance_optimization_examples() {
    println!("\n=== 性能优化示例 / Performance Optimization Examples ===");
    
    let data = vec![1, 2, 3, 4, 5];
    
    // 示例 1：使用引用避免克隆 / Example 1: Use references to avoid cloning
    let sum = calculate_sum(&data);
    println!("Sum: {}", sum);
    
    // 示例 2：使用迭代器链 / Example 2: Use iterator chains
    let result: Vec<i32> = data
        .iter()
        .filter(|&&x| x > 2)
        .map(|&x| x * 2)
        .collect();
    
    println!("Filtered and mapped: {:?}", result);
    
    // 示例 3：使用切片 / Example 3: Use slices
    let slice = &data[1..4];
    println!("Slice: {:?}", slice);
    
    // 示例 4：使用智能指针共享数据 / Example 4: Use smart pointers to share data
    let shared_data = Rc::new(data);
    let shared_clone = Rc::clone(&shared_data);
    
    println!("Shared data: {:?}", shared_data);
    println!("Shared clone: {:?}", shared_clone);
}

/// 计算和的函数 / Function to calculate sum
fn calculate_sum(data: &[i32]) -> i32 {
    data.iter().sum()
}

/// 错误处理示例 / Error Handling Examples
fn error_handling_examples() {
    println!("\n=== 错误处理示例 / Error Handling Examples ===");
    
    // 示例 1：Result 类型 / Example 1: Result Type
    let result = safe_division(10, 2);
    match result {
        Ok(value) => println!("Division result: {}", value),
        Err(error) => println!("Error: {}", error),
    }
    
    let result2 = safe_division(10, 0);
    match result2 {
        Ok(value) => println!("Division result: {}", value),
        Err(error) => println!("Error: {}", error),
    }
    
    // 示例 2：Option 类型 / Example 2: Option Type
    let option = safe_get_first(&[1, 2, 3]);
    match option {
        Some(value) => println!("First element: {}", value),
        None => println!("No elements"),
    }
    
    let option2 = safe_get_first(&[]);
    match option2 {
        Some(value) => println!("First element: {}", value),
        None => println!("No elements"),
    }
    
    // 示例 3：自定义错误类型 / Example 3: Custom Error Types
    let custom_result = safe_custom_operation("valid");
    match custom_result {
        Ok(value) => println!("Custom operation result: {}", value),
        Err(error) => println!("Custom error: {}", error),
    }
    
    let custom_result2 = safe_custom_operation("");
    match custom_result2 {
        Ok(value) => println!("Custom operation result: {}", value),
        Err(error) => println!("Custom error: {}", error),
    }
}

/// 安全除法函数 / Safe division function
fn safe_division(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

/// 安全获取第一个元素函数 / Safe get first element function
fn safe_get_first(data: &[i32]) -> Option<i32> {
    if data.is_empty() {
        None
    } else {
        Some(data[0])
    }
}

/// 自定义错误类型 / Custom Error Type
#[derive(Debug)]
enum CustomError {
    EmptyString,
    InvalidInput,
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CustomError::EmptyString => write!(f, "Empty string"),
            CustomError::InvalidInput => write!(f, "Invalid input"),
        }
    }
}

impl std::error::Error for CustomError {}

/// 安全自定义操作函数 / Safe custom operation function
fn safe_custom_operation(input: &str) -> Result<String, CustomError> {
    if input.is_empty() {
        Err(CustomError::EmptyString)
    } else if input == "invalid" {
        Err(CustomError::InvalidInput)
    } else {
        Ok(input.to_uppercase())
    }
}

/// 设计模式示例 / Design Pattern Examples
fn design_pattern_examples() {
    println!("\n=== 设计模式示例 / Design Pattern Examples ===");
    
    // 示例 1：工厂模式 / Example 1: Factory Pattern
    let resource1 = ResourceFactory::create("type1");
    let resource2 = ResourceFactory::create("type2");
    
    println!("Resource1: {:?}", resource1);
    println!("Resource2: {:?}", resource2);
    
    // 示例 2：观察者模式 / Example 2: Observer Pattern
    let mut subject = Subject::new();
    
    let observer1 = Box::new(ConcreteObserver::new("Observer1"));
    let observer2 = Box::new(ConcreteObserver::new("Observer2"));
    
    subject.add_observer(observer1);
    subject.add_observer(observer2);
    
    subject.notify("Hello, observers!");
    
    // 示例 3：单例模式 / Example 3: Singleton Pattern
    let singleton1 = Singleton::get_instance();
    let singleton2 = Singleton::get_instance();
    
    println!("Singleton1: {:?}", singleton1);
    println!("Singleton2: {:?}", singleton2);
    println!("Are they the same? {}", std::ptr::eq(singleton1, singleton2));
}

/// 资源工厂 / Resource Factory
struct ResourceFactory;

impl ResourceFactory {
    fn create(resource_type: &str) -> Box<dyn Resource> {
        match resource_type {
            "type1" => Box::new(Type1Resource::new()),
            "type2" => Box::new(Type2Resource::new()),
            _ => panic!("Unknown resource type"),
        }
    }
}

/// 资源 trait / Resource Trait
#[allow(unused)]
trait Resource: std::fmt::Debug {
    fn get_name(&self) -> &str;
}

/// 类型1资源 / Type1 Resource
#[allow(dead_code)]
#[derive(Debug)]
struct Type1Resource {
    name: String,
}

impl Type1Resource {
    fn new() -> Self {
        Self {
            name: "Type1".to_string(),
        }
    }
}

impl Resource for Type1Resource {
    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 类型2资源 / Type2 Resource
#[allow(dead_code)]
#[derive(Debug)]
struct Type2Resource {
    name: String,
}

impl Type2Resource {
    fn new() -> Self {
        Self {
            name: "Type2".to_string(),
        }
    }
}

impl Resource for Type2Resource {
    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 主题 / Subject
#[allow(dead_code)]
struct Subject {
    observers: Vec<Box<dyn Observer>>,
}

impl Subject {
    fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }
    
    fn add_observer(&mut self, observer: Box<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn notify(&self, message: &str) {
        for observer in &self.observers {
            observer.update(message);
        }
    }
}

/// 观察者 trait / Observer Trait
trait Observer {
    fn update(&self, message: &str);
}

/// 具体观察者 / Concrete Observer
#[allow(dead_code)]
struct ConcreteObserver {
    name: String,
}

impl ConcreteObserver {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, message: &str) {
        println!("{} received: {}", self.name, message);
    }
}

/// 单例 / Singleton
struct Singleton {
    data: String,
}

#[allow(static_mut_refs)]
impl Singleton {
    fn get_instance() -> &'static Singleton {
        static INIT: std::sync::Once = std::sync::Once::new();
        static mut INSTANCE: Option<Singleton> = None;
        
        unsafe {
            INIT.call_once(|| {
                INSTANCE = Some(Singleton {
                    data: "Singleton data".to_string(),
                });
            });
            INSTANCE.as_ref().unwrap()
        }
    }
}

impl std::fmt::Debug for Singleton {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Singleton {{ data: {} }}", self.data)
    }
}

/// 主函数 / Main Function
fn main() {
    println!("Rust 所有权系统综合示例 / Rust Ownership System Comprehensive Examples");
    println!("================================================");
    
    // 运行所有示例 / Run all examples
    ownership_basics();
    borrowing_basics();
    lifetime_basics();
    smart_pointer_examples();
    concurrency_safety_examples();
    performance_optimization_examples();
    error_handling_examples();
    design_pattern_examples();
    
    println!("\n所有示例运行完成！/ All examples completed!");
}
