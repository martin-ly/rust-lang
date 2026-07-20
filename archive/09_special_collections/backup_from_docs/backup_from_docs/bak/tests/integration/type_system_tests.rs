//! 类型系统集成测试
//! 
//! 测试Rust类型系统的各种特性

use c02_type_system::*;

#[test]
fn test_generic_types() {
    let int_container = GenericContainer::new(42);
    let string_container = GenericContainer::new("hello".to_string());
    
    assert_eq!(int_container.value, 42);
    assert_eq!(string_container.value, "hello");
}

#[test]
fn test_trait_objects() {
    let shapes: Vec<Box<dyn Shape>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Rectangle { width: 4.0, height: 6.0 }),
    ];
    
    let total_area: f64 = shapes.iter().map(|s| s.area()).sum();
    assert!(total_area > 0.0);
}

#[test]
fn test_enum_patterns() {
    let message = Message::Write("hello".to_string());
    
    match message {
        Message::Write(text) => assert_eq!(text, "hello"),
        _ => panic!("Expected Write variant"),
    }
}

#[test]
fn test_option_handling() {
    let some_value = Some(42);
    let none_value: Option<i32> = None;
    
    assert_eq!(some_value.unwrap(), 42);
    assert!(none_value.is_none());
}

#[test]
fn test_result_handling() {
    let success = Ok::<i32, String>(42);
    let failure = Err::<i32, String>("error".to_string());
    
    assert_eq!(success.unwrap(), 42);
    assert!(failure.is_err());
}

#[test]
fn test_lifetime_parameters() {
    let s1 = "hello";
    let s2 = "world";
    
    let result = longest_string(s1, s2);
    assert_eq!(result, "world"); // "world" 更长
}

// 测试结构体和trait定义
struct GenericContainer<T> {
    value: T,
}

impl<T> GenericContainer<T> {
    fn new(value: T) -> Self {
        Self { value }
    }
}

trait Shape {
    fn area(&self) -> f64;
}

struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }
}

enum Message {
    Write(String),
    Move { x: i32, y: i32 },
    Quit,
}

fn longest_string<'a>(s1: &'a str, s2: &'a str) -> &'a str {
    if s1.len() > s2.len() {
        s1
    } else {
        s2
    }
}
