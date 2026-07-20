//! 泛型集成测试
//! 
//! 测试Rust泛型系统的各种特性

use c04_generic::*;

#[test]
fn test_generic_functions() {
    let result = generic_add(5, 3);
    assert_eq!(result, 8);
    
    let result = generic_add(5.5, 3.2);
    assert!((result - 8.7).abs() < 0.001);
}

#[test]
fn test_generic_structs() {
    let int_pair = Pair::new(1, 2);
    assert_eq!(int_pair.first, 1);
    assert_eq!(int_pair.second, 2);
    
    let string_pair = Pair::new("hello".to_string(), "world".to_string());
    assert_eq!(string_pair.first, "hello");
    assert_eq!(string_pair.second, "world");
}

#[test]
fn test_trait_bounds() {
    let numbers = vec![1, 2, 3, 4, 5];
    let result = find_max(&numbers);
    assert_eq!(result, Some(5));
    
    let empty: Vec<i32> = vec![];
    let result = find_max(&empty);
    assert_eq!(result, None);
}

#[test]
fn test_associated_types() {
    let counter = Counter::new();
    let mut iterator = counter.take(5);
    
    let result: Vec<u32> = iterator.collect();
    assert_eq!(result, vec![0, 1, 2, 3, 4]);
}

#[test]
fn test_const_generics() {
    let array = [1, 2, 3, 4, 5];
    let sum = sum_array(&array);
    assert_eq!(sum, 15);
}

#[test]
fn test_generic_impl_blocks() {
    let container = Container::new(42);
    assert_eq!(container.value(), 42);
    
    let string_container = Container::new("hello".to_string());
    assert_eq!(string_container.value(), "hello");
}

#[test]
fn test_where_clauses() {
    let result = complex_generic_function(5, "test".to_string());
    assert_eq!(result, "test5");
}

// 测试结构体和trait定义
struct Pair<T> {
    first: T,
    second: T,
}

impl<T> Pair<T> {
    fn new(first: T, second: T) -> Self {
        Self { first, second }
    }
}

struct Container<T> {
    value: T,
}

impl<T> Container<T> {
    fn new(value: T) -> Self {
        Self { value }
    }
    
    fn value(&self) -> &T {
        &self.value
    }
}

struct Counter {
    count: u32,
}

impl Counter {
    fn new() -> Self {
        Self { count: 0 }
    }
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.count;
        self.count += 1;
        Some(current)
    }
}

// 辅助函数
fn generic_add<T>(a: T, b: T) -> T 
where 
    T: std::ops::Add<Output = T>,
{
    a + b
}

fn find_max<T>(slice: &[T]) -> Option<&T>
where
    T: PartialOrd,
{
    slice.iter().max()
}

fn sum_array<const N: usize>(arr: &[i32; N]) -> i32 {
    arr.iter().sum()
}

fn complex_generic_function<T, U>(value: T, string: U) -> String
where
    T: std::fmt::Display,
    U: std::fmt::Display,
{
    format!("{}{}", string, value)
}
