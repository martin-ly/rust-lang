//! 跨模块集成测试
//! 
//! 测试不同模块之间的交互和集成

use c01_ownership_borrow_scope::*;
use c02_type_system::*;
use c03_control_fn::*;

#[test]
fn test_ownership_with_type_system() {
    let data: Vec<GenericType<i32>> = vec![
        GenericType::new(1),
        GenericType::new(2),
        GenericType::new(3),
    ];
    
    let result = process_generic_data(data);
    assert_eq!(result.len(), 3);
}

#[test]
fn test_async_with_ownership() {
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        let data = vec![1, 2, 3];
        let result = async_process_data(data).await;
        assert_eq!(result, 6);
    });
}

#[test]
fn test_generic_with_control_flow() {
    let numbers = vec![1, 2, 3, 4, 5];
    let filtered = filter_and_process(&numbers, |x| x % 2 == 0);
    assert_eq!(filtered, vec![4, 8]); // 2*2, 4*2
}

#[test]
fn test_complex_data_flow() {
    let input = "hello world";
    let result = complex_data_processing(input);
    assert_eq!(result, "HELLO WORLD");
}

#[test]
fn test_error_propagation() {
    let result = process_with_errors("valid");
    assert!(result.is_ok());
    
    let error_result = process_with_errors("");
    assert!(error_result.is_err());
}

#[test]
fn test_concurrent_ownership() {
    let data = std::sync::Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = Vec::new();
    
    for i in 0..3 {
        let data = std::sync::Arc::clone(&data);
        let handle = std::thread::spawn(move || {
            let sum: i32 = data.iter().sum();
            sum + i
        });
        handles.push(handle);
    }
    
    let results: Vec<i32> = handles
        .into_iter()
        .map(|h| h.join().unwrap())
        .collect();
    
    assert_eq!(results.len(), 3);
    assert!(results.iter().all(|&x| x >= 15));
}

#[test]
fn test_generic_collections() {
    let mut collection = GenericCollection::new();
    collection.add(1);
    collection.add(2);
    collection.add(3);
    
    assert_eq!(collection.len(), 3);
    assert_eq!(collection.sum(), 6);
}

#[test]
fn test_async_stream_processing() {
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        let stream = create_async_stream();
        let results: Vec<i32> = stream.take(5).collect().await;
        assert_eq!(results, vec![0, 1, 2, 3, 4]);
    });
}

// 辅助结构体和函数
struct GenericType<T> {
    value: T,
}

impl<T> GenericType<T> {
    fn new(value: T) -> Self {
        Self { value }
    }
}

struct GenericCollection<T> {
    items: Vec<T>,
}

impl<T> GenericCollection<T> 
where 
    T: Copy + std::ops::Add<Output = T> + Default,
{
    fn new() -> Self {
        Self { items: Vec::new() }
    }
    
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn len(&self) -> usize {
        self.items.len()
    }
    
    fn sum(&self) -> T {
        self.items.iter().fold(T::default(), |acc, &x| acc + x)
    }
}

fn process_generic_data<T>(data: Vec<GenericType<T>>) -> Vec<T> {
    data.into_iter().map(|item| item.value).collect()
}

async fn async_process_data(data: Vec<i32>) -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    data.iter().sum()
}

fn filter_and_process<T, F>(items: &[T], predicate: F) -> Vec<T>
where
    T: Copy + std::ops::Mul<Output = T>,
    F: Fn(&T) -> bool,
{
    items
        .iter()
        .filter(|x| predicate(x))
        .map(|&x| x * x)
        .collect()
}

fn complex_data_processing(input: &str) -> String {
    if input.is_empty() {
        return String::new();
    }
    
    input.to_uppercase()
}

fn process_with_errors(input: &str) -> Result<String, String> {
    if input.is_empty() {
        return Err("Empty input".to_string());
    }
    
    Ok(input.to_uppercase())
}

fn create_async_stream() -> impl futures::Stream<Item = i32> {
    futures::stream::iter(0..10)
}
