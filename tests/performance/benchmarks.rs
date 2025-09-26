//! 性能基准测试
//! 
//! 测试各个模块的性能特征

use std::time::Instant;

#[test]
fn test_ownership_performance() {
    let start = Instant::now();
    
    // 测试移动语义性能
    let data = vec![1; 1000];
    let _moved_data = data; // 移动
    
    let move_time = start.elapsed();
    
    // 测试克隆性能
    let start = Instant::now();
    let data = vec![1; 1000];
    let _cloned_data = data.clone(); // 克隆
    
    let clone_time = start.elapsed();
    
    // 移动应该比克隆快
    assert!(move_time < clone_time);
}

#[test]
fn test_generic_performance() {
    let start = Instant::now();
    
    // 测试泛型函数调用
    for i in 0..1000 {
        let _result = generic_function::<i32>(i);
    }
    
    let duration = start.elapsed();
    
    // 应该在合理时间内完成
    assert!(duration.as_millis() < 100);
}

#[test]
fn test_iteration_performance() {
    let data: Vec<i32> = (0..10000).collect();
    
    let start = Instant::now();
    
    // 测试迭代器性能
    let sum: i32 = data.iter().sum();
    
    let duration = start.elapsed();
    
    assert_eq!(sum, 49995000);
    assert!(duration.as_millis() < 50);
}

#[test]
fn test_string_concatenation_performance() {
    let strings = vec!["hello"; 1000];
    
    let start = Instant::now();
    
    // 测试字符串连接性能
    let result = strings.join(" ");
    
    let duration = start.elapsed();
    
    assert!(result.len() > 0);
    assert!(duration.as_millis() < 100);
}

#[test]
fn test_hash_map_performance() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    
    let start = Instant::now();
    
    // 测试HashMap插入性能
    for i in 0..10000 {
        map.insert(i, i * 2);
    }
    
    let insert_time = start.elapsed();
    
    let start = Instant::now();
    
    // 测试HashMap查找性能
    for i in 0..10000 {
        let _value = map.get(&i);
    }
    
    let lookup_time = start.elapsed();
    
    assert!(insert_time.as_millis() < 100);
    assert!(lookup_time.as_millis() < 100);
}

#[test]
fn test_memory_allocation_performance() {
    let start = Instant::now();
    
    // 测试大量内存分配
    let mut vecs = Vec::new();
    for i in 0..1000 {
        let vec = vec![i; 100];
        vecs.push(vec);
    }
    
    let duration = start.elapsed();
    
    assert_eq!(vecs.len(), 1000);
    assert!(duration.as_millis() < 200);
}

// 辅助函数
fn generic_function<T>(value: T) -> T {
    value
}
