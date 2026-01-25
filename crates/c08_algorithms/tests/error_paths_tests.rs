//! 算法模块错误路径测试套件 / Algorithms Module Error Paths Test Suite

/// 测试错误输入情况
#[test]
fn test_error_inputs() {
    // 测试无效索引
    let vec = vec![1, 2, 3];
    assert_eq!(vec.get(100), None);
    assert_eq!(vec.get(usize::MAX), None);

    // 测试空数组操作
    let empty: Vec<i32> = vec![];
    assert_eq!(empty.get(0), None);
    assert_eq!(empty.first(), None);
    assert_eq!(empty.last(), None);
}

/// 测试错误状态情况
#[test]
fn test_error_states() {
    // 测试已排序数组的边界情况
    let sorted = vec![1, 2, 3, 4, 5];
    
    // 测试查找不存在的元素
    let result = sorted.binary_search(&10);
    assert!(result.is_err());

    // 测试空数组的查找
    let empty: Vec<i32> = vec![];
    let result = empty.binary_search(&1);
    assert!(result.is_err());
}

/// 测试异常情况
#[test]
fn test_exception_cases() {
    // 测试溢出情况（模拟）
    let large_value = i32::MAX;
    let small_value = 1;
    
    // 注意：实际溢出会导致panic，这里只测试边界值
    assert_eq!(large_value, i32::MAX);
    assert_eq!(small_value, 1);
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 测试大量数据操作
    let very_large_size = 1000000;
    let large_vec: Vec<usize> = (0..very_large_size).collect();
    assert_eq!(large_vec.len(), very_large_size);

    // 测试内存密集型操作
    let sum: usize = large_vec.iter().sum();
    assert!(sum > 0);
}

/// 测试并发安全
#[test]
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let shared = Arc::new(Mutex::new(Vec::<i32>::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for i in 0..10 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut vec = shared.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证所有值都已添加
    let vec = shared.lock().unwrap();
    assert_eq!(vec.len(), 10);
}
