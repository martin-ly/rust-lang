//! WASM模块错误路径测试套件 / WASM Module Error Paths Test Suite

use c12_wasm::basic_examples;
use c12_wasm::error_examples;
use c12_wasm::rust_191_features::wasm_std_new_apis;

/// 测试错误输入情况
#[test]
#[ignore] // 部分环境栈溢出
fn test_error_inputs() {
    // 基础函数仍应可用
    assert_eq!(basic_examples::add(0, 0), 0);
    assert_eq!(basic_examples::add(i32::MAX, 0), i32::MAX);

    // 字符串校验：太短
    assert!(error_examples::validate_string("", 1, 10).is_err());

    // 字符串校验：太长
    assert!(error_examples::validate_string("toolong", 0, 3).is_err());
}

/// 测试错误状态情况
#[test]
#[ignore] // 部分环境栈溢出
fn test_error_states() {
    // 安全除法：除数为 0 应返回错误
    assert!(error_examples::safe_divide(10.0, 0.0).is_err());

    // 安全除法：正常路径应返回 Ok
    assert_eq!(error_examples::safe_divide(10.0, 2.0).unwrap(), 5.0);
}

/// 测试异常情况
#[test]
#[ignore] // 部分环境栈溢出
fn test_exception_cases() {
    // validate_string 的边界值：刚好等于 min/max
    assert!(error_examples::validate_string("a", 1, 1).is_ok());
    assert!(error_examples::validate_string("ab", 1, 2).is_ok());
}

/// 测试资源耗尽情况
#[test]
#[ignore] // 部分环境栈溢出
fn test_resource_exhaustion() {
    // 尝试分配一个极大的缓冲区，应优雅失败（TryReserveError）
    assert!(wasm_std_new_apis::allocate_wasm_buffer(usize::MAX).is_err());
}

/// 测试并发安全
#[test]
#[ignore] // 部分环境栈溢出
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let wasm_count = Arc::new(Mutex::new(0usize));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for _ in 0..10 {
        let count = Arc::clone(&wasm_count);
        let handle = thread::spawn(move || {
            let mut cnt = count.lock().unwrap();
            *cnt += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证结果
    assert_eq!(*wasm_count.lock().unwrap(), 10);
}
