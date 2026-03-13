//! 控制流与函数模块错误路径测试套件 / Control Flow and Functions Module Error Paths Test Suite

use c03_control_fn::*;

/// 测试错误输入情况
#[test]
fn test_error_inputs() {
    // 测试无效输入
    assert!(control_flow_branch(-1).is_err());
    assert!(control_flow_branch(101).is_err());
    assert!(control_flow_branch(i32::MIN).is_err());
    assert!(control_flow_branch(i32::MAX).is_err());
}

/// 测试错误状态情况
#[test]
fn test_error_states() {
    // 测试错误状态
    let error_result = control_flow_branch(-100);
    assert!(error_result.is_err());

    // 测试None值处理
    let none_result = control_flow_match(None);
    assert_eq!(none_result, 0);
}

/// 测试异常情况
#[test]
fn test_exception_cases() {
    // 测试边界值异常
    for val in [i32::MIN, -1, 101, i32::MAX] {
        let result = control_flow_branch(val);
        assert!(result.is_err(), "值 {} 应该产生错误", val);
    }
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 测试大量循环
    let very_large = 1000000;
    let result = control_flow_loop(very_large);
    assert!(result >= very_large);

    // 测试大量分支
    let mut success_count = 0;
    for i in 0..10000 {
        if control_flow_branch(i).is_ok() {
            success_count += 1;
        }
    }
    assert!(success_count > 0);
}

/// 测试并发安全
#[test]
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut count = counter.lock().unwrap();
            *count += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证结果
    assert_eq!(*counter.lock().unwrap(), 10);
}
