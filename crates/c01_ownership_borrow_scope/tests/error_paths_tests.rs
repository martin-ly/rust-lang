//! 所有权和借用作用域模块错误路径测试套件 / Ownership and Borrowing Scope Module Error Paths Test Suite

use c01_ownership_borrow_scope::scope::{ScopeError, ScopeManager, ScopeType};

/// 测试错误输入情况
#[test]
fn test_error_inputs() {
    let mut manager = ScopeManager::new();

    // 测试在空栈中操作变量
    assert!(manager.add_variable("var".to_string()).is_err());
    assert!(manager.remove_variable("var").is_err());
    assert!(manager.get_variable_scope_path("var").is_none());

    // 测试退出空栈
    assert!(manager.exit_scope().is_err());
}

/// 测试错误状态情况
#[test]
fn test_error_states() {
    let mut manager = ScopeManager::new();

    // 创建作用域后退出
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    manager.exit_scope().unwrap();

    // 现在栈为空，再次退出应该失败
    assert!(manager.exit_scope().is_err());

    // 尝试在空栈中添加变量应该失败
    assert!(manager.add_variable("var".to_string()).is_err());
}

/// 测试异常情况
#[test]
fn test_exception_cases() {
    let mut manager = ScopeManager::new();

    // 测试变量不存在的情况
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    
    // 尝试移除不存在的变量
    assert!(manager.remove_variable("nonexistent").is_err());
    
    // 尝试查找不存在的变量
    assert!(manager.get_variable_scope_path("nonexistent").is_none());

    manager.exit_scope().unwrap();
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    let mut manager = ScopeManager::new();

    // 测试大量作用域创建
    let large_number = 10000;
    for i in 0..large_number {
        let scope_name = format!("scope_{}", i);
        manager.enter_scope(scope_name, ScopeType::Block).unwrap();
    }

    assert_eq!(manager.get_scope_depth(), large_number);

    // 清理
    for _ in 0..large_number {
        manager.exit_scope().unwrap();
    }

    assert_eq!(manager.get_scope_depth(), 0);
}

/// 测试并发安全
#[test]
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let manager = Arc::new(Mutex::new(ScopeManager::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for i in 0..10 {
        let manager = Arc::clone(&manager);
        let handle = thread::spawn(move || {
            let mut mgr = manager.lock().unwrap();
            let scope_name = format!("thread_{}", i);
            mgr.enter_scope(scope_name, ScopeType::Block).unwrap();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证所有作用域都已创建
    let mgr = manager.lock().unwrap();
    assert_eq!(mgr.get_scope_depth(), 10);
}
