//! 所有权、借用和作用域模块集成测试套件 / Ownership, Borrowing and Scope Module Integration Test Suite

use std::sync::{Arc, Mutex};

/// 测试所有权转移集成
#[test]
fn test_ownership_transfer_integration() {
    let data = vec![1, 2, 3, 4, 5];
    let moved_data = data; // 所有权转移
    
    // 验证所有权已转移
    assert_eq!(moved_data.len(), 5);
    // data 不再可用
}

/// 测试借用集成
#[test]
fn test_borrowing_integration() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 不可变借用
    let borrowed = &data;
    assert_eq!(borrowed.len(), 5);
    
    // 可变借用
    let mut mutable_data = vec![1, 2, 3];
    let mutable_borrow = &mut mutable_data;
    mutable_borrow.push(4);
    
    assert_eq!(mutable_data.len(), 4);
}

/// 测试作用域集成
#[test]
fn test_scope_integration() {
    let outer = 10;
    
    {
        let inner = 20;
        assert_eq!(inner, 20);
        assert_eq!(outer, 10);
    }
    
    // inner 已超出作用域
    assert_eq!(outer, 10);
}

/// 测试生命周期集成
#[test]
fn test_lifetime_integration() {
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() {
            x
        } else {
            y
        }
    }
    
    let string1 = String::from("long string");
    let result;
    {
        let string2 = String::from("xyz");
        result = longest(string1.as_str(), string2.as_str());
    }
    
    assert_eq!(result, "long string");
}

/// 测试并发所有权集成
#[test]
fn test_concurrent_ownership_integration() {
    let shared = Arc::new(Mutex::new(0));
    let shared_clone = Arc::clone(&shared);
    
    let mut value = shared_clone.lock().unwrap();
    *value += 1;
    
    assert_eq!(*shared.lock().unwrap(), 1);
}

/// 测试智能指针集成
#[test]
fn test_smart_pointer_integration() {
    use std::rc::Rc;
    
    let rc1 = Rc::new(5);
    let rc2 = Rc::clone(&rc1);
    
    assert_eq!(Rc::strong_count(&rc1), 2);
    assert_eq!(*rc1, 5);
    assert_eq!(*rc2, 5);
}
