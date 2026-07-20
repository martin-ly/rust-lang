//! 所有权系统集成测试
//! 
//! 测试所有权、借用和生命周期的集成功能

use c01_ownership_borrow_scope::*;

#[test]
fn test_ownership_system_integration() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 测试所有权转移
    let owned_data = take_ownership(data);
    assert_eq!(owned_data.len(), 5);
    
    // 测试借用
    let borrowed_data = &owned_data;
    assert_eq!(borrowed_data[0], 1);
}

#[test]
fn test_lifetime_integration() {
    let long_lived = String::from("long lived");
    let result = longest_string(&long_lived, "short");
    assert_eq!(result, "long lived");
}

#[test]
fn test_borrowing_patterns() {
    let mut data = vec![1, 2, 3];
    
    // 测试可变借用
    let first = &mut data[0];
    *first = 10;
    
    // 测试不可变借用
    let second = &data[1];
    assert_eq!(*second, 2);
    
    assert_eq!(data[0], 10);
}

#[test]
fn test_ownership_transfer() {
    let s1 = String::from("hello");
    let s2 = s1; // s1 被移动
    
    // s1 不再可用
    // let len = s1.len(); // 这会导致编译错误
    
    assert_eq!(s2.len(), 5);
}

#[test]
fn test_clone_vs_move() {
    let s1 = String::from("hello");
    let s2 = s1.clone(); // 克隆，s1 仍然可用
    
    assert_eq!(s1.len(), 5);
    assert_eq!(s2.len(), 5);
}

// 辅助函数
fn take_ownership(data: Vec<i32>) -> Vec<i32> {
    data
}

fn longest_string<'a>(s1: &'a str, s2: &'a str) -> &'a str {
    if s1.len() > s2.len() {
        s1
    } else {
        s2
    }
}
