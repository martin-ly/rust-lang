//! 边界情况测试套件 / Edge Cases Test Suite

use c01_ownership_borrow_scope::scope::{ScopeManager, ScopeType};

/// 测试空值/空集合边界情况
#[test]
fn test_empty_collections() {
    let mut manager = ScopeManager::new();

    // 空作用域栈
    assert_eq!(manager.get_scope_depth(), 0);
    assert!(manager.get_current_scope().is_none());
    assert_eq!(manager.get_all_scopes().len(), 0);
    assert_eq!(manager.get_all_variables().len(), 0);

    // 空作用域中的变量操作
    manager
        .enter_scope("empty_scope".to_string(), ScopeType::Block)
        .unwrap();
    assert_eq!(manager.get_all_variables().len(), 0);

    // 尝试在空作用域中查找不存在的变量
    assert_eq!(
        manager.get_variable_scope_path("nonexistent"),
        Some(vec!["empty_scope".to_string()])
    );

    manager.exit_scope().unwrap();
}

/// 测试最大值/最小值边界情况
#[test]
fn test_max_min_values() {
    let mut manager = ScopeManager::new();

    // 测试大量作用域嵌套
    let max_depth = 1000;
    for i in 0..max_depth {
        let scope_name = format!("scope_{}", i);
        manager
            .enter_scope(scope_name, ScopeType::Block)
            .unwrap();
    }

    assert_eq!(manager.get_scope_depth(), max_depth);

    // 测试大量变量
    for i in 0..1000 {
        let var_name = format!("var_{}", i);
        manager
            .declare_variable(var_name, "i32".to_string(), i.to_string(), false, None)
            .unwrap();
    }

    assert_eq!(manager.get_all_variables().len(), 1000);

    // 清理
    for _ in 0..max_depth {
        manager.exit_scope().unwrap();
    }
}

/// 测试边界值情况
#[test]
fn test_boundary_values() {
    let mut manager = ScopeManager::new();

    // 测试深度为1的情况
    manager
        .enter_scope("single".to_string(), ScopeType::Block)
        .unwrap();
    assert_eq!(manager.get_scope_depth(), 1);
    manager.exit_scope().unwrap();

    // 测试空字符串作为作用域名
    manager
        .enter_scope(String::new(), ScopeType::Block)
        .unwrap();
    assert_eq!(manager.get_scope_depth(), 1);
    manager.exit_scope().unwrap();

    // 测试很长的作用域名
    let long_name = "a".repeat(1000);
    manager.enter_scope(long_name, ScopeType::Block).unwrap();
    assert_eq!(manager.get_scope_depth(), 1);
    manager.exit_scope().unwrap();
}

/// 测试溢出/下溢情况
#[test]
fn test_overflow_underflow() {
    let mut manager = ScopeManager::new();

    // 测试退出空栈（下溢）
    assert!(manager.exit_scope().is_err());
    assert_eq!(manager.get_scope_depth(), 0);

    // 测试在空栈中操作变量
    assert!(manager
        .declare_variable(
            "var".to_string(),
            "i32".to_string(),
            "0".to_string(),
            false,
            None
        )
        .is_err());

    // 测试重复进入同名作用域
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    assert!(manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .is_err()); // 不允许同名作用域

    // 清理
    manager.exit_scope().unwrap();
}

/// 测试错误路径
#[test]
fn test_error_paths() {
    let mut manager = ScopeManager::new();

    // 测试无效输入
    assert!(manager.exit_scope().is_err());

    // 测试错误状态
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    manager.exit_scope().unwrap();
    // 现在栈为空，再次退出应该失败
    assert!(manager.exit_scope().is_err());

    // 测试变量不存在的情况
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    assert!(manager.find_variable("nonexistent").is_none());
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
