//! 作用域管理模块测试套件 / Scope Management Module Test Suite

use c01_ownership_borrow_scope::scope::{
    Scope, ScopeAnalyzer, ScopeError, ScopeManager, ScopeType, VariableInfo,
};

#[test]
fn test_scope_creation() {
    let scope = Scope::new("test_scope".to_string(), ScopeType::Block, 0);

    assert_eq!(scope.name, "test_scope");
    assert_eq!(scope.scope_type, ScopeType::Block);
    assert_eq!(scope.depth, 0);
    assert_eq!(scope.variables.len(), 0);
    assert!(scope.parent.is_none());
}

#[test]
fn test_scope_variable_management() {
    let mut scope = Scope::new("test_scope".to_string(), ScopeType::Block, 0);

    // 添加变量
    scope.add_variable("x".to_string());
    scope.add_variable("y".to_string());

    assert_eq!(scope.variables.len(), 2);
    assert!(scope.contains_variable("x"));
    assert!(scope.contains_variable("y"));

    // 移除变量
    assert!(scope.remove_variable("x"));
    assert!(!scope.contains_variable("x"));
    assert_eq!(scope.variables.len(), 1);

    // 重复添加
    scope.add_variable("y".to_string());
    assert_eq!(scope.variables.len(), 1); // 不应该重复添加
}

#[test]
fn test_scope_manager_basic_operations() {
    let mut manager = ScopeManager::new();

    // 初始状态
    assert_eq!(manager.get_scope_depth(), 0);
    assert!(manager.get_current_scope().is_none());

    // 进入作用域
    manager
        .enter_scope("main".to_string(), ScopeType::Function)
        .unwrap();
    assert_eq!(manager.get_scope_depth(), 1);
    assert!(manager.get_current_scope().is_some());

    // 进入嵌套作用域
    manager
        .enter_scope("inner".to_string(), ScopeType::Block)
        .unwrap();
    assert_eq!(manager.get_scope_depth(), 2);

    // 退出作用域
    manager.exit_scope().unwrap();
    assert_eq!(manager.get_scope_depth(), 1);

    manager.exit_scope().unwrap();
    assert_eq!(manager.get_scope_depth(), 0);
}

#[test]
fn test_scope_manager_variable_declaration() {
    let mut manager = ScopeManager::new();
    manager
        .enter_scope("main".to_string(), ScopeType::Function)
        .unwrap();

    // 声明变量
    manager
        .declare_variable(
            "x".to_string(),
            "i32".to_string(),
            "42".to_string(),
            false,
            None,
        )
        .unwrap();

    // 查找变量
    let var = manager.find_variable("x");
    assert!(var.is_some());

    let var_info = var.unwrap();
    assert_eq!(var_info.name, "x");
    assert_eq!(var_info.var_type, "i32");
    assert_eq!(var_info.value, "42");
    assert_eq!(var_info.scope_name, "main");
    assert!(!var_info.is_mutable);
    assert!(var_info.lifetime.is_none());
}

#[test]
fn test_scope_manager_nested_scopes() {
    let mut manager = ScopeManager::new();

    // 主作用域
    manager
        .enter_scope("main".to_string(), ScopeType::Function)
        .unwrap();
    manager
        .declare_variable(
            "main_var".to_string(),
            "i32".to_string(),
            "100".to_string(),
            false,
            None,
        )
        .unwrap();

    // 嵌套作用域
    manager
        .enter_scope("inner".to_string(), ScopeType::Block)
        .unwrap();
    manager
        .declare_variable(
            "inner_var".to_string(),
            "String".to_string(),
            "hello".to_string(),
            false,
            None,
        )
        .unwrap();

    // 检查变量可见性
    assert!(manager.is_variable_visible("main_var"));
    assert!(manager.is_variable_visible("inner_var"));

    // 退出内层作用域
    manager.exit_scope().unwrap();

    // 内层变量应该不可见
    assert!(manager.is_variable_visible("main_var"));
    assert!(!manager.is_variable_visible("inner_var"));
}

#[test]
fn test_scope_manager_error_handling() {
    let mut manager = ScopeManager::new();

    // 尝试退出不存在的作用域
    let result = manager.exit_scope();
    assert!(matches!(result, Err(ScopeError::NoScopeToExit)));

    // 尝试声明变量但没有作用域
    let result = manager.declare_variable(
        "x".to_string(),
        "i32".to_string(),
        "42".to_string(),
        false,
        None,
    );
    assert!(matches!(result, Err(ScopeError::ScopeNotFound)));

    // 重复的作用域名称
    manager
        .enter_scope("test".to_string(), ScopeType::Block)
        .unwrap();
    let result = manager.enter_scope("test".to_string(), ScopeType::Block);
    assert!(matches!(result, Err(ScopeError::ScopeNameExists)));
}

#[test]
fn test_scope_analyzer() {
    let mut manager = ScopeManager::new();

    // 创建嵌套作用域结构
    manager
        .enter_scope("main".to_string(), ScopeType::Function)
        .unwrap();
    manager
        .enter_scope("loop".to_string(), ScopeType::Loop)
        .unwrap();
    manager
        .enter_scope("conditional".to_string(), ScopeType::Conditional)
        .unwrap();

    // 添加一些变量
    manager
        .declare_variable(
            "x".to_string(),
            "i32".to_string(),
            "42".to_string(),
            false,
            None,
        )
        .unwrap();
    manager
        .declare_variable(
            "y".to_string(),
            "String".to_string(),
            "hello".to_string(),
            true,
            None,
        )
        .unwrap();

    let analyzer = ScopeAnalyzer::new(manager);

    // 分析嵌套关系
    let nesting = analyzer.analyze_nesting();
    assert_eq!(nesting.len(), 3);

    // 分析变量生命周期
    let lifecycle = analyzer.analyze_variable_lifecycle();
    assert_eq!(lifecycle.len(), 2);

    // 检测内存泄漏
    let leaks = analyzer.detect_memory_leaks();
    assert_eq!(leaks.len(), 0); // 所有变量都应该可见
}

#[test]
fn test_scope_type_variants() {
    // 测试所有作用域类型
    let types = vec![
        ScopeType::Block,
        ScopeType::Function,
        ScopeType::Module,
        ScopeType::Loop,
        ScopeType::Conditional,
        ScopeType::Expression,
    ];

    for scope_type in types {
        let scope = Scope::new("test".to_string(), scope_type.clone(), 0);
        assert_eq!(scope.scope_type, scope_type);
    }
}

#[test]
fn test_variable_info() {
    let var_info = VariableInfo::new(
        "test_var".to_string(),
        "i32".to_string(),
        "42".to_string(),
        "main".to_string(),
        true,
        Some("'a".to_string()),
    );

    assert_eq!(var_info.name, "test_var");
    assert_eq!(var_info.var_type, "i32");
    assert_eq!(var_info.value, "42");
    assert_eq!(var_info.scope_name, "main");
    assert!(var_info.is_mutable);
    assert_eq!(var_info.lifetime, Some("'a".to_string()));
}

#[test]
fn test_scope_manager_complex_scenario() {
    let mut manager = ScopeManager::new();

    // 模拟复杂的程序结构
    manager
        .enter_scope("main".to_string(), ScopeType::Function)
        .unwrap();
    manager
        .declare_variable(
            "main_var".to_string(),
            "i32".to_string(),
            "0".to_string(),
            true,
            None,
        )
        .unwrap();

    // 循环作用域
    manager
        .enter_scope("for_loop".to_string(), ScopeType::Loop)
        .unwrap();
    manager
        .declare_variable(
            "i".to_string(),
            "usize".to_string(),
            "0".to_string(),
            true,
            None,
        )
        .unwrap();

    // 条件分支
    manager
        .enter_scope("if_branch".to_string(), ScopeType::Conditional)
        .unwrap();
    manager
        .declare_variable(
            "temp".to_string(),
            "i32".to_string(),
            "100".to_string(),
            false,
            None,
        )
        .unwrap();

    // 检查作用域信息
    assert_eq!(manager.get_scope_depth(), 3);

    let all_scopes = manager.get_all_scopes();
    assert_eq!(all_scopes.len(), 3);

    let all_variables = manager.get_all_variables();
    assert_eq!(all_variables.len(), 3);

    // 检查变量作用域路径
    let main_var_path = manager.get_variable_scope_path("main_var");
    assert!(main_var_path.is_some());
    assert_eq!(main_var_path.unwrap().len(), 1);

    let i_path = manager.get_variable_scope_path("i");
    assert!(i_path.is_some());
    assert_eq!(i_path.unwrap().len(), 2);

    // 退出作用域
    manager.exit_scope().unwrap(); // if_branch
    manager.exit_scope().unwrap(); // for_loop
    manager.exit_scope().unwrap(); // main

    assert_eq!(manager.get_scope_depth(), 0);
}

#[test]
fn test_scope_error_display() {
    let errors = vec![
        ScopeError::NoScopeToExit,
        ScopeError::ScopeNameExists,
        ScopeError::ScopeNotFound,
        ScopeError::VariableNotFound,
        ScopeError::InvalidDepth,
    ];

    for error in errors {
        let error_string = error.to_string();
        assert!(!error_string.is_empty());
        assert!(error_string.len() > 0);
    }
}

#[test]
fn test_scope_manager_edge_cases() {
    let mut manager = ScopeManager::new();

    // 空作用域栈的边界情况
    assert_eq!(manager.get_scope_depth(), 0);
    assert!(manager.get_current_scope().is_none());
    assert_eq!(manager.get_all_scopes().len(), 0);
    assert_eq!(manager.get_all_variables().len(), 0);

    // 单个作用域的情况
    manager
        .enter_scope("single".to_string(), ScopeType::Block)
        .unwrap();
    assert_eq!(manager.get_scope_depth(), 1);
    assert!(manager.get_current_scope().is_some());

    // 大量嵌套作用域
    for i in 0..100 {
        let scope_name = format!("scope_{}", i);
        manager.enter_scope(scope_name, ScopeType::Block).unwrap();
    }

    assert_eq!(manager.get_scope_depth(), 101);

    // 清理所有作用域
    for _ in 0..101 {
        manager.exit_scope().unwrap();
    }

    assert_eq!(manager.get_scope_depth(), 0);
}

#[test]
fn test_scope_visibility_rules() {
    let mut manager = ScopeManager::new();

    // 创建作用域层次结构
    manager
        .enter_scope("global".to_string(), ScopeType::Module)
        .unwrap();
    manager
        .declare_variable(
            "global_var".to_string(),
            "i32".to_string(),
            "0".to_string(),
            false,
            None,
        )
        .unwrap();

    manager
        .enter_scope("function".to_string(), ScopeType::Function)
        .unwrap();
    manager
        .declare_variable(
            "func_var".to_string(),
            "String".to_string(),
            "hello".to_string(),
            false,
            None,
        )
        .unwrap();

    manager
        .enter_scope("block".to_string(), ScopeType::Block)
        .unwrap();
    manager
        .declare_variable(
            "block_var".to_string(),
            "f64".to_string(),
            "3.14".to_string(),
            false,
            None,
        )
        .unwrap();

    // 检查可见性规则
    assert!(manager.is_variable_visible("global_var")); // 全局变量在所有作用域可见
    assert!(manager.is_variable_visible("func_var")); // 函数变量在函数和嵌套作用域可见
    assert!(manager.is_variable_visible("block_var")); // 块变量仅在块内可见

    // 退出块作用域
    manager.exit_scope().unwrap();

    assert!(manager.is_variable_visible("global_var")); // 仍然可见
    assert!(manager.is_variable_visible("func_var")); // 仍然可见
    assert!(!manager.is_variable_visible("block_var")); // 不再可见

    // 退出函数作用域
    manager.exit_scope().unwrap();

    assert!(manager.is_variable_visible("global_var")); // 仍然可见
    assert!(!manager.is_variable_visible("func_var")); // 不再可见
    assert!(!manager.is_variable_visible("block_var")); // 不再可见
}
