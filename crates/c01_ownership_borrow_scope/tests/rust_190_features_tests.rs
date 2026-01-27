//! # Rust 1.90 特性测试 / Rust 1.90 Features Tests (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新测试请参考 `rust_192_comprehensive_tests.rs`
//!
//! 本测试文件全面测试 Rust 1.90 版本的所有新特性和改进。
//! This test file comprehensively tests all new features and improvements in Rust 1.90.

use c01_ownership_borrow_scope::{
    // Rust 1.90 特性 / Rust 1.90 Features
    ImprovedBorrowChecker,
    LifetimeInferencer,
    SmartPointerManager,
    SmartPointerType,
    OptimizedScopeManager,
    Rust190ScopeType,
    ConcurrencySafetyChecker,
    LockType,
    AccessType,
    SmartMemoryManager,
    AllocationType,
    // 基础语法 / Basic Syntax
    run_all_basic_syntax_examples,
    run_all_rust_190_features_examples,
};

// 导入 Rust 1.90 特性模块中的类型 / Import types from Rust 1.90 features module
use c01_ownership_borrow_scope::rust_190_features::BorrowType;

use std::sync::{Arc, Mutex};
use std::thread;

/// # 1. 改进的借用检查器测试 / Improved Borrow Checker Tests

#[test]
fn test_improved_borrow_checker_basic() {
    let mut checker = ImprovedBorrowChecker::new();

    // 测试不可变借用 / Test immutable borrows
    let borrow1 = checker.create_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Immutable);
    assert!(borrow1.is_ok());

    let borrow2 = checker.create_borrow("owner1".to_string(), "borrower2".to_string(), BorrowType::Immutable);
    assert!(borrow2.is_ok());

    // 测试可变借用冲突 / Test mutable borrow conflict
    let borrow3 = checker.create_borrow("owner1".to_string(), "borrower3".to_string(), BorrowType::Mutable);
    assert!(borrow3.is_err());

    // 测试统计信息 / Test statistics
    let stats = checker.get_borrow_statistics();
    assert_eq!(stats.immutable_borrows, 2);
    assert_eq!(stats.mutable_borrows, 0);
}

#[test]
fn test_improved_borrow_checker_exclusive() {
    let mut checker = ImprovedBorrowChecker::new();

    // 测试独占借用 / Test exclusive borrow
    let borrow1 = checker.create_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Exclusive);
    assert!(borrow1.is_ok());

    // 测试独占借用冲突 / Test exclusive borrow conflict
    let borrow2 = checker.create_borrow("owner1".to_string(), "borrower2".to_string(), BorrowType::Immutable);
    assert!(borrow2.is_err());

    let borrow3 = checker.create_borrow("owner1".to_string(), "borrower3".to_string(), BorrowType::Mutable);
    assert!(borrow3.is_err());
}

/// # 2. 增强的生命周期推断测试 / Enhanced Lifetime Inference Tests

#[test]
fn test_lifetime_inferencer_basic() {
    let mut inferencer = LifetimeInferencer::new();

    // 测试生命周期推断 / Test lifetime inference
    let lifetime1 = inferencer.infer_lifetime("'a".to_string(), "scope1".to_string());
    assert_eq!(lifetime1.name, "'a");
    assert_eq!(lifetime1.scope, "scope1");

    let lifetime2 = inferencer.infer_lifetime("'b".to_string(), "scope2".to_string());
    assert_eq!(lifetime2.name, "'b");
    assert_eq!(lifetime2.scope, "scope2");

    // 测试生命周期约束 / Test lifetime constraints
    let constraint_result = inferencer.check_lifetime_constraints(&lifetime1, &lifetime2);
    assert!(constraint_result);
}

#[test]
fn test_lifetime_optimization() {
    let mut inferencer = LifetimeInferencer::new();

    let mut lifetime = inferencer.infer_lifetime("'a".to_string(), "scope1".to_string());
    lifetime.add_constraint("'b".to_string());
    lifetime.add_constraint("'c".to_string());
    lifetime.add_constraint("'b".to_string()); // 重复约束 / Duplicate constraint

    let optimized = inferencer.optimize_lifetime(&lifetime);
    assert_eq!(optimized.constraints.len(), 2); // 去重后应该只有2个 / Should have 2 after deduplication
}

/// # 3. 新的智能指针特性测试 / New Smart Pointer Features Tests

#[test]
fn test_smart_pointer_manager_basic() {
    let mut manager = SmartPointerManager::new();

    // 测试创建智能指针 / Test creating smart pointers
    manager.create_smart_pointer("ptr1".to_string(), SmartPointerType::Rc);
    manager.create_smart_pointer("ptr2".to_string(), SmartPointerType::Arc);
    manager.create_smart_pointer("ptr3".to_string(), SmartPointerType::Box);

    // 测试克隆智能指针 / Test cloning smart pointers
    let result = manager.clone_smart_pointer("ptr1");
    assert!(result.is_ok());

    // 测试引用计数 / Test reference count
    let count = manager.get_reference_count("ptr1");
    assert_eq!(count, Some(2));

    // 测试不存在的指针 / Test non-existent pointer
    let result = manager.clone_smart_pointer("non_existent");
    assert!(result.is_err());
}

#[test]
fn test_smart_pointer_analysis() {
    let mut manager = SmartPointerManager::new();

    // 创建多个智能指针 / Create multiple smart pointers
    manager.create_smart_pointer("rc_ptr".to_string(), SmartPointerType::Rc);
    manager.create_smart_pointer("arc_ptr".to_string(), SmartPointerType::Arc);
    manager.create_smart_pointer("box_ptr".to_string(), SmartPointerType::Box);

    // 克隆 Rc 指针多次 / Clone Rc pointer multiple times
    for _ in 0..5 {
        manager.clone_smart_pointer("rc_ptr").unwrap();
    }

    // 分析使用情况 / Analyze usage
    let suggestions = manager.analyze_usage();
    assert!(!suggestions.is_empty());
}

/// # 4. 优化的作用域管理测试 / Optimized Scope Management Tests

#[test]
fn test_optimized_scope_manager_basic() {
    let mut manager = OptimizedScopeManager::new();

    // 测试进入作用域 / Test entering scope
    manager.enter_scope("main".to_string(), Rust190ScopeType::Function);
    manager.enter_scope("block1".to_string(), Rust190ScopeType::Block);

    // 测试添加变量 / Test adding variables
    let result = manager.add_variable("x".to_string());
    assert!(result.is_ok());

    let result = manager.add_lifetime("'a".to_string());
    assert!(result.is_ok());

    // 测试退出作用域 / Test exiting scope
    let scope_info = manager.exit_scope();
    assert!(scope_info.is_ok());

    // 测试统计信息 / Test statistics
    let stats = manager.get_scope_statistics();
    assert!(stats.total_scopes > 0);
}

#[test]
fn test_scope_nesting() {
    let mut manager = OptimizedScopeManager::new();

    // 创建嵌套作用域 / Create nested scopes
    manager.enter_scope("main".to_string(), Rust190ScopeType::Function);
    manager.enter_scope("block1".to_string(), Rust190ScopeType::Block);
    manager.enter_scope("block2".to_string(), Rust190ScopeType::Block);
    manager.enter_scope("async_scope".to_string(), Rust190ScopeType::Async);
    manager.enter_scope("macro_scope".to_string(), Rust190ScopeType::Macro);

    // 添加变量到不同作用域 / Add variables to different scopes
    manager.add_variable("main_var".to_string()).unwrap();
    manager.add_variable("block1_var".to_string()).unwrap();
    manager.add_variable("block2_var".to_string()).unwrap();
    manager.add_variable("async_var".to_string()).unwrap();
    manager.add_variable("macro_var".to_string()).unwrap();

    // 退出所有作用域 / Exit all scopes
    for _ in 0..5 {
        let scope_info = manager.exit_scope();
        assert!(scope_info.is_ok());
    }

    // 测试退出不存在的作用域 / Test exiting non-existent scope
    let result = manager.exit_scope();
    assert!(result.is_err());
}

/// # 5. 增强的并发安全测试 / Enhanced Concurrency Safety Tests

#[test]
fn test_concurrency_safety_checker_basic() {
    let mut checker = ConcurrencySafetyChecker::new();

    // 测试注册线程 / Test registering threads
    checker.register_thread("thread1".to_string(), "Worker 1".to_string());
    checker.register_thread("thread2".to_string(), "Worker 2".to_string());

    // 测试注册锁 / Test registering locks
    checker.register_lock("mutex1".to_string(), LockType::Mutex);
    checker.register_lock("rwlock1".to_string(), LockType::RwLock);
    checker.register_lock("condvar1".to_string(), LockType::ConditionVariable);

    // 测试记录资源访问 / Test recording resource access
    checker.record_access("thread1".to_string(), "resource1".to_string(), AccessType::Write);
    checker.record_access("thread2".to_string(), "resource1".to_string(), AccessType::Write);

    // 测试数据竞争检测 / Test data race detection
    let races = checker.detect_data_races();
    assert!(!races.is_empty());
}

#[test]
fn test_data_race_detection() {
    let mut checker = ConcurrencySafetyChecker::new();

    // 注册线程 / Register threads
    checker.register_thread("thread1".to_string(), "Worker 1".to_string());
    checker.register_thread("thread2".to_string(), "Worker 2".to_string());

    // 记录冲突的访问 / Record conflicting accesses
    checker.record_access("thread1".to_string(), "shared_resource".to_string(), AccessType::Write);
    checker.record_access("thread2".to_string(), "shared_resource".to_string(), AccessType::Write);

    // 检测数据竞争 / Detect data races
    let races = checker.detect_data_races();
    assert!(!races.is_empty());

    // 验证竞争报告 / Verify race reports
    for race in races {
        assert_eq!(race.access1.resource, "shared_resource");
        assert_eq!(race.access2.resource, "shared_resource");
        assert_ne!(race.access1.thread_id, race.access2.thread_id);
    }
}

/// # 6. 智能内存管理测试 / Smart Memory Management Tests

#[test]
fn test_smart_memory_manager_basic() {
    let mut manager = SmartMemoryManager::new();

    // 测试记录内存分配 / Test recording memory allocation
    manager.record_allocation("alloc1".to_string(), 1024, AllocationType::Heap);
    manager.record_allocation("alloc2".to_string(), 512, AllocationType::Stack);
    manager.record_allocation("alloc3".to_string(), 2048, AllocationType::Heap);

    // 测试记录内存释放 / Test recording memory deallocation
    let result = manager.record_deallocation("alloc1");
    assert!(result.is_ok());

    // 测试重复释放 / Test double deallocation
    let result = manager.record_deallocation("alloc1");
    assert!(result.is_err());

    // 测试释放不存在的分配 / Test deallocating non-existent allocation
    let result = manager.record_deallocation("non_existent");
    assert!(result.is_err());

    // 测试统计信息 / Test statistics
    let stats = manager.get_memory_statistics();
    assert_eq!(stats.total_allocations, 3);
    assert_eq!(stats.active_allocations, 2);
    assert_eq!(stats.heap_allocations, 2);
    assert_eq!(stats.stack_allocations, 1);
}

#[test]
fn test_memory_analysis() {
    let mut manager = SmartMemoryManager::new();

    // 记录大分配 / Record large allocations
    manager.record_allocation("large_alloc1".to_string(), 2 * 1024 * 1024, AllocationType::Heap); // 2MB
    manager.record_allocation("large_alloc2".to_string(), 1024 * 1024, AllocationType::Stack); // 1MB

    // 记录多个堆分配 / Record multiple heap allocations
    for i in 0..20 {
        manager.record_allocation(format!("heap_alloc_{}", i), 1024, AllocationType::Heap);
    }

    // 分析内存使用 / Analyze memory usage
    let suggestions = manager.analyze_memory_usage();
    assert!(!suggestions.is_empty());

    // 验证建议内容 / Verify suggestion content
    let has_large_allocation_suggestion = suggestions.iter()
        .any(|s| s.contains("Large allocations detected"));
    assert!(has_large_allocation_suggestion);

    let has_high_heap_ratio_suggestion = suggestions.iter()
        .any(|s| s.contains("High heap allocation ratio"));
    assert!(has_high_heap_ratio_suggestion);
}

/// # 7. 集成测试 / Integration Tests

#[test]
fn test_rust_190_features_integration() {
    // 测试所有 Rust 1.90 特性示例 / Test all Rust 1.90 features examples
    run_all_rust_190_features_examples();

    // 测试所有基础语法示例 / Test all basic syntax examples
    run_all_basic_syntax_examples();
}

#[test]
fn test_concurrent_operations() {
    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 创建多个线程进行并发操作 / Create multiple threads for concurrent operations
    for i in 0..5 {
        let data_clone = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut data = data_clone.lock().unwrap();
            data.push(i);
            println!("Thread {} added {}", i, i);
        });
        handles.push(handle);
    }

    // 等待所有线程完成 / Wait for all threads to complete
    for handle in handles {
        handle.join().unwrap();
    }

    // 验证结果 / Verify results
    let final_data = shared_data.lock().unwrap();
    assert_eq!(final_data.len(), 8); // 原始3个 + 5个新添加的 / Original 3 + 5 newly added
}

#[test]
fn test_memory_safety() {
    // 测试内存安全 / Test memory safety
    let data = Box::new(vec![1, 2, 3, 4, 5]);
    let processed_data: Vec<i32> = data.iter()
        .map(|x| x * 2)
        .filter(|&x| x % 2 == 0)
        .collect();

    assert_eq!(processed_data, vec![2, 4, 6, 8, 10]);

    // data 在作用域结束时自动释放 / data is automatically freed when it goes out of scope
}

#[test]
fn test_ownership_transfer() {
    // 测试所有权转移 / Test ownership transfer
    let s1 = String::from("hello");
    let s2 = s1; // 所有权转移 / ownership transfer

    // s1 不再有效 / s1 is no longer valid
    // println!("{}", s1); // 这会编译错误 / This would compile error

    assert_eq!(s2, "hello");
}

#[test]
fn test_borrowing_rules() {
    // 测试借用规则 / Test borrowing rules
    let mut s = String::from("hello");

    // 可以有多个不可变借用 / Can have multiple immutable borrows
    let r1 = &s;
    let r2 = &s;
    assert_eq!(*r1, "hello");
    assert_eq!(*r2, "hello");

    // 不可变借用结束后可以有可变借用 / Can have mutable borrow after immutable borrows end
    let r3 = &mut s;
    r3.push_str(", world");
    assert_eq!(*r3, "hello, world");
}

#[test]
fn test_lifetime_inference() {
    // 测试生命周期推断 / Test lifetime inference
    let string1 = String::from("long string is long");
    let string2 = String::from("xyz");

    let result = longest(&string1, &string2);
    assert_eq!(result, "long string is long");
}

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

#[test]
fn test_smart_pointers() {
    // 测试智能指针 / Test smart pointers
    use std::rc::Rc;
    use std::cell::RefCell;

    let data = Rc::new(RefCell::new(vec![1, 2, 3]));
    let data_clone = Rc::clone(&data);

    data.borrow_mut().push(4);
    data_clone.borrow_mut().push(5);

    assert_eq!(data.borrow().len(), 5);
    assert_eq!(Rc::strong_count(&data), 2);
}

#[test]
fn test_error_handling() {
    // 测试错误处理 / Test error handling
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    let result1 = divide(10, 2);
    assert!(result1.is_ok());
    assert_eq!(result1.unwrap(), 5);

    let result2 = divide(10, 0);
    assert!(result2.is_err());
    assert_eq!(result2.unwrap_err(), "Division by zero");
}

#[test]
fn test_performance_optimization() {
    // 测试性能优化 / Test performance optimization
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 零成本抽象 / Zero-cost abstractions
    let sum: i32 = numbers.iter()
        .map(|x| x * x)
        .filter(|&x| x % 2 == 0)
        .sum();

    assert_eq!(sum, 220); // 4 + 16 + 36 + 64 + 100
}

/// # 8. 压力测试 / Stress Tests

#[test]
fn test_high_concurrency() {
    let shared_counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 创建大量线程 / Create many threads
    for _ in 0..100 {
        let counter_clone = Arc::clone(&shared_counter);
        let handle = thread::spawn(move || {
            let mut counter = counter_clone.lock().unwrap();
            *counter += 1;
        });
        handles.push(handle);
    }

    // 等待所有线程完成 / Wait for all threads to complete
    for handle in handles {
        handle.join().unwrap();
    }

    // 验证结果 / Verify results
    let final_counter = shared_counter.lock().unwrap();
    assert_eq!(*final_counter, 100);
}

#[test]
fn test_memory_intensive_operations() {
    // 测试内存密集型操作 / Test memory-intensive operations
    let mut large_data = Vec::with_capacity(10000);

    for i in 0..10000 {
        large_data.push(i);
    }

    // 处理大量数据 / Process large amounts of data
    let processed_data: Vec<i32> = large_data.iter()
        .map(|x| x * 2)
        .filter(|&x| x % 2 == 0)
        .collect();

    assert_eq!(processed_data.len(), 10000);

    // 清理内存 / Clean up memory
    large_data.clear();
    large_data.shrink_to_fit();
    assert_eq!(large_data.capacity(), 0);
}

#[test]
fn test_complex_ownership_patterns() {
    // 测试复杂所有权模式 / Test complex ownership patterns
    use std::collections::HashMap;

    let mut data_map = HashMap::new();
    data_map.insert("key1".to_string(), vec![1, 2, 3]);
    data_map.insert("key2".to_string(), vec![4, 5, 6]);

    // 复杂的所有权操作 / Complex ownership operations
    let mut processed_map = HashMap::new();
    for (key, mut values) in data_map {
        values.push(values.len() as i32);
        processed_map.insert(key, values);
    }

    assert_eq!(processed_map.len(), 2);
    assert_eq!(processed_map["key1"], vec![1, 2, 3, 3]);
    assert_eq!(processed_map["key2"], vec![4, 5, 6, 3]);
}
