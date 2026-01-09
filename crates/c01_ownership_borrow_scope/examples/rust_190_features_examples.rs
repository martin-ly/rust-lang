//! # Rust 1.90 特性示例 / Rust 1.90 Features Examples (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//!
//! 本示例展示了 Rust 1.90 版本的新特性和改进，包括：
//! This example demonstrates new features and improvements in Rust 1.90, including:
//!
//! - 改进的借用检查器 / Improved borrow checker
//! - 增强的生命周期推断 / Enhanced lifetime inference
//! - 新的智能指针特性 / New smart pointer features
//! - 优化的作用域管理 / Optimized scope management
//! - 增强的并发安全 / Enhanced concurrency safety
//! - 智能内存管理 / Smart memory management

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
    run_all_rust_190_features_examples,
    get_rust_190_features_info,
    // 基础语法 / Basic Syntax
    run_all_basic_syntax_examples,
    get_basic_syntax_info,
};

// 导入 Rust 1.90 特性模块中的类型 / Import types from Rust 1.90 features module
use c01_ownership_borrow_scope::rust_190_features::BorrowType;

/// 主函数 / Main Function
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("{}", get_rust_190_features_info());
    println!("{}", get_basic_syntax_info());

    println!("\n=== 运行 Rust 1.90 特性示例 / Running Rust 1.90 Features Examples ===");
    run_all_rust_190_features_examples();

    println!("\n=== 运行基础语法示例 / Running Basic Syntax Examples ===");
    run_all_basic_syntax_examples();

    println!("\n=== 运行详细示例 / Running Detailed Examples ===");

    // 1. 改进的借用检查器示例 / Improved Borrow Checker Example
    improved_borrow_checker_detailed_example();

    // 2. 增强的生命周期推断示例 / Enhanced Lifetime Inference Example
    enhanced_lifetime_inference_detailed_example();

    // 3. 新的智能指针特性示例 / New Smart Pointer Features Example
    new_smart_pointer_features_detailed_example();

    // 4. 优化的作用域管理示例 / Optimized Scope Management Example
    optimized_scope_management_detailed_example();

    // 5. 增强的并发安全示例 / Enhanced Concurrency Safety Example
    enhanced_concurrency_safety_detailed_example();

    // 6. 智能内存管理示例 / Smart Memory Management Example
    smart_memory_management_detailed_example();

    println!("\n=== 所有示例运行完成 / All Examples Completed ===");

    Ok(())
}

/// 改进的借用检查器详细示例 / Improved Borrow Checker Detailed Example
fn improved_borrow_checker_detailed_example() {
    println!("\n--- 改进的借用检查器详细示例 / Improved Borrow Checker Detailed Example ---");

    let mut checker = ImprovedBorrowChecker::new();

    // 创建不可变借用 / Create immutable borrows
    println!("创建不可变借用 / Creating immutable borrows");
    let borrow1 = checker.create_borrow("owner1".to_string(), "borrower1".to_string(), BorrowType::Immutable);
    match borrow1 {
        Ok(record) => println!("✓ 不可变借用创建成功 / Immutable borrow created successfully: {:?}", record),
        Err(result) => println!("✗ 不可变借用创建失败 / Immutable borrow creation failed: {:?}", result),
    }

    let borrow2 = checker.create_borrow("owner1".to_string(), "borrower2".to_string(), BorrowType::Immutable);
    match borrow2 {
        Ok(record) => println!("✓ 第二个不可变借用创建成功 / Second immutable borrow created successfully: {:?}", record),
        Err(result) => println!("✗ 第二个不可变借用创建失败 / Second immutable borrow creation failed: {:?}", result),
    }

    // 尝试创建可变借用（应该失败）/ Try to create mutable borrow (should fail)
    println!("\n尝试创建可变借用 / Attempting to create mutable borrow");
    let borrow3 = checker.create_borrow("owner1".to_string(), "borrower3".to_string(), BorrowType::Mutable);
    match borrow3 {
        Ok(record) => println!("✓ 可变借用创建成功 / Mutable borrow created successfully: {:?}", record),
        Err(result) => println!("✗ 可变借用创建失败（预期）/ Mutable borrow creation failed (expected): {:?}", result),
    }

    // 尝试创建独占借用（应该失败）/ Try to create exclusive borrow (should fail)
    println!("\n尝试创建独占借用 / Attempting to create exclusive borrow");
    let borrow4 = checker.create_borrow("owner1".to_string(), "borrower4".to_string(), BorrowType::Exclusive);
    match borrow4 {
        Ok(record) => println!("✓ 独占借用创建成功 / Exclusive borrow created successfully: {:?}", record),
        Err(result) => println!("✗ 独占借用创建失败（预期）/ Exclusive borrow creation failed (expected): {:?}", result),
    }

    // 获取统计信息 / Get statistics
    let stats = checker.get_borrow_statistics();
    println!("\n借用统计信息 / Borrow Statistics: {:?}", stats);
}

/// 增强的生命周期推断详细示例 / Enhanced Lifetime Inference Detailed Example
fn enhanced_lifetime_inference_detailed_example() {
    println!("\n--- 增强的生命周期推断详细示例 / Enhanced Lifetime Inference Detailed Example ---");

    let mut inferencer = LifetimeInferencer::new();

    // 推断生命周期 / Infer lifetimes
    println!("推断生命周期 / Inferring lifetimes");
    let lifetime1 = inferencer.infer_lifetime("'a".to_string(), "scope1".to_string());
    let lifetime2 = inferencer.infer_lifetime("'b".to_string(), "scope2".to_string());
    let lifetime3 = inferencer.infer_lifetime("'c".to_string(), "scope3".to_string());

    println!("生命周期 'a: {:?}", lifetime1);
    println!("生命周期 'b: {:?}", lifetime2);
    println!("生命周期 'c: {:?}", lifetime3);

    // 添加约束 / Add constraints
    println!("\n添加生命周期约束 / Adding lifetime constraints");
    let mut lifetime1_mut = lifetime1.clone();
    lifetime1_mut.add_constraint("'b".to_string());
    lifetime1_mut.add_constraint("'c".to_string());

    let mut lifetime2_mut = lifetime2.clone();
    lifetime2_mut.add_constraint("'a".to_string());

    println!("带约束的生命周期 'a: {:?}", lifetime1_mut);
    println!("带约束的生命周期 'b: {:?}", lifetime2_mut);

    // 检查生命周期约束 / Check lifetime constraints
    println!("\n检查生命周期约束 / Checking lifetime constraints");
    let constraint_result = inferencer.check_lifetime_constraints(&lifetime1_mut, &lifetime2_mut);
    println!("生命周期约束检查结果 / Lifetime constraint check result: {}", constraint_result);

    // 优化生命周期 / Optimize lifetime
    println!("\n优化生命周期 / Optimizing lifetime");
    let optimized_lifetime = inferencer.optimize_lifetime(&lifetime1_mut);
    println!("优化后的生命周期 / Optimized lifetime: {:?}", optimized_lifetime);
}

/// 新的智能指针特性详细示例 / New Smart Pointer Features Detailed Example
fn new_smart_pointer_features_detailed_example() {
    println!("\n--- 新的智能指针特性详细示例 / New Smart Pointer Features Detailed Example ---");

    let mut manager = SmartPointerManager::new();

    // 创建不同类型的智能指针 / Create different types of smart pointers
    println!("创建智能指针 / Creating smart pointers");
    manager.create_smart_pointer("rc_ptr".to_string(), SmartPointerType::Rc);
    manager.create_smart_pointer("arc_ptr".to_string(), SmartPointerType::Arc);
    manager.create_smart_pointer("box_ptr".to_string(), SmartPointerType::Box);
    manager.create_smart_pointer("refcell_ptr".to_string(), SmartPointerType::RefCell);
    manager.create_smart_pointer("smart_opt_ptr".to_string(), SmartPointerType::SmartOptimized);

    // 克隆智能指针 / Clone smart pointers
    println!("\n克隆智能指针 / Cloning smart pointers");
    for i in 0..5 {
        let result = manager.clone_smart_pointer("rc_ptr");
        match result {
            Ok(_) => println!("✓ Rc 指针克隆成功 #{} / Rc pointer cloned successfully #{}", i + 1, i + 1),
            Err(e) => println!("✗ Rc 指针克隆失败 / Rc pointer clone failed: {}", e),
        }
    }

    for i in 0..3 {
        let result = manager.clone_smart_pointer("arc_ptr");
        match result {
            Ok(_) => println!("✓ Arc 指针克隆成功 #{} / Arc pointer cloned successfully #{}", i + 1, i + 1),
            Err(e) => println!("✗ Arc 指针克隆失败 / Arc pointer clone failed: {}", e),
        }
    }

    // 获取引用计数 / Get reference counts
    println!("\n获取引用计数 / Getting reference counts");
    println!("rc_ptr 引用计数 / rc_ptr reference count: {:?}", manager.get_reference_count("rc_ptr"));
    println!("arc_ptr 引用计数 / arc_ptr reference count: {:?}", manager.get_reference_count("arc_ptr"));
    println!("box_ptr 引用计数 / box_ptr reference count: {:?}", manager.get_reference_count("box_ptr"));
    println!("refcell_ptr 引用计数 / refcell_ptr reference count: {:?}", manager.get_reference_count("refcell_ptr"));
    println!("smart_opt_ptr 引用计数 / smart_opt_ptr reference count: {:?}", manager.get_reference_count("smart_opt_ptr"));

    // 分析使用情况 / Analyze usage
    println!("\n分析智能指针使用情况 / Analyzing smart pointer usage");
    let suggestions = manager.analyze_usage();
    for suggestion in suggestions {
        println!("💡 优化建议 / Optimization suggestion: {}", suggestion);
    }
}

/// 优化的作用域管理详细示例 / Optimized Scope Management Detailed Example
fn optimized_scope_management_detailed_example() {
    println!("\n--- 优化的作用域管理详细示例 / Optimized Scope Management Detailed Example ---");

    let mut manager = OptimizedScopeManager::new();

    // 进入主作用域 / Enter main scope
    println!("进入主作用域 / Entering main scope");
    manager.enter_scope("main".to_string(), Rust190ScopeType::Function);
    manager.add_variable("main_var".to_string()).unwrap();
    manager.add_lifetime("'main".to_string()).unwrap();

    // 进入代码块作用域 / Enter block scope
    println!("进入代码块作用域 / Entering block scope");
    manager.enter_scope("block1".to_string(), Rust190ScopeType::Block);
    manager.add_variable("block1_var".to_string()).unwrap();
    manager.add_lifetime("'block1".to_string()).unwrap();

    // 进入嵌套作用域 / Enter nested scope
    println!("进入嵌套作用域 / Entering nested scope");
    manager.enter_scope("block2".to_string(), Rust190ScopeType::Block);
    manager.add_variable("block2_var".to_string()).unwrap();
    manager.add_lifetime("'block2".to_string()).unwrap();

    // 进入异步作用域 / Enter async scope
    println!("进入异步作用域 / Entering async scope");
    manager.enter_scope("async_scope".to_string(), Rust190ScopeType::Async);
    manager.add_variable("async_var".to_string()).unwrap();
    manager.add_lifetime("'async".to_string()).unwrap();

    // 进入宏作用域 / Enter macro scope
    println!("进入宏作用域 / Entering macro scope");
    manager.enter_scope("macro_scope".to_string(), Rust190ScopeType::Macro);
    manager.add_variable("macro_var".to_string()).unwrap();
    manager.add_lifetime("'macro".to_string()).unwrap();

    // 获取统计信息 / Get statistics
    let stats = manager.get_scope_statistics();
    println!("\n作用域统计信息 / Scope Statistics: {:?}", stats);

    // 退出作用域 / Exit scopes
    println!("\n退出作用域 / Exiting scopes");
    let scope_info = manager.exit_scope().unwrap();
    println!("退出的作用域 / Exited scope: {:?}", scope_info);

    let scope_info = manager.exit_scope().unwrap();
    println!("退出的作用域 / Exited scope: {:?}", scope_info);

    let scope_info = manager.exit_scope().unwrap();
    println!("退出的作用域 / Exited scope: {:?}", scope_info);

    let scope_info = manager.exit_scope().unwrap();
    println!("退出的作用域 / Exited scope: {:?}", scope_info);

    let scope_info = manager.exit_scope().unwrap();
    println!("退出的作用域 / Exited scope: {:?}", scope_info);

    // 获取最终统计信息 / Get final statistics
    let final_stats = manager.get_scope_statistics();
    println!("\n最终作用域统计信息 / Final Scope Statistics: {:?}", final_stats);
}

/// 增强的并发安全详细示例 / Enhanced Concurrency Safety Detailed Example
fn enhanced_concurrency_safety_detailed_example() {
    println!("\n--- 增强的并发安全详细示例 / Enhanced Concurrency Safety Detailed Example ---");

    let mut checker = ConcurrencySafetyChecker::new();

    // 注册线程 / Register threads
    println!("注册线程 / Registering threads");
    checker.register_thread("thread1".to_string(), "Worker Thread 1".to_string());
    checker.register_thread("thread2".to_string(), "Worker Thread 2".to_string());
    checker.register_thread("thread3".to_string(), "Worker Thread 3".to_string());

    // 注册锁 / Register locks
    println!("注册锁 / Registering locks");
    checker.register_lock("mutex1".to_string(), LockType::Mutex);
    checker.register_lock("rwlock1".to_string(), LockType::RwLock);
    checker.register_lock("condvar1".to_string(), LockType::ConditionVariable);

    // 记录资源访问 / Record resource access
    println!("\n记录资源访问 / Recording resource access");

    // 线程1的访问 / Thread 1 access
    checker.record_access("thread1".to_string(), "resource1".to_string(), AccessType::Write);
    checker.record_access("thread1".to_string(), "resource2".to_string(), AccessType::Read);

    // 线程2的访问 / Thread 2 access
    checker.record_access("thread2".to_string(), "resource1".to_string(), AccessType::Write);
    checker.record_access("thread2".to_string(), "resource3".to_string(), AccessType::Read);

    // 线程3的访问 / Thread 3 access
    checker.record_access("thread3".to_string(), "resource1".to_string(), AccessType::Exclusive);
    checker.record_access("thread3".to_string(), "resource4".to_string(), AccessType::Read);

    // 检测数据竞争 / Detect data races
    println!("\n检测数据竞争 / Detecting data races");
    let races = checker.detect_data_races();

    if races.is_empty() {
        println!("✓ 未检测到数据竞争 / No data races detected");
    } else {
        println!("⚠️ 检测到 {} 个数据竞争 / Detected {} data races", races.len(), races.len());
        for (i, race) in races.iter().enumerate() {
            println!("  数据竞争 #{} / Data race #{}: {}", i + 1, i + 1, race.description);
            println!("    规则 / Rule: {}", race.rule_name);
            println!("    访问1 / Access 1: Thread {} -> {} ({:?})",
                     race.access1.thread_id, race.access1.resource, race.access1.access_type);
            println!("    访问2 / Access 2: Thread {} -> {} ({:?})",
                     race.access2.thread_id, race.access2.resource, race.access2.access_type);
        }
    }
}

/// 智能内存管理详细示例 / Smart Memory Management Detailed Example
fn smart_memory_management_detailed_example() {
    println!("\n--- 智能内存管理详细示例 / Smart Memory Management Detailed Example ---");

    let mut manager = SmartMemoryManager::new();

    // 记录内存分配 / Record memory allocations
    println!("记录内存分配 / Recording memory allocations");
    manager.record_allocation("heap_alloc1".to_string(), 1024, AllocationType::Heap);
    manager.record_allocation("heap_alloc2".to_string(), 2048, AllocationType::Heap);
    manager.record_allocation("stack_alloc1".to_string(), 512, AllocationType::Stack);
    manager.record_allocation("stack_alloc2".to_string(), 256, AllocationType::Stack);
    manager.record_allocation("static_alloc1".to_string(), 4096, AllocationType::Static);

    // 记录大分配 / Record large allocations
    manager.record_allocation("large_heap_alloc".to_string(), 2 * 1024 * 1024, AllocationType::Heap); // 2MB
    manager.record_allocation("large_stack_alloc".to_string(), 1024 * 1024, AllocationType::Stack); // 1MB

    // 记录内存释放 / Record memory deallocation
    println!("\n记录内存释放 / Recording memory deallocation");
    match manager.record_deallocation("heap_alloc1") {
        Ok(_) => println!("✓ 堆分配1释放成功 / Heap allocation 1 freed successfully"),
        Err(e) => println!("✗ 堆分配1释放失败 / Heap allocation 1 free failed: {}", e),
    }

    match manager.record_deallocation("stack_alloc1") {
        Ok(_) => println!("✓ 栈分配1释放成功 / Stack allocation 1 freed successfully"),
        Err(e) => println!("✗ 栈分配1释放失败 / Stack allocation 1 free failed: {}", e),
    }

    // 尝试释放已释放的分配 / Try to free already freed allocation
    match manager.record_deallocation("heap_alloc1") {
        Ok(_) => println!("✓ 堆分配1再次释放成功 / Heap allocation 1 freed again successfully"),
        Err(e) => println!("✗ 堆分配1再次释放失败（预期）/ Heap allocation 1 free again failed (expected): {}", e),
    }

    // 尝试释放不存在的分配 / Try to free non-existent allocation
    match manager.record_deallocation("non_existent") {
        Ok(_) => println!("✓ 不存在分配释放成功 / Non-existent allocation freed successfully"),
        Err(e) => println!("✗ 不存在分配释放失败（预期）/ Non-existent allocation free failed (expected): {}", e),
    }

    // 获取内存统计信息 / Get memory statistics
    println!("\n获取内存统计信息 / Getting memory statistics");
    let stats = manager.get_memory_statistics();
    println!("内存统计信息 / Memory Statistics: {:?}", stats);

    // 分析内存使用 / Analyze memory usage
    println!("\n分析内存使用 / Analyzing memory usage");
    let suggestions = manager.analyze_memory_usage();

    if suggestions.is_empty() {
        println!("✓ 内存使用正常，无优化建议 / Memory usage is normal, no optimization suggestions");
    } else {
        println!("💡 内存优化建议 / Memory optimization suggestions:");
        for (i, suggestion) in suggestions.iter().enumerate() {
            println!("  {}. {}", i + 1, suggestion);
        }
    }
}
