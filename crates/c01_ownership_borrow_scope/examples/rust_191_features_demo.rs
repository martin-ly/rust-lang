//! Rust 1.91 特性演示示例
//!
//! 本示例展示了 Rust 1.91 中与所有权、借用、生命周期相关的新特性和改进：
//!
//! 1. 改进的类型检查器（借用检查器优化）
//! 2. 增强的 const 上下文（对生命周期的影响）
//! 3. 优化的内存分配器（所有权和内存管理改进）
//! 4. 改进的生命周期推断（编译时优化）

use c01_ownership_borrow_scope::rust_191_features::*;

fn main() {
    println!("=== Rust 1.91 特性演示示例 ===\n");

    // 1. 改进的类型检查器（借用检查器优化）
    demo_improved_borrow_checker();

    // 2. 增强的 const 上下文（对生命周期的影响）
    demo_enhanced_const_context();

    // 3. 优化的内存分配器（所有权和内存管理改进）
    demo_optimized_memory_allocator();

    // 4. 改进的生命周期推断（编译时优化）
    demo_improved_lifetime_inference();

    println!("\n=== 所有演示完成 ===");
}

/// 演示改进的借用检查器
fn demo_improved_borrow_checker() {
    println!("1. 改进的类型检查器（借用检查器优化）");
    println!("   Rust 1.91: 编译时间减少 10-20%，借用检查器缓存机制\n");

    let mut checker = Rust191BorrowChecker::new();

    // 创建多个借用
    println!("   创建 100 个不可变借用...");
    for i in 0..100 {
        let owner = format!("owner_{}", i % 10); // 10 个不同的所有者
        let borrower = format!("borrower_{}", i);

        match checker.create_borrow(
            owner,
            borrower,
            BorrowType191::Immutable,
        ) {
            Ok(_) => {
                if i < 3 {
                    println!("   ✓ 借用 {} 创建成功", i);
                }
            }
            Err(e) => {
                println!("   ✗ 借用 {} 创建失败: {:?}", i, e);
            }
        }
    }

    // 查看统计信息
    let stats = checker.get_statistics();
    println!("\n   统计信息:");
    println!("   - 总检查次数: {}", stats.total_checks);
    println!("   - 缓存命中: {}", stats.cache_hits);
    println!("   - 缓存未命中: {}", stats.cache_misses);
    if stats.total_checks > 0 {
        let hit_rate = (stats.cache_hits as f64 / stats.total_checks as f64) * 100.0;
        println!("   - 缓存命中率: {:.2}%", hit_rate);
    }
    println!("   - 平均检查时间: {} μs", stats.avg_check_time);
    println!("   - 借用冲突次数: {}\n", stats.conflicts);
}

/// 演示增强的 const 上下文
fn demo_enhanced_const_context() {
    println!("2. 增强的 const 上下文（对生命周期的影响）");
    println!("   Rust 1.91: 可以在 const 上下文中创建对非静态常量的引用\n");

    // Rust 1.91: 可以引用非静态常量
    const VALUE: i32 = 42;
    const REF: &i32 = &VALUE; // ✅ Rust 1.91 支持
    const LITERAL_REF: &i32 = &100; // ✅ 可以直接引用字面量

    println!("   const VALUE: i32 = {}", VALUE);
    println!("   const REF: &i32 = &VALUE  // ✅ Rust 1.91");
    println!("   REF 的值: {}\n", *REF);

    println!("   const LITERAL_REF: &i32 = &100  // ✅ Rust 1.91");
    println!("   LITERAL_REF 的值: {}\n", *LITERAL_REF);

    // 配置系统示例
    const MAX_CONNECTIONS: usize = 100;
    const BUFFER_SIZE: usize = 1024;
    const TOTAL_SIZE: usize = MAX_CONNECTIONS * BUFFER_SIZE;

    // Rust 1.91: 可以创建对计算结果的引用
    const SIZE_REF: &usize = &TOTAL_SIZE;
    const SIZE_DOUBLED: usize = *SIZE_REF * 2;

    println!("   配置系统示例:");
    println!("   const MAX_CONNECTIONS: usize = {}", MAX_CONNECTIONS);
    println!("   const BUFFER_SIZE: usize = {}", BUFFER_SIZE);
    println!("   const TOTAL_SIZE: usize = {}", TOTAL_SIZE);
    println!("   const SIZE_REF: &usize = &TOTAL_SIZE  // ✅ Rust 1.91");
    println!("   SIZE_REF 的值: {}", *SIZE_REF);
    println!("   SIZE_DOUBLED: {}\n", SIZE_DOUBLED);

    // 创建 const 上下文中的生命周期推断器
    let mut inferencer = ConstContextLifetimeInferencer191::new_in_const_context();
    let lifetime1 = inferencer.infer_lifetime("'a".to_string(), "const_scope".to_string());
    let lifetime2 = inferencer.infer_lifetime("'b".to_string(), "const_scope".to_string());

    println!("   生命周期推断（const 上下文）:");
    println!("   lifetime1: {:?}", lifetime1);
    println!("   lifetime2: {:?}", lifetime2);

    let constraint_result = inferencer.check_lifetime_constraints(&lifetime1, &lifetime2);
    println!("   生命周期约束检查（const 上下文）: {}\n", constraint_result);
}

/// 演示优化的内存分配器
fn demo_optimized_memory_allocator() {
    println!("3. 优化的内存分配器（所有权和内存管理改进）");
    println!("   Rust 1.91: 小对象分配性能提升 25-30%，对象池优化\n");

    let mut manager = OptimizedMemoryManager191::new();

    // 分配小对象（使用对象池优化）
    println!("   分配 50 个小对象（16 bytes）...");
    for i in 0..50 {
        let id = format!("small_{}", i);
        manager.record_allocation(id, 16, AllocationType191::SmallPool);
        if i < 3 {
            println!("   ✓ 分配小对象 {}", i);
        }
    }

    // 释放一些对象（归还到池中）
    println!("\n   释放前 20 个对象（归还到池中）...");
    for i in 0..20 {
        let id = format!("small_{}", i);
        match manager.record_deallocation(&id) {
            Ok(_) => {
                if i < 3 {
                    println!("   ✓ 释放对象 {}", i);
                }
            }
            Err(e) => {
                println!("   ✗ 释放对象 {} 失败: {}", i, e);
            }
        }
    }

    // 再次分配（应该复用池中的对象）
    println!("\n   再次分配 10 个对象（应该复用池中的对象）...");
    for i in 0..10 {
        let id = format!("small_{}", i);
        manager.record_allocation(id, 16, AllocationType191::SmallPool);
        if i < 3 {
            println!("   ✓ 复用对象 {}", i);
        }
    }

    // 查看统计信息
    let stats = manager.get_statistics();
    println!("\n   统计信息:");
    println!("   - 总分配数: {}", stats.total_allocations);
    println!("   - 小对象分配数: {}", stats.small_object_allocations);
    println!("   - 小对象池命中次数: {}", stats.small_pool_hits);
    if stats.small_object_allocations > 0 {
        let hit_rate =
            (stats.small_pool_hits as f64 / stats.small_object_allocations as f64) * 100.0;
        println!("   - 小对象池命中率: {:.2}%", hit_rate);
    }
    println!("   - 总分配大小: {} bytes", stats.total_size);
    println!("   - 活跃分配数: {}\n", stats.active_allocations);
}

/// 演示改进的生命周期推断
fn demo_improved_lifetime_inference() {
    println!("4. 改进的生命周期推断（编译时优化）");
    println!("   Rust 1.91: 编译时间减少 10-20%，生命周期推断缓存\n");

    let mut inferencer = OptimizedLifetimeInferencer191::new();

    // 推断生命周期（使用缓存优化）
    println!("   推断 50 个生命周期参数...");
    for i in 0..50 {
        let name = format!("'a_{}", i % 10); // 10 个不同的生命周期名称
        let scope = format!("scope_{}", i % 5); // 5 个不同的作用域

        let _lifetime = inferencer.infer_lifetime_cached(name, scope);
        if i < 3 {
            println!("   ✓ 推断生命周期 {}", i);
        }
    }

    // 查看统计信息
    let stats = inferencer.get_statistics();
    println!("\n   统计信息:");
    println!("   - 总推断次数: {}", stats.total_inferences);
    println!("   - 缓存命中: {}", stats.cache_hits);
    if stats.total_inferences > 0 {
        let hit_rate =
            (stats.cache_hits as f64 / stats.total_inferences as f64) * 100.0;
        println!("   - 缓存命中率: {:.2}%", hit_rate);
    }
    println!("   - 平均推断时间: {} μs\n", stats.avg_inference_time);
}

/// 运行完整的 Rust 1.91 特性示例
#[allow(dead_code)]
fn run_complete_demo() {
    println!("=== 运行完整的 Rust 1.91 特性示例 ===\n");
    run_all_rust_191_features_examples();
}
