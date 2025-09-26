//! Rust 1.90 内存安全高级演示示例
//! 
//! 本示例展示了如何使用 c02_type_system 库中的内存安全高级特性模块。

use c02_type_system::memory_safety_advanced::*;
use std::time::Duration;
use std::thread;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🛡️  Rust 1.90 内存安全高级演示");
    println!("=================================");
    
    // 运行主演示函数
    demonstrate_memory_safety_advanced();
    
    // 额外的详细演示
    demonstrate_advanced_lifetimes();
    demonstrate_memory_layout_optimization();
    demonstrate_zero_cost_abstractions();
    demonstrate_smart_pointers();
    demonstrate_memory_leak_detection();
    demonstrate_buffer_overflow_protection();
    demonstrate_memory_alignment_cache();
    
    Ok(())
}

/// 演示高级生命周期管理
fn demonstrate_advanced_lifetimes() {
    println!("\n🔗 高级生命周期管理详细演示");
    println!("=============================");
    
    // 1. 生命周期追踪器演示
    println!("\n--- 生命周期追踪器演示 ---");
    let data = 42i32;
    let tracker = advanced_lifetimes::LifetimeTracker::new(&data, 1);
    
    println!("  📊 追踪器信息:");
    println!("    ID: {}", tracker.tracker_id());
    println!("    年龄: {:?}", tracker.age());
    println!("    数据: {}", tracker.get_data());
    
    // 模拟时间流逝
    thread::sleep(Duration::from_millis(100));
    println!("    更新后年龄: {:?}", tracker.age());
    
    // 2. 生命周期组合器演示
    println!("\n--- 生命周期组合器演示 ---");
    let short_data = 100i32;
    let long_data = "长期数据".to_string();
    
    let combinator = advanced_lifetimes::LifetimeCombinator::new(&short_data, &long_data);
    
    println!("  🔗 生命周期组合:");
    println!("    短期数据: {}", combinator.get_short());
    println!("    长期数据: {}", combinator.get_long());
    
    let combined_result = combinator.combine(|short, long| {
        format!("组合结果: {} + {}", short, long)
    });
    println!("    {}", combined_result);
    
    // 3. 生命周期验证器演示
    println!("\n--- 生命周期验证器演示 ---");
    let mut validator = advanced_lifetimes::LifetimeValidator::new("test_lifetime");
    
    println!("  ✅ 生命周期验证:");
    println!("    ID: {}", validator.lifetime_id());
    println!("    是否有效: {}", validator.validate());
    
    // 模拟生命周期失效
    validator.invalidate();
    println!("    失效后是否有效: {}", validator.validate());
}

/// 演示内存布局优化
fn demonstrate_memory_layout_optimization() {
    println!("\n🏗️  内存布局优化详细演示");
    println!("=========================");
    
    // 1. 缓存行对齐演示
    println!("\n--- 缓存行对齐演示 ---");
    let aligned_int = memory_layout::CacheAligned::new(42u64);
    let aligned_string = memory_layout::CacheAligned::new("Hello, World!".to_string());
    
    println!("  📐 缓存对齐结构:");
    println!("    对齐整数: {}", aligned_int.get());
    println!("    对齐字符串: {}", aligned_string.get());
    
    // 2. 内存池演示
    println!("\n--- 内存池演示 ---");
    let pool = memory_layout::MemoryPool::new(1024, 5);
    
    println!("  🏊 内存池信息:");
    println!("    总块数: {}", pool.total_blocks);
    println!("    块大小: {} 字节", pool.block_size);
    println!("    可用块数: {}", pool.available_blocks());
    
    // 分配一些内存块
    let mut allocated_blocks = Vec::new();
    for i in 0..3 {
        if let Some(ptr) = pool.allocate() {
            allocated_blocks.push(ptr);
            println!("    分配块 {}: {:p}", i, ptr);
        }
    }
    
    println!("    分配后可用块数: {}", pool.available_blocks());
    
    // 释放内存块
    for (i, ptr) in allocated_blocks.iter().enumerate() {
        pool.deallocate(*ptr);
        println!("    释放块 {}: {:p}", i, ptr);
    }
    
    println!("    释放后可用块数: {}", pool.available_blocks());
    
    // 3. 内存对齐工具演示
    println!("\n--- 内存对齐工具演示 ---");
    let addr = 0x1001;
    let alignment = 8;
    
    println!("  🔧 对齐工具:");
    println!("    原始地址: 0x{:x}", addr);
    println!("    对齐大小: {}", alignment);
    println!("    向上对齐: 0x{:x}", memory_layout::AlignmentUtils::align_up(addr, alignment));
    println!("    向下对齐: 0x{:x}", memory_layout::AlignmentUtils::align_down(addr, alignment));
    println!("    是否对齐: {}", memory_layout::AlignmentUtils::is_aligned(addr, alignment));
    
    println!("    u64 对齐: {}", memory_layout::AlignmentUtils::get_alignment::<u64>());
    println!("    u64 大小: {}", memory_layout::AlignmentUtils::get_size::<u64>());
}

/// 演示零成本抽象
fn demonstrate_zero_cost_abstractions() {
    println!("\n⚡ 零成本抽象详细演示");
    println!("=====================");
    
    // 1. 零成本包装器演示
    println!("\n--- 零成本包装器演示 ---");
    let mut wrapper = zero_cost_abstractions::ZeroCostWrapper::new(42);
    
    println!("  📦 零成本包装器:");
    println!("    初始值: {}", *wrapper);
    
    *wrapper = 100;
    println!("    修改后值: {}", *wrapper);
    
    let inner_value = wrapper.into_inner();
    println!("    提取内部值: {}", inner_value);
    
    // 2. 编译时计算演示
    println!("\n--- 编译时计算演示 ---");
    const FACTORIAL_3: u32 = zero_cost_abstractions::compile_time_factorial(3);
    const FACTORIAL_6: u32 = zero_cost_abstractions::compile_time_factorial(6);
    
    println!("  🧮 编译时计算:");
    println!("    3! = {}", FACTORIAL_3);
    println!("    6! = {}", FACTORIAL_6);
    
    // 3. 零成本迭代器演示
    println!("\n--- 零成本迭代器演示 ---");
    let data = vec![1, 2, 3, 4, 5];
    let mut iter = zero_cost_abstractions::ZeroCostIterator::new(&data);
    
    println!("  🔄 零成本迭代器:");
    while let Some(item) = iter.next() {
        println!("    迭代项: {}", item);
    }
}

/// 演示智能指针
fn demonstrate_smart_pointers() {
    println!("\n🧠 智能指针详细演示");
    println!("===================");
    
    // 1. 引用计数智能指针演示
    println!("\n--- 引用计数智能指针演示 ---");
    let rc1 = smart_pointers::RefCounted::new(42);
    println!("  📊 引用计数智能指针:");
    println!("    初始值: {}", rc1.get());
    
    let rc2 = rc1.clone();
    println!("    克隆后值: {}", rc2.get());
    
    // 修改值
    *rc1.get_mut() = 100;
    println!("    修改后 rc1: {}", rc1.get());
    println!("    修改后 rc2: {}", rc2.get());
    
    // 2. 弱引用演示
    println!("\n--- 弱引用演示 ---");
    let rc = smart_pointers::RefCounted::new(200);
    let weak = smart_pointers::WeakRef::new(&rc);
    
    println!("  🔗 弱引用:");
    if let Some(upgraded) = weak.upgrade() {
        println!("    弱引用升级成功: {}", upgraded.get());
    } else {
        println!("    弱引用升级失败");
    }
    
    // 3. 自定义分配器演示
    println!("\n--- 自定义分配器演示 ---");
    let pool = memory_layout::MemoryPool::new(512, 3);
    let _allocator = smart_pointers::CustomAllocator::new(pool);
    
    println!("  🏗️  自定义分配器:");
    println!("    分配器已创建，使用内存池进行分配");
}

/// 演示内存泄漏检测
fn demonstrate_memory_leak_detection() {
    println!("\n🔍 内存泄漏检测详细演示");
    println!("=======================");
    
    // 1. 内存泄漏检测器演示
    println!("\n--- 内存泄漏检测器演示 ---");
    let detector = memory_leak_detection::MemoryLeakDetector::new();
    
    println!("  🔍 内存泄漏检测:");
    let initial_stats = detector.get_memory_stats();
    println!("    初始统计: 总分配={}, 总释放={}, 当前分配={}", 
             initial_stats.total_allocated, 
             initial_stats.total_deallocated, 
             initial_stats.current_allocations);
    
    // 模拟一些分配
    let mock_ptr1 = 0x1000 as *mut u8;
    let mock_ptr2 = 0x2000 as *mut u8;
    
    detector.track_allocation(mock_ptr1, 1024);
    detector.track_allocation(mock_ptr2, 2048);
    
    let after_alloc_stats = detector.get_memory_stats();
    println!("    分配后统计: 总分配={}, 总释放={}, 当前分配={}", 
             after_alloc_stats.total_allocated, 
             after_alloc_stats.total_deallocated, 
             after_alloc_stats.current_allocations);
    
    // 模拟一些释放
    detector.track_deallocation(mock_ptr1);
    
    let after_dealloc_stats = detector.get_memory_stats();
    println!("    释放后统计: 总分配={}, 总释放={}, 当前分配={}", 
             after_dealloc_stats.total_allocated, 
             after_dealloc_stats.total_deallocated, 
             after_dealloc_stats.current_allocations);
    
    // 检查泄漏
    let leaks = detector.get_leaks();
    println!("    检测到泄漏数: {}", leaks.len());
    for (i, leak) in leaks.iter().enumerate() {
        println!("      泄漏 {}: 大小={}, 时间={:?}", i, leak.size, leak.timestamp);
    }
}

/// 演示缓冲区溢出防护
fn demonstrate_buffer_overflow_protection() {
    println!("\n🛡️  缓冲区溢出防护详细演示");
    println!("=========================");
    
    // 1. 安全缓冲区演示
    println!("\n--- 安全缓冲区演示 ---");
    let mut safe_buffer = buffer_overflow_protection::SafeBuffer::new(50);
    
    println!("  🛡️  安全缓冲区:");
    
    // 正常写入
    match safe_buffer.write(0, b"Hello, World!") {
        Ok(_) => println!("    ✅ 正常写入成功"),
        Err(e) => println!("    ❌ 写入失败: {}", e),
    }
    
    // 正常读取
    match safe_buffer.read(0, 13) {
        Ok(data) => println!("    ✅ 正常读取: {}", String::from_utf8_lossy(data)),
        Err(e) => println!("    ❌ 读取失败: {}", e),
    }
    
    // 尝试溢出写入
    let large_data = vec![0u8; 100];
    match safe_buffer.write(0, &large_data) {
        Ok(_) => println!("    ❌ 溢出写入成功 (不应该发生)"),
        Err(e) => println!("    ✅ 溢出写入被阻止: {}", e),
    }
    
    // 尝试越界读取
    match safe_buffer.read(40, 20) {
        Ok(_) => println!("    ❌ 越界读取成功 (不应该发生)"),
        Err(e) => println!("    ✅ 越界读取被阻止: {}", e),
    }
    
    // 2. 边界检查工具演示
    println!("\n--- 边界检查工具演示 ---");
    let data = vec![1, 2, 3, 4, 5];
    
    println!("  🔍 边界检查:");
    
    // 正常访问
    match buffer_overflow_protection::BoundsChecker::safe_get(&data, 2) {
        Ok(value) => println!("    ✅ 正常访问索引 2: {}", value),
        Err(e) => println!("    ❌ 访问失败: {}", e),
    }
    
    // 越界访问
    match buffer_overflow_protection::BoundsChecker::safe_get(&data, 10) {
        Ok(value) => println!("    ❌ 越界访问成功 (不应该发生): {}", value),
        Err(e) => println!("    ✅ 越界访问被阻止: {}", e),
    }
    
    // 修改访问
    let mut mut_data = data.clone();
    match buffer_overflow_protection::BoundsChecker::safe_get_mut(&mut mut_data, 1) {
        Ok(value) => {
            *value = 100;
            println!("    ✅ 正常修改索引 1: {}", value);
        },
        Err(e) => println!("    ❌ 修改失败: {}", e),
    }
}

/// 演示内存对齐和缓存优化
fn demonstrate_memory_alignment_cache() {
    println!("\n⚡ 内存对齐和缓存优化详细演示");
    println!("=============================");
    
    // 1. 缓存友好结构演示
    println!("\n--- 缓存友好结构演示 ---");
    let mut cache_friendly = memory_alignment_cache::CacheFriendlyStruct::new();
    
    println!("  🏗️  缓存友好结构:");
    
    // 更新热数据
    for i in 0..8 {
        cache_friendly.update_hot_data(i, (i * 10) as u64);
    }
    
    println!("    热数据: {:?}", cache_friendly.hot_data);
    
    // 读取热数据
    for i in 0..8 {
        if let Some(value) = cache_friendly.get_hot_data(i) {
            println!("    热数据[{}]: {}", i, value);
        }
    }
    
    // 2. 内存访问模式优化演示
    println!("\n--- 内存访问模式优化演示 ---");
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    println!("  🔄 内存访问模式:");
    
    // 顺序访问
    println!("    顺序访问:");
    memory_alignment_cache::MemoryAccessOptimizer::sequential_access(&data, |x| {
        print!("      {}", x);
    });
    println!();
    
    // 随机访问
    let indices = vec![0, 2, 4, 6, 8];
    println!("    随机访问 (索引: {:?}):", indices);
    memory_alignment_cache::MemoryAccessOptimizer::random_access(&data, &indices, |x| {
        print!("      {}", x);
    });
    println!();
    
    // 分块访问
    println!("    分块访问 (块大小: 3):");
    memory_alignment_cache::MemoryAccessOptimizer::blocked_access(&data, 3, |chunk| {
        print!("      {:?}", chunk);
    });
    println!();
    
    // 3. 内存预取演示
    println!("\n--- 内存预取演示 ---");
    let prefetch_data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    
    println!("  🚀 内存预取:");
    for (i, value) in prefetch_data.iter().enumerate() {
        if i < prefetch_data.len() - 1 {
            // 预取下一个元素
            memory_alignment_cache::MemoryPrefetcher::prefetch_read(&prefetch_data[i + 1]);
        }
        println!("    处理元素 {}: {}", i, value);
    }
    
    println!("\n✅ 所有内存安全高级演示完成！");
}
