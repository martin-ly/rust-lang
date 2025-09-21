//! 内存优化演示示例
//! 
//! 展示如何使用c17_iot的内存优化功能来管理IoT系统的内存使用

use c17_iot::memory_optimization::{
    MemoryOptimizer,
    //MemoryPool, 
    MemoryPoolConfig, 
    OptimizationConfig,
    //MemoryStats,
    //MemoryPoolStats,
    //OptimizationResult,
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动内存优化演示...");

    println!("📊 开始演示IoT系统内存优化功能...");

    // 1. 内存优化器创建和配置
    println!("\n1️⃣ 内存优化器创建和配置");
    demo_memory_optimizer_creation().await?;

    // 2. 内存池管理
    println!("\n2️⃣ 内存池管理");
    demo_memory_pool_management().await?;

    // 3. 内存监控
    println!("\n3️⃣ 内存监控");
    demo_memory_monitoring().await?;

    // 4. 自动优化
    println!("\n4️⃣ 自动优化");
    demo_automatic_optimization().await?;

    // 5. 内存清理
    println!("\n5️⃣ 内存清理");
    demo_memory_cleanup().await?;

    // 6. 性能对比
    println!("\n6️⃣ 性能对比");
    demo_performance_comparison().await?;

    // 7. 内存泄漏检测
    println!("\n7️⃣ 内存泄漏检测");
    demo_memory_leak_detection().await?;

    // 8. 优化建议
    println!("\n8️⃣ 优化建议");
    demo_optimization_recommendations().await?;

    println!("\n✅ 内存优化演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 智能内存池管理");
    println!("  - 实时内存监控");
    println!("  - 自动内存优化");
    println!("  - 内存泄漏检测");
    println!("  - 性能优化建议");

    Ok(())
}

/// 内存优化器创建和配置演示
async fn demo_memory_optimizer_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建优化配置
    let config = OptimizationConfig {
        auto_optimization: true,
        memory_threshold: 75.0,
        optimization_interval: Duration::from_secs(30),
        enable_compression: true,
        enable_preallocation: true,
        preallocation_size: 2 * 1024 * 1024, // 2MB
        enable_gc: true,
        gc_interval: Duration::from_secs(120), // 2分钟
    };

    println!("  创建内存优化器...");
    let optimizer = MemoryOptimizer::new(config);
    
    // 获取初始内存统计
    let stats = optimizer.get_memory_stats().await;
    println!("  初始内存统计:");
    println!("    总内存: {} 字节", stats.total_memory);
    println!("    已使用: {} 字节", stats.used_memory);
    println!("    可用内存: {} 字节", stats.available_memory);
    println!("    使用率: {:.2}%", stats.memory_usage_percent);

    Ok(())
}

/// 内存池管理演示
async fn demo_memory_pool_management() -> Result<(), Box<dyn std::error::Error>> {
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    // 创建多个内存池
    let pools_config = vec![
        ("sensor_data_pool", 1024, 10240, 512),
        ("communication_buffer", 2048, 20480, 1024),
        ("cache_pool", 512, 5120, 256),
        ("temp_storage", 4096, 40960, 2048),
    ];

    println!("  创建内存池...");
    for (name, initial, max, min) in pools_config {
        let config = MemoryPoolConfig {
            name: name.to_string(),
            initial_size: initial,
            max_size: max,
            min_size: min,
            growth_factor: 1.5,
            auto_cleanup: true,
            cleanup_interval: Duration::from_secs(60),
            max_idle_time: Duration::from_secs(300),
        };
        
        optimizer.create_memory_pool(config).await?;
        println!("    创建内存池: {} (初始: {}B, 最大: {}B, 最小: {}B)", 
                name, initial, max, min);
    }

    // 获取内存池统计
    let pool_stats = optimizer.get_all_pool_stats().await;
    println!("  内存池统计:");
    for (name, stats) in pool_stats {
        println!("    {}: 总项数={}, 可用={}, 使用中={}, 内存使用={}B", 
                name, stats.total_items, stats.available_items, 
                stats.used_items, stats.total_memory_usage);
    }

    Ok(())
}

/// 内存监控演示
async fn demo_memory_monitoring() -> Result<(), Box<dyn std::error::Error>> {
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    println!("  启动内存监控...");
    optimizer.start_monitoring().await?;
    
    // 模拟一些内存活动
    println!("  模拟内存活动...");
    for i in 0..5 {
        println!("    监控周期 {}: 模拟内存分配和释放", i + 1);
        
        // 获取当前内存统计
        let stats = optimizer.get_memory_stats().await;
        println!("      当前内存使用: {:.2}%", stats.memory_usage_percent);
        println!("      分配次数: {}", stats.allocation_count);
        println!("      释放次数: {}", stats.deallocation_count);
        
        sleep(Duration::from_millis(500)).await;
    }
    
    // 停止监控
    optimizer.stop_monitoring().await?;
    println!("  内存监控已停止");

    Ok(())
}

/// 自动优化演示
async fn demo_automatic_optimization() -> Result<(), Box<dyn std::error::Error>> {
    let config = OptimizationConfig {
        auto_optimization: true,
        memory_threshold: 50.0, // 降低阈值以便触发优化
        optimization_interval: Duration::from_secs(5),
        enable_compression: true,
        enable_preallocation: true,
        preallocation_size: 1024 * 1024,
        enable_gc: true,
        gc_interval: Duration::from_secs(30),
    };

    let optimizer = MemoryOptimizer::new(config);
    
    // 创建一些内存池
    let pool_config = MemoryPoolConfig {
        name: "test_pool".to_string(),
        initial_size: 1024,
        max_size: 10240,
        min_size: 512,
        growth_factor: 1.5,
        auto_cleanup: true,
        cleanup_interval: Duration::from_secs(10),
        max_idle_time: Duration::from_secs(20),
    };
    
    optimizer.create_memory_pool(pool_config).await?;
    
    println!("  启动自动优化...");
    optimizer.start_monitoring().await?;
    
    // 等待自动优化触发
    println!("  等待自动优化触发...");
    sleep(Duration::from_secs(10)).await;
    
    // 执行手动优化
    println!("  执行手动优化...");
    let result = optimizer.optimize().await?;
    println!("  优化结果:");
    println!("    释放内存: {} 字节", result.memory_freed);
    println!("    优化池数: {}", result.pools_optimized);
    println!("    移除项数: {}", result.items_removed);
    println!("    优化耗时: {:?}", result.optimization_time);
    
    optimizer.stop_monitoring().await?;

    Ok(())
}

/// 内存清理演示
async fn demo_memory_cleanup() -> Result<(), Box<dyn std::error::Error>> {
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    // 创建内存池
    let pool_config = MemoryPoolConfig {
        name: "cleanup_test_pool".to_string(),
        initial_size: 1024,
        max_size: 10240,
        min_size: 512,
        growth_factor: 1.5,
        auto_cleanup: true,
        cleanup_interval: Duration::from_secs(5),
        max_idle_time: Duration::from_secs(10),
    };
    
    optimizer.create_memory_pool(pool_config).await?;
    
    if let Some(pool) = optimizer.get_memory_pool("cleanup_test_pool").await {
        println!("  获取内存池项...");
        
        // 获取一些项
        let items = vec![
            pool.acquire(512).await?,
            pool.acquire(1024).await?,
            pool.acquire(768).await?,
        ];
        
        println!("  获取了 {} 个内存池项", items.len());
        
        // 释放一些项
        for (i, item) in items.iter().enumerate() {
            if i < 2 { // 只释放前两个
                pool.release(&item.id).await?;
                println!("  释放了内存池项: {}", item.id);
            }
        }
        
        // 等待清理
        println!("  等待自动清理...");
        sleep(Duration::from_secs(8)).await;
        
        // 手动清理
        println!("  执行手动清理...");
        let removed_count = pool.cleanup().await?;
        println!("  清理完成，移除了 {} 个项", removed_count);
        
        // 获取清理后的统计
        let stats = pool.get_stats().await;
        println!("  清理后统计:");
        println!("    总项数: {}", stats.total_items);
        println!("    可用项数: {}", stats.available_items);
        println!("    使用中项数: {}", stats.used_items);
        println!("    内存使用: {} 字节", stats.total_memory_usage);
    }

    Ok(())
}

/// 性能对比演示
async fn demo_performance_comparison() -> Result<(), Box<dyn std::error::Error>> {
    println!("  性能对比测试...");
    
    // 测试1: 无内存池的直接分配
    println!("  测试1: 直接内存分配");
    let start = std::time::Instant::now();
    let mut direct_allocations = Vec::new();
    
    for _i in 0..1000 {
        let data = vec![0u8; 1024];
        direct_allocations.push(data);
    }
    
    let direct_time = start.elapsed();
    println!("    直接分配1000个1KB块耗时: {:?}", direct_time);
    
    // 测试2: 使用内存池
    println!("  测试2: 内存池分配");
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    let pool_config = MemoryPoolConfig {
        name: "perf_test_pool".to_string(),
        initial_size: 1024,
        max_size: 100 * 1024,
        min_size: 512,
        growth_factor: 1.5,
        auto_cleanup: false,
        cleanup_interval: Duration::from_secs(60),
        max_idle_time: Duration::from_secs(300),
    };
    
    optimizer.create_memory_pool(pool_config).await?;
    
    if let Some(pool) = optimizer.get_memory_pool("perf_test_pool").await {
        let start = std::time::Instant::now();
        let mut pool_items = Vec::new();
        
        for _ in 0..1000 {
            let item = pool.acquire(1024).await?;
            pool_items.push(item);
        }
        
        let pool_time = start.elapsed();
        println!("    内存池分配1000个1KB块耗时: {:?}", pool_time);
        
        // 性能对比
        let speedup = direct_time.as_nanos() as f64 / pool_time.as_nanos() as f64;
        println!("    性能提升: {:.2}x", speedup);
        
        // 释放所有项
        for item in pool_items {
            pool.release(&item.id).await?;
        }
        
        let final_stats = pool.get_stats().await;
        println!("    最终统计: 总项数={}, 可用={}, 使用中={}", 
                final_stats.total_items, final_stats.available_items, final_stats.used_items);
    }

    Ok(())
}

/// 内存泄漏检测演示
async fn demo_memory_leak_detection() -> Result<(), Box<dyn std::error::Error>> {
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    println!("  内存泄漏检测演示...");
    
    // 模拟正常的内存使用
    println!("  模拟正常内存使用...");
    let pool_config = MemoryPoolConfig {
        name: "leak_test_pool".to_string(),
        initial_size: 1024,
        max_size: 10240,
        min_size: 512,
        growth_factor: 1.5,
        auto_cleanup: true,
        cleanup_interval: Duration::from_secs(5),
        max_idle_time: Duration::from_secs(10),
    };
    
    optimizer.create_memory_pool(pool_config).await?;
    
    if let Some(pool) = optimizer.get_memory_pool("leak_test_pool").await {
        // 正常使用：获取后释放
        println!("  正常使用模式:");
        for i in 0..5 {
            let item = pool.acquire(512).await?;
            println!("    获取项 {}: {}", i + 1, item.id);
            pool.release(&item.id).await?;
            println!("    释放项 {}: {}", i + 1, item.id);
        }
        
        // 模拟内存泄漏：获取但不释放
        println!("  模拟内存泄漏模式:");
        let mut leaked_items = Vec::new();
        for i in 0..3 {
            let item = pool.acquire(512).await?;
            leaked_items.push(item);
            println!("    获取项 {}: {} (未释放)", i + 1, leaked_items[i].id);
        }
        
        // 获取统计信息
        let stats = pool.get_stats().await;
        println!("  内存池统计:");
        println!("    总项数: {}", stats.total_items);
        println!("    可用项数: {}", stats.available_items);
        println!("    使用中项数: {}", stats.used_items);
        println!("    命中率: {:.2}%", stats.hit_rate);
        
        // 检测潜在泄漏
        if stats.used_items > 0 {
            println!("  ⚠️  检测到潜在内存泄漏: {} 个项未释放", stats.used_items);
        }
        
        // 清理泄漏的项
        println!("  清理泄漏的项...");
        for item in leaked_items {
            pool.release(&item.id).await?;
            println!("    释放泄漏项: {}", item.id);
        }
        
        let final_stats = pool.get_stats().await;
        println!("  清理后统计:");
        println!("    总项数: {}", final_stats.total_items);
        println!("    可用项数: {}", final_stats.available_items);
        println!("    使用中项数: {}", final_stats.used_items);
    }

    Ok(())
}

/// 优化建议演示
async fn demo_optimization_recommendations() -> Result<(), Box<dyn std::error::Error>> {
    let optimizer = MemoryOptimizer::new(OptimizationConfig::default());
    
    println!("  生成优化建议...");
    
    // 执行优化以获取建议
    let result = optimizer.optimize().await?;
    
    println!("  优化结果:");
    println!("    释放内存: {} 字节", result.memory_freed);
    println!("    优化池数: {}", result.pools_optimized);
    println!("    移除项数: {}", result.items_removed);
    println!("    压缩比率: {:.2}%", result.compression_ratio);
    println!("    优化耗时: {:?}", result.optimization_time);
    
    if !result.recommendations.is_empty() {
        println!("  优化建议:");
        for (i, recommendation) in result.recommendations.iter().enumerate() {
            println!("    {}. {}", i + 1, recommendation);
        }
    } else {
        println!("  当前内存使用状况良好，无需特殊优化");
    }
    
    // 获取详细的内存统计
    let memory_stats = optimizer.get_memory_stats().await;
    println!("  详细内存统计:");
    println!("    总内存: {} 字节 ({:.2} MB)", 
            memory_stats.total_memory, memory_stats.total_memory as f64 / 1024.0 / 1024.0);
    println!("    已使用: {} 字节 ({:.2} MB)", 
            memory_stats.used_memory, memory_stats.used_memory as f64 / 1024.0 / 1024.0);
    println!("    可用内存: {} 字节 ({:.2} MB)", 
            memory_stats.available_memory, memory_stats.available_memory as f64 / 1024.0 / 1024.0);
    println!("    使用率: {:.2}%", memory_stats.memory_usage_percent);
    println!("    峰值内存: {} 字节 ({:.2} MB)", 
            memory_stats.peak_memory, memory_stats.peak_memory as f64 / 1024.0 / 1024.0);
    println!("    分配次数: {}", memory_stats.allocation_count);
    println!("    释放次数: {}", memory_stats.deallocation_count);
    println!("    潜在泄漏: {}", memory_stats.potential_leaks);

    Ok(())
}
