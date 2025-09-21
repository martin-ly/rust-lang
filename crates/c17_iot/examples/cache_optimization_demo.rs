//! 缓存优化演示示例
//! 
//! 展示如何使用c17_iot的智能缓存系统来优化IoT数据访问性能

use c17_iot::data_storage::cache_optimizer::{
    CacheOptimizer, CacheConfig, CacheStrategy, PrewarmingStrategy
};
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动缓存优化演示...");

    // 创建缓存配置
    let config = CacheConfig {
        strategy: CacheStrategy::Adaptive,
        max_capacity: 1024 * 1024, // 1MB
        default_ttl: Duration::from_secs(3600), // 1小时
        enable_prewarming: true,
        prewarming_strategy: PrewarmingStrategy::FrequencyBased,
        enable_compression: false,
        compression_threshold: 1024,
    };

    // 创建缓存优化器
    let optimizer = CacheOptimizer::<String>::new(config);

    println!("📊 开始缓存操作演示...");

    // 1. 基础缓存操作
    println!("\n1️⃣ 基础缓存操作");
    
    // 设置一些缓存数据
    let test_data = vec![
        ("sensor_temp_001", "25.5°C"),
        ("sensor_humidity_001", "60%"),
        ("sensor_pressure_001", "1013.25 hPa"),
        ("device_status_001", "online"),
        ("config_network", "192.168.1.100"),
    ];

    for (key, value) in &test_data {
        optimizer.set(key.to_string(), value.to_string(), None).await?;
        println!("  缓存设置: {} = {}", key, value);
    }

    // 读取缓存数据
    println!("\n📖 读取缓存数据:");
    for (key, _) in &test_data {
        if let Some(value) = optimizer.get(key).await {
            println!("  缓存命中: {} = {}", key, value);
        } else {
            println!("  缓存未命中: {}", key);
        }
    }

    // 2. 缓存统计信息
    println!("\n2️⃣ 缓存统计信息");
    let stats = optimizer.get_stats().await;
    for (level, stat) in stats.iter() {
        println!("  {:?}: 容量 {}/{} 字节, 命中率 {:.1}%", 
            level, stat.used_capacity, stat.total_capacity, stat.hit_rate * 100.0);
    }

    // 3. 缓存预热演示
    println!("\n3️⃣ 缓存预热演示");
    let mut prewarm_data = HashMap::new();
    for i in 0..10 {
        prewarm_data.insert(
            format!("prewarm_key_{}", i),
            format!("prewarm_value_{}", i)
        );
    }
    
    optimizer.prewarm(prewarm_data).await?;
    println!("  预热完成，添加了10个预热数据项");

    // 4. 性能测试
    println!("\n4️⃣ 性能测试");
    let start = std::time::Instant::now();
    
    // 执行1000次缓存操作
    for i in 0..1000 {
        let key = format!("perf_test_{}", i % 20); // 重复使用20个键
        let value = format!("value_{}", i);
        
        optimizer.set(key.clone(), value, None).await?;
        let _ = optimizer.get(&key).await;
    }
    
    let duration = start.elapsed();
    println!("  1000次缓存操作耗时: {:?}", duration);
    println!("  平均每次操作: {:?}", duration / 1000);

    // 5. 缓存优化
    println!("\n5️⃣ 缓存优化");
    let optimization_result = optimizer.optimize().await?;
    
    println!("  优化耗时: {:?}", optimization_result.duration);
    println!("  优化建议数量: {}", optimization_result.optimizations.len());
    
    for optimization in &optimization_result.optimizations {
        println!("  - {:?}: {}", optimization.optimization_type, optimization.description);
    }

    // 6. 不同缓存策略对比
    println!("\n6️⃣ 不同缓存策略对比");
    
    let strategies = vec![
        CacheStrategy::LRU,
        CacheStrategy::LFU,
        CacheStrategy::TTL,
        CacheStrategy::FIFO,
        CacheStrategy::Adaptive,
    ];

    for strategy in strategies {
        let config = CacheConfig {
            strategy: strategy.clone(),
            max_capacity: 512 * 1024, // 512KB
            default_ttl: Duration::from_secs(1800), // 30分钟
            enable_prewarming: false,
            prewarming_strategy: PrewarmingStrategy::Manual,
            enable_compression: false,
            compression_threshold: 1024,
        };

        let test_optimizer = CacheOptimizer::<String>::new(config);
        
        // 添加测试数据
        for i in 0..50 {
            test_optimizer.set(
                format!("strategy_test_{}", i),
                format!("value_{}", i),
                None
            ).await?;
        }

        // 执行一些读取操作
        for i in 0..100 {
            let _ = test_optimizer.get(&format!("strategy_test_{}", i % 50)).await;
        }

        let stats = test_optimizer.get_stats().await;
        let total_hits: u64 = stats.values().map(|s| s.hits).sum();
        let total_misses: u64 = stats.values().map(|s| s.misses).sum();
        let hit_rate = if total_hits + total_misses > 0 {
            total_hits as f64 / (total_hits + total_misses) as f64
        } else {
            0.0
        };

        println!("  {:?}: 命中率 {:.1}%", strategy, hit_rate * 100.0);
    }

    // 7. 缓存清理演示
    println!("\n7️⃣ 缓存清理演示");
    
    // 添加一些带TTL的数据
    optimizer.set("temp_data".to_string(), "temporary".to_string(), 
        Some(Duration::from_secs(1))).await?;
    
    println!("  添加了1秒TTL的临时数据");
    sleep(Duration::from_secs(2)).await;
    
    // 尝试读取过期数据
    if let Some(value) = optimizer.get("temp_data").await {
        println!("  意外: 过期数据仍然存在: {}", value);
    } else {
        println!("  正确: 过期数据已被清理");
    }

    // 手动清理
    optimizer.clear().await;
    println!("  手动清理所有缓存数据");

    // 最终统计
    let final_stats = optimizer.get_stats().await;
    let total_used: usize = final_stats.values().map(|s| s.used_capacity).sum();
    println!("  清理后总使用容量: {} 字节", total_used);

    println!("\n✅ 缓存优化演示完成!");
    Ok(())
}
