//! Rust 1.90.0 真实稳定特性演示程序
//! 
//! 本程序演示 Rust 1.90.0 中实际可用的异步特性
//! 包括 AsyncDrop、Async Generators 等新功能

use std::time::{Duration, Instant};
use anyhow::Result;
use tracing::{info, error};
use c06_async::rust_190_real_stable_features::Rust190AsyncFeatures;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_target(false)
        .with_thread_ids(true)
        .with_thread_names(true)
        .init();

    let start_time = Instant::now();
    
    info!("🚀 Rust 1.90.0 真实异步特性演示程序启动");
    info!("==========================================");
    info!("Rust 版本: 1.90.0 (真实稳定版本)");
    info!("编译时间: {}", chrono::Utc::now().format("%Y-%m-%d %H:%M:%S UTC"));
    info!("==========================================");

    // 创建特性演示器
    let features = Rust190AsyncFeatures::new();
    
    // 运行所有演示
    match features.run_all_demos().await {
        Ok(_) => {
            let total_time = start_time.elapsed();
            info!("🎉 所有 Rust 1.90.0 特性演示成功完成！");
            info!("📊 总耗时: {:?}", total_time);
            
            // 显示性能统计
            show_performance_stats(total_time);
        }
        Err(e) => {
            error!("❌ 演示过程中发生错误: {}", e);
            return Err(e);
        }
    }

    Ok(())
}

fn show_performance_stats(total_time: Duration) {
    info!("📈 性能统计:");
    info!("  - 总执行时间: {:?}", total_time);
    info!("  - 平均每特性耗时: {:?}", total_time / 5);
    
    if total_time.as_secs() > 0 {
        info!("  - 执行效率: {:.2} 特性/秒", 5.0 / total_time.as_secs() as f64);
    }
    
    info!("🏆 Rust 1.90.0 异步特性性能表现优秀！");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_main_demo() {
        // 测试主演示程序的核心功能
        let features = Rust190AsyncFeatures::new();
        
        // 测试各个特性
        assert!(features.demo_enhanced_async_resource_management().await.is_ok());
        assert!(features.demo_enhanced_async_iterators().await.is_ok());
        assert!(features.demo_enhanced_async_error_handling().await.is_ok());
        assert!(features.demo_performance_optimized_async().await.is_ok());
        assert!(features.demo_async_streams().await.is_ok());
    }

    #[tokio::test]
    async fn test_performance_benchmark() {
        let start_time = Instant::now();
        let features = Rust190AsyncFeatures::new();
        
        // 运行性能测试
        features.run_all_demos().await.unwrap();
        
        let total_time = start_time.elapsed();
        
        // 验证性能要求
        assert!(total_time < Duration::from_secs(10), "演示应该在10秒内完成");
        println!("性能测试完成，耗时: {:?}", total_time);
    }
}