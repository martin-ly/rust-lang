//! 性能优化演示程序
//!
//! 本示例展示如何使用 C07 进程管理模块的性能优化功能，
//! 包括内存优化、CPU优化、I/O优化和性能监控。
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **性能优化**: 通过监控和调整提升系统性能的过程
//!   - **属性**: 内存优化、CPU优化、I/O优化、自动优化
//!   - **关系**: 与进程管理、性能监控相关
//!
//! - **性能监控**: 实时监控系统资源使用情况
//!   - **属性**: 内存监控、CPU监控、I/O监控、缓存监控
//!   - **关系**: 与性能优化、资源管理相关
//!
//! ### 思维导图
//!
//! ```text
//! 性能优化演示
//! │
//! ├── 内存优化
//! │   ├── 内存监控
//! │   └── 内存优化规则
//! ├── CPU 优化
//! │   ├── CPU 监控
//! │   └── CPU 优化规则
//! ├── I/O 优化
//! │   ├── I/O 监控
//! │   └── I/O 优化规则
//! └── 性能监控
//!     ├── 实时监控
//!     └── 历史数据
//! ```
#[cfg(feature = "async")]
use c07_process::performance::enhanced::*;
use std::time::Duration;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 C07 性能优化演示程序");
    println!("========================\n");

    // 创建性能配置
    let config = PerformanceConfig {
        memory_threshold: 0.8,                          // 内存使用阈值 80%
        cpu_threshold: 0.7,                             // CPU使用阈值 70%
        io_threshold: 0.6,                              // I/O使用阈值 60%
        cache_threshold: 0.75,                          // 缓存使用阈值 75%
        auto_optimization: true,                        // 启用自动优化
        optimization_interval: Duration::from_secs(30), // 优化间隔 30秒
        monitoring_interval: Duration::from_secs(5),    // 监控间隔 5秒
        history_retention: Duration::from_secs(3600),   // 历史保留 1小时
    };

    println!("📊 创建性能管理器...");
    let manager = EnhancedPerformanceManager::new(config).await;
    println!("✅ 性能管理器创建成功\n");

    // 演示内存优化
    println!("🔧 执行内存优化...");
    let memory_result = manager.optimize_memory().await;
    println!("内存优化结果:");
    println!("  - 成功: {}", memory_result.success);
    println!(
        "  - 性能提升: {:.1}%",
        memory_result.performance_gain * 100.0
    );
    println!("  - 消息: {}", memory_result.message);
    if !memory_result.optimizations_applied.is_empty() {
        println!("  - 应用的优化:");
        for opt in &memory_result.optimizations_applied {
            println!("    * {}", opt);
        }
    }
    println!();

    // 演示CPU优化
    println!("⚡ 执行CPU优化...");
    let cpu_result = manager
        .optimize_cpu(|usage| async move {
            println!("  - 当前CPU使用率: {:.1}%", usage * 100.0);

            if usage > 0.8 {
                OptimizationResult {
                    success: true,
                    performance_gain: 0.25,
                    message: "高CPU使用率检测，应用优化策略".to_string(),
                    optimizations_applied: vec![
                        "调整线程池大小".to_string(),
                        "启用CPU节流".to_string(),
                        "优先处理关键任务".to_string(),
                    ],
                }
            } else if usage > 0.6 {
                OptimizationResult {
                    success: true,
                    performance_gain: 0.15,
                    message: "中等CPU使用率，应用中等优化".to_string(),
                    optimizations_applied: vec!["调整线程优先级".to_string()],
                }
            } else {
                OptimizationResult {
                    success: true,
                    performance_gain: 0.0,
                    message: "CPU使用率正常".to_string(),
                    optimizations_applied: vec![],
                }
            }
        })
        .await;
    println!("CPU优化结果:");
    println!("  - 成功: {}", cpu_result.success);
    println!("  - 性能提升: {:.1}%", cpu_result.performance_gain * 100.0);
    println!("  - 消息: {}", cpu_result.message);
    if !cpu_result.optimizations_applied.is_empty() {
        println!("  - 应用的优化:");
        for opt in &cpu_result.optimizations_applied {
            println!("    * {}", opt);
        }
    }
    println!();

    // 演示I/O优化
    println!("💾 执行I/O优化...");
    let io_result = manager.optimize_io().await;
    println!("I/O优化结果:");
    println!("  - 成功: {}", io_result.success);
    println!("  - 性能提升: {:.1}%", io_result.performance_gain * 100.0);
    println!("  - 消息: {}", io_result.message);
    if !io_result.optimizations_applied.is_empty() {
        println!("  - 应用的优化:");
        for opt in &io_result.optimizations_applied {
            println!("    * {}", opt);
        }
    }
    println!();

    // 获取性能报告
    println!("📈 获取性能报告...");
    let report = manager.get_performance_report().await;
    println!("性能报告:");
    println!("  - 时间戳: {:?}", report.timestamp);
    println!("  - 性能分数: {:.2}", report.performance_score);
    println!(
        "  - 内存压力: {:.1}%",
        report.memory_stats.memory_pressure * 100.0
    );
    println!("  - CPU使用率: {:.1}%", report.cpu_stats.cpu_usage * 100.0);
    println!(
        "  - I/O使用率: {:.1}%",
        report.io_stats.io_utilization * 100.0
    );
    println!(
        "  - 缓存命中率: {:.1}%",
        report.cache_stats.hit_ratio * 100.0
    );
    println!();

    // 等待一段时间以收集监控数据
    println!("⏳ 等待 10 秒以收集监控数据...");
    tokio::time::sleep(Duration::from_secs(10)).await;
    println!("✅ 监控数据收集完成\n");

    // 再次获取性能报告以查看变化
    println!("📊 获取更新后的性能报告...");
    let updated_report = manager.get_performance_report().await;
    println!("更新后的性能报告:");
    println!("  - 时间戳: {:?}", updated_report.timestamp);
    println!("  - 性能分数: {:.2}", updated_report.performance_score);
    println!(
        "  - 内存压力: {:.1}%",
        updated_report.memory_stats.memory_pressure * 100.0
    );
    println!(
        "  - CPU使用率: {:.1}%",
        updated_report.cpu_stats.cpu_usage * 100.0
    );
    println!(
        "  - I/O使用率: {:.1}%",
        updated_report.io_stats.io_utilization * 100.0
    );
    println!(
        "  - 缓存命中率: {:.1}%",
        updated_report.cache_stats.hit_ratio * 100.0
    );
    println!();

    println!("✅ 性能优化演示完成！");
    println!("\n💡 提示:");
    println!("  - 性能管理器会在后台持续监控和优化");
    println!("  - 可以通过配置调整优化策略和阈值");
    println!("  - 详细使用说明请参考: docs/performance_optimization_usage_guide.md");

    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 此示例需要启用 'async' feature");
    println!("请在 Cargo.toml 中添加: features = [\"async\"]");
}
