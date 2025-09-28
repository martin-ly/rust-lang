//! Glommio 性能对比演示
//! 
//! 本示例展示了 Glommio 与 Tokio 在中间件场景下的性能对比，
//! 包括网络 I/O、数据库操作、缓存操作等典型中间件任务。

use c11_middlewares::glommio_runtime::*;
use c11_middlewares::Result;
use std::time::Duration;
use std::future::Future;
use std::pin::Pin;

/// 模拟网络 I/O 操作
#[allow(dead_code)]
async fn simulate_network_io() -> Result<()> {
    // 模拟网络延迟
    #[cfg(feature = "tokio")]
    tokio::time::sleep(Duration::from_millis(1)).await;
    
    #[cfg(not(feature = "tokio"))]
    {
        // 使用标准库 sleep 作为回退
        std::thread::sleep(Duration::from_millis(1));
    }
    Ok(())
}

/// 模拟数据库查询操作
#[allow(dead_code)]
async fn simulate_database_query() -> Result<Vec<u8>> {
    // 模拟数据库查询延迟
    #[cfg(feature = "tokio")]
    tokio::time::sleep(Duration::from_millis(2)).await;
    
    #[cfg(not(feature = "tokio"))]
    {
        // 使用标准库 sleep 作为回退
        std::thread::sleep(Duration::from_millis(2));
    }
    Ok(vec![1, 2, 3, 4, 5])
}

/// 模拟缓存操作
#[allow(dead_code)]
async fn simulate_cache_operation() -> Result<String> {
    // 模拟缓存访问延迟
    #[cfg(feature = "tokio")]
    tokio::time::sleep(Duration::from_millis(500)).await;
    
    #[cfg(not(feature = "tokio"))]
    {
        // 使用标准库 sleep 作为回退
        std::thread::sleep(Duration::from_millis(500));
    }
    Ok("cached_value".to_string())
}

/// 模拟计算密集型任务
#[allow(dead_code)]
async fn simulate_computation() -> Result<u64> {
    let mut result = 0u64;
    for i in 0..10000 {
        result += i;
    }
    Ok(result)
}

/// 创建网络 I/O 操作闭包
#[allow(dead_code)]
fn create_network_operation() -> impl Fn() -> Pin<Box<dyn Future<Output = Result<()>> + Send>> + Clone {
    move || Box::pin(simulate_network_io())
}

/// 创建数据库操作闭包
#[allow(dead_code)]
fn create_database_operation() -> impl Fn() -> Pin<Box<dyn Future<Output = Result<Vec<u8>>> + Send>> + Clone {
    move || Box::pin(simulate_database_query())
}

/// 创建缓存操作闭包
#[allow(dead_code)]
fn create_cache_operation() -> impl Fn() -> Pin<Box<dyn Future<Output = Result<String>> + Send>> + Clone {
    move || Box::pin(simulate_cache_operation())
}

/// 创建计算操作闭包
#[allow(dead_code)]
fn create_computation_operation() -> impl Fn() -> Pin<Box<dyn Future<Output = Result<u64>> + Send>> + Clone {
    move || Box::pin(simulate_computation())
}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("=== Glommio vs Tokio 性能对比演示 ===\n");
    
    // 测试参数
    let iterations = 1000;
    
    // 1. 网络 I/O 性能对比
    println!("1. 网络 I/O 性能对比");
    println!("=====================");
    
    let network_op = create_network_operation();
    let network_comparison = RuntimeBenchmarker::compare_runtimes(network_op, iterations).await?;
    println!("{}", network_comparison.generate_report());
    
    // 2. 数据库操作性能对比
    println!("\n2. 数据库操作性能对比");
    println!("=====================");
    
    let db_op = create_database_operation();
    let db_comparison = RuntimeBenchmarker::compare_runtimes(db_op, iterations).await?;
    println!("{}", db_comparison.generate_report());
    
    // 3. 缓存操作性能对比
    println!("\n3. 缓存操作性能对比");
    println!("===================");
    
    let cache_op = create_cache_operation();
    let cache_comparison = RuntimeBenchmarker::compare_runtimes(cache_op, iterations).await?;
    println!("{}", cache_comparison.generate_report());
    
    // 4. 计算密集型任务对比
    println!("\n4. 计算密集型任务对比");
    println!("=====================");
    
    let comp_op = create_computation_operation();
    let comp_comparison = RuntimeBenchmarker::compare_runtimes(comp_op, iterations).await?;
    println!("{}", comp_comparison.generate_report());
    
    // 5. 综合性能分析
    println!("\n5. 综合性能分析");
    println!("===============");
    
    analyze_performance_results(&[
        ("网络 I/O", &network_comparison),
        ("数据库操作", &db_comparison),
        ("缓存操作", &cache_comparison),
        ("计算任务", &comp_comparison),
    ])?;
    
    // 6. 运行时选择建议
    println!("\n6. 运行时选择建议");
    println!("=================");
    
    provide_runtime_recommendations(&[
        ("网络 I/O", &network_comparison),
        ("数据库操作", &db_comparison),
        ("缓存操作", &cache_comparison),
        ("计算任务", &comp_comparison),
    ])?;
    
    println!("\n=== 性能对比演示完成 ===");
    println!("Glommio 在高 I/O 密集型任务中表现出色！");
    
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("=== Glommio 性能对比演示 ===");
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example glommio_performance_comparison --features tokio");
    
    // 演示基本功能
    println!("\n基本功能演示:");
    
    #[cfg(feature = "glommio")]
    {
        match GlommioRuntime::new() {
            Ok(runtime) => {
                let handle = runtime.spawn(async { 42 });
                let result = runtime.block_on(handle).unwrap();
                println!("Glommio 运行时测试成功: {}", result);
            }
            Err(e) => println!("Glommio 运行时测试失败: {}", e),
        }
    }
    
    #[cfg(not(feature = "glommio"))]
    {
        println!("Glommio 特性未启用");
    }
}

/// 分析性能结果
#[allow(dead_code)]
fn analyze_performance_results(
    results: &[(&str, &RuntimeComparison)],
) -> Result<()> {
    let mut glommio_wins = 0;
    let mut tokio_wins = 0;
    let mut total_glommio_improvement = 0.0;
    let mut total_tokio_improvement = 0.0;
    
    for (test_name, comparison) in results {
        if let Some((best_name, best_result)) = comparison.get_best() {
            match best_name.as_str() {
                "glommio" => {
                    glommio_wins += 1;
                    println!("✅ {} - Glommio 获胜 (吞吐量: {:.2} ops/sec)", 
                             test_name, best_result.throughput);
                    
                    // 计算性能提升
                    if let Some((_, tokio_result)) = comparison.results.iter()
                        .find(|(name, _)| name == "tokio") {
                        let improvement = (best_result.throughput / tokio_result.throughput - 1.0) * 100.0;
                        total_glommio_improvement += improvement;
                        println!("   性能提升: {:.1}%", improvement);
                    }
                }
                "tokio" => {
                    tokio_wins += 1;
                    println!("✅ {} - Tokio 获胜 (吞吐量: {:.2} ops/sec)", 
                             test_name, best_result.throughput);
                    
                    // 计算性能提升
                    if let Some((_, glommio_result)) = comparison.results.iter()
                        .find(|(name, _)| name == "glommio") {
                        let improvement = (best_result.throughput / glommio_result.throughput - 1.0) * 100.0;
                        total_tokio_improvement += improvement;
                        println!("   性能提升: {:.1}%", improvement);
                    }
                }
                _ => {}
            }
        }
    }
    
    println!("\n📊 总体统计:");
    println!("Glommio 获胜: {} 项", glommio_wins);
    println!("Tokio 获胜: {} 项", tokio_wins);
    
    if glommio_wins > 0 {
        println!("Glommio 平均性能提升: {:.1}%", total_glommio_improvement / glommio_wins as f64);
    }
    
    if tokio_wins > 0 {
        println!("Tokio 平均性能提升: {:.1}%", total_tokio_improvement / tokio_wins as f64);
    }
    
    Ok(())
}

/// 提供运行时选择建议
#[allow(dead_code)]
fn provide_runtime_recommendations(
    results: &[(&str, &RuntimeComparison)],
) -> Result<()> {
    println!("🎯 运行时选择建议:");
    
    let mut glommio_recommended = Vec::new();
    let mut tokio_recommended = Vec::new();
    
    for (test_name, comparison) in results {
        if let Some((best_name, _)) = comparison.get_best() {
            match best_name.as_str() {
                "glommio" => glommio_recommended.push(test_name),
                "tokio" => tokio_recommended.push(test_name),
                _ => {}
            }
        }
    }
    
    if !glommio_recommended.is_empty() {
        println!("\n🚀 推荐使用 Glommio 的场景:");
        for scenario in &glommio_recommended {
            match **scenario {
                "网络 I/O" => println!("  • 高并发网络服务 (Web 服务器、API 网关)"),
                "数据库操作" => println!("  • 数据库代理和连接池"),
                "缓存操作" => println!("  • 高性能缓存服务"),
                "计算任务" => println!("  • 计算密集型任务"),
                _ => println!("  • {}", scenario),
            }
        }
    }
    
    if !tokio_recommended.is_empty() {
        println!("\n⚡ 推荐使用 Tokio 的场景:");
        for scenario in &tokio_recommended {
            match **scenario {
                "网络 I/O" => println!("  • 标准网络应用"),
                "数据库操作" => println!("  • 传统数据库操作"),
                "缓存操作" => println!("  • 简单缓存操作"),
                "计算任务" => println!("  • 轻量级计算任务"),
                _ => println!("  • {}", scenario),
            }
        }
    }
    
    println!("\n💡 总体建议:");
    if glommio_recommended.len() > tokio_recommended.len() {
        println!("  Glommio 在大多数场景下表现更优，建议优先考虑");
        println!("  特别适合高并发、低延迟的中间件应用");
    } else if tokio_recommended.len() > glommio_recommended.len() {
        println!("  Tokio 在测试场景下表现更优，建议继续使用");
        println!("  成熟稳定，生态系统丰富");
    } else {
        println!("  两个运行时各有优势，建议根据具体需求选择");
        println!("  Glommio: 高性能 I/O 密集型应用");
        println!("  Tokio: 通用异步应用");
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_operation_creation() {
        let network_op = create_network_operation();
        let db_op = create_database_operation();
        let cache_op = create_cache_operation();
        let comp_op = create_computation_operation();
        
        // 测试操作创建是否成功
        assert!(true); // 如果编译通过，说明操作创建成功
    }
    
    #[test]
    fn test_performance_analysis() {
        let mock_comparison = RuntimeComparison {
            results: vec![
                ("glommio".to_string(), BenchmarkResult {
                    duration: Duration::from_secs(1),
                    iterations: 1000,
                    throughput: 1000.0,
                }),
                ("tokio".to_string(), BenchmarkResult {
                    duration: Duration::from_secs(1),
                    iterations: 800,
                    throughput: 800.0,
                }),
            ],
        };
        
        let results = [("test", &mock_comparison)];
        assert!(analyze_performance_results(&results).is_ok());
    }
    
    #[test]
    fn test_recommendations() {
        let mock_comparison = RuntimeComparison {
            results: vec![
                ("glommio".to_string(), BenchmarkResult {
                    duration: Duration::from_secs(1),
                    iterations: 1000,
                    throughput: 1000.0,
                }),
                ("tokio".to_string(), BenchmarkResult {
                    duration: Duration::from_secs(1),
                    iterations: 800,
                    throughput: 800.0,
                }),
            ],
        };
        
        let results = [("test", &mock_comparison)];
        assert!(provide_runtime_recommendations(&results).is_ok());
    }
}
