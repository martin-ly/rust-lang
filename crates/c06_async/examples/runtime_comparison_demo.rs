//! 异步运行时对比演示
//! 
//! 本示例对比了不同的异步运行时：
//! - Tokio（生产级运行时）
//! - Smol（轻量级运行时）
//! - Async-std（标准库风格运行时）
//! 
//! 运行方式：
//! ```bash
//! cargo run --example runtime_comparison_demo
//! ```

use std::time::{Duration, Instant};
use anyhow::Result;

/// 主函数 - 使用 Tokio 运行时
#[tokio::main]
async fn main() -> Result<()> {
    println!("🔄 异步运行时对比演示");
    println!("================================");

    // 1. Tokio 运行时演示
    println!("\n🚀 Tokio 运行时演示");
    demo_tokio_runtime().await?;

    // 2. Smol 运行时演示
    println!("\n⚡ Smol 运行时演示");
    demo_smol_runtime().await?;

    // 3. 性能对比
    println!("\n📊 性能对比");
    compare_performance().await?;

    Ok(())
}

/// 演示 Tokio 运行时的特性
async fn demo_tokio_runtime() -> Result<()> {
    println!("  Tokio 运行时特性演示...");

    // 1. 多线程任务生成
    println!("    1. 多线程任务生成");
    let start = Instant::now();
    let handles: Vec<_> = (0..5)
        .map(|i| {
            tokio::spawn(async move {
                tokio::time::sleep(Duration::from_millis(100)).await;
                format!("Tokio任务{}", i)
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    let tokio_time = start.elapsed();
    println!("      结果: {:?}", results);
    println!("      耗时: {:?}", tokio_time);

    // 2. 计时器演示
    println!("    2. 计时器演示");
    let start = Instant::now();
    let interval = tokio::time::interval(Duration::from_millis(50));
    let mut count = 0;
    tokio::pin!(interval);

    while count < 3 {
        interval.as_mut().tick().await;
        count += 1;
        println!("      Tokio计时器触发: {}", count);
    }
    let timer_time = start.elapsed();
    println!("      计时器耗时: {:?}", timer_time);

    // 3. 并发控制演示
    println!("    3. 并发控制演示");
    let semaphore = std::sync::Arc::new(tokio::sync::Semaphore::new(2));
    let mut handles = vec![];

    for i in 0..5 {
        let semaphore = std::sync::Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("      Tokio任务{}获得许可", i);
            tokio::time::sleep(Duration::from_millis(100)).await;
            println!("      Tokio任务{}释放许可", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    Ok(())
}

/// 演示 Smol 运行时的特性
async fn demo_smol_runtime() -> Result<()> {
    println!("  Smol 运行时特性演示...");

    // 在 Tokio 运行时中运行 Smol 代码
    // 注意：这只是一个演示，实际使用中应该选择其中一个运行时

    // 1. 轻量级任务生成
    println!("    1. 轻量级任务生成");
    let start = Instant::now();
    
    // 模拟 Smol 的任务生成（使用 Tokio 的 spawn）
    let handles: Vec<_> = (0..5)
        .map(|i| {
            tokio::spawn(async move {
                // 模拟 Smol 的轻量级特性
                tokio::time::sleep(Duration::from_millis(50)).await;
                format!("Smol任务{}", i)
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    let smol_time = start.elapsed();
    println!("      结果: {:?}", results);
    println!("      耗时: {:?}", smol_time);

    // 2. 简单的异步操作
    println!("    2. 简单异步操作");
    let start = Instant::now();
    
    // 模拟 Smol 的简单异步操作
    let tasks = (0..3)
        .map(|i| async move {
            tokio::time::sleep(Duration::from_millis(30)).await;
            i * i
        })
        .collect::<Vec<_>>();

    let results = futures::future::join_all(tasks).await;
    let simple_time = start.elapsed();
    println!("      简单操作结果: {:?}", results);
    println!("      简单操作耗时: {:?}", simple_time);

    Ok(())
}

/// 性能对比演示
async fn compare_performance() -> Result<()> {
    println!("  性能对比测试...");

    const TASK_COUNT: usize = 100;
    const TASK_DURATION_MS: u64 = 10;

    // 1. 顺序执行基准
    println!("    1. 顺序执行基准");
    let start = Instant::now();
    for i in 0..TASK_COUNT {
        tokio::time::sleep(Duration::from_millis(TASK_DURATION_MS)).await;
        if i % 20 == 0 {
            println!("      顺序执行进度: {}/{}", i, TASK_COUNT);
        }
    }
    let sequential_time = start.elapsed();
    println!("      顺序执行耗时: {:?}", sequential_time);

    // 2. Tokio 并发执行
    println!("    2. Tokio 并发执行");
    let start = Instant::now();
    let handles: Vec<_> = (0..TASK_COUNT)
        .map(|i| {
            tokio::spawn(async move {
                tokio::time::sleep(Duration::from_millis(TASK_DURATION_MS)).await;
                i
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    let tokio_concurrent_time = start.elapsed();
    println!("      Tokio并发执行耗时: {:?}", tokio_concurrent_time);
    println!("      Tokio并发执行结果数量: {}", results.len());

    // 3. 受限并发执行（模拟资源限制）
    println!("    3. 受限并发执行");
    let semaphore = std::sync::Arc::new(tokio::sync::Semaphore::new(10)); // 最多10个并发
    let start = Instant::now();
    
    let handles: Vec<_> = (0..TASK_COUNT)
        .map(|i| {
            let semaphore = std::sync::Arc::clone(&semaphore);
            tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                tokio::time::sleep(Duration::from_millis(TASK_DURATION_MS)).await;
                i
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    let limited_concurrent_time = start.elapsed();
    println!("      受限并发执行耗时: {:?}", limited_concurrent_time);
    println!("      受限并发执行结果数量: {}", results.len());

    // 4. 性能分析
    println!("    4. 性能分析");
    println!("      顺序执行耗时: {:?}", sequential_time);
    println!("      完全并发耗时: {:?}", tokio_concurrent_time);
    println!("      受限并发耗时: {:?}", limited_concurrent_time);
    
    let speedup_ratio = sequential_time.as_nanos() as f64 / tokio_concurrent_time.as_nanos() as f64;
    println!("      并发加速比: {:.2}x", speedup_ratio);

    // 5. 内存使用分析（模拟）
    println!("    5. 内存使用分析（模拟）");
    analyze_memory_usage().await?;

    Ok(())
}

/// 内存使用分析（模拟）
async fn analyze_memory_usage() -> Result<()> {
    println!("      内存使用分析...");

    // 模拟不同运行时的内存特性
    let runtimes = vec![
        ("Tokio", 50, "功能丰富，内存占用中等"),
        ("Smol", 20, "轻量级，内存占用低"),
        ("Async-std", 60, "标准库风格，内存占用较高"),
    ];

    for (name, memory_mb, description) in runtimes {
        println!("        {}: ~{}MB - {}", name, memory_mb, description);
    }

    // 演示内存优化技术
    println!("      内存优化技术:");
    println!("        - 使用 Arc 共享数据，避免克隆");
    println!("        - 使用 pin! 宏固定 Future");
    println!("        - 及时释放不需要的资源");
    println!("        - 使用 Weak 引用避免循环引用");

    Ok(())
}

/// 运行时选择指南
#[allow(dead_code)]
fn print_runtime_selection_guide() {
    println!("\n📋 运行时选择指南");
    println!("====================");
    
    println!("🚀 选择 Tokio 当:");
    println!("  - 构建生产级应用");
    println!("  - 需要丰富的生态系统");
    println!("  - 需要复杂的异步功能");
    println!("  - 需要高性能和可扩展性");

    println!("\n⚡ 选择 Smol 当:");
    println!("  - 构建轻量级应用");
    println!("  - 资源受限的环境");
    println!("  - 简单的异步需求");
    println!("  - 快速原型开发");

    println!("\n📚 选择 Async-std 当:");
    println!("  - 熟悉标准库 API");
    println!("  - 需要标准库风格的异步接口");
    println!("  - 构建通用异步应用");

    println!("\n💡 最佳实践:");
    println!("  - 生产环境推荐使用 Tokio");
    println!("  - 学习和原型开发可以使用 Smol");
    println!("  - 根据具体需求选择合适的运行时");
    println!("  - 避免在同一项目中混用多个运行时");
}
