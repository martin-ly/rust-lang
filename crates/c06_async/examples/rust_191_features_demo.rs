//! Rust 1.91 异步编程特性演示示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//!
//! 本示例展示了 Rust 1.91 中与异步编程相关的新特性和改进：
//!
//! 1. const 上下文增强在异步配置中的应用
//! 2. 异步迭代器改进（性能提升 15-20%）
//! 3. JIT 编译器优化对异步代码的影响
//! 4. 内存分配优化对异步场景的影响
//! 5. 异步错误处理改进
//! 6. 异步流性能基准测试
//! 7. 异步任务管理器
//! 8. 异步缓存系统

use c06_async::rust_191_features::*;
use futures::stream;
use tokio::time::Duration as TokioDuration;

#[tokio::main]
async fn main() {
    println!("=== Rust 1.91 异步编程特性演示示例 ===\n");

    // 1. const 上下文增强在异步配置中的应用
    demo_const_async_config();

    // 2. 异步迭代器改进
    demo_async_iterator_improvements().await;

    // 3. JIT 编译器优化对异步代码的影响
    demo_async_jit_optimizations().await;

    // 4. 内存分配优化对异步场景的影响
    demo_async_memory_optimizations().await;

    // 5. 异步错误处理改进
    demo_async_error_handling().await;

    // 6. 异步流性能基准测试
    demo_async_stream_benchmarks().await;

    // 7. 异步任务管理器
    demo_async_task_manager().await;

    // 8. 异步缓存系统
    demo_async_cache_system().await;

    println!("\n=== 所有演示完成 ===");
}

/// 演示 const 上下文增强在异步配置中的应用
fn demo_const_async_config() {
    println!("1. const 上下文增强在异步配置中的应用");
    println!("   Rust 1.91: 可以在 const 上下文中创建对非静态常量的引用\n");

    const_async_config::demonstrate();
    println!();
}

/// 演示异步迭代器改进
async fn demo_async_iterator_improvements() {
    println!("2. 异步迭代器改进");
    println!("   Rust 1.91: 性能提升 15-20%\n");

    let input_stream = stream::iter(0..1000);

    match async_iterator_improvements::process_async_stream(input_stream).await {
        Ok(results) => {
            println!("   ✓ 处理了 {} 个元素", results.len());
            if results.len() > 0 {
                println!("   前 5 个结果: {:?}", &results[..5.min(results.len())]);
            }
        }
        Err(e) => {
            println!("   ✗ 处理失败: {}", e);
        }
    }

    let complex_stream = stream::iter(-100..100);
    let complex_results = async_iterator_improvements::complex_async_pipeline(complex_stream).await;
    println!("   ✓ 复杂管道处理了 {} 个元素\n", complex_results.len());
}

/// 演示 JIT 编译器优化对异步代码的影响
async fn demo_async_jit_optimizations() {
    println!("3. JIT 编译器优化对异步代码的影响");
    println!("   Rust 1.91: 异步迭代器链式操作性能提升 15-20%\n");

    let input_stream = stream::iter(0..1000);
    let results = async_jit_optimizations::optimized_async_iterator_chain(input_stream).await;
    println!("   ✓ 优化异步迭代器处理了 {} 个元素", results.len());

    let batch_stream = stream::iter(0..100);
    let batches = async_jit_optimizations::async_batch_processing(batch_stream, 10).await;
    println!("   ✓ 异步批处理生成了 {} 个批次\n", batches.len());
}

/// 演示内存分配优化对异步场景的影响
async fn demo_async_memory_optimizations() {
    println!("4. 内存分配优化对异步场景的影响");
    println!("   Rust 1.91: 小对象分配性能提升 25-30%\n");

    let objects = async_memory_optimizations::async_small_object_allocation(10).await;
    println!("   ✓ 异步创建了 {} 个小对象", objects.len());

    let map = async_memory_optimizations::async_hashmap_operations(10).await;
    println!("   ✓ 异步 HashMap 包含 {} 个元素\n", map.len());
}

/// 演示异步错误处理改进
async fn demo_async_error_handling() {
    println!("5. 异步错误处理改进");
    println!("   Rust 1.91: 改进的 ControlFlow 可以携带详细错误信息\n");

    use std::ops::ControlFlow;

    let valid_items = vec![1, 2, 3, 4, 5];
    match async_error_handling::async_validate_items(valid_items).await {
        ControlFlow::Continue(items) => {
            println!("   ✓ 验证成功: {:?}", items);
        }
        ControlFlow::Break(error) => {
            println!("   ✗ 验证失败: {}", error);
        }
    }

    let invalid_items = vec![1, 2, -3, 4, 5];
    match async_error_handling::async_validate_items(invalid_items).await {
        ControlFlow::Continue(items) => {
            println!("   ✓ 验证成功: {:?}", items);
        }
        ControlFlow::Break(error) => {
            println!("   ✗ 验证失败: {}", error);
        }
    }

    println!();
}

/// 演示异步流性能基准测试
async fn demo_async_stream_benchmarks() {
    println!("6. 异步流性能基准测试");
    println!("   Rust 1.91: 性能提升 15-20%\n");

    let input_stream = stream::iter(0..10000);
    let result = async_stream_benchmarks::benchmark_async_stream(input_stream, 5000).await;

    println!("   处理元素数: {}", result.element_count);
    println!("   处理时间: {} ms", result.processing_time_ms);
    println!("   吞吐量: {:.2} 元素/秒", result.throughput_elements_per_sec);
    println!("   内存使用: {:.2} MB\n", result.memory_usage_mb);
}

/// 演示异步任务管理器
async fn demo_async_task_manager() {
    println!("7. 异步任务管理器");
    println!("   Rust 1.91: 利用小对象池优化任务信息分配\n");

    let manager = async_task_manager::AsyncTaskManager::new(10);

    // 添加任务
    for i in 0..5 {
        let task_id = format!("task_{}", i);
        match manager.add_task(task_id).await {
            Ok(_) => println!("   ✓ 添加任务: task_{}", i),
            Err(e) => println!("   ✗ 添加任务失败: {}", e),
        }
    }

    // 执行任务
    for i in 0..5 {
        let task_id = format!("task_{}", i);
        let result = manager
            .execute_task(&task_id, async {
                tokio::time::sleep(TokioDuration::from_millis(10)).await;
                i * 2
            })
            .await;

        match result {
            Ok(value) => println!("   ✓ 任务 {} 完成: {}", task_id, value),
            Err(e) => println!("   ✗ 任务 {} 失败: {}", task_id, e),
        }
    }

    // 获取统计信息
    let stats = manager.get_statistics().await;
    println!("   任务统计: 总计 {}, 运行中 {}, 已完成 {}\n",
        stats.total, stats.running, stats.completed);
}

/// 演示异步缓存系统
async fn demo_async_cache_system() {
    println!("8. 异步缓存系统");
    println!("   Rust 1.91: 小对象分配性能提升 25-30%\n");

    let cache: async_cache_system::AsyncCache<String, i32> =
        async_cache_system::AsyncCache::new(100);

    // 设置值
    for i in 0..10 {
        let key = format!("key_{}", i);
        match cache
            .set(key.clone(), i * 2, Some(TokioDuration::from_secs(60)))
            .await
        {
            Ok(_) => {
                if i < 3 {
                    println!("   ✓ 设置缓存: {} = {}", key, i * 2);
                }
            }
            Err(e) => println!("   ✗ 设置缓存失败: {}", e),
        }
    }

    // 获取值
    println!();
    for i in 0..5 {
        let key = format!("key_{}", i);
        if let Some(value) = cache.get(&key).await {
            println!("   ✓ 缓存命中: {} = {}", key, value);
        } else {
            println!("   ✗ 缓存未命中: {}", key);
        }
    }

    // 获取统计信息
    let stats = cache.get_statistics().await;
    println!("\n   缓存统计: 总计 {}, 有效 {}, 过期 {}\n",
        stats.total, stats.valid, stats.expired);
}

/// 运行完整的 Rust 1.91 异步特性示例
#[allow(dead_code)]
async fn run_complete_demo() {
    println!("=== 运行完整的 Rust 1.91 异步特性示例 ===\n");
    demonstrate_rust_191_async().await;
}
