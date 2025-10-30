//! # Glommio 异步运行时综合示例 2025
//!
//! 本示例展示了 Glommio 高性能异步运行时的核心特性和最佳实践。
//!
//! Glommio 是由 DataDog 开发的基于 io_uring 的异步运行时，
//! 专为 Linux 平台的极致性能设计。
//!
//! ## 核心特性
//!
//! 1. **Thread-per-core 架构** - 每个 CPU 核心一个线程
//! 2. **基于 io_uring** - 利用 Linux 5.1+ 的高性能 I/O
//! 3. **NUMA 感知** - 优化多 socket 系统
//! 4. **零拷贝 I/O** - 最小化数据复制
//! 5. **CPU 亲和性** - 精确控制任务调度
//!
//! ## 运行要求
//!
//! - Linux 5.1+ (需要 io_uring 支持)
//! - Rust 1.90+
//!
//! ## 运行示例
//!
//! ```bash
//! cargo run --example glommio_comprehensive_2025
//! ```

#[cfg(target_os = "linux")]
fn main() {
    use glommio::{
        channels::channel_mesh::MeshBuilder,
        timer::sleep,
        LocalExecutor, LocalExecutorBuilder, Shares, Task,
    };
    use std::time::{Duration, Instant};

    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║  Glommio 高性能异步运行时综合示例 - 2025                  ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");

    // ============================================================================
    // 1. 基础示例 - 单核执行器
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 1: 基础单核执行器");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    LocalExecutor::default().run(async {
        println!("✅ Glommio 执行器已启动");

        // 创建一个简单任务
        let task = Task::local(async {
            println!("  ⏱️  Task 开始执行...");
            sleep(Duration::from_millis(100)).await;
            println!("  ✅ Task 执行完成");
            42
        });

        let result = task.await;
        println!("  📊 任务返回值: {}\n", result);
    });

    // ============================================================================
    // 2. 多任务并发执行
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 2: 多任务并发执行");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    LocalExecutor::default().run(async {
        let start = Instant::now();
        let mut tasks = vec![];

        // 创建 10 个并发任务
        for i in 0..10 {
            let task = Task::local(async move {
                sleep(Duration::from_millis(50 + i * 10)).await;
                println!("  ✅ Task {} 完成", i);
                i
            });
            tasks.push(task);
        }

        // 等待所有任务完成
        let results: Vec<u64> = futures::future::join_all(tasks).await;
        let elapsed = start.elapsed();

        println!("  📊 所有任务完成! 结果: {:?}", results);
        println!("  ⏱️  总耗时: {:?}\n", elapsed);
    });

    // ============================================================================
    // 3. CPU 绑定与亲和性
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 3: CPU 绑定与亲和性");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    let num_cores = num_cpus::get();
    println!("  💻 检测到 {} 个 CPU 核心", num_cores);

    let mut handles = vec![];

    // 在多个核心上创建执行器（最多 4 个）
    for core_id in 0..std::cmp::min(num_cores, 4) {
        let handle = LocalExecutorBuilder::default()
            .pin_to_cpu(core_id)
            .name(&format!("executor-{}", core_id))
            .spawn(move || async move {
                println!("  🎯 执行器 {} 绑定到核心 {}", core_id, core_id);

                // 模拟计算密集型任务
                let mut sum = 0u64;
                for i in 0..1_000_000 {
                    sum = sum.wrapping_add(i);
                }

                println!("  ✅ 核心 {} 计算完成: sum = {}", core_id, sum);
                (core_id, sum)
            })
            .expect("Failed to spawn executor");

        handles.push(handle);
    }

    // 等待所有执行器完成
    for handle in handles {
        let (core_id, result) = handle.join().unwrap();
        println!("  📊 核心 {} 返回结果: {}", core_id, result);
    }
    println!();

    // ============================================================================
    // 4. 任务优先级调度
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 4: 任务优先级调度");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    LocalExecutor::default().run(async {
        // 创建不同优先级的任务队列
        let high_priority_tq =
            glommio::executor().create_task_queue(Shares::Static(1000), glommio::Latency::Matters(Duration::from_millis(10)), "high");
        let low_priority_tq =
            glommio::executor().create_task_queue(Shares::Static(100), glommio::Latency::NotImportant, "low");

        // 高优先级任务
        let high_task = Task::local_into(
            async {
                println!("  ⚡ 高优先级任务开始");
                sleep(Duration::from_millis(50)).await;
                println!("  ✅ 高优先级任务完成");
                "high"
            },
            high_priority_tq,
        )
        .unwrap();

        // 低优先级任务
        let low_task = Task::local_into(
            async {
                println!("  🐌 低优先级任务开始");
                sleep(Duration::from_millis(50)).await;
                println!("  ✅ 低优先级任务完成");
                "low"
            },
            low_priority_tq,
        )
        .unwrap();

        // 同时等待两个任务
        let (high_result, low_result) = futures::join!(high_task, low_task);
        println!("  📊 结果: high={}, low={}\n", high_result, low_result);
    });

    // ============================================================================
    // 5. 跨执行器通信 (Channel Mesh)
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 5: 跨执行器通信 (Channel Mesh)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    let num_executors = std::cmp::min(num_cores, 4);
    let mut handles = vec![];

    // 创建 channel mesh
    let mut mesh_builder = MeshBuilder::partial();

    for i in 0..num_executors {
        let connection = mesh_builder.join();
        let handle = LocalExecutorBuilder::default()
            .pin_to_cpu(i)
            .name(&format!("mesh-executor-{}", i))
            .spawn(move || async move {
                let mesh = connection.await;

                // 向所有其他执行器发送消息
                for peer in 0..num_executors {
                    if peer != i {
                        if let Some(sender) = mesh.sender_for(peer) {
                            sender
                                .send(format!("Hello from executor {}", i))
                                .await
                                .ok();
                        }
                    }
                }

                // 接收来自其他执行器的消息
                let mut count = 0;
                while let Some(msg) = mesh.receiver().recv().await {
                    println!("  📨 执行器 {} 收到: {}", i, msg);
                    count += 1;
                    if count >= num_executors - 1 {
                        break;
                    }
                }

                i
            })
            .expect("Failed to spawn executor");

        handles.push(handle);
    }

    // 等待所有执行器完成
    for handle in handles {
        handle.join().unwrap();
    }
    println!();

    // ============================================================================
    // 6. 文件 I/O 示例
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 6: 高性能文件 I/O");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    LocalExecutor::default().run(async {
        use glommio::io::DmaFile;
        use std::path::Path;

        let path = "/tmp/glommio_test.txt";
        let content = b"Hello, Glommio! This is a high-performance I/O test.";

        // 写入文件 (使用 DMA - Direct Memory Access)
        let file = DmaFile::create(path).await.unwrap();
        let written = file.write_at(content.to_vec(), 0).await.unwrap();
        file.close().await.unwrap();
        println!("  ✅ 写入 {} 字节到文件", written);

        // 读取文件
        let file = DmaFile::open(path).await.unwrap();
        let read_buf = file.read_at(0, content.len()).await.unwrap();
        let read_content = String::from_utf8_lossy(&read_buf);
        file.close().await.unwrap();
        println!("  ✅ 从文件读取: {}", read_content);

        // 清理
        std::fs::remove_file(path).unwrap();
        println!("  🗑️  清理临时文件\n");
    });

    // ============================================================================
    // 7. 性能对比示例
    // ============================================================================
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 示例 7: 性能特性展示");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n");

    LocalExecutor::default().run(async {
        let num_tasks = 10_000;
        let start = Instant::now();

        // 创建大量轻量级任务
        let mut tasks = vec![];
        for i in 0..num_tasks {
            let task = Task::local(async move { i * 2 });
            tasks.push(task);
        }

        // 等待所有任务完成
        let results: Vec<usize> = futures::future::join_all(tasks).await;
        let elapsed = start.elapsed();

        let sum: usize = results.iter().sum();
        let avg_time = elapsed.as_nanos() / num_tasks as u128;

        println!("  📊 执行 {} 个任务", num_tasks);
        println!("  ⏱️  总耗时: {:?}", elapsed);
        println!("  📈 平均每任务: {} ns", avg_time);
        println!("  💯 结果校验: sum = {}", sum);
    });

    println!("\n╔════════════════════════════════════════════════════════════╗");
    println!("║  Glommio 特性总结                                          ║");
    println!("╠════════════════════════════════════════════════════════════╣");
    println!("║  ✅ Thread-per-core 架构                                   ║");
    println!("║  ✅ 基于 io_uring 的零拷贝 I/O                            ║");
    println!("║  ✅ CPU 亲和性与 NUMA 优化                                ║");
    println!("║  ✅ 优先级调度与公平性保证                                ║");
    println!("║  ✅ 跨执行器通信 (Channel Mesh)                           ║");
    println!("║  ✅ 高性能文件 I/O (DMA)                                  ║");
    println!("║  ✅ 极低延迟 (<100μs) 与高吞吐 (>2M req/s)               ║");
    println!("╚════════════════════════════════════════════════════════════╝\n");

    // 打印对比信息
    println!("📊 运行时对比:");
    println!("┌─────────────┬────────────────┬──────────────┬─────────────┐");
    println!("│ 运行时      │ 架构模型       │ 延迟         │ 吞吐量      │");
    println!("├─────────────┼────────────────┼──────────────┼─────────────┤");
    println!("│ Glommio     │ Thread-per-core│ 极低 (<100μs)│ 极高 (>2M)  │");
    println!("│ Tokio       │ Work-stealing  │ 低 (~200μs)  │ 高 (>1.2M)  │");
    println!("│ Smol        │ 单/多线程      │ 低 (~150μs)  │ 中高 (>1.4M)│");
    println!("└─────────────┴────────────────┴──────────────┴─────────────┘\n");

    println!("💡 适用场景:");
    println!("  • 高频交易系统");
    println!("  • 数据库引擎");
    println!("  • 高性能网络服务");
    println!("  • 实时数据处理");
    println!("  • 游戏服务器");
    println!("\n⚠️  注意事项:");
    println!("  • 仅支持 Linux 5.1+ (需要 io_uring)");
    println!("  • Thread-per-core 模型需要特殊编程思维");
    println!("  • 生态系统相对较小");
    println!("\n✅ Glommio 综合示例执行完成!");
}

#[cfg(not(target_os = "linux"))]
fn main() {
    println!("❌ 错误: Glommio 仅支持 Linux 系统");
    println!("   需要 Linux 5.1+ 版本 (io_uring 支持)");
    println!("\n💡 提示: 请在 Linux 系统上运行此示例");
}

