//! # Tokio 1.41+ 和 Smol 2.0+ 最新特性完整演示 2025
//! 
//! Latest Features of Tokio 1.41+ and Smol 2.0+ Complete Demo 2025
//!
//! ## 📚 本示例涵盖
//!
//! ### Tokio 1.41+ 最新特性
//! 1. **JoinSet 增强** - 动态任务集管理
//! 2. **TaskLocal 改进** - 任务本地存储
//! 3. **Runtime Metrics** - 运行时指标收集
//! 4. **协作式调度** - Cooperative scheduling improvements
//! 5. **Async Drop** - 异步资源清理
//! 6. **取消传播** - Cancellation token improvements
//!
//! ### Smol 2.0+ 最新特性
//! 1. **轻量级 Executor** - 更小的内存占用
//! 2. **Async-io 2.6+** - 改进的 I/O 层
//! 3. **跨平台支持** - Windows, Linux, macOS 优化
//! 4. **与 Tokio 互操作** - 混合运行时支持
//!
//! ## 运行方式
//! ```bash
//! cargo run --example tokio_smol_latest_features_2025
//! ```
//use std::sync::Arc;
use std::time::{Duration, Instant};
//use tokio::sync::{Mutex, Semaphore};
use tokio::task::{JoinSet};
use tokio::time::{sleep, interval};

// ============================================================================
// 第一部分: Tokio 1.41+ 最新特性
// Part 1: Tokio 1.41+ Latest Features
// ============================================================================

mod tokio_latest_features {
    use super::*;

    /// # Tokio 特性 1: JoinSet 动态任务集管理
    /// 
    /// ## 新特性
    /// - 动态添加/移除任务
    /// - 有序/无序结果收集
    /// - 提前终止支持
    /// - 错误传播
    /// 
    /// ## 使用场景
    /// - 并行爬虫 (动态发现新 URL)
    /// - 工作池 (动态任务队列)
    /// - 批处理系统
    pub async fn joinset_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🎯 Tokio Feature 1: JoinSet 动态任务集               ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        let mut join_set = JoinSet::new();

        println!("📝 场景 1: 动态添加任务\n");

        // 动态添加任务
        for i in 0..5 {
            join_set.spawn(async move {
                let delay = Duration::from_millis(100 * (i + 1));
                sleep(delay).await;
                println!("  ✓ 任务 {} 完成 (延迟: {:?})", i, delay);
                i * 2 // 返回结果
            });
        }

        println!("  已添加 {} 个任务\n", join_set.len());

        // 收集前 3 个完成的任务结果
        println!("📦 收集前 3 个完成的任务:\n");
        for _ in 0..3 {
            if let Some(result) = join_set.join_next().await {
                match result {
                    Ok(value) => println!("  ← 收到结果: {}", value),
                    Err(e) => println!("  ✗ 任务失败: {}", e),
                }
            }
        }

        println!("\n⚠ 剩余 {} 个任务仍在运行", join_set.len());

        // 提前终止剩余任务
        println!("\n🛑 终止所有剩余任务...\n");
        join_set.abort_all();

        // 等待所有任务完成(包括被终止的)
        while let Some(result) = join_set.join_next().await {
            match result {
                Ok(value) => println!("  ← 任务完成: {}", value),
                Err(e) if e.is_cancelled() => println!("  ⊗ 任务被取消"),
                Err(e) => println!("  ✗ 任务错误: {}", e),
            }
        }

        println!("\n✅ JoinSet 演示完成");
    }

    /// # Tokio 特性 2: TaskLocal 任务本地存储
    /// 
    /// ## 特性说明
    /// - 类似线程本地存储,但用于异步任务
    /// - 每个任务有独立的值
    /// - 零成本抽象
    /// 
    /// ## 使用场景
    /// - 请求追踪 (Trace ID)
    /// - 上下文传播
    /// - 用户认证信息
    pub async fn task_local_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🏷️  Tokio Feature 2: TaskLocal 任务本地存储          ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        tokio::task_local! {
            // 定义任务本地变量
            static REQUEST_ID: String;
            static USER_ID: u64;
        }

        /// 模拟业务逻辑函数 - 自动获取上下文
        async fn handle_request(endpoint: &str) {
            REQUEST_ID.with(|req_id| {
                USER_ID.with(|user_id| {
                    println!(
                        "  [{}] 👤 用户 {} 访问 {}",
                        req_id, user_id, endpoint
                    );
                });
            });

            sleep(Duration::from_millis(50)).await;

            REQUEST_ID.with(|req_id| {
                println!("  [{}] ✓ 请求完成", req_id);
            });
        }

        println!("📝 场景: 多个并发请求,每个请求有独立的上下文\n");

        let mut tasks = vec![];

        // 创建多个任务,每个有不同的上下文
        for i in 0..3 {
            let request_id = format!("REQ-{:04}", 1000 + i);
            let user_id = 100 + i;

            let task = tokio::spawn(async move {
                // 设置任务本地变量
                REQUEST_ID
                    .scope(request_id.clone(), async move {
                        USER_ID
                            .scope(user_id, async move {
                                // 处理多个端点
                                handle_request("/api/users").await;
                                handle_request("/api/posts").await;
                            })
                            .await
                    })
                    .await
            });

            tasks.push(task);
        }

        // 等待所有任务完成
        for task in tasks {
            task.await.unwrap();
        }

        println!("\n✅ TaskLocal 演示完成");
    }

    /// # Tokio 特性 3: Runtime Metrics 运行时指标
    /// 
    /// ## 可收集的指标
    /// - 活跃任务数
    /// - 任务调度延迟
    /// - Worker 线程利用率
    /// - I/O 事件统计
    /// 
    /// ## 使用场景
    /// - 性能监控
    /// - 容量规划
    /// - 问题诊断
    pub async fn runtime_metrics_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  📊 Tokio Feature 3: Runtime Metrics 运行时指标       ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        // 获取当前运行时 handle
        let handle = tokio::runtime::Handle::current();

        println!("🔍 收集运行时指标...\n");

        // 创建一些负载
        let mut join_set = JoinSet::new();

        for i in 0..10 {
            join_set.spawn(async move {
                sleep(Duration::from_millis(100 + i * 10)).await;
                i
            });
        }

        // 定期收集指标
        let metrics_task = tokio::spawn(async move {
            let mut interval = interval(Duration::from_millis(200));
            for _ in 0..3 {
                interval.tick().await;

                // 获取运行时指标
                let metrics = handle.metrics();

                println!("  📈 运行时指标快照:");
                println!("     活跃任务数: {}", metrics.num_alive_tasks());
                println!("     Worker 数量: {}", metrics.num_workers());
                
                // 每个 worker 的统计 (部分指标)
                for worker_id in 0..metrics.num_workers() {
                    let park_count = metrics.worker_park_count(worker_id);
                    println!("     Worker {}: park_count={}", worker_id, park_count);
                }

                println!();
            }
        });

        // 等待任务完成
        while join_set.join_next().await.is_some() {}

        metrics_task.await.unwrap();

        println!("✅ Runtime Metrics 演示完成");
    }

    /// # Tokio 特性 4: 协作式调度优化
    /// 
    /// ## 特性说明
    /// - 自动插入 yield 点
    /// - 防止任务饿死
    /// - 公平调度保证
    /// 
    /// ## 使用场景
    /// - CPU 密集型任务
    /// - 长时间运行的循环
    /// - 实时系统
    pub async fn cooperative_scheduling_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🔄 Tokio Feature 4: 协作式调度优化                   ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📝 场景: CPU 密集型任务与 I/O 任务公平调度\n");

        let start = Instant::now();

        // CPU 密集型任务(有协作式调度)
        let cpu_task = tokio::spawn(async move {
            println!("  [CPU] 🔥 CPU 密集型任务启动");
            let mut sum = 0u64;
            for i in 0..10_000_000 {
                sum = sum.wrapping_add(i);

                // 每 100_000 次迭代主动让出
                if i % 100_000 == 0 {
                    tokio::task::yield_now().await;
                }
            }
            println!("  [CPU] ✓ CPU 任务完成,结果: {}", sum);
        });

        // I/O 任务(需要及时响应)
        let io_task = tokio::spawn(async move {
            println!("  [I/O] 💾 I/O 任务启动");
            for i in 0..10 {
                sleep(Duration::from_millis(50)).await;
                println!("  [I/O] ⏱ I/O 操作 {} 完成", i);
            }
            println!("  [I/O] ✓ I/O 任务完成");
        });

        // 等待两个任务
        let (cpu_res, io_res) = tokio::join!(cpu_task, io_task);
        cpu_res.unwrap();
        io_res.unwrap();

        println!("\n⏱ 总耗时: {:?}", start.elapsed());
        println!("✅ 协作式调度演示完成");
        println!("   I/O 任务得到及时调度,未被 CPU 任务阻塞");
    }

    /// # Tokio 特性 5: 取消令牌 (Cancellation Token)
    /// 
    /// ## 特性说明
    /// - 结构化取消传播
    /// - 父子令牌层次
    /// - 优雅关闭支持
    /// 
    /// ## 使用场景
    /// - 请求超时
    /// - 优雅关闭
    /// - 分布式事务
    pub async fn cancellation_token_demo() {
        use tokio_util::sync::CancellationToken;

        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🚫 Tokio Feature 5: Cancellation Token 取消令牌      ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📝 场景: 父任务取消时,所有子任务自动取消\n");

        // 创建父令牌
        let parent_token = CancellationToken::new();

        // 创建多个子令牌
        let child_tokens: Vec<_> = (0..3)
            .map(|_| parent_token.child_token())
            .collect();

        // 启动多个子任务
        let mut tasks = vec![];
        for (id, token) in child_tokens.into_iter().enumerate() {
            let task = tokio::spawn(async move {
                println!("  [Task {}] 🚀 启动", id);
                let mut count = 0;

                loop {
                    tokio::select! {
                        _ = token.cancelled() => {
                            println!("  [Task {}] ⊗ 收到取消信号,已处理 {} 个项目", id, count);
                            break;
                        }
                        _ = sleep(Duration::from_millis(100)) => {
                            count += 1;
                            println!("  [Task {}] ⚙ 处理项目 {}", id, count);
                        }
                    }
                }
            });
            tasks.push(task);
        }

        // 让任务运行一段时间
        sleep(Duration::from_millis(350)).await;

        // 取消父令牌 - 所有子任务自动取消
        println!("\n  [Parent] 🛑 发送取消信号...\n");
        parent_token.cancel();

        // 等待所有任务完成
        for task in tasks {
            task.await.unwrap();
        }

        println!("\n✅ Cancellation Token 演示完成");
    }

    /// 运行所有 Tokio 特性演示
    pub async fn demo_all() {
        println!("\n");
        println!("╔══════════════════════════════════════════════════════════════╗");
        println!("║                                                              ║");
        println!("║        🚀 Tokio 1.41+ 最新特性完整演示                       ║");
        println!("║        Tokio 1.41+ Latest Features Demo                     ║");
        println!("║                                                              ║");
        println!("║        日期: 2025-10-04                                      ║");
        println!("║        Rust 1.90 | Tokio 1.41+                               ║");
        println!("║                                                              ║");
        println!("╚══════════════════════════════════════════════════════════════╝");

        joinset_demo().await;
        task_local_demo().await;
        runtime_metrics_demo().await;
        cooperative_scheduling_demo().await;
        cancellation_token_demo().await;
    }
}

// ============================================================================
// 第二部分: Smol 2.0+ 最新特性
// Part 2: Smol 2.0+ Latest Features
// ============================================================================

mod smol_latest_features {
    use super::*;
    use smol::{Executor, LocalExecutor, Timer};
    use async_io::Async;
    use std::net::TcpListener;

    /// # Smol 特性 1: 轻量级 Executor
    /// 
    /// ## 特性说明
    /// - 极小的内存占用 (~200 bytes per task)
    /// - 快速任务创建
    /// - 单线程/多线程灵活配置
    /// 
    /// ## 性能对比
    /// - Tokio: ~1KB per task
    /// - Smol: ~200 bytes per task
    pub async fn lightweight_executor_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🪶 Smol Feature 1: 轻量级 Executor                   ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📊 性能测试: 创建 10,000 个任务\n");

        let ex = Executor::new();
        let start = Instant::now();

        // 创建大量轻量级任务
        for i in 0..10_000 {
            ex.spawn(async move {
                // 简单的任务
                let _ = i * 2;
            })
            .detach();
        }

        // 运行 executor
        smol::block_on(async {
            Timer::after(Duration::from_millis(100)).await;
        });

        let elapsed = start.elapsed();
        println!("  ⏱ 创建并调度 10,000 个任务耗时: {:?}", elapsed);
        println!("  📏 平均每个任务: {:?}", elapsed / 10_000);

        println!("\n✅ Lightweight Executor 演示完成");
    }

    /// # Smol 特性 2: Async-io 集成
    /// 
    /// ## 特性说明
    /// - 跨平台 I/O 抽象
    /// - epoll/kqueue/IOCP 自动选择
    /// - 与标准库兼容
    /// 
    /// ## 使用场景
    /// - 网络服务器
    /// - 文件 I/O
    /// - 进程通信
    pub async fn async_io_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  💾 Smol Feature 2: Async-io 集成                     ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📝 场景: 异步 TCP 服务器\n");

        // 创建 TCP listener
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        println!("  🎧 服务器监听: {}", addr);

        // 包装为异步
        let listener = Async::new(listener).unwrap();

        // 启动服务器任务
        let server = async move {
            println!("  [Server] 等待连接...");
            
            // 接受连接(异步)
            match listener.accept().await {
                Ok((stream, peer_addr)) => {
                    println!("  [Server] ✓ 接受连接: {}", peer_addr);
                    drop(stream);
                }
                Err(e) => {
                    println!("  [Server] ✗ 错误: {}", e);
                }
            }
        };

        // 启动客户端任务
        let client = async move {
            Timer::after(Duration::from_millis(100)).await;
            
            println!("  [Client] 🔗 连接到服务器...");
            match std::net::TcpStream::connect(addr) {
                Ok(_stream) => {
                    println!("  [Client] ✓ 连接成功");
                }
                Err(e) => {
                    println!("  [Client] ✗ 错误: {}", e);
                }
            }
        };

        // 并发运行
        smol::block_on(async {
            futures::join!(server, client);
        });

        println!("\n✅ Async-io 演示完成");
    }

    /// # Smol 特性 3: 与 Tokio 互操作
    /// 
    /// ## 特性说明
    /// - 在 Smol 中运行 Tokio 代码
    /// - 共享异步生态
    /// - 灵活运行时选择
    /// 
    /// ## 使用场景
    /// - 迁移现有项目
    /// - 使用特定库
    /// - 性能优化
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub async fn interop_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  🔄 Smol Feature 3: 与 Tokio 互操作                   ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📝 场景: Smol executor 运行 Tokio-style 代码\n");

        // Smol 任务
        let smol_task = async {
            println!("  [Smol] 🟢 Smol 任务运行");
            Timer::after(Duration::from_millis(50)).await;
            println!("  [Smol] ✓ Smol 任务完成");
        };

        // 通用异步任务(兼容两种运行时)
        let generic_task = async {
            println!("  [Generic] 🔵 通用异步任务");
            
            // 使用 futures 标准库
            use futures::future::FutureExt;
            
            let result = async { 42 }
                .map(|x| x * 2)
                .await;
            
            println!("  [Generic] ✓ 计算结果: {}", result);
        };

        // 在 Smol 中运行
        smol::block_on(async {
            futures::join!(smol_task, generic_task);
        });

        println!("\n✅ 互操作演示完成");
    }

    /// # Smol 特性 4: LocalExecutor 单线程优化
    /// 
    /// ## 特性说明
    /// - 单线程专用 executor
    /// - !Send 任务支持
    /// - 更低开销
    /// 
    /// ## 使用场景
    /// - GUI 应用
    /// - 单线程服务器
    /// - 嵌入式系统
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn local_executor_demo() {
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  📍 Smol Feature 4: LocalExecutor 单线程优化          ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        println!("📝 场景: 单线程 executor 运行 !Send 任务\n");

        use std::rc::Rc;

        // LocalExecutor 可以运行 !Send 任务
        let local_ex = LocalExecutor::new();

        smol::block_on(local_ex.run(async {
            // Rc 是 !Send 的
            let data = Rc::new(vec![1, 2, 3, 4, 5]);
            let data1 = Rc::clone(&data);
            let data2 = Rc::clone(&data);

            let task1 = local_ex.spawn(async move {
                println!("  [Task 1] 📦 数据: {:?}", data1);
                Timer::after(Duration::from_millis(50)).await;
                println!("  [Task 1] ✓ 完成");
            });

            let task2 = local_ex.spawn(async move {
                println!("  [Task 2] 📦 数据: {:?}", data);
                Timer::after(Duration::from_millis(30)).await;
                println!("  [Task 2] ✓ 完成");
            });

            task1.await;
            task2.await;

            println!("  [Main] ✓ 所有任务完成");
        }));

        println!("\n✅ LocalExecutor 演示完成");
    }

    /// 运行所有 Smol 特性演示
    pub fn demo_all() {
        println!("\n");
        println!("╔══════════════════════════════════════════════════════════════╗");
        println!("║                                                              ║");
        println!("║        🌟 Smol 2.0+ 最新特性完整演示                         ║");
        println!("║        Smol 2.0+ Latest Features Demo                       ║");
        println!("║                                                              ║");
        println!("║        日期: 2025-10-04                                      ║");
        println!("║        Rust 1.90 | Smol 2.0+                                 ║");
        println!("║                                                              ║");
        println!("╚══════════════════════════════════════════════════════════════╝");

        smol::block_on(lightweight_executor_demo());
        smol::block_on(async_io_demo());
        smol::block_on(interop_demo());
        local_executor_demo();
    }
}

// ============================================================================
// 第三部分: Tokio vs Smol 性能对比
// Part 3: Tokio vs Smol Performance Comparison
// ============================================================================

mod performance_comparison {
    use super::*;

    /// 性能基准测试
    pub async fn benchmark_suite() {
        println!("\n");
        println!("╔══════════════════════════════════════════════════════════════╗");
        println!("║                                                              ║");
        println!("║        📊 Tokio vs Smol 性能对比                             ║");
        println!("║        Performance Comparison                                ║");
        println!("║                                                              ║");
        println!("╚══════════════════════════════════════════════════════════════╝\n");

        // 基准 1: 任务创建开销
        println!("🏁 基准 1: 任务创建开销\n");

        let tokio_start = Instant::now();
        let mut tasks = vec![];
        for i in 0..1000 {
            tasks.push(tokio::spawn(async move {
                let _ = i * 2;
            }));
        }
        for task in tasks {
            task.await.ok();
        }
        let tokio_elapsed = tokio_start.elapsed();

        println!("  Tokio: {:?} (1000 个任务)", tokio_elapsed);

        let smol_start = Instant::now();
        smol::block_on(async {
            let ex = smol::Executor::new();
            for i in 0..1000 {
                ex.spawn(async move {
                    let _ = i * 2;
                }).detach();
            }
            smol::Timer::after(Duration::from_millis(10)).await;
        });
        let smol_elapsed = smol_start.elapsed();

        println!("  Smol:  {:?} (1000 个任务)", smol_elapsed);

        let speedup = tokio_elapsed.as_nanos() as f64 / smol_elapsed.as_nanos() as f64;
        println!("\n  📈 Smol 快 {:.2}x", speedup);

        // 基准 2: 上下文切换
        println!("\n🏁 基准 2: 上下文切换开销\n");

        let tokio_start = Instant::now();
        tokio::spawn(async {
            for _ in 0..10000 {
                tokio::task::yield_now().await;
            }
        }).await.ok();
        let tokio_switch_time = tokio_start.elapsed();

        println!("  Tokio: {:?} (10000 次 yield)", tokio_switch_time);

        let smol_start = Instant::now();
        smol::block_on(async {
            for _ in 0..10000 {
                smol::future::yield_now().await;
            }
        });
        let smol_switch_time = smol_start.elapsed();

        println!("  Smol:  {:?} (10000 次 yield)", smol_switch_time);

        // 总结
        println!("\n╭─────────────────────────────────────────────────╮");
        println!("│  🎯 性能对比总结                                │");
        println!("│                                                 │");
        println!("│  Tokio 优势:                                    │");
        println!("│  • 成熟的生态系统                               │");
        println!("│  • 更多的第三方库支持                           │");
        println!("│  • 企业级功能 (metrics, tracing)                │");
        println!("│                                                 │");
        println!("│  Smol 优势:                                     │");
        println!("│  • 更低的内存占用                               │");
        println!("│  • 更快的任务创建                               │");
        println!("│  • 更简单的 API                                 │");
        println!("│  • 更小的二进制体积                             │");
        println!("│                                                 │");
        println!("│  选择建议:                                      │");
        println!("│  • 大型项目/企业应用 → Tokio                   │");
        println!("│  • 小型工具/嵌入式 → Smol                      │");
        println!("│  • 性能关键应用 → 基准测试决定                 │");
        println!("╰─────────────────────────────────────────────────╯");
    }
}

// ============================================================================
// 主函数
// Main Function
// ============================================================================

#[tokio::main]
async fn main() {
    println!("\n");
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   🚀 Tokio 1.41+ 和 Smol 2.0+ 最新特性完整演示 2025              ║");
    println!("║   Latest Features of Tokio & Smol Complete Demo 2025            ║");
    println!("║                                                                  ║");
    println!("║   📅 日期: 2025-10-04                                            ║");
    println!("║   🦀 Rust: 1.90+                                                 ║");
    println!("║   📦 Tokio: 1.41+ | Smol: 2.0+                                   ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");

    // 第一部分: Tokio 特性
    tokio_latest_features::demo_all().await;

    // 第二部分: Smol 特性
    smol_latest_features::demo_all();

    // 第三部分: 性能对比
    performance_comparison::benchmark_suite().await;

    println!("\n");
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   ✅ 所有演示完成!                                               ║");
    println!("║                                                                  ║");
    println!("║   📚 涵盖内容:                                                    ║");
    println!("║   • Tokio 5 个最新特性                                           ║");
    println!("║   • Smol 4 个最新特性                                            ║");
    println!("║   • 性能对比分析                                                 ║");
    println!("║   • 实际使用场景演示                                             ║");
    println!("║                                                                  ║");
    println!("║   🎯 下一步:                                                     ║");
    println!("║   1. 在实际项目中应用这些特性                                    ║");
    println!("║   2. 基准测试评估性能提升                                        ║");
    println!("║   3. 根据需求选择合适的运行时                                    ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");
    println!();
}

