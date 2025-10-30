//! # Glommio 高性能异步运行时模块
//!
//! Glommio 是由 DataDog 开发的基于 io_uring 的高性能异步运行时。
//! 它采用 thread-per-core 架构，专为极致性能设计。
//!
//! ## 核心特性
//!
//! - **Thread-per-core 架构**: 每个 CPU 核心一个线程，避免线程切换开销
//! - **基于 io_uring**: 利用 Linux 5.1+ 的高性能 I/O 接口
//! - **NUMA 感知**: 针对多 socket 系统优化
//! - **零拷贝 I/O**: 最小化数据复制
//! - **CPU 亲和性**: 精确控制任务调度到特定核心
//!
//! ## 适用场景
//!
//! - 高频交易系统
//! - 数据库引擎
//! - 高性能网络服务
//! - 实时数据处理
//!
//! ## 限制
//!
//! - **仅支持 Linux**: 依赖 io_uring (Linux 5.1+)
//! - **学习曲线**: thread-per-core 模型需要特殊的编程思维
//! - **生态系统**: 相对较小的生态系统

#![cfg(target_os = "linux")]

use std::time::Duration;

/// Glommio 运行时示例
///
/// # 示例
///
/// ```rust,no_run
/// use c06_async::glommio::GlommioExample;
///
/// # #[cfg(target_os = "linux")]
/// GlommioExample::run_basic_example();
/// ```
pub struct GlommioExample;

impl GlommioExample {
    /// 运行基本示例
    pub fn run_basic_example() {
        #[cfg(target_os = "linux")]
        {
            use glommio::{LocalExecutorBuilder, Task};

            let handle = LocalExecutorBuilder::default()
                .spawn(|| async move {
                    println!("✅ Glommio: Hello from thread-per-core runtime!");

                    // 创建并运行一个简单任务
                    let task = Task::local(async {
                        glommio::timer::sleep(Duration::from_millis(100)).await;
                        println!("✅ Glommio: Task completed");
                        42
                    });

                    let result = task.await;
                    println!("✅ Glommio: Task result: {}", result);
                })
                .unwrap();

            handle.join().unwrap();
        }
    }

    /// 运行 I/O 密集型示例
    pub fn run_io_intensive_example() {
        #[cfg(target_os = "linux")]
        {
            use glommio::{LocalExecutorBuilder, Task};
            use std::io::Write;

            let handle = LocalExecutorBuilder::default()
                .spawn(|| async move {
                    println!("✅ Glommio: I/O Intensive Example");

                    // 使用 Glommio 的文件 I/O
                    let task = Task::local(async {
                        // 创建临时文件
                        let path = "/tmp/glommio_test.txt";
                        let mut file = std::fs::File::create(path).unwrap();
                        file.write_all(b"Hello Glommio!").unwrap();

                        // 读取文件
                        let content = std::fs::read_to_string(path).unwrap();
                        println!("✅ File content: {}", content);

                        // 清理
                        std::fs::remove_file(path).unwrap();
                    });

                    task.await;
                })
                .unwrap();

            handle.join().unwrap();
        }
    }

    /// 运行多核并行示例
    pub fn run_multicore_example() {
        #[cfg(target_os = "linux")]
        {
            use glommio::LocalExecutorBuilder;

            println!("✅ Glommio: Multi-core Example");
            let num_cores = num_cpus::get();
            println!("✅ Detected {} CPU cores", num_cores);

            let mut handles = vec![];

            // 在每个核心上创建一个执行器
            for core_id in 0..std::cmp::min(num_cores, 4) {
                let handle = LocalExecutorBuilder::default()
                    .pin_to_cpu(core_id)
                    .spawn(move || async move {
                        println!("✅ Glommio: Running on core {}", core_id);

                        // 模拟计算密集型任务
                        let mut sum = 0u64;
                        for i in 0..1_000_000 {
                            sum = sum.wrapping_add(i);
                        }

                        println!("✅ Core {} completed: sum = {}", core_id, sum);
                        sum
                    })
                    .unwrap();

                handles.push(handle);
            }

            // 等待所有执行器完成
            for (i, handle) in handles.into_iter().enumerate() {
                let result = handle.join().unwrap();
                println!("✅ Core {} result: {}", i, result);
            }
        }
    }
}

/// Glommio 性能特性分析
pub struct GlommioPerformance;

impl GlommioPerformance {
    /// 获取性能特性描述
    pub fn get_characteristics() -> Vec<(&'static str, &'static str)> {
        vec![
            ("架构模型", "Thread-per-core (每核心一线程)"),
            ("I/O 接口", "io_uring (Linux 5.1+)"),
            ("延迟", "极低 (<100μs)"),
            ("吞吐量", "极高 (>2M req/s)"),
            ("CPU 效率", "极高 (>95% CPU 利用率)"),
            ("内存开销", "低 (每任务 ~2KB)"),
            ("上下文切换", "几乎无 (同核心内)"),
            ("NUMA 优化", "支持"),
            ("零拷贝", "支持"),
        ]
    }

    /// 与其他运行时的对比
    pub fn compare_with_others() -> Vec<(&'static str, &'static str, &'static str, &'static str)> {
        vec![
            ("特性", "Glommio", "Tokio", "Smol"),
            ("架构", "Thread-per-core", "Work-stealing", "单线程/多线程"),
            ("Linux 依赖", "是 (io_uring)", "否", "否"),
            ("延迟", "极低", "低", "低"),
            ("吞吐量", "极高", "高", "中高"),
            ("学习曲线", "陡峭", "中等", "平缓"),
            ("生态系统", "小", "大", "中"),
            ("适用场景", "高性能服务器", "通用异步", "轻量级应用"),
        ]
    }
}

/// Glommio 最佳实践
pub struct GlommioBestPractices;

impl GlommioBestPractices {
    /// 获取最佳实践建议
    pub fn get_practices() -> Vec<(&'static str, &'static str)> {
        vec![
            ("任务分配", "将任务固定到特定核心，避免跨核心通信"),
            ("数据结构", "使用线程局部数据结构，避免同步开销"),
            ("I/O 操作", "尽量使用 Glommio 提供的 I/O API"),
            ("CPU 绑定", "明确指定 CPU 亲和性，避免迁移"),
            ("NUMA", "在 NUMA 系统上注意内存分配位置"),
            ("错误处理", "使用 Result 而非 panic，保持执行器稳定"),
            ("监控", "使用 Glommio 的统计功能监控性能"),
            ("测试", "在目标 Linux 版本上进行充分测试"),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_os = "linux")]
    fn test_glommio_characteristics() {
        let chars = GlommioPerformance::get_characteristics();
        assert!(!chars.is_empty());
        assert!(chars.iter().any(|(k, _)| *k == "架构模型"));
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_glommio_comparison() {
        let comparison = GlommioPerformance::compare_with_others();
        assert!(comparison.len() > 1);
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_best_practices() {
        let practices = GlommioBestPractices::get_practices();
        assert!(!practices.is_empty());
    }
}

