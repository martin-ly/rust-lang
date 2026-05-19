# Glommio 快速入门指南

## 🚀 5 分钟上手 Glommio

Glommio 是基于 **io_uring** 的极致性能异步运行时，专为 Linux 平台设计。

## ⚡ 为什么选择 Glommio?

| 优势  | 说明  |
| :--- | :--- |
| 🏆 **极低延迟** | P99 < 100μs |
| 🚀 **高吞吐**   | > 2M req/s  |
| 💾 **低内存**   | ~2KB/任务   |
| 🎯 **CPU 效率** | > 95%       |

## 📋 系统要求

```bash
# 检查 Linux 版本 (需要 >= 5.1)
uname -r

# 检查 io_uring 支持
cat /proc/sys/kernel/io_uring_disabled  # 应该为 0 或 不存在

# 安装依赖 (Debian/Ubuntu)
sudo apt-get install liburing-dev
```

## 📦 安装

在 `Cargo.toml` 中添加:

```toml
[dependencies]
glommio = "0.9.0"
futures = "0.3"
```

**重要**: Glommio 仅支持 Linux，建议使用条件依赖:

```toml
[target.'cfg(target_os = "linux")'.dependencies]
glommio = "0.9.0"
```

## 💻 Hello World

```rust
use glommio::{LocalExecutor, Task};

fn main() {
    // 创建执行器并运行
    LocalExecutor::default().run(async {
        println!("🚀 Hello from Glommio!");

        // 创建任务
        let task = Task::local(async {
            println!("✅ Task running");
            42
        });

        // 等待结果
        let result = task.await;
        println!("📊 Result: {}", result);
    });
}
```

运行:

```bash
cargo run
# 输出:
# 🚀 Hello from Glommio!
# ✅ Task running
# 📊 Result: 42
```

## 🔄 并发任务

```rust
use glommio::{LocalExecutor, Task};
use futures::future::join_all;

fn main() {
    LocalExecutor::default().run(async {
        // 创建 10 个并发任务
        let tasks: Vec<_> = (0..10)
            .map(|i| Task::local(async move {
                println!("Task {} running", i);
                i * 2
            }))
            .collect();

        // 等待所有任务完成
        let results = join_all(tasks).await;
        println!("Results: {:?}", results);
    });
}
```

## 🎯 CPU 绑定

Glommio 的核心优势: 将任务绑定到特定 CPU 核心。

```rust
use glommio::LocalExecutorBuilder;

fn main() {
    // 绑定到核心 0
    let handle = LocalExecutorBuilder::default()
        .pin_to_cpu(0)
        .name("worker-0")
        .spawn(|| async move {
            println!("Running on CPU 0");
            // 你的工作负载
        })
        .unwrap();

    handle.join().unwrap();
}
```

## 💾 高性能文件 I/O

使用 DMA (Direct Memory Access) 实现零拷贝 I/O:

```rust
use glommio::{LocalExecutor, io::DmaFile};

fn main() {
    LocalExecutor::default().run(async {
        // 写入文件
        let file = DmaFile::create("/tmp/test.txt").await.unwrap();
        let data = b"Hello Glommio!".to_vec();
        file.write_at(data, 0).await.unwrap();
        file.close().await.unwrap();

        // 读取文件
        let file = DmaFile::open("/tmp/test.txt").await.unwrap();
        let content = file.read_at(0, 14).await.unwrap();
        println!("{}", String::from_utf8_lossy(&content));
        file.close().await.unwrap();

        // 清理
        std::fs::remove_file("/tmp/test.txt").unwrap();
    });
}
```

## 🌐 网络服务器

```rust
use glommio::{LocalExecutor, Task, net::TcpListener};

fn main() {
    LocalExecutor::default().run(async {
        let listener = TcpListener::bind("127.0.0.1:8080").unwrap();
        println!("Server listening on 8080");

        loop {
            match listener.accept().await {
                Ok(stream) => {
                    // 为每个连接创建任务
                    Task::local(async move {
                        // 处理连接
                        println!("New connection");
                    }).detach();
                }
                Err(e) => eprintln!("Error: {}", e),
            }
        }
    });
}
```

## 🔀 多核并行

充分利用多核心:

```rust
use glommio::LocalExecutorBuilder;

fn main() {
    let num_cores = num_cpus::get();
    let mut handles = vec![];

    // 为每个核心创建执行器
    for core_id in 0..num_cores {
        let handle = LocalExecutorBuilder::default()
            .pin_to_cpu(core_id)
            .spawn(move || async move {
                println!("Worker {} on core {}", core_id, core_id);
                // 工作负载
            })
            .unwrap();

        handles.push(handle);
    }

    // 等待所有执行器完成
    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 📚 运行示例

本项目提供了完整的示例:

```bash
# 运行综合示例
cargo run --example glommio_comprehensive_2025

# 运行性能基准测试
cargo bench --bench glommio_benchmarks
```

## ⚠️ 常见问题

### Q: 为什么我的程序无法编译?

A: 确保你在 Linux 5.1+ 上，并安装了 `liburing-dev`。

### Q: 如何选择核心数量?

A: 一般等于 CPU 核心数，可通过 `num_cpus::get()` 获取。

### Q: 为什么延迟仍然高?

A: 确保:

- 使用 CPU pinning
- 避免跨核心通信
- 使用 release 模式编译

### Q: 能在 Windows/macOS 上运行吗?

A: 不能。Glommio 依赖 Linux 的 io_uring。

## 🎓 下一步

- 📖 阅读 [Glommio 最佳实践](../tier_02_guides/09_glommio_best_practices_2025.md)
- 📊 查看 [运行时对比分析](../tier_03_references/06_runtime_comparison_glommio_2025.md)
- 💻 探索 [综合示例](../../examples/glommio_comprehensive_2025.rs)

## 🔗 资源

- [官方文档](https://docs.rs/glommio)
- [GitHub](https://github.com/DataDog/glommio)
- [io_uring 介绍](https://kernel.dk/io_uring.pdf)

---

**提示**: Glommio 适合高性能、延迟敏感的 Linux 应用。如需跨平台，考虑使用 Tokio。

**最后更新**: 2025-10-30
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
