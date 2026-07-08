> **EN**: Async Process Management in Rust
> **Summary**: Managing child processes inside Rust's async runtime: tokio::process, async I/O, timeouts, cancellation, and structured concurrency.

# Rust 异步进程管理

> **权威页地位**：本页为 Rust 异步进程管理概念的 canonical 解释来源。
> **对应 crate 示例**：`crates/c07_process/docs/05_async_process_management.md` 现为摘要页，指向此处。

---

## 1. 为什么需要异步进程管理

在异步运行时中管理子进程时，同步 `std::process` 会阻塞当前线程，导致整个运行时线程池被占满。`tokio::process` 将 `std::process` 的 I/O 与等待操作转移到异步任务中，从而：

- 不阻塞工作线程
- 支持并发管理大量子进程
- 与 `tokio::time::timeout`、取消 token 无缝集成

## 2. `tokio::process` 核心 API

| 类型 | 作用 |
| :--- | :--- |
| `tokio::process::Command` | 异步进程构建器 |
| `tokio::process::Child` | 子进程句柄 |
| `tokio::process::ChildStdin` | 异步标准输入 |
| `tokio::process::ChildStdout` | 异步标准输出 |
| `tokio::process::ChildStderr` | 异步标准错误 |

```rust
use tokio::process::Command;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new("echo")
        .arg("hello from async process")
        .output()
        .await?;

    println!("{}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

## 3. 异步生命周期管理

### 3.1 超时控制

```rust
use tokio::process::Command;
use tokio::time::{timeout, Duration};

async fn run_with_timeout() -> Result<(), Box<dyn std::error::Error>> {
    let result = timeout(
        Duration::from_secs(5),
        Command::new("sleep").arg("10").output(),
    ).await;

    match result {
        Ok(Ok(output)) => println!("完成: {}", output.status),
        Ok(Err(e)) => println!("进程错误: {}", e),
        Err(_) => println!("超时"),
    }
    Ok(())
}
```

### 3.2 异步通信

通过 `tokio::io::AsyncWriteExt` 和 `AsyncBufReadExt` 异步读写子进程管道：

```rust
use tokio::io::{AsyncWriteExt, AsyncBufReadExt, BufReader};
use tokio::process::Command;
use std::process::Stdio;

async fn communicate() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(b"hello\n").await?;
        // 关闭 stdin，让子进程结束
    }

    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        let mut lines = reader.lines();
        while let Some(line) = lines.next_line().await? {
            println!("{}", line);
        }
    }

    child.wait().await?;
    Ok(())
}
```

## 4. 结构化并发

使用 `tokio::select!` 或 `JoinSet` 同时管理多个子进程，并在取消时统一清理：

```rust
use tokio::process::Command;

async fn run_many() -> Result<(), Box<dyn std::error::Error>> {
    let mut set = tokio::task::JoinSet::new();

    for i in 0..4 {
        set.spawn(async move {
            Command::new("echo").arg(format!("task {}", i)).output().await
        });
    }

    while let Some(result) = set.join_next().await {
        let output = result??;
        println!("{}", String::from_utf8_lossy(&output.stdout));
    }

    Ok(())
}
```

## 5. 取消与清理

当持有 `Child` 句柄的任务被取消时，`Child` 的 `Drop` 实现默认会尝试 `kill` 子进程，但**不会等待其结束**。对于需要确保资源完全释放的场景，应显式调用 `kill().await` 和 `wait().await`。

```rust
async fn cancellable_child() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("long_running_task").spawn()?;

    // 在取消时显式清理
    tokio::select! {
        _ = child.wait() => {}
        _ = tokio::signal::ctrl_c() => {
            child.kill().await?;
            child.wait().await?;
        }
    }

    Ok(())
}
```

## 6. 最佳实践

- 优先使用 `tokio::process` 而非 `std::process`  inside async runtime。
- 为所有可能长时间运行的子进程设置超时。
- 在取消路径中显式等待子进程终止，避免僵尸进程。
- 将子进程输出流式处理，避免一次性加载大量数据。

---

## 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [高级进程管理](02_advanced_process_management.md)
- [Async/Await](../01_async/02_async.md)
- [Future 与 Executor 机制](../01_async/39_future_and_executor_mechanisms.md)

---

> **权威来源**: [Tokio Process](https://docs.rs/tokio/latest/tokio/process/) · [Rust Async Book](https://rust-lang.github.io/async-book/)
