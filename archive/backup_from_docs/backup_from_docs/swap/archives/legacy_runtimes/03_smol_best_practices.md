# Smol 最佳实践与惯用法（Rust 1.90，2025 版）

Smol 是轻量级异步运行时，适合嵌入式、CLI、库内嵌与资源受限场景。本文给出生产可用的配置、模式与易错点；示例见 `examples/smol_patterns.rs`。

## 目录

- [Smol 最佳实践与惯用法（Rust 1.90，2025 版）](#smol-最佳实践与惯用法rust-1902025-版)
  - [目录](#目录)
  - [1. 运行与集成](#1-运行与集成)
    - [2. 常用模式](#2-常用模式)
    - [3. 观测与错误处理](#3-观测与错误处理)
    - [4. 易错点](#4-易错点)
    - [5. 场景选型](#5-场景选型)

## 1. 运行与集成

- 启动：`smol::block_on(async { ... })` 作为入口；库开发可暴露 async API 由上层决定运行时。
- 定时器/IO：使用 `async_io`/`futures-lite` 配套（Smol v2 生态）；TCP/UDP/文件通过 `Async<T>` 包装。
- 任务：`smol::spawn(fut).detach()` 生成分离任务；需要结构化管理时，保留 `JoinHandle` 自行实现任务集或用 `FuturesUnordered`。

### 2. 常用模式

1) 异步 TCP echo（最小化）：

    ```rust
    use smol::io::{AsyncReadExt, AsyncWriteExt};
    use smol::net::TcpListener;

    pub async fn echo(addr: &str) -> std::io::Result<()> {
        let listener = TcpListener::bind(addr).await?;
        loop {
            let (mut stream, _) = listener.accept().await?;
            smol::spawn(async move {
                let mut buf = vec![0u8; 1024];
                loop {
                    let n = match stream.read(&mut buf).await { Ok(0) => break, Ok(n) => n, Err(_) => break };
                    if stream.write_all(&buf[..n]).await.is_err() { break; }
                }
            }).detach();
        }
    }
    ```

2) 并发与背压（FuturesUnordered + semaphore）：

    ```rust
    use futures::stream::{FuturesUnordered, StreamExt};
    use std::sync::Arc;
    use async_lock::Semaphore;

    async fn work(i: usize) -> anyhow::Result<usize> { Ok(i * 2) }

    pub async fn limited(n: usize) -> anyhow::Result<Vec<usize>> {
        let limiter = Arc::new(Semaphore::new(64));
        let mut futs = FuturesUnordered::new();
        for i in 0..n {
            let sem = limiter.clone();
            futs.push(async move { let _p = sem.acquire().await; work(i).await });
        }
        let mut out = Vec::new();
        while let Some(r) = futs.next().await { out.push(r?); }
        Ok(out)
    }
    ```

### 3. 观测与错误处理

- 日志：`tracing` 一样可用；为 CLI/嵌入式建议简化为文本或 JSON 输出。
- 错误：尽量保留上下文（`anyhow`/`thiserror`），区分可重试与不可重试，搭配退避重试。

### 4. 易错点

- 分离任务丢失错误：`detach()` 后错误无人接收；在关键路径保留 `JoinHandle` 并集中收割结果。
- 与 Tokio 生态混用：避免在同进程混跑多运行时的 I/O 类型；必要时以进程边界或明确定界层隔离。
- 无界并发：`spawn` 大量任务导致内存与调度抖动；采用信号量或批量调度。

### 5. 场景选型

- 选择 Smol 当：二进制体积敏感、运行时需嵌入库、依赖面尽量小、平台受限。
- 选择 Tokio 当：需要成熟 I/O 生态（数据库/HTTP/消息中间件等）、多线程高吞吐、可观测与工具链完善。

参见：`docs/async_cookbook_tokio_smol.md`、`docs/async_best_practices.md`。
