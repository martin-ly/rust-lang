> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# 最小基准指南（同步/异步）

## 📊 目录

- [最小基准指南（同步/异步）](#最小基准指南同步异步)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [适用范围](#适用范围)
  - [准备](#准备)
  - [运行](#运行)
  - [关注指标](#关注指标)
  - [推荐对照](#推荐对照)
  - [导航](#导航)

## 目标

- 提供统一、可复制的基准最小步骤，对比同步与异步在吞吐/延迟上的差异。

## 适用范围

- Windows PowerShell 与 Linux shell；默认使用工作区内的 `c05_threads` 与 `c06_async`。

## 准备

```powershell
# PowerShell（Windows）
cd .\crates\c05_threads
cargo bench --no-run | cat

cd ..\c06_async
cargo bench --no-run | cat
```

```bash
# Bash（Linux）
cd ./crates/c05_threads && cargo bench --no-run | cat
cd ../c06_async && cargo bench --no-run | cat
```

可选：

```powershell
$env:RUSTFLAGS = "-C target-cpu=native"
```

## 运行

```powershell
cargo bench -p c05_threads | cat
cargo bench -p c06_async | cat
```

## 关注指标

- 吞吐（ops/s）与延迟（ns/op）：不同容量、批量与并发参数下的变化。
- 抖动：p95/p99 相对均值的偏差。
- 资源占用：线程数、上下文切换、内存峰值（可用 `WPA`/`perf`）。

## 推荐对照

- 通道：`priority_channels_bench.rs` vs `async_benches.rs`（bounded/unbounded）。
- 背压：`backpressure_bench.rs` vs `async_benches.rs`（Semaphore/容量变化）。
- 线程/任务：`concurrency_benchmark.rs` vs JoinSet/select 参数化用例。

## 导航

- 同步范式：[`01_synchronous/00_index.md`](./01_synchronous/00_index.md)
- 异步范式：[`02_async/00_index.md`](./02_async/00_index.md)
