# Tokio 最佳实践与惯用法（Rust 1.90，2025 版）

本文面向使用 Rust 1.90 的项目，系统化整理 Tokio 运行时在生产中的推荐配置、常见模式、易错点与调试观测方法，并提供可复制片段（详见 `docs/async_cookbook_tokio_smol.md` 与 `examples/tokio_patterns.rs`）。

## 0. 目录（严格编号）

1. 运行时配置
2. 结构化并发
3. 同步原语与背压
4. 超时、重试与速率限制
5. 常见模式片段（Tokio）
6. 调试与观测
7. 易错点清单
8. 与生态的集成建议
9. 迁移与评估

- 目标读者：服务端工程、网络编程、批处理/调度、爬虫与 I/O 密集任务。
- 版本假设：Rust 1.90，Tokio 1.x（工作区锁定最新稳定版），`futures`、`tracing`、`tokio-util`、`tokio-stream` 等常用配套。

## 1. 运行时配置

- 默认入口：`#[tokio::main(flavor = "multi_thread", worker_threads = num_cpus::get())]`。在容器/云原生环境，优先尊重 `CPU quota`，必要时外部注入线程数。
- I/O 驱动：网络与文件 I/O 混部通常没问题；极端高吞吐网服可考虑单独进程或细分服务域。
- 阻塞调用：使用 `tokio::task::spawn_blocking` 包裹 CPU/阻塞 I/O；不要在 async 任务内直接调用阻塞 API。
- Coop/公平性：Tokio 调度器具备协作式让步；尽量避免长时间循环不 `await`。

## 2. 结构化并发

- 首选 `JoinSet` 管理动态任务集，支持显式 `abort`，并在 `drop` 时统一回收。
- `select!` 用于竞争式等待（任务完成/超时/取消）与“先到先得”逻辑。
- 组合子：`try_join!/join!` 适合固定数量并行；大量动态并发优先 `JoinSet` 或 `FuturesUnordered`（配 `buffer_unordered`）。
- 取消语义：父任务 `drop`/`abort` 应传递取消；使用 `tokio::time::timeout` 构建超时边界。

## 3. 同步原语与背压

- mpsc：优先使用有界通道确定背压；容量与生产速率、消费速率、内存预算协同设计。
- oneshot：请求/响应配对；丢弃一端要能被另一端检测并及时结束。
- `Semaphore`：控制并发限额；与 `buffer_unordered(N)` 吻合设计。
- `Notify`：轻量唤醒，不承载数据；避免“丢唤醒”，配合状态机使用。

## 4. 超时、重试与速率限制

- 超时：外层粗粒度（请求级别），内层细粒度（子步骤）。避免全链路共享一个过小的超时。
- 重试：使用指数退避与抖动；区分可重试（网络瞬断）与不可重试（validation）错误。
- 限速/令牌桶：优先在入口处做速率限制，避免压力深入系统。

## 5. 常见模式片段（Tokio）

1) JoinSet 批量并发并收割结果：

    ```rust
    use tokio::task::JoinSet;

    async fn fetch(id: usize) -> anyhow::Result<usize> { Ok(id * 2) }

    pub async fn run_batch(ids: Vec<usize>) -> anyhow::Result<Vec<usize>> {
        let mut set = JoinSet::new();
        for id in ids { set.spawn(fetch(id)); }
        let mut out = Vec::new();
        while let Some(res) = set.join_next().await { out.push(res??); }
        Ok(out)
    }
    ```

2) select 竞争：任务/超时/取消：

    ```rust
    use tokio::{select, time::{timeout, Duration}};

    async fn op() { /* ... */ }

    pub async fn run() {
        let task = tokio::spawn(op());
        let res = select! {
            _ = timeout(Duration::from_secs(2), async {}) => "timeout",
            r = task => if r.is_ok() { "done" } else { "join-error" },
        };
        tracing::info!(%res, "select finished");
    }
    ```

3) 背压：有界通道 + 消费速率：

    ```rust
    use tokio::sync::mpsc;

    pub async fn pipeline() {
        let (tx, mut rx) = mpsc::channel::<u64>(1024);
        let prod = tokio::spawn(async move {
            for i in 0..10_000u64 { if tx.send(i).await.is_err() { break; } }
        });
        let cons = tokio::spawn(async move {
            while let Some(v) = rx.recv().await { /* process v */ }
        });
        let _ = tokio::join!(prod, cons);
    }
    ```

4) 限流：Semaphore 控并发：

    ```rust
    use std::sync::Arc;
    use tokio::sync::Semaphore;

    async fn work(_i: usize) { /* ... */ }

    pub async fn limited(n: usize) {
        let limiter = Arc::new(Semaphore::new(64));
        let mut set = tokio::task::JoinSet::new();
        for i in 0..n {
            let permit = limiter.clone().acquire_owned().await.unwrap();
            set.spawn(async move { let _p = permit; work(i).await; });
        }
        while set.join_next().await.is_some() {}
    }
    ```

### 6. 调试与观测

- 结构化日志：`tracing` + `tracing-subscriber`，按目标模块设定级别；生产环境输出 JSON 便于采集。
- 任务观测：`tokio-console`（实时任务/资源洞察）在开发/压测环境启用；生产建议谨慎开启。
- 指标：配合 `prometheus` 导出 QPS、延迟 p50/p95、队列长度、丢弃率、错误分布。

### 7. 易错点清单

- 在 async 任务中执行阻塞 I/O；应使用 `spawn_blocking`。
- 在 `select!` 分支内遗漏取消与资源回收；要显式 `abort` 或消费 `JoinHandle`。
- 无界队列导致内存飙升；生产中优先有界并结合背压策略。
- 忽略错误传播，吞掉 `Result`；要区分可重试/不可重试并记录上下文。
- 忽略 shutdown 流程；在服务停止时应广播关闭信号并等待任务收敛。

### 8. 与生态的集成建议

- HTTP：`hyper/axum`；TCP：`tokio::net`；数据库：使用官方异步驱动并启用连接池；缓存：`redis` 异步客户端；消息：`nats`/`kafka` 异步客户端。
- 文件/对象存储：S3/GCS 客户端建议显式超时与重试；大对象采用分块并行上传/下载。

### 9. 迁移与评估

- 从同步迁移：先边界异步化（I/O 入口），再向内渗透；保持模块边界清晰。
- 性能评估：基准优先关注延迟分布与尾部（p99），其次是吞吐与资源占用；避免仅观察平均值。

参见：`examples/tokio_patterns.rs`、`docs/async_cookbook_tokio_smol.md`、`docs/async_best_practices.md`。
