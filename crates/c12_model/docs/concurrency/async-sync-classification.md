# 同步与异步模型：分类、等价关系与Rust 1.90 映射

> 配套章节：`concurrency/backpressure-models.md`、`concurrency/async-recursion.md`、`architecture/design-models.md`

## 分层视角

- **语义层（What）**：程序与执行的语义模型（操作语义、指称语义、公理语义）。
- **并发层（How）**：线程、任务、事件循环、消息传递、同步原语。
- **工程层（With）**：运行时、库与工具（Tokio、`async-channel`、`tower`、`tracing`、`loom`）。

## 模型分类

1) 同步模型（阻塞/直接式）
   - 线程/锁：`Mutex`、`RwLock`、`Condvar`。
   - 消息传递：`std::sync::mpsc`（阻塞消费者）。
   - 等待语义：调用线程被阻塞，调用栈即控制流载体。

2) 异步模型（非阻塞/间接式）
   - Future/`async`/`await`：以状态机形式编译；需要执行器驱动（Tokio）。
   - Waker/调度：基于就绪事件与唤醒。
   - 取消/超时：`tokio::time::timeout`、结构化并发 `JoinSet`/`scope`。

3) 混合模型（同步封装异步、或异步落地同步）
   - 同步外壳 + 异步内核（线程池 + 异步 IO）。
   - 异步外壳 + 同步内核（阻塞适配 `spawn_blocking`）。

## 等价关系与可替换性（形式化要点）

- 计算等价：在无资源约束与相同可观察行为前提下，阻塞调用可被 `await` 状态机替换；反向可由线程池/阻塞执行器包装（存在调度与上下文切换代价）。
- 可观测等价：以行为轨迹（trace）或双向模拟（bisimulation）比较同步/异步实现；将 I/O 时序与有序性建模为 LTL/CTL 性质。
- 性能非等价：延迟/吞吐由调度策略、背压与容量等决定；不保证性能等价。

### 判定准则

- 接口等价：公开 API 与错误语义不变（包括超时/取消语义）。
- 时序等价：在给定时序逻辑性质集合下（如“响应必达且在 T 内”）两实现皆满足。
- 资源界：两实现均满足有界内存与有界并发上限，不出现无界增长。

### 替代策略与模式

- 阻塞 I/O → 异步 I/O：以 `tokio` 等价 API 替换，并在边界处使用 `spawn_blocking`。
- 同步队列 → 有界异步通道：`std::sync::mpsc` → `tokio::mpsc::channel(n)`/`async-channel::bounded(n)`。
- 内联重试 → 中间件：`tower::{Timeout,Retry,RateLimit,ConcurrencyLimit}` 组合。
- 显式取消：为所有外部 I/O 添加超时；传播父级取消（`JoinSet`/`scope`）。

### 典型陷阱

- 在异步路径内执行阻塞计算导致执行器饥饿。
- 无界缓冲隐藏背压，放大尾延迟与内存占用。
- 递归异步未设度量或预算，导致不可终止或爆炸式任务增长。
  - 参考：`async-recursion.md`

## Rust 1.90 语义映射

- `async fn` → 编译为状态机；`Pin`/`Unpin` 保证自引用安全。
- `Send`/`Sync` → 线程安全边界；`!Send` Future 需单线程调度器或`spawn_local`。
- `?Sized`、常量泛型 `_` 推断 → 在模型参数化与类型驱动配置中简化 API。
- 标准库增强：匿名管道、`OnceLock` 稳定等利好初始化与并发安全配置。

## 设计指引

- I/O 密集 → 异步优先；CPU 密集 → 同步 + 线程池或 `spawn_blocking`。
- 组合优先使用消息传递（Actor/CSP）而非共享可变状态；必要时使用细粒度锁。
- 明确取消与超时边界，采用结构化并发控制生命周期。
- 所有 `await` 邻域明确背压与容量约束，避免隐藏的无界排队。

## 与库特性映射（本仓）

- `tokio-adapter`：启用 Tokio 执行器/定时器/通道适配。
- `tower-examples`：演示限流、超时与重试等中间件组合。
- `advanced-algorithms`：在图模型/调度优化示例中对比同步/异步实现代价。
- `examples/async_backpressure_demo.rs`：展示有界通道与 `tower` 中间件组合。

## 检查清单（Checklist）

- 是否存在阻塞调用驻留在异步路径？是则改为 `spawn_blocking` 或异步替身。
- 是否设置了队列容量与背压策略？参见背压章节。
- 是否定义了取消、重试与超时策略？
- 是否度量 P99、队列长度 L、丢弃率 p_drop，并在 SLO 失效时触发限流/降级？

## 形式化等价与映射矩阵

| 维度 | 同步模型 | 异步模型 | 等价/替换策略 | Rust 1.90 映射 |
|------|----------|----------|---------------|----------------|
| 控制流 | 调用栈承载 | 状态机+Waker | 封装为 `await` 点 | `async fn` → 状态机、`Pin`|
| 等待 | 阻塞线程 | 非阻塞挂起 | `spawn_blocking` 作为边界 | `tokio::task::spawn_blocking` |
| 取消 | 线程中断/自定义标志 | 结构化并发向下传播 | 父级超时/取消令牌 | `JoinSet`/`scope`/`timeout` |
| 队列 | `mpsc`/`Condvar` | `tokio::mpsc`/`async-channel` | 有界容量+溢出策略统一 | `try_send`/`reserve` |
| 背压 | 阻塞生产者 | `await` send/credit | 统一以容量和速率治理 | `tower::limit`/`buffer` |

说明：等价指可观测行为在指定接口下保持一致；性能不保证等价。

## 同步↔异步替换清单

- 阻塞网络 I/O → `tokio::net` 等价 API，保留接口不变；边界使用 `spawn_blocking` 封装遗留阻塞。
- 线程池任务 API → `JoinSet`/`scope` 管理生命周期；显式超时与取消。
- 条件变量等待 → 有界通道 + 接收端驱动（拉模式）或信用流控。

## Rust 1.90 API 映射表（补充）

| 主题 | API/类型 | 备注 |
|------|---------|------|
| 并发上限 | `Semaphore` | 控制同时进行任务数 |
| 可取消等待 | `tokio::time::timeout` | 任何外部 I/O 必须设超时 |
| 局部任务 | `spawn_local` | 适配 `!Send` Future |
| 初始化 | `OnceLock` | 线程安全一次初始化 |

## 度量与SLO

- 指标：P50/P99 延迟、队列长度、有效到达率 λ_eff、失败/丢弃率。
- 目标：确保 ρ = λ_eff/μ < 1；在达到阈值时应用降级或 shed load。
