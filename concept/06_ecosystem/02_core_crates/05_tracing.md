> **EN**: Structured Application Tracing with `tracing`
> **Summary**: `tracing` is a Rust framework for emitting structured, context-aware diagnostics through spans and events, designed to compose across async/await boundaries and integrate with OpenTelemetry and the broader observability stack.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **生态版本**: tracing 0.1.41+ · tracing-subscriber 0.3.19+
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Procedure
> **前置概念**:
> [Traits](../../02_intermediate/00_traits/01_traits.md) ·
> [Async / Await](../../03_advanced/01_async/01_async.md) ·
> [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) ·
> [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md)
> **后置概念**:
> [Application Domains](../06_data_and_distributed/01_application_domains.md) ·
> [Tokio Runtime Internals](../04_web_and_networking/10_tokio_runtime_internals.md)
> **主要来源**:
> [docs.rs/tracing](https://docs.rs/tracing/latest/tracing/) ·
> [tokio-rs/tracing on GitHub](https://github.com/tokio-rs/tracing) ·
> [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust) ·
> [Tokio Blog](https://tokio.rs/blog/)

---

# `tracing`：结构化追踪与可观测性

---

## 一、权威定义

> **[tracing](https://docs.rs/tracing/latest/tracing/)** A framework for instrumenting Rust programs with structured, event-based diagnostic information.

- **crate 定位**：`tracing` 是 Rust 生态中**结构化日志 / 分布式追踪**的事实标准基础设施。它与旧式 `log` 门面的核心差异在于：
  - `log` 输出的是**扁平事件流**；
  - `tracing` 输出的是**带有上下文层级（span）的结构化事件**，天然支持跨 `async` 任务、跨线程、跨服务的请求链路传播。
- **Wikipedia / 行业定义**：**Distributed tracing** is a method of observing requests as they propagate through distributed systems; it records the path of a request and the time spent in each service. `tracing` 在单进程内提供了同样的语义原语（span + event），并通过 OpenTelemetry exporter 扩展到多语言链路追踪。

---

## 二、关键类型与 Traits

| **类型 / Trait** | **角色** | **典型用法** |
|:---|:---|:---|
| `Span` | 一段执行上下文，可包含开始 / 结束时间与结构化字段 | `let span = info_span!("request", request_id = %id);` |
| `Event` | 单点诊断记录（类似日志行），发生在某个 span 内 | `info!(target = "app", "request processed");` |
| `Subscriber` | 收集与消费 span/event 的 trait；一个进程通常只有一个全局 subscriber | `tracing_subscriber::fmt::init()` 安装默认 subscriber |
| `Layer` | 可组合的 subscriber 中间件；多个 layer 可叠加 | `fmt::layer()` + `EnvFilter::from_default_env()` |
| `#[instrument]` | 过程宏，自动为函数创建 span 并捕获参数 | `#[instrument(skip(password))]` |
| `Instrument` trait | 将 future 绑定到指定 span，保证 await 期间上下文不丢失 | `future.instrument(span)` |
| `Level` | 事件级别：`TRACE` / `DEBUG` / `INFO` / `WARN` / `ERROR` | `tracing::info!("...")` |
| `Dispatch` | subscriber 的线程本地句柄；用于跨线程传递 subscriber | `dispatcher::with_default(&dispatch, f)` |
| `field` 语法 | 在 span/event 上附加结构化键值 | `info!(%user, ?request, "done")` |

> **关键洞察**：`Span` 与 `Event` 的组合让 `tracing` 不再只是“更好的 `println!`”，而是把**调用栈、异步任务、请求 ID** 等上下文编码进诊断数据；下游 subscriber 可以按 JSON、OpenTelemetry、Prometheus 等多种格式消费。

---

## 三、惯用法与示例

### 3.1 最小可用示例

```rust,ignore
// Cargo.toml
// [dependencies]
// tracing = "0.1"
// tracing-subscriber = { version = "0.3", features = ["env-filter"] }

use tracing::{info, warn};

fn main() {
    // 安装默认的 fmt subscriber（读取 RUST_LOG 环境变量）
    tracing_subscriber::fmt::init();

    info!("service starting");
    do_work(42);
    warn!("deprecated endpoint called");
}

#[tracing::instrument]
fn do_work(id: u64) {
    info!(id, "working on item");
}
```

> **运行**：`RUST_LOG=info cargo run` 会输出带时间戳、级别、目标模块的事件行。

### 3.2 异步场景：保持 span 上下文

```rust,ignore
// Cargo.toml
// tracing = "0.1"
// tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt"] }
// tokio = { version = "1", features = ["full"] }

use tracing::{info, info_span, Instrument};

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let root = info_span!("process_order", order_id = %"ORD-1234");

    process_order()
        .instrument(root)
        .await;
}

async fn process_order() {
    info!("validating order");
    validate().await;
    info!("order shipped");
}

async fn validate() {
    // 即使跨 await 点，当前 span 上下文仍然保留
    info!("validation passed");
}
```

> **关键设计**：`.instrument(span)` 把 future 绑定到 span；每次 poll 都会自动 `enter`/`exit` span，因此 `async fn` 内部的事件仍然关联到同一个 `order_id`。

### 3.3 结构化输出与字段捕获

```rust,ignore
use tracing::{info, info_span};

fn main() {
    tracing_subscriber::fmt()
        .with_target(false)
        .json()
        .init();

    let span = info_span!("http_request", method = %"GET", route = %"/users/42");
    let _guard = span.enter();

    // % 表示 Display，? 表示 Debug
    info!(status = 200, latency_ms = 12.5, "request completed");
}
```

> **输出（JSON）**：`{"timestamp":"...","level":"INFO","fields":{"status":200,"latency_ms":12.5},"target":"...","span":{"http_request":{"method":"GET","route":"/users/42"}}}`

---

## 四、常见陷阱与边界测试

### 陷阱 1：在 subscriber 初始化之前使用 tracing 宏

事件会被**静默丢弃**，不会报错也不会输出。

```rust,ignore
// ❌ 错误：先记录事件，再初始化 subscriber
fn main() {
    tracing::info!("this will be LOST");
    tracing_subscriber::fmt::init();
    tracing::info!("this will be printed");
}
```

```rust,ignore
// ✅ 正确：先安装 subscriber，再记录事件
fn main() {
    tracing_subscriber::fmt::init();
    tracing::info!("this will be printed");
}
```

> **修正**：`tracing` 使用线程本地分发器；没有 subscriber 时事件被丢弃。应在 `main` 开头尽早初始化 subscriber，并在库代码中**只使用 `tracing` 宏，不初始化 subscriber**（初始化是应用层职责）。

### 陷阱 2：`#[instrument]` 默认捕获所有函数参数

大对象或敏感字段（密码、token）会被默认输出。

```rust,ignore
// ❌ 错误：password 会被写入日志
#[tracing::instrument]
async fn login(user: String, password: String) {
    tracing::info!("login attempt");
}
```

```rust,ignore
// ✅ 正确：显式跳过敏感字段
#[tracing::instrument(skip(password))]
async fn login(user: String, password: String) {
    tracing::info!("login attempt");
}
```

> **修正**：使用 `skip(...)` 排除敏感或大体积参数；使用 `fields(...)` 显式添加脱敏后的上下文。

### 陷阱 3：在 `spawn` 的任务中丢失父 span

`tokio::spawn` 会丢失当前 span，需要显式传递。

```rust,ignore
// ❌ 错误： spawned task 的事件没有 request_id 上下文
#[tracing::instrument]
async fn handle_request() {
    tokio::spawn(async move {
        tracing::info!("background job"); // 无 request_id
    });
}
```

```rust,ignore
// ✅ 正确：使用 tokio::spawn 的 tracing 集成或手动 instrument
use tracing::Instrument;

#[tracing::instrument]
async fn handle_request() {
    let current_span = tracing::Span::current();
    tokio::spawn(
        async move {
            tracing::info!("background job"); // 保留 request_id
        }
        .instrument(current_span),
    );
}
```

> **修正**：`tokio::spawn` 的 future 会在新任务上下文执行；通过 `.instrument(Span::current())` 把父 span 传入，或使用 `tracing-futures` 提供的集成。

---

## 五、版本说明

| **项目** | **说明** |
|:---|:---|
| **当前稳定主版本** | `tracing` 0.1.x（活跃维护），`tracing-subscriber` 0.3.x |
| **MSRV 政策** | 通常支持最近 6–12 个月的 stable Rust；具体以 `Cargo.toml` `rust-version` 为准 |
| **Rust 1.97 / Edition 2024** | `tracing` 宏与 `#[instrument]` 在 Edition 2024 下兼容；新增的 `async fn` in trait 与 return-position impl trait 不影响核心 API |
| **最近值得注意的特性** | `valuable` 支持（结构化值）、`log` crate 兼容层、`opentelemetry` 集成通过 `tracing-opentelemetry` |
| **典型依赖组合** | `tracing` + `tracing-subscriber` + `tracing-opentelemetry`（分布式链路）/ `sentry-tracing`（错误聚合） |

> **选型建议**：新项目直接用 `tracing` 替代 `log`；需要与旧 `log` 生态互操作时启用 `tracing` 的 `log` feature，或让 `tracing-subscriber` 同时接收 `log` 事件。

---

## 六、思维导图（Mindmap）

```mermaid
mindmap
  root((tracing))
    核心抽象
      Span 执行上下文
      Event 单点记录
      Level 级别控制
    Subscriber 层
      Subscriber trait
      Layer 可组合中间件
      Dispatch 线程本地分发
    惯用法
      tracing::info!
      span! 与 enter
      #[instrument]
      .instrument()
    异步传播
      await 保持 span
      tokio::spawn 传递 span
      OpenTelemetry 集成
    常见陷阱
      未初始化 subscriber 静默丢事件
      #[instrument] 默认捕获敏感字段
      spawn 任务丢失父上下文
    下游消费
      fmt 文本/JSON
      tracing-opentelemetry
      sentry-tracing / metrics
```

> **认知功能**：本 mindmap 以 `tracing` 的设计轴心展开——“在正确的地方捕获结构化上下文，并通过可组合的 subscriber 输出到不同观测后端”。

---

## 七、嵌入式测验

### 测验 1：`tracing` 与 `log` 的主要区别（理解层）

`tracing` 相比 `log` 最核心的改进是什么？

- A. `tracing` 的宏语法更简洁
- B. `tracing` 原生支持 span 上下文和结构化字段
- C. `tracing` 只能在 async 程序中使用
- D. `tracing` 不需要初始化 subscriber

<details>
<summary>✅ 答案</summary>

**B. `tracing` 原生支持 span 上下文和结构化字段**。

`log` 输出扁平日志行；`tracing` 以 `Span` 为载体记录执行上下文，事件可携带结构化键值，并能跨 `await` 点保持上下文。
</details>

---

### 测验 2：`#[instrument]` 的正确用法（应用层）

以下哪个用法能避免把密码写入 span 字段？

- A. `#[instrument]`
- B. `#[instrument(skip(password))]`
- C. `#[instrument(fields(password))]`
- D. `#[instrument(hide(password))]`

<details>
<summary>✅ 答案</summary>

**B. `#[instrument(skip(password))]`**。

`skip(...)` 显式排除指定参数；其余参数仍会被捕获为 span 字段。没有 `hide` 属性。
</details>

---

### 测验 3：异步任务 span 传播（应用层）

在 `tokio::spawn` 的任务中保留父 span 上下文，推荐做法是？

- A. 自动继承，无需额外代码
- B. 使用 `tracing::Span::current()` 并 `.instrument(...)`
- C. 在任务内部重新 `info_span!`
- D. 把 subscriber 克隆后传给新任务

<details>
<summary>✅ 答案</summary>

**B. 使用 `tracing::Span::current()` 并 `.instrument(...)`**。

`tokio::spawn` 默认不继承当前 span；通过 `future.instrument(tracing::Span::current())` 把父 span 显式绑定到新 future 上。
</details>

---

### 测验 4：初始化顺序（理解层）

在 `main` 中先调用 `tracing::info!` 再调用 `tracing_subscriber::fmt::init()`，会发生什么？

- A. 程序 panic
- B. 事件被缓存，初始化后自动输出
- C. 事件被静默丢弃
- D. 编译错误

<details>
<summary>✅ 答案</summary>

**C. 事件被静默丢弃**。

没有 subscriber 时，`tracing` 事件不会报错也不会缓存，直接丢弃。应用层应在记录任何事件之前完成 subscriber 初始化。
</details>

---

### 测验 5：字段语法（记忆/理解层）

在 `tracing` 宏中，`info!(%user, ?request, "done")` 里的 `%` 和 `?` 分别表示？

- A. `%` = Debug，`?` = Display
- B. `%` = Display，`?` = Debug
- C. `%` = 十六进制，`?` = 二进制
- D. `%` = 引用，`?` = 克隆

<details>
<summary>✅ 答案</summary>

**B. `%` = Display，`?` = Debug**。

`%value` 使用 `std::fmt::Display` 格式化，`?value` 使用 `std::fmt::Debug` 格式化。
</details>

---

## 八、国际权威来源

- **P0 — Rust 官方文档**
  - [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)（理解 Rust 所有权、trait、async 等前置概念） — 链接状态：公开可访问，未在本机实时验证。
- **P2 — crate 官方文档与仓库**
  - [docs.rs/tracing](https://docs.rs/tracing/latest/tracing/) — `tracing` API 权威文档 — 链接状态：公开可访问，未在本机实时验证。
  - [tokio-rs/tracing on GitHub](https://github.com/tokio-rs/tracing) — 源码、发布说明、示例 — 链接状态：公开可访问，未在本机实时验证。
  - [tracing-subscriber docs.rs](https://docs.rs/tracing-subscriber/latest/tracing_subscriber/) — subscriber 与 layer 机制 — 链接状态：公开可访问，未在本机实时验证。
  - [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust) — 分布式追踪集成参考 — 链接状态：公开可访问，未在本机实时验证。
- **P2 — 行业参考**
  - [Wikipedia: Distributed tracing](https://en.wikipedia.org/wiki/Distributed_tracing) — 分布式追踪概念 — 链接状态：公开可访问，未在本机实时验证。
  - [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/) — 可观测性数据模型 — 链接状态：公开可访问，未在本机实时验证。

> **链接验证声明**：以上链接均来自公开可访问域名；本文件编写时未执行实时 HTTP 可达性检查，建议在 CI 死链检查门中复核。

---

## 九、相关概念链接

- [Async / Await](../../03_advanced/01_async/01_async.md)
- [Concurrency Safety](../../03_advanced/00_concurrency/01_concurrency.md)
- [Traits and Trait Objects](../../02_intermediate/00_traits/01_traits.md)
- [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md)
- [Tokio Runtime Internals](../04_web_and_networking/10_tokio_runtime_internals.md)
- [Application Domains](../06_data_and_distributed/01_application_domains.md)
- [Core Crates 索引](01_core_crates.md)
- [Rust vs Java](../../05_comparative/02_managed_languages/01_rust_vs_java.md) — 可观测性与企业生态的跨语言对比

---

> **文档版本**: 1.0
> **最后更新**: 2026-07-31
> **状态**: Wave D — L6 ecosystem part 1 新建权威页
