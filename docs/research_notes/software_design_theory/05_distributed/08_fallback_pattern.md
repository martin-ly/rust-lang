# Fallback / Degrade 韧性模式 {#fallback-degrade-韧性模式}

> **概念族**: 软件设计 / 分布式模式 / Fallback
>
> **层级**: L4-L6
> **Bloom 层级**: L4 分析 / L5 评价 / L6 创造
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
>
> **目标**: 为分布式系统中的 Fallback（回退）与 Degrade（降级）策略提供形式化定义、Rust 实现方案、反例边界与权威来源对齐。
>
> **权威来源**: [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Tonic Docs](https://docs.rs/tonic/latest/tonic/) | [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/)

---

## 目录 {#目录}

- [Fallback / Degrade 韧性模式](#fallback-degrade-韧性模式)
  - [目录](#目录)
  - [一、问题定义](#一问题定义)
  - [二、核心定义](#二核心定义)
    - [Def Fallback（回退）](#def-fallback回退)
    - [Def Degrade（降级）](#def-degrade降级)
    - [Fallback vs Degrade 对比](#fallback-vs-degrade-对比)
    - [Axiom](#axiom)
    - [Theorem](#theorem)
  - [三、Rust 实现方案](#三rust-实现方案)
    - [3.1 枚举策略](#31-枚举策略)
    - [3.2 async 策略组合](#32-async-策略组合)
    - [3.3 代码示例](#33-代码示例)
  - [四、反例边界](#四反例边界)
    - [反例 1：Fallback 级联失败](#反例-1fallback-级联失败)
    - [反例 2：降级后不再恢复](#反例-2降级后不再恢复)
  - [五、权威来源](#五权威来源)
  - [六、相关概念](#六相关概念)

---

## 一、问题定义 {#一问题定义}

在分布式系统中，服务依赖可能因网络抖动、超时、过载或局部故障而失败。若直接将失败透传给上游，可能引发级联雪崩。Fallback / Degrade 模式通过**在失败时提供替代路径或受限但可用的响应**，提升系统在部分失效下的可用性（availability）与韧性（resilience）。

Rust 的强类型系统、枚举与 `async/await` 语义，使得我们可以把 fallback 策略显式建模为类型，并通过编译期约束避免隐式降级。

---

## 二、核心定义 {#二核心定义}

### Def Fallback（回退） {#def-fallback回退}

```text
Fallback(S, F, R) :=
  给定主服务 S: A → Result<B, E>
  给定回退函数 F: A → B
  对任意请求 a ∈ A
  若 S(a) 返回 Err(_) 或超时
  则返回 F(a) 作为近似结果 R
```

回退强调**失败时的替代结果**：可能是默认值、缓存值、本地计算值或从备用服务获取的值。结果语义上可能不是最强一致，但仍可接受。

### Def Degrade（降级） {#def-degrade降级}

```text
Degrade(S, S', R) :=
  给定完整服务 S: A → B
  给定降级服务 S': A → B'
  其中 B' ⊂ B（B' 是 B 的语义子集，例如更少字段、更低精度、更旧数据）
  当系统处于高负载、依赖不可用或触发特定条件时
  主动将请求路由到 S'，以牺牲部分功能换取可用性
```

降级强调**主动减少服务范围**：从完整功能切换到受限功能，并在条件解除后恢复。

### Fallback vs Degrade 对比 {#fallback-vs-degrade-对比}

| 维度 | Fallback | Degrade |
|------|----------|---------|
| 触发时机 | 主路径失败/超时后被动触发 | 主动根据负载/健康状态切换 |
| 结果语义 | 保持返回类型，内容降级或近似 | 返回类型/字段可能直接减少 |
| 恢复策略 | 通常每次调用独立判断 | 需要明确的恢复阈值与状态机 |
| 与 Circuit Breaker 关系 | 常与熔断器配合：Open 状态直接走 fallback | 常与负载/健康指标配合 |
| Rust 建模 | `Result<T, E>` + `or_else` / `unwrap_or_else` | 枚举状态机 + 策略分发 |

> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

### Axiom {#axiom}

- **A-FB-1（有界语义损失）**: 回退或降级结果与主路径结果的差异必须在业务可接受范围内；否则该 fallback 无效。
- **A-FB-2（可观测性）**: 任何 fallback / degrade 路径必须被记录、监控或指标化，避免静默失败。
- **A-FB-3（失败隔离）**: Fallback 本身不能依赖于导致主路径失败的同一依赖，否则不能称之为独立回退。

### Theorem {#theorem}

- **T-FB-1（独立性保证）**: 若 fallback 函数 `F` 对 `S` 无依赖，则 `S` 的不可用不会导致 `F` 不可用。
- **T-FB-2（降级闭包）**: 若降级服务 `S'` 的调用图是完整服务 `S` 调用图的子图，则降级路径不会引入新的外部依赖失败点。

**Proof (T-FB-1 自然语言证明 L2)**: 假设 `F` 的输入仅来自请求 `a`，且 `F` 不调用 `S` 的任何方法。根据 A-FB-3，`F` 的失败原因集合与 `S` 的失败原因集合不相交。因此 `S` 的失败不会传播到 `F`，`F` 仍可按定义返回结果。∎

---

## 三、Rust 实现方案 {#三rust-实现方案}

### 3.1 枚举策略 {#31-枚举策略}

使用 Rust 枚举将主路径、fallback、降级状态显式化：

```rust
#[derive(Debug, Clone)]
pub enum ServiceOutcome<T> {
    Primary(T),
    Fallback(T, FallbackReason),
    Degraded(T),
}

#[derive(Debug, Clone)]
pub enum FallbackReason {
    Timeout,
    Failure(String),
    CircuitOpen,
}
```

> **来源**: [The Rust Programming Language – Enums and Pattern Matching](https://doc.rust-lang.org/book/ch06-00-enums.html)

### 3.2 async 策略组合 {#32-async-策略组合}

利用 `tokio::time::timeout` 与 `async/await` 组合实现超时触发 fallback：

```rust
use std::time::Duration;
use tokio::time::timeout;

async fn with_fallback<F, Fut, T, E>(
    primary: F,
    fallback: impl FnOnce() -> T,
    limit: Duration,
) -> ServiceOutcome<T>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    match timeout(limit, primary()).await {
        Ok(Ok(value)) => ServiceOutcome::Primary(value),
        Ok(Err(e)) => ServiceOutcome::Fallback(fallback(), FallbackReason::Failure(e.to_string())),
        Err(_) => ServiceOutcome::Fallback(fallback(), FallbackReason::Timeout),
    }
}
```

> **来源**: [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

### 3.3 代码示例 {#33-代码示例}

完整示例见 [`crates/c06_async/examples/fallback_degrade_pattern.rs`](../../../../../crates/c06_async/examples/fallback_degrade_pattern.rs)。

示例包含：

1. 主服务 / 备用服务异步调用；
2. 超时后自动 fallback；
3. 主动降级开关（degradation flag）；
4. 结果枚举 `ServiceOutcome` 与监控指标；
5. 恢复逻辑演示。

```rust
// 伪代码片段：主路径失败 -> fallback -> 降级状态机
let outcome = service.call_with_resilience(request).await;
match outcome {
    ServiceOutcome::Primary(v) => info!("主路径成功: {}", v),
    ServiceOutcome::Fallback(v, reason) => warn!("回退触发: {:?} -> {}", reason, v),
    ServiceOutcome::Degraded(v) => warn!("降级模式: {}", v),
}
```

---

## 四、反例边界 {#四反例边界}

### 反例 1：Fallback 级联失败 {#反例-1fallback-级联失败}

**场景**: 主服务 `S` 失败，fallback `F` 仍尝试调用 `S` 的缓存接口，而该缓存接口也依赖 `S` 所在集群。

**违反**: A-FB-3（失败隔离）。

**后果**: 表面上有 fallback，实际仍然失败，且可能放大故障流量。

**修复**: Fallback 必须依赖独立数据源或本地计算，避免共享失败域。

### 反例 2：降级后不再恢复 {#反例-2降级后不再恢复}

**场景**: 系统触发降级后没有恢复检测逻辑，长期运行在降级模式。

**违反**: A-FB-2（可观测性）与 Degrade 定义中的恢复要求。

**后果**: 用户长期看到旧数据或残缺功能，体验持续受损。

**修复**: 引入半开/恢复探测状态机，定期尝试主路径并自动恢复。

---

## 五、权威来源 {#五权威来源}

| 优先级 | 来源 | 说明 |
|--------|------|------|
| P0 | [The Rust Programming Language](https://doc.rust-lang.org/book/) | `Result<T, E>`、枚举、模式匹配、错误处理 |
| P0 | [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | `async/await`、`Future`、Pin、异步状态机 |
| P0 | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | 超时、任务调度、异步运行时 |
| P1 | [Rust Reference](https://doc.rust-lang.org/reference/) | 类型系统、生命周期、Send/Sync 语义 |
| P1 | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 模式分类、惯用法与最佳实践 |
| P2 | [Tonic Docs](https://docs.rs/tonic/latest/tonic/) | gRPC / 服务中间件中的 fallback / interceptor 实践 |
| P2 | [AWS Well-Architected Reliability Pillar](https://docs.aws.amazon.com/wellarchitected/latest/reliability-pillar/welcome.html) | 分布式韧性设计原则（回退、降级、限流） |

---

## 六、相关概念 {#六相关概念}

- [03_circuit_breaker.md](03_circuit_breaker.md) — 熔断器常与 fallback 组合使用。
- [06_timeout_pattern.md](06_timeout_pattern.md) — 超时是触发 fallback 的典型条件。
- [07_retry_pattern.md](07_retry_pattern.md) — 重试与 fallback 是相邻层次：重试失败后再 fallback。
- [../02_workflow/02_compensation_chain.md](../02_workflow/02_compensation_chain.md) — Saga 补偿链是跨事务的语义回退。
- [../04_compositional_engineering/README.md](../04_compositional_engineering/README.md) — 服务组合与降级策略。

---

*本文档是 Rust 形式化工程系统的一部分*

**维护者**: Rust 学习项目团队
**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
