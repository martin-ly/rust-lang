# `must_not_suspend` Lint Preview
>
> **EN**: `must_not_suspend` Lint Preview (Chinese)
> **Summary**: `must_not_suspend` Lint Preview (Chinese). Emerging Rust feature or ecosystem trend: `must_not_suspend` Lint Preview (Chinese).
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: F×Eva — 评价跨 await 点的借用安全性
> **前置依赖**: [Async/Await](../03_advanced/02_async.md) · [Interior Mutability](../02_intermediate/08_interior_mutability.md)
> **后置延伸**: [Async Drop](./18_async_drop_preview.md)
> **来源**: [RFC 3014](https://rust-lang.github.io/rfcs/3014-must-not-suspend-lint.html) · [Tracking Issue](https://github.com/rust-lang/rust/issues/83310)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 10.4 边界测试：`must_not_suspend` 与跨 await 点的借用（运行时错误）

```rust,compile_fail
use std::cell::RefCell;

async fn bad_async() {
    let data = RefCell::new(42);
    let borrow = data.borrow_mut();
    // ❌ 运行时 panic: 若 .await 后其他任务尝试借用 data
    // async 函数可能在 await 点挂起，RefCell 的 borrow 跨越 await
    tokio::task::yield_now().await;
    println!("{}", borrow);
}

fn main() {}
```

> **修正**:
>
> **`must_not_suspend`** lint（nightly，`-W must_not_suspend`）警告：
> 某些类型（`RefCell`、`MutexGuard`、`RwLockReadGuard`）在 async 函数中跨越 `.await` 点可能导致**运行时 panic** 或**死锁**。
>
> 原因：
>
> 1) `RefCell::borrow_mut()` 获取的引用在 await 点仍然持有；
> 2) 其他任务可能在同一线程尝试 `borrow()`/`borrow_mut()` → panic；
> 3) `MutexGuard` 跨 await 可能导致死锁（若 executor 是单线程）。
>
> 解决：
>
> 1) 在 `.await` 前 drop guard；
> 2) 使用 `tokio::sync::Mutex`（`async` 锁，可跨 await）；
> 3) 重新设计数据结构避免跨 await 借用。这与 Go 的 defer + 锁（`defer mu.Unlock()`，goroutine 不挂起当前线程）或 Java 的 `synchronized`（阻塞线程，不挂起任务）不同——Rust 的 async/await 是协作式调度，锁跨越 yield 点危险。
> [来源: [must_not_suspend lint](https://doc.rust-lang.org/nightly/rustc/lints/listing/allowed-by-default.html#must-not-suspend)] ·
> [来源: [Async Rust](https://rust-lang.github.io/async-book/)]
>
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **`must_not_suspend` Lint Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| `must_not_suspend` Lint Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| `must_not_suspend` Lint Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| `must_not_suspend` Lint Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 `must_not_suspend` Lint Preview 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 `must_not_suspend` Lint Preview 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: `must_not_suspend` Lint Preview 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "`must_not_suspend` Lint Preview 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
