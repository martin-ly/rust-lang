# `must_not_suspend` Lint Preview

> **代码状态**: [综述级 — 含可编译示例]
>
> **EN**: `must_not_suspend` Lint Preview
> **Summary**: Preview of the `must_not_suspend` lint that warns when types like `MutexGuard` or `RefCell` borrows are held across `.await` points in async code; nightly experimental.
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: F×Eva — 评价跨 await 点的借用（Borrowing）安全性
> **前置依赖**: [Async/Await](../../03_advanced/01_async/02_async.md) · [Interior Mutability](../../02_intermediate/02_memory_management/08_interior_mutability.md) · [Concurrency Patterns](../../03_advanced/00_concurrency/10_concurrency_patterns.md)
> **后置延伸**: [Async Drop](18_async_drop_preview.md)
> **来源**: [RFC 3014 — Must Not Suspend Lint](https://rust-lang.github.io/rfcs/3014-must-not-suspend-lint.html) · [Tracking Issue #83310](https://github.com/rust-lang/rust/issues/83310) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 一、功能动机：跨 await 点持有的危险

异步 Rust 的核心机制是 `.await` 点：当 future 遇到 `.await` 时，它可能将控制权交还给 executor，当前任务被挂起。如果某个 async 函数在挂起前持有了以下类型的值，就可能引入运行时（Runtime）故障：

- `std::cell::RefCell` 的 `Ref` / `RefMut`：跨 await 时仍持有借用（Borrowing），其他任务可能 panic；
- `std::sync::MutexGuard` / `RwLockReadGuard`：跨 await 时仍持有锁，可能导致死锁；
- 某些 `unsafe` 或 raw handle：挂起期间可能因资源状态变化而 UB。

`must_not_suspend` lint 的目标就是在编译期警告这类危险持有。它不影响类型系统（Type System），而是作为**静态分析工具**帮助开发者发现 async 代码中的常见反模式。

---

## 二、语法说明：如何启用与使用

### 2.1 启用 lint

```rust,ignore
#![warn(must_not_suspend)]

use std::cell::RefCell;

async fn problematic(data: &RefCell<i32>) {
    let mut borrow = data.borrow_mut();
    tokio::task::yield_now().await;   // lint 警告：borrow_mut 跨越 await
    *borrow += 1;
}
```

### 2.2 自定义类型标记

未来可能允许类型作者通过属性主动声明“我的类型不应跨越 await”：

```rust,ignore
#[must_not_suspend]
struct SensitiveHandle;
```

### 2.3 解决方式

```rust,editable
use std::cell::RefCell;

async fn safe_version(data: &RefCell<i32>) {
    {
        let mut borrow = data.borrow_mut();
        *borrow += 1;
    } // guard 在此作用域结束，释放借用

    // 现在可以安全 await
    // tokio::task::yield_now().await;
}

fn main() {
    let data = RefCell::new(0);
    // 注意：此处没有实际运行时，仅展示编译期结构
    let _ = safe_version(&data);
}
```

---

## 三、与稳定 Rust 的对比及迁移建议

| 问题 | 稳定 Rust 当前行为 | 启用 `must_not_suspend` 后 |
|:---|:---|:---|
| `RefCell` 借用（Borrowing）跨 await | 编译通过，运行时（Runtime）可能 panic | 编译期警告 |
| `MutexGuard` 跨 await | 编译通过，可能死锁 | 编译期警告 |
| 异步锁选择 | 开发者自行判断 | lint 引导使用 `tokio::sync::Mutex` 等 async-aware 锁 |

### 3.1 稳定 Rust 中的最佳实践

即使 lint 尚未稳定，开发者也应遵循以下原则：

1. **在 `.await` 前 drop guard**：使用嵌套作用域或显式 `drop(guard)`；
2. **使用异步锁**：在 async 上下文中优先使用 `tokio::sync::Mutex` / `async-lock`；
3. **避免在 async 函数中使用 `std::sync::Mutex`**：除非能证明锁持有时间极短且不跨越 await；
4. **代码审查**：对跨越 await 的借用保持警觉，尤其是 `RefCell`、`RwLock`、`parking_lot` 等类型。

### 3.2 迁移建议

1. **在 CI 中启用 `-W must_not_suspend`**：nightly 项目可以将其设为 error，提前捕获问题；
2. **不要 suppress 所有警告**：逐个评估警告是否真的是 bug；
3. **结合 `Send` 分析**：`must_not_suspend` 与 `Send` 是正交约束，两者共同保证 async 代码健康。

> **版本说明**：`must_not_suspend` 目前仍是 nightly 实验性 lint，没有进入 stable 的明确时间表。它未来可能成为默认允许（allow-by-default）或默认警告（warn-by-default）的 lint。

---

## 四、边界测试：`must_not_suspend` 与跨 await 点的借用（运行时错误）

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
> 某些类型（`RefCell`、`MutexGuard`、`RwLockReadGuard`）在 async 函数中跨越 `.await` 点可能导致**运行时（Runtime） panic** 或**死锁**。
>
> 原因：
>
> 1) `RefCell::borrow_mut()` 获取的引用（Reference）在 await 点仍然持有；
> 2) 其他任务可能在同一线程尝试 `borrow()`/`borrow_mut()` → panic；
> 3) `MutexGuard` 跨 await 可能导致死锁（若 executor 是单线程）。
>
> 解决：
>
> 1) 在 `.await` 前 drop guard；
> 2) 使用 `tokio::sync::Mutex`（`async` 锁，可跨 await）；
> 3) 重新设计数据结构避免跨 await 借用（Borrowing）。这与 Go 的 defer + 锁（`defer mu.Unlock()`，goroutine 不挂起当前线程）或 Java 的 `synchronized`（阻塞线程，不挂起任务）不同——Rust 的 async/await 是协作式调度，锁跨越 yield 点危险。
> [来源: [must_not_suspend lint](https://doc.rust-lang.org/nightly/rustc/lints/listing/allowed-by-default.html#must-not-suspend)] ·
> [来源: [Async Rust](https://rust-lang.github.io/async-book/index.html)]
>
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

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

## 嵌入式测验（Embedded Quiz）

### 测验 1：`must_not_suspend`  lint 的作用是什么？（理解层）

**题目**: `must_not_suspend`  lint 的作用是什么？

<details>
<summary>✅ 答案与解析</summary>

警告在异步（Async）上下文中持有不应该跨越 await 点的类型（如 `MutexGuard`、`RwLockReadGuard`）。防止因挂起导致的死锁或语义错误。
</details>

> **前置概念**: N/A
---

### 测验 2：为什么 `MutexGuard` 不应该跨越 await 点？（理解层）

**题目**: 为什么 `MutexGuard` 不应该跨越 await 点？

<details>
<summary>✅ 答案与解析</summary>

若 async 任务在持有锁时挂起，其他任务无法获取该锁，可能导致死锁或严重的性能退化。锁的持有时间应尽可能短。
</details>

---

### 测验 3：`must_not_suspend` 与 `Send` trait 有什么关系？（理解层）

**题目**: `must_not_suspend` 与 `Send` trait 有什么关系？

<details>
<summary>✅ 答案与解析</summary>

`Send` 保证类型可以跨线程。`must_not_suspend` 更严格：即使类型是 `Send`，也不应该跨越 await 点。两者是正交的约束。
</details>

---

### 测验 4：这个 lint 对异步代码质量有什么帮助？（理解层）

**题目**: 这个 lint 对异步（Async）代码质量有什么帮助？

<details>
<summary>✅ 答案与解析</summary>

在编译期捕获常见的 async 反模式，减少运行时（Runtime）死锁和性能问题。特别适用于代码审查和大型团队的异步代码规范。
</details>

---

### 测验 5：`must_not_suspend` 目前的状态是什么？（理解层）

**题目**: `must_not_suspend` 目前的状态是什么？

<details>
<summary>✅ 答案与解析</summary>

已在 nightly 中作为实验性 lint 提供。预计在未来版本中稳定化，可能成为默认启用的警告。
</details>

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/futures — 生态权威 API 文档](https://docs.rs/futures) · [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper)
