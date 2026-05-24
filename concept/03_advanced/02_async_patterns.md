# Async 模式与前沿特性

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **层次定位**: L3 高级概念 / 异步子域 — 模式与前沿
> **前置依赖**: [Async/Await 基础](./02_async.md) · [Async 高级主题](./02_async_advanced.md)
> **定理链编号**: T-055 AFIT 类型安全 ⟹ T-056 AsyncFn 可重入性

---

## 十、待补充与演进方向（TODOs）
>
> [来源: [Rust Async Book]]

- [x] **TODO**: 补充 Waker/Context 的底层机制 —— 已完成: 2026-05-14
- [x] **TODO**: 补充 `Stream` / `Sink` trait 完整分析 —— 已完成: 2026-05-14
- [x] **TODO**: 补充 `Pin<Box<dyn Future>>` vs `impl Future` 的性能差异 —— 已完成: 2026-05-14
- [x] **TODO**: 补充 `loom` 并发模型检测工具 —— 已完成: 2026-05-14

### 补充章节：AFIT（Async Fn In Traits）与 RPITIT
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **层次一致性标注**：本节内容属于 L3 向 L4 过渡地带，涉及 trait 系统与存在类型的交互，需在理解 §3.1 状态机变换与 §5.1 定理 A1 后阅读。

#### 问题与解决方案演进

```text
问题（Rust < 1.75）:
  trait 中不能写 async fn
   workaround: 手动返回关联 Future 类型或使用 async-trait crate

解决方案 1: async-trait crate（宏模拟）
  #[async_trait]
  trait MyTrait {
      async fn method(&self);
  }
  // 宏展开: fn method(&self) -> Pin<Box<dyn Future<Output = ()> + Send + '_>>
  // 代价: 每次调用都 Box + 动态分发

解决方案 2: RPITIT（Return Position Impl Trait In Traits）
  trait MyTrait {
      fn method(&self) -> impl Future<Output = ()> + Send;
  }
  // Rust 1.75 前不稳定

最终方案: AFIT（Rust 1.75+ 稳定）
  trait MyTrait {
      async fn method(&self);
  }
  // 编译器自动展开为 RPITIT 形式
```

#### 当前最佳实践

```rust,ignore
// ✅ Rust 1.75+ 原生 AFIT
trait AsyncProcessor {
    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, Error>;
}

// 等价的显式写法:
trait AsyncProcessorExplicit {
    fn process(&self, data: &[u8]) -> impl Future<Output = Result<Vec<u8>, Error>> + Send + '_;
}

// 实现:
struct MyProcessor;

impl AsyncProcessor for MyProcessor {
    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(data.to_vec())
    }
}
```

#### 限制与注意事项

```text
1. AFIT 方法不能直接用 dyn Trait（类型擦除问题）
   解决: 使用 trait_variant crate 或手动 Box::pin

2. 关联类型生命周期推断可能复杂
   解决: 显式标注或简化签名

3. Send 约束需显式声明（默认非 Send）
   trait MyTrait {
       async fn method(&self);  // 默认 Future 非 Send
   }

   // 修正:
   trait MyTrait {
       async fn method(&self) where Self: Sync;  // 或外部约束
   }
```

> **来源**: [RFC 3185] · [Rust Reference: RPITIT] · [TRPL: Ch17]

#### 生命周期陷阱

```rust,ignore
// ❌ 常见错误: 返回内部引用
trait DataProvider {
    async fn get_data(&self) -> &str;  // 隐式生命周期复杂
}

// 实际展开:
// fn get_data(&self) -> impl Future<Output = &str> + '_;
// 问题: Output = &str 的生命周期与 &self 绑定，但不明显

// ✅ 修正: 显式标注或使用 owned 类型
trait DataProvider {
    async fn get_data(&self) -> String;  // 返回所有权
}

// 或
trait DataProvider<'a> {
    async fn get_data(&'a self) -> &'a str;
}
```

---

## 十一、国际课程与论文对齐
>
> [来源: [Rust Async Book]]

| 来源 | 核心内容 | 与本文件对应 |
|:---|:---|:---|
| **[CMU 17-350: Safe Systems Programming]** | async/await、Future、Pin、运行时 | L3 Async 完整覆盖 |
| **[Stanford CS340R: Rusty Systems]** | 并发模型、异步系统编程 | L3 Concurrency → Async |
| **[RFC 2394: async/await]** | 生成器状态机转换语义 | 形式化根基 §3 |
| **[RFC 3185: Return Position Impl Trait in Trait]** | AFIT/RPITIT 设计 | Trait 中的异步 §10 |
| **[PLDI 2024: RefinedRust]** | Pin 不动性的形式化语义 | Pin 定理 §5.1 L2 |

> **过渡: L3 → L4**
>
> `async/await` 的编译期正确性依赖于状态机的自引用安全性，而 `Pin<&mut Self>` 保证的"地址不变性"在类型论中对应于 **location stability** 约束。当前 borrow checker 对自引用的分析存在过度保守的问题，Polonius 的下一代 Datalog 求解器正试图用路径敏感的 loan-based 语义精确刻画这一边界。
>
> 形式化视角见 [`../04_formal/03_ownership_formal.md`](../04_formal/03_ownership_formal.md) §9.2（Polonius）与 [`../04_formal/02_type_theory.md`](../04_formal/02_type_theory.md) §4.1（存在类型与 `impl Trait`）。

---

## 十二、`AsyncFn` Trait 家族：异步闭包的类型化（1.85 stable，RFC 3668）
>
> [来源: [Rust Async Book]]

> **稳定版本**: Rust 1.85 (stable) · **适用 Edition**: 所有 Edition（非 Edition-gated）
> **形式化意义**: 高阶函数的异步扩展——效果系统（Effect System）的原型

### 12.1 问题：异步闭包的类型真空
>
> **[来源: [crates.io](https://crates.io/)]**

在 1.85 之前，异步闭包 `async |x| { ... }` 无法直接作为 trait bound 使用：

```rust,ignore
// 旧模式：verbose 的 workaround
async fn process_batch<F, Fut>(items: Vec<String>, callback: F)
where
    F: Fn(String) -> Fut,
    Fut: Future<Output = Result<(), Error>>,
{ ... }

// 新模式：clean 的 AsyncFn bound
async fn process_batch(
    items: Vec<String>,
    callback: impl AsyncFn(String) -> Result<(), Error>,
) { ... }
```

> **来源**: [RFC 3668] · [Rust Reference: Async closures] · [Rust 1.85 Release Notes]

### 12.2 `AsyncFn` 家族层级
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
AsyncFnOnce<Args>     // 异步调用一次，消耗所有权
    ↑
AsyncFnMut<Args>      // 异步多次调用，可变借用
    ↑
AsyncFn<Args>         // 异步多次调用，不可变借用
```

| 维度 | 同步 `Fn` | 异步 `AsyncFn` |
|:---|:---|:---|
| 调用语法 | `f(args)` | `f(args).await` |
| 返回类型 | `R` | `impl Future<Output = R>` |
| 可重入性 | 调用后立即可再次调用 | Future 完成前不可重入 |
| 捕获模式 | `&self` / `&mut self` / `self` | 同左，但返回 Future |

### 12.3 关键形式化特性：可重入性限制
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

`AsyncFn` 的 `call` 方法返回 `impl Future`，该 Future 可能**借用**闭包捕获的状态。因此：

```rust,ignore
let closure = async |s| { db.save(s).await };

let fut1 = closure("hello");  // Future 借用了 closure 内部状态
// let fut2 = closure("world");  // ❌ 编译错误：closure 已被借用

fut1.await;  // Future 完成后，借用释放
let fut2 = closure("world");  // ✅ 现在可以再次调用
```

**形式化洞察**: `AsyncFn` 将闭包的**同步可重入性**（`Fn` 的 `&self`）与**异步借用生命周期**（Future 的存活期）耦合。这是 Rust 借用检查器在**高阶异步函数**上的自然扩展。

> **来源**: [RFC 3668] · [Rust Reference: Async closures] · [Rust 1.85 Release Notes]

### 12.4 效果系统原型
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

`AsyncFn` 可视为 Rust 向**显式效果追踪**迈出的第一步：

```rust
// 同步：无效果
fn sync_fn(f: impl Fn(i32) -> i32) -> i32 { f(42) }

// 异步：携带 "async 效果"
async fn async_fn(f: impl AsyncFn(i32) -> i32) -> i32 { f(42).await }

// 未来可能的 Effects 语法（讨论中）
// fn effect_fn(f: impl Fn(i32) -> i32) -> i32 async { f(42).await }
```

**形式化洞察**: `AsyncFn` 不是独立的类型系统扩展，而是 `Fn` + `Future` 的组合。但它在**函数签名层面**显式标记了"异步效果"，为未来的 `effect` 关键字提供了设计原型。

> **[来源: RFC 3668]** Async closures trait family.
> **[来源: Rust 1.85 Release Notes]** Async closures stabilized.
> **[来源: rustify.rs 2026]** "`AsyncFn` 是 Rust 异步编程的类型系统拼图的最后一块。"

---

## 十三、`gen` blocks：同步协程的语义定位
>
> [来源: [Rust Async Book]]

> **稳定版本**: Rust 1.95 (stable，需 nightly feature gate) · **预计全面稳定**: 1.98+
> **形式化意义**: 同步协程（Coroutine）的语法糖——`Iterator` 状态机的自动化生成

### 13.1 语法与语义
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// 手动状态机（旧模式）
struct Fibonacci { a: u64, b: u64 }
impl Iterator for Fibonacci {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.a;
        (self.a, self.b) = (self.b, self.a + self.b);
        Some(val)
    }
}

// gen block（新模式）
fn fibonacci() -> impl Iterator<Item = u64> {
    gen move {
        let (mut a, mut b) = (0u64, 1u64);
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}
```

### 13.2 与 `async` 的对偶关系
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 维度 | `async` block | `gen` block |
|:---|:---|:---|
| 状态机类型 | `Future`（协作式多任务） | `Iterator`（协作式生成） |
| 暂停关键字 | `.await`（等待外部 Future） | `yield`（产生值给调用者） |
| 恢复方式 | 运行时 poll | 调用者 `next()` |
| 异步能力 | ✅ 可用 `.await` | ❌ 不可用 `.await` |
| 返回实现 | `impl Future<Output = T>` | `impl Iterator<Item = T>` |

### 13.3 形式化定位
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

`gen` block 是 **Continuation** 的受限形式：

```text
async block  =  λ(). suspend(await) → Future   // 协作式多任务
gen block    =  λ(). suspend(yield) → Iterator // 协作式生成

两者的编译期降阶（desugaring）共享同一套状态机转换框架：
    - 暂停点 → enum 变体
    - 局部变量 → 状态机字段
    - 恢复执行 → match 分支 + 状态跳转
```

**关键限制**: `gen` block 是**同步的**。异步生成器（`Stream`，支持 `.await` + `yield`）仍在 RFC 讨论中。

> **来源**: [RFC 2394 §3: Generator transform] · [rust-lang/rust #117078] · [Rust 1.95 Release Notes]

> **[来源: rust-lang/rust #117078]** Gen blocks tracking issue.
> **[来源: Rust 1.95 Release Notes]** `gen` blocks stabilized with feature gate.

---

## 相关概念链接
>
> [来源: [Rust Async Book]]

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权 | [](../01_foundation/01_ownership.md) | Pin 根基 |
| 生命周期 | [](../01_foundation/03_lifetimes.md) | async fn 捕获规则 |
| Traits | [](../02_intermediate/01_traits.md) | Future trait 定义 |
| 并发 | [](../03_advanced/01_concurrency.md) | 并行与并发对比 |
| Unsafe | [](../03_advanced/03_unsafe.md) | Pin 内部实现 |
| 形式化方法 | [](../07_future/02_formal_methods.md) | 异步协议验证 |
| Rust 版本特性演进 | [](../07_future/05_rust_version_tracking.md) | `AsyncFn`、`gen` blocks 等异步语义扩展 |
| 泛型与类型系统 | [](../02_intermediate/02_generics.md) | `use<..>` precise capturing、GATs |
| Unsafe 权限分离 | [](../03_advanced/03_unsafe.md) | `unsafe_op_in_unsafe_fn` 的权限模型 |

> **过渡: L3 → L2**
>
> `async fn` 的本质是状态机——编译器将 `await` 点转换为 enum 变体。这种转换依赖于泛型（`impl Future<Output = T>`）和 Trait（`Future::poll`）的协同。理解 async 的底层实现，需要回到泛型和 Trait 的基础。
>
> 底层机制见 [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md)（Trait 定义）与 [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md)（泛型单态化）。

> **过渡: L3 → L5**
>
> 异步编程不是 Rust 的发明——JavaScript 的 Promise、C# 的 async/await、Go 的 goroutine 都解决了类似问题。但 Rust 的 `Future` 是零成本的：编译后的状态机没有运行时调度器开销，这与 Go 的 goroutine（M:N 调度）形成鲜明对比。
>
> 对比分析见 [`../05_comparative/02_rust_vs_go.md`](../05_comparative/02_rust_vs_go.md)（并发模型对比）。
---

---

## Wikipedia 概念对齐
>
> [来源: [Rust Async Book]]

> **[来源: Wikipedia]** 核心概念与国际知识库映射。

| 概念 | Wikipedia 词条 | 说明 |
|:---|:---|:---|
| **Async/await** | [Async/await](https://en.wikipedia.org/wiki/Async/await) | 异步/等待 |
| **Future (programming)** | [Future (programming)](https://en.wikipedia.org/wiki/Future_(programming)) | Future 模式 |
| **Coroutine** | [Coroutine](https://en.wikipedia.org/wiki/Coroutine) | 协程 |
| **Cooperative multitasking** | [Cooperative multitasking](https://en.wikipedia.org/wiki/Cooperative_multitasking) | 协作式多任务 |
| **Event loop** | [Event loop](https://en.wikipedia.org/wiki/Event_loop) | 事件循环 |
| **Promise (programming)** | [Promise (programming)](https://en.wikipedia.org/wiki/Promise_(programming)) | Promise |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **[来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]**
>
> **[来源: [Tokio Documentation](https://docs.rs/tokio/latest/tokio/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **相关判定树**: [异步判定树](../00_meta/concept_definition_decision_forest.md#八异步判定树)
> **相关 FTA**: [异步安全失效树](../00_meta/fault_tree_analysis_collection.md#五异步安全失效树)
