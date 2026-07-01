# C02 类型系统 - 高级主题

> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 持续完善

---

## 概述

本目录聚焦 Rust 类型系统的高级能力：在编译期表达不变式、约束程序状态、以及在类型层面编码协议。掌握这些主题后，可以把 Rust 的类型检查器当作一个轻量级形式化验证工具来使用。

---

## 核心主题

### 1. 高阶 trait bound（HRTB）

HRTB 允许为所有生命周期同时写约束，典型用例是让闭包接受任意生命周期的引用：

```rust
fn with_closure<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s = String::from("hello");
    let _ = f(&s);
}
```
关键点：`for<'a>` 把生命周期参数从调用方“升级”为 universally quantified，使得闭包签名更灵活。

### 2. 泛型关联类型（GAT）

GAT 让关联类型本身可以带泛型参数，从而在 trait 中表达“类型族”：

```rust
trait Container {
    type Item<'a>
    where
        Self: 'a;

    fn get(&self, index: usize) -> Option<Self::Item<'_>>;
}
```
应用场景：自定义 lending iterator、零拷贝解析器、泛型容器抽象。

### 3. 幽灵类型（Phantom Types / PhantomData）

`PhantomData<T>` 用于在类型中携带编译期标记而不存储运行时数据：

- 标记生命周期：让裸指针拥有像引用一样的生命周期语义。
- 标记类型参数：实现类型级状态机或单位系统。
- 满足编译器对未使用泛型参数的要求。

```rust
use std::marker::PhantomData;

struct Meters; // 单位标签
struct Kilometers;

struct Length<U>(f64, PhantomData<U>);
```
### 4. 类型级状态机

通过泛型参数把状态编码进类型，让非法状态转移在编译期被拒绝：

```rust
struct Idle;
struct Running;

struct StateMachine<S> {
    value: i32,
    _state: PhantomData<S>,
}

impl StateMachine<Idle> {
    fn start(self) -> StateMachine<Running> { /* ... */ }
}

// 只有在 Running 状态才能 stop
impl StateMachine<Running> {
    fn stop(self) -> StateMachine<Idle> { /* ... */ }
}
```
### 5. 类型操作与类型转换

- `From` / `TryFrom`：可失败与不可失败转换。
- `AsRef` / `AsMut`：廉价引用转换。
- `Deref` 与 `DerefMut`：自定义解引用，实现智能指针。
- 类型等价判断：通过 `core::any::TypeId` 或泛型单态化后的性质验证。

### 6. 型变（Variance）

型变决定子类型关系如何穿透泛型构造器：

- **协变**：`Box<T>`、`Vec<T>`、`&T` 等。
- **逆变**：函数参数位置、闭包捕获。
- **不变**：内部可变性容器（`Cell<T>`、`RefCell<T>`、`Mutex<T>`）、裸指针。

理解型变对生命周期借用、API 设计和 unsafe 抽象至关重要。

---

## 源码对应

| 主题 | 源码模块 | 示例 |
|------|----------|------|
| HRTB | `src/type_system_frontier.rs` | `examples/generics_where_performance.rs` |
| GAT | `src/type_class/` | `examples/const_eval_assoc_consts.rs` |
| Phantom Types | `src/type_composition/` | `examples/type_equivalence_newtype_examples.rs` |
| 类型级状态机 | `src/type_operation/` | `examples/pattern_matching_advanced.rs` |
| Variance | `src/type_variance/` | `examples/variance_examples.rs` |
| Unsafe 类型抽象 | `src/unsafe/` | `examples/unsafe_cell_interior_mutability.rs` |

---

## 推荐学习顺序

1. 先掌握 **HRTB** 与 **GAT**，它们是现代泛型库的基础。
2. 学习 **Phantom Types** 与 **类型级状态机**，把类型系统当作状态验证工具。
3. 深入 **型变** 与 **unsafe 类型抽象**，理解内存安全背后的理论依据。

---

## 相关链接

- [返回 C02 文档](../README.md)
- [类型系统快速参考](../../../../docs/02_reference/quick_reference/type_system.md)
- [Variance 源码](../../src/type_variance)
- [Rust Reference - Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html)

---

*本文档是 Rust 学习系统的一部分。*

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-06-24 重构，补充 HRTB/GAT/Phantom Types/类型级状态机概览

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-24
**状态**: 🔄 持续完善
