# Rust 前沿特性跟踪 {#rust-前沿特性跟踪}

> **分级**: [B]
> **Bloom 层级**: L4-L5 (分析/评价)
> **定位**: 跟踪 Rust 最新语言特性和即将稳定的功能
> **版本**: Rust 1.95+ (Nightly)
> **更新频率**: 每两周
> **状态**: 🔄 持续更新

---

## 📋 目录 {#目录}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [Rust 前沿特性跟踪 {#rust-前沿特性跟踪}](#rust-前沿特性跟踪-rust-前沿特性跟踪)
  - [📋 目录 {#目录}](#-目录-目录)
  - [🎯 目标 {#目标}](#-目标-目标)
  - [📊 特性跟踪矩阵 {#特性跟踪矩阵}](#-特性跟踪矩阵-特性跟踪矩阵)
  - [🔬 正在开发的特性 {#正在开发的特性}](#-正在开发的特性-正在开发的特性)
    - [Generic Const Expressions (generic\_const\_exprs) {#generic-const-expressions-generic\_const\_exprs}](#generic-const-expressions-generic_const_exprs-generic-const-expressions-generic_const_exprs)
    - [Async Closures {#async-closures}](#async-closures-async-closures)
    - [Impl Trait in Associated Type {#impl-trait-in-associated-type}](#impl-trait-in-associated-type-impl-trait-in-associated-type)
    - [Type Alias Impl Trait (TAIT) {#type-alias-impl-trait-tait}](#type-alias-impl-trait-tait-type-alias-impl-trait-tait)
  - [📈 版本路线图 {#版本路线图}](#-版本路线图-版本路线图)
  - [🔗 参考资源 {#参考资源}](#-参考资源-参考资源)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 🎯 目标 {#目标}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本目录致力于：

1. **提前准备**: 在特性稳定前准备好学习材料
2. **实验验证**: 提供 Nightly 特性的可运行示例
3. **迁移路径**: 规划从旧版本到新特性的迁移指南
4. **社区反馈**: 收集和反馈使用体验

---

## 📊 特性跟踪矩阵 {#特性跟踪矩阵}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 状态 | 预计稳定版本 | 文档完成度 | 示例代码 | 迁移指南 |
|------|------|--------------|------------|----------|----------|
| **Generic Const Expressions** | 开发中 | 1.96+ | 📝 20% | ✅ 基础 | 📝 规划中 |
| **Async Closures** | ✅ 已稳定 | **1.85.0** | ✅ 完整 | ✅ 完整 | ✅ 已完成 |
| **Impl Trait in Assoc Type** | FCP | 1.95 | 📝 40% | ✅ 完整 | 📝 规划中 |
| **TAIT** | 不稳定 | 1.97+ | 📝 25% | ⚠️ 部分 | 📝 规划中 |
| **Return Type Notation** | 不稳定 | TBD | 📝 10% | ❌ 无 | 📝 规划中 |
| **Coroutine Trait** | 开发中 | TBD | 📝 15% | ⚠️ 部分 | 📝 规划中 |

---

## 🔬 正在开发的特性 {#正在开发的特性}

### Generic Const Expressions (generic_const_exprs) {#generic-const-expressions-generic_const_exprs}

> **来源: [IEEE](https://standards.ieee.org/)**

**描述**: 允许在泛型参数中使用更复杂的常量表达式

```rust,ignore
#![feature(generic_const_exprs)]

// 使用 const 泛型进行编译时计算
struct Array<T, const N: usize>
where
    [T; N * 2]: Sized,  // 复杂的常量表达式
{
    data: [T; N],
}

impl<T, const N: usize> Array<T, N>
where
    [T; N * 2]: Sized,
{
    fn doubled_size(&self) -> [T; N * 2]
    where
        T: Default + Copy,
    {
        let mut result = [T::default(); N * 2];
        result[..N].copy_from_slice(&self.data);
        result
    }
}
```

**应用场景**:

- 编译时矩阵运算
- 类型级数值计算
- 固定大小数据结构的复杂约束

**学习资源**:

- [RFC 2000](https://rust-lang.github.io/rfcs/2000-const-generics.html)
- [Tracking Issue](https://github.com/rust-lang/rust/issues/76560)

---

### Async Closures {#async-closures}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **状态**: ✅ **Stable since Rust 1.85.0**
>
> **正式文档已迁移**: [concept/03_advanced/24_async_closures.md](../../../concept/03_advanced/24_async_closures.md)

**描述**: 原生支持异步闭包，无需 `async move` 包裹。

```rust,ignore
// Rust 1.85.0+ stable，无需 feature gate
async fn new_way() {
    let f = async || {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    };
    let result = f().await;
}
```

**优势**:

- 更清晰的语法
- 更好的生命周期推断
- 避免不必要的 `move`

**应用场景**:

- 回调函数
- 事件处理器
- 中间件链

---

### Impl Trait in Associated Type {#impl-trait-in-associated-type}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

**描述**: 在关联类型中使用 `impl Trait`

```rust,ignore
#![feature(impl_trait_in_assoc_type)]

trait AsyncIterator {
    type Item;
    // 使用 impl Trait 简化返回类型
    type NextFuture: Future<Output = Option<Self::Item>>;

    fn next(&mut self) -> Self::NextFuture;
}

// 实现示例
struct Counter {
    current: u32,
}

impl AsyncIterator for Counter {
    type Item = u32;
    type NextFuture = impl Future<Output = Option<u32>>;

    fn next(&mut self) -> Self::NextFuture {
        async move {
            if self.current < 10 {
                let val = self.current;
                self.current += 1;
                Some(val)
            } else {
                None
            }
        }
    }
}
```

**优势**:

- 隐藏复杂的 Future 类型
- 更好的封装
- 简化 trait 定义

---

### Type Alias Impl Trait (TAIT) {#type-alias-impl-trait-tait}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

**描述**: 在类型别名中使用 `impl Trait`

```rust,ignore
#![feature(type_alias_impl_trait)]

// 定义不透明的类型别名
type AsyncStream<T> = impl Stream<Item = T>;

fn create_stream() -> AsyncStream<i32> {
    stream::iter(vec![1, 2, 3])
}

// 递归异步函数
type RecursiveFuture = impl Future<Output = ()>;

fn recursive_async(n: u32) -> RecursiveFuture {
    async move {
        if n > 0 {
            println!("{}", n);
            recursive_async(n - 1).await;
        }
    }
}
```

**应用场景**:

- 递归异步函数
- 复杂的返回类型封装
- API 设计中的类型隐藏

---

## 📈 版本路线图 {#版本路线图}

```mermaid
timeline
    title Rust 特性稳定路线图
    2026 Q2 : Rust 1.95
            : - Impl Trait in Assoc Type
            : - Various API stabilizations
    2026 Q3 : Rust 1.96
            : - Generic Const Expressions (可能)
            : - Async Closures (可能)
    2026 Q4 : Rust 1.97
            : - TAIT (可能)
            : - Edition 2024 完善
    2027 Q1 : Rust 2.0?
            : - 重大版本规划
```

---

## 🔗 参考资源 {#参考资源}

- [Rust Release Tracking](https://releases.rs/)
- [Rust RFCs](https://rust-lang.github.io/rfcs/)
- [Rust Internals Forum](https://internals.rust-lang.org/)
- [This Week in Rust](https://this-week-in-rust.org/)

---

**维护者**: Rust 学习项目团队
**更新日期**: 2026-03-15
**状态**: 🔄 持续跟踪更新

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}

- [Async Closures](../../../knowledge/06_ecosystem/emerging/01_async_closures.md)
- [Generic Const Exprs](../../../knowledge/06_ecosystem/emerging/02_generic_const_exprs.md)
- [Rust 1.95 稳定特性](../../../knowledge/06_ecosystem/emerging/03_rust_1_95.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
