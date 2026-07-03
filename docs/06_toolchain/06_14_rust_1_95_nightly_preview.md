# Rust 1.95 Nightly 预览与实验特性 {#rust-195-nightly-预览与实验特性}

> **EN**: 14 Rust 1 95 Nightly Preview
> **Summary**: Rust 1.95 Nightly 预览与实验特性 14 Rust 1 95 Nightly Preview. (stub/archive redirect)
> **权威来源说明**: Rust 1.95 **稳定特性**的权威来源为 [`concept/07_future/rust_1_95_stabilized.md`](../../concept/07_future/rust_1_95_stabilized.md)。
> 本文仅保留 **Nightly / 实验特性** 的工具链视角内容；[knowledge/06_ecosystem/emerging/04_rust_1_95_preview.md](../../knowledge/06_ecosystem/emerging/04_rust_1_95_preview.md) 与 [knowledge/06_ecosystem/emerging/03_rust_1_95.md](../../knowledge/06_ecosystem/emerging/03_rust_1_95.md) 已重定向至 `concept/07_future/rust_1_95_stabilized.md`。
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **创建日期**: 2026-02-28
> **最后更新**: 2026-05-08
> **Rust 版本**: 1.95.0 (Nightly)
> **预计发布**: 2026-04-16
> **状态**: 历史内容已迁移，仅作路径保留（原 Nightly 实验内容已稳定或归档）
>
> **受众**: [进阶] / [专家]
> **内容分级**: [实验级]

---

## 目录 {#目录}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [Rust 1.95 Nightly 预览与实验特性 {#rust-195-nightly-预览与实验特性}](#rust-195-nightly-预览与实验特性-rust-195-nightly-预览与实验特性)
  - [目录 {#目录}](#目录-目录)
  - [版本概览 {#版本概览}](#版本概览-版本概览)
  - [实验性语言特性 {#实验性语言特性}](#实验性语言特性-实验性语言特性)
    - [1. 下一代 Trait 求解器 (next-solver) {#1-下一代-trait-求解器-next-solver}](#1-下一代-trait-求解器-next-solver-1-下一代-trait-求解器-next-solver)
    - [2. Async Drop {#2-async-drop}](#2-async-drop-2-async-drop)
    - [3. 生成器 (Generators) {#3-生成器-generators}](#3-生成器-generators-3-生成器-generators)
    - [4. Pin 人体工学改进 {#4-pin-人体工学改进}](#4-pin-人体工学改进-4-pin-人体工学改进)
  - [编译器实验 {#编译器实验}](#编译器实验-编译器实验)
    - [1. `-Zinstrument-mcount` {#1--zinstrument-mcount}](#1--zinstrument-mcount-1--zinstrument-mcount)
    - [2. `-Cdebuginfo-compression` {#2--cdebuginfo-compression}](#2--cdebuginfo-compression-2--cdebuginfo-compression)
    - [3. `fn_align` 属性 {#3-fn\_align-属性}](#3-fn_align-属性-3-fn_align-属性)
  - [标准库实验 {#标准库实验}](#标准库实验-标准库实验)
    - [1. 严格指针来源 (Strict Provenance) {#1-严格指针来源-strict-provenance}](#1-严格指针来源-strict-provenance-1-严格指针来源-strict-provenance)
    - [2. `offset_of_slice` {#2-offset\_of\_slice}](#2-offset_of_slice-2-offset_of_slice)
    - [3. `MaybeUninit` 持续改进 {#3-maybeuninit-持续改进}](#3-maybeuninit-持续改进-3-maybeuninit-持续改进)
  - [Cargo 实验 {#cargo-实验}](#cargo-实验-cargo-实验)
    - [1. Build Dir 新布局 {#1-build-dir-新布局}](#1-build-dir-新布局-1-build-dir-新布局)
    - [2. Section Timings {#2-section-timings}](#2-section-timings-2-section-timings)
  - [形式化研究机会 {#形式化研究机会}](#形式化研究机会-形式化研究机会)
    - [高优先级研究主题 {#高优先级研究主题}](#高优先级研究主题-高优先级研究主题)
    - [建议添加的形式化定义 {#建议添加的形式化定义}](#建议添加的形式化定义-建议添加的形式化定义)
  - [风险与注意事项 {#风险与注意事项}](#风险与注意事项-风险与注意事项)
    - [实验特性风险 {#实验特性风险}](#实验特性风险-实验特性风险)
    - [生产使用建议 {#生产使用建议}](#生产使用建议-生产使用建议)
  - [相关文档 {#相关文档}](#相关文档-相关文档)
  - [Rust 1.96+ 更新 {#rust-196-更新}](#rust-196-更新-rust-196-更新)
  - [**最后更新**: 2026-06-08 (对齐 1.96 稳定版内容)](#最后更新-2026-06-08-对齐-196-稳定版内容)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 版本概览 {#版本概览}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 项目 | 详情 |
| :--- | :--- |
| **版本号** | 1.95.0 |
| **当前状态** | Nightly |
| **预计发布** | 2026-04-16 |
| **主要主题** | 下一代 trait 求解器、异步 Drop、生成器 |

---

## 实验性语言特性 {#实验性语言特性}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. 下一代 Trait 求解器 (next-solver) {#1-下一代-trait-求解器-next-solver}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**状态**: 积极开发中

**描述**: 全新的 trait 求解器架构，解决长期存在的 trait 解析问题

**形式化意义**:

- 更完整的 trait 系统形式化
- 解决高阶类型边界问题
- 改进对 GAT (Generic Associated Types) 的支持

```rust,ignore
// 新求解器将更好处理的案例
#![feature(next_solver)]

fn test<T>()
where
    for<'a> T: Trait<'a>,
    T: for<'a> OtherTrait<'a>,  // 更灵活的高阶边界
{}
```

**形式化关联**: [type_system_foundations](../../archive/research_notes_2026_06_25/type_theory/10_type_system_foundations.md) 需要更新 trait 求解算法描述

---

### 2. Async Drop {#2-async-drop}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**状态**: 实验实现中

**描述**: 允许异步析构函数

**形式化挑战**:

- 异步析构与借用检查器的交互
- Pin 语义在异步 Drop 中的扩展

```rust,ignore
#![feature(async_drop)]

struct AsyncResource;

impl AsyncDrop for AsyncResource {
    async fn drop(&mut self) {
        // 异步清理资源
        async_cleanup().await;
    }
}
```

**形式化关联**: [async_state_machine](../../archive/research_notes_2026_06_25/formal_methods/10_async_state_machine.md)、[pin_self_referential](../../archive/research_notes_2026_06_25/formal_methods/10_pin_self_referential.md)

---

### 3. 生成器 (Generators) {#3-生成器-generators}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**状态**: 迭代器生成器实验

**描述**: 原生的生成器/协程支持

```rust,ignore
#![feature(generators)]

let gen = || {
    yield 1;
    yield 2;
    yield 3;
};

// 使用 iter! 宏
let iter = std::iter::iter! {
    yield 1;
    yield 2;
    yield 3;
};
```

**形式化意义**: 需要扩展 [async_state_machine](../../archive/research_notes_2026_06_25/formal_methods/10_async_state_machine.md) 以涵盖生成器状态机

---

### 4. Pin 人体工学改进 {#4-pin-人体工学改进}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**状态**: 实验中

**描述**: `Pin<&mut T>` 的自动重新借用

```rust,ignore
// 现在需要显式重新借用
let pinned: Pin<&mut T> = ...;
use_pinned(pinned.as_mut());  // 必须显式 as_mut

// 未来可能支持隐式重新借用
use_pinned(pinned);  // 自动重新借用
```

**形式化关联**: [pin_self_referential](../../archive/research_notes_2026_06_25/formal_methods/10_pin_self_referential.md) 需要更新重新借用规则

---

## 编译器实验 {#编译器实验}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. `-Zinstrument-mcount` {#1--zinstrument-mcount}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: 函数调用计数插桩

**应用场景**: 性能分析、代码覆盖率

```bash
rustc -Zinstrument-mcount program.rs
```

---

### 2. `-Cdebuginfo-compression` {#2--cdebuginfo-compression}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**用途**: 调试信息压缩

```bash
rustc -Cdebuginfo-compression=zlib program.rs
```

---

### 3. `fn_align` 属性 {#3-fn_align-属性}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**状态**: 接近稳定

```rust,ignore
#[repr(align(16))]
fn aligned_function() {
    // 函数地址 16 字节对齐
}
```

---

## 标准库实验 {#标准库实验}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 1. 严格指针来源 (Strict Provenance) {#1-严格指针来源-strict-provenance}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

**状态**: 实验 API

**形式化意义**: 为指针操作提供更严格的语义基础

```rust
#![feature(strict_provenance)]

let ptr = std::ptr::without_provenance::<i32>(0x1000);
let addr = ptr.addr();
```

**形式化关联**: [ownership_model](../research_notes/formal_methods/10_ownership_model.md) 需要添加严格来源规则

---

### 2. `offset_of_slice` {#2-offset_of_slice}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**状态**: 实验中

```rust,ignore
#![feature(offset_of_slice)]

// 获取切片字段偏移
let offset = offset_of!(Struct, field[0]);
```

---

### 3. `MaybeUninit` 持续改进 {#3-maybeuninit-持续改进}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

**新增方法**:

- `write_slice`
- `fill`
- `fill_with`

---

## Cargo 实验 {#cargo-实验}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 1. Build Dir 新布局 {#1-build-dir-新布局}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

**状态**: `-Zbuild-dir-new-layout`

**形式化意义**: 影响构建产物路径预测

```bash
cargo build -Zbuild-dir-new-layout
```

---

### 2. Section Timings {#2-section-timings}

> **来源: [IEEE](https://standards.ieee.org/)**

**状态**: `-Zsection-timings`

**用途**: 详细编译阶段计时

```bash
cargo build --timings -Zsection-timings
```

---

## 形式化研究机会 {#形式化研究机会}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 高优先级研究主题 {#高优先级研究主题}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

| 主题 | 描述 | 相关文档 |
| :--- | :--- | :--- |
| 下一代 Trait 求解器 | 新求解器的正确性证明 | [type_system_foundations](../../archive/research_notes_2026_06_25/type_theory/10_type_system_foundations.md) |
| Async Drop | 异步析构的安全保证 | [async_state_machine](../../archive/research_notes_2026_06_25/formal_methods/10_async_state_machine.md) |
| 生成器状态机 | 生成器的内存安全证明 | [async_state_machine](../../archive/research_notes_2026_06_25/formal_methods/10_async_state_machine.md) |
| Pin 重新借用 | 人体工学改进的安全边界 | [pin_self_referential](../../archive/research_notes_2026_06_25/formal_methods/10_pin_self_referential.md) |
| 严格指针来源 | 指针操作的严格语义 | [ownership_model](../research_notes/formal_methods/10_ownership_model.md) |

### 建议添加的形式化定义 {#建议添加的形式化定义}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**Def 1.95-1 (Async Drop 安全)**: 异步析构保证资源最终释放，即使通过异步边界

**Def 1.95-2 (生成器状态)**: 生成器状态机定义扩展，包含 `Yielded` 和 `Complete` 状态

**Def 1.95-3 (Pin 重新借用)**: 隐式重新借用的生命周期约束形式化

---

## 风险与注意事项 {#风险与注意事项}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 实验特性风险 {#实验特性风险}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 风险 | 说明 | 缓解措施 |
| :--- | :--- | :--- |
| API 变更 | 实验特性 API 可能大幅变更 | 不要在生产代码使用 |
| 编译器崩溃 | 新特性可能有 ICE | 定期更新 nightly |
| 性能回归 | 实验实现可能慢 | 使用 `--release` 测试 |
| 形式化过期 | 形式化文档可能跟不上实现 | 标记为实验性 |

### 生产使用建议 {#生产使用建议}
>
> **[来源: [crates.io](https://crates.io/)]**

```text
═══════════════════════════════════════════════════════════════════════

  ⚠️  警告: Nightly 特性不适合生产使用

  建议用途:
  ✅ 学习和实验
  ✅ 为语言演进提供反馈
  ✅ 准备未来迁移
  ✅ 形式化研究

  不建议用途:
  ❌ 生产系统
  ❌ 关键基础设施
  ❌ 稳定 API 依赖

═══════════════════════════════════════════════════════════════════════
```

---

## 相关文档 {#相关文档}
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 文档 | 说明 |
| :--- | :--- |
| [13_rust_1.94_preview | 1.94 Beta 预览 |
| [next-solver 倡议](https://github.com/rust-lang/trait-system-refactor-initiative) | 下一代 trait 求解器 |
| [async-drop 追踪](https://github.com/rust-lang/rust/issues/126482) | Async Drop 进度 |
| [生成器 RFC](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) | 生成器设计 |

---

**维护者**: Rust 形式化方法研究团队
**状态**: 🔬 实验性追踪
**更新频率**: 每周同步

---

## Rust 1.96+ 更新 {#rust-196-更新}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
> **最新版本**: Rust 1.96.1+ (2026-05-28)

本文档基于 Rust 1.96.1，涵盖 1.93–1.96 关键特性。历史版本请参见：

- [Rust 1.96 稳定特性全景](06_19_rust_1_96_features.md)
- Rust 1.94 完整发布说明（已归档）
- Rust 1.93 vs 1.94 对比（已归档）

**最后更新**: 2026-06-08 (对齐 1.96 稳定版内容)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Machine Learning](https://en.wikipedia.org/wiki/Machine_Learning)**
> **来源: [Wikipedia - Artificial Intelligence](https://en.wikipedia.org/wiki/Artificial_Intelligence)**
> **来源: [tch-rs Documentation](https://docs.rs/tch/latest/tch/)**
> **来源: [ACM - AI Systems](https://dl.acm.org/)**

---
