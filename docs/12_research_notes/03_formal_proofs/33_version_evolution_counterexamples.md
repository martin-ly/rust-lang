# 版本演进边界与迁移反例 {#版本演进边界与迁移反例}

> **EN**: Version Evolution Counterexamples
> **Summary**: 版本演进边界与迁移反例 Version Evolution Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6-L7 (版本边界 / 演进)
> **Bloom 层级**: L5-L6
> **概念族**: 版本演进 / 反例边界
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [版本演进边界与迁移反例 {#版本演进边界与迁移反例}](#版本演进边界与迁移反例-版本演进边界与迁移反例)
  - [目录 {#目录}](#目录-目录)
  - [1. Edition 2024 drop order 尾部表达式变化 {#1-edition-2024-drop-order-尾部表达式变化}](#1-edition-2024-drop-order-尾部表达式变化-1-edition-2024-drop-order-尾部表达式变化)
    - [现象 {#现象-6}](#现象-现象-6)
    - [后果 {#后果}](#后果-后果)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. `unsafe_op_in_unsafe_fn` lint 默认启用 {#2-unsafe\_op\_in\_unsafe\_fn-lint-默认启用}](#2-unsafe_op_in_unsafe_fn-lint-默认启用-2-unsafe_op_in_unsafe_fn-lint-默认启用)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [编译器错误 {#编译器错误}](#编译器错误-编译器错误)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. `gen` 关键字保留 {#3-gen-关键字保留}](#3-gen-关键字保留-3-gen-关键字保留)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. `match` 临时变量作用域变化 {#4-match-临时变量作用域变化}](#4-match-临时变量作用域变化-4-match-临时变量作用域变化)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. 依赖最低 Rust 版本声明不足 {#5-依赖最低-rust-版本声明不足}](#5-依赖最低-rust-版本声明不足-5-依赖最低-rust-版本声明不足)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. 混用 Edition 的 workspace 成员 {#6-混用-edition-的-workspace-成员}](#6-混用-edition-的-workspace-成员-6-混用-edition-的-workspace-成员)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [问题 {#问题}](#问题-问题)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. 忽略弃用警告导致未来编译失败 {#7-忽略弃用警告导致未来编译失败}](#7-忽略弃用警告导致未来编译失败-7-忽略弃用警告导致未来编译失败)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)

---

## 1. Edition 2024 drop order 尾部表达式变化 {#1-edition-2024-drop-order-尾部表达式变化}

### 现象 {#现象-6}

在 Edition 2021 中，块尾部表达式的临时变量按**相反**顺序 drop；Edition 2024 改为**正序** drop。

```rust
// 依赖临时值 drop 顺序的代码在 Edition 2024 行为改变
let x = {
    let a = Mutex::new(1);
    let b = Mutex::new(2);
    a.lock().unwrap().clone() + b.lock().unwrap().clone()
};
```

### 后果 {#后果}

如果临时对象持有互斥资源，drop 顺序变化可能影响死锁或语义。

### 修复方案 {#修复方案-6}

- 明确使用 `let` 绑定控制生命周期（Lifetimes）。
- 不依赖临时值的隐式 drop 顺序编写程序逻辑。

> **权威来源**: [Rust Edition Guide – Tail Expr Drop Order](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)

---

## 2. `unsafe_op_in_unsafe_fn` lint 默认启用 {#2-unsafe_op_in_unsafe_fn-lint-默认启用}

### 现象 {#现象-6}

Edition 2024 中，`unsafe fn` 内部调用 `unsafe` 操作需要额外 `unsafe` 块。

```rust
unsafe fn foo(ptr: *mut u8) {
    *ptr = 1; // ❌ Edition 2024 下需要 unsafe 块
}
```

### 编译器错误 {#编译器错误}

```text
warning: call to unsafe function is unsafe and requires unsafe block
```

### 修复方案 {#修复方案-6}

```rust
unsafe fn foo(ptr: *mut u8) {
    unsafe { *ptr = 1; }
}
```

---

## 3. `gen` 关键字保留 {#3-gen-关键字保留}

### 现象 {#现象-6}

Rust 1.75+ 引入了 `gen` 块（不稳定），`gen` 逐渐成为保留关键字。

```rust
let gen = 1; // ⚠️ 未来版本可能冲突
```

### 修复方案 {#修复方案-6}

- 避免使用 `gen` 作为标识符。
- 使用 `cargo fix --edition 2024` 自动迁移。

---

## 4. `match` 临时变量作用域变化 {#4-match-临时变量作用域变化}

### 现象 {#现象-6}

Edition 2024 对 `match` 临时值作用域有调整，某些借用（Borrowing）模式可能不再通过。

```rust
let x: Option<&String> = match Some(String::from("hello")) {
    Some(ref s) => Some(s), // 依赖临时值生命周期
    None => None,
};
```

### 修复方案 {#修复方案-6}

- 显式绑定值到 `let`，避免依赖 match 临时值作用域。
- 运行 `cargo fix` 并检查借用错误。

---

## 5. 依赖最低 Rust 版本声明不足 {#5-依赖最低-rust-版本声明不足}

### 现象 {#现象-6}

```toml
[package]
name = "my-lib"
rust-version = "1.70"
```

但代码中使用了 Rust 1.80 才稳定的 API，导致使用 `rust-version = "1.70"` 的下游编译失败。

### 修复方案 {#修复方案-6}

- `rust-version` 应真实反映代码所需的最低稳定版本。
- CI 中使用该版本进行构建验证。

---

## 6. 混用 Edition 的 workspace 成员 {#6-混用-edition-的-workspace-成员}

### 现象 {#现象-6}

```toml
# crate-a/Cargo.toml {#crate-acargotoml}
edition = "2021"

# crate-b/Cargo.toml {#crate-bcargotoml}
edition = "2024"
```

### 问题 {#问题}

- 同一 workspace 中不同 edition 的 crate 行为不一致。
- 跨 crate 的宏（Macro）展开可能受 edition 差异影响。

### 修复方案 {#修复方案-6}

- Workspace 成员尽量统一 edition。
- 迁移时批量升级，使用 `cargo fix --edition`。

---

## 7. 忽略弃用警告导致未来编译失败 {#7-忽略弃用警告导致未来编译失败}

### 现象 {#现象-6}

```rust
#[deprecated(since = "1.90.0", note = "use new_fn instead")]
pub fn old_fn() {}

fn main() {
    old_fn(); // 当前只是 warning，未来可能删除
}
```

### 修复方案 {#修复方案-6}

- 及时替换弃用 API。
- CI 中设置 `RUSTFLAGS="-D warnings"` 强制处理。

---

## 总结 {#总结}

| 反例 | 涉及版本特性 | 后果 | 修复方向 |
|------|--------------|------|----------|
| drop order 变化 | Edition 2024 | 资源释放顺序改变 | 显式 let 绑定 |
| unsafe fn lint | Edition 2024 | 编译 warning/error | 内部 unsafe 块 |
| `gen` 关键字 | 1.75+ | 未来语法冲突 | 重命名标识符 |
| match 临时作用域 | Edition 2024 | 借用检查失败 | 显式绑定 |
| rust-version 不足 | Cargo | 下游编译失败 | 准确声明 + CI |
| Edition 混用 | workspace | 行为不一致 | 统一 edition |
| 弃用 API | 标准库 / crate | 未来编译失败 | 替换 + deny warnings |

> **权威来源**: [Rust Edition Guide – Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) | [Rust Release Notes](https://releases.rs/) | [Cargo Book – rust-version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) | [The Rust Programming Language – Appendix E](https://doc.rust-lang.org/book/appendix-05-editions.html)

## 相关概念 {#相关概念}

- [Rust 1.94 研究更新](../12_version_research/02_rust_194_research_update.md)
- [Rust 1.94/1.95 特性矩阵](10_rust_194_195_feature_matrix.md)
- [Rust 1.93 反例索引](10_rust_193_counterexamples_index.md)
- [知识图谱索引](../06_concept_models/13_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../01_alignment_matrices/30_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 2094: Non-lexical lifetimes](https://rust-lang.github.io/rfcs/2094-nll.html)
- [RFC 2585: Unsafe blocks in unsafe fn](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)
- [RFC 3513: gen blocks](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [Rust Release Blog](https://blog.rust-lang.org/)
- [This Week in Rust](https://this-week-in-rust.org/)

> **来源: [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/)**
> **来源: [RustSEM: A Formal Semantics for Rust](https://link.springer.com/article/10.1007/s10703-024-00460-3)**
