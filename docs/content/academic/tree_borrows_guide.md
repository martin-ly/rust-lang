# Tree Borrows 详解

> **论文**: Tree Borrows: An Aliasing Model for Rust
> **会议**: PLDI 2025 (Distinguished Paper Award)
> **作者**: Neven Villani, Ralf Jung, et al.
> **状态**: 🔄 正在整合到 Rust 编译器

---

## 📋 目录

- [Tree Borrows 详解](#tree-borrows-详解)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心改进](#核心改进)
  - [📊 与 Stacked Borrows 对比](#-与-stacked-borrows-对比)
    - [关键区别示例](#关键区别示例)
  - [🌳 核心概念](#-核心概念)
    - [树结构](#树结构)
    - [权限模型](#权限模型)
    - [状态转换](#状态转换)
  - [💡 实际影响](#-实际影响)
    - [更多代码合法](#更多代码合法)
    - [直观性提升](#直观性提升)
  - [🔄 迁移指南](#-迁移指南)
    - [测试代码兼容性](#测试代码兼容性)
    - [常见问题](#常见问题)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

Tree Borrows 是 Rust 内存模型的最新研究成果，旨在替代 Stacked Borrows 成为 Rust 的标准别名模型。

### 核心改进

```
Stacked Borrows (旧模型)
├─ 基于栈的内存访问跟踪
├─ 严格的访问规则
└─ 拒绝某些直觉上合法的代码

Tree Borrows (新模型)
├─ 基于树的内存访问跟踪
├─ 更灵活的访问规则
└─ 接受更多合法的代码模式
```

---

## 📊 与 Stacked Borrows 对比

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| **数据结构** | 栈 | 树 |
| **兼容性** | 30K crates | 30K + 54% 通过 |
| **形式化** | 已验证 | Rocq 形式化 |
| **拒绝率** | 较高 | 降低 54% |
| **直观性** | 一般 | 更好 |

### 关键区别示例

```rust
// 示例: 通过引用重新借用
fn example() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;  // 通过 y 重新借用

    *z = 1;
    *y = 2;  // Stacked Borrows: 可能 UB
             // Tree Borrows: OK
}
```

---

## 🌳 核心概念

### 树结构

```
Stacked Borrows 视图:
    [ Unique(0) ]
    [ Unique(1) ]
    [ Unique(2) ]
    └─ 严格的栈顺序

Tree Borrows 视图:
           [ Unique(0) ] (根)
           /           \
    [ Shared(1) ]  [ Unique(2) ] (子节点)
    └─ 允许分支和共存
```

### 权限模型

```rust
// 每种借用都有权限标签
enum Permission {
    Unique,      // 独占读写
    SharedRead,  // 共享只读
    SharedWrite, // 共享写入
    Disabled,    // 禁用
}
```

### 状态转换

```
状态转换图:

  Unique
    │
    ├─ 创建子借用 ──→ SharedRead/SharedWrite
    │
    ├─ 读取访问 ──→ 保持 Unique
    │
    └─ 写入访问 ──→ 禁用子借用

  SharedRead
    │
    ├─ 创建子借用 ──→ SharedRead
    │
    └─ 读取访问 ──→ 保持 SharedRead

  SharedWrite
    │
    ├─ 创建子借用 ──→ SharedWrite/SharedRead
    │
    └─ 写入访问 ──→ 转换为 SharedRead
```

---

## 💡 实际影响

### 更多代码合法

```rust
// 示例1: 重叠借用
fn overlapping_borrows() {
    let mut data = [1, 2, 3, 4, 5];

    let left = &mut data[..2];
    let right = &mut data[3..];

    // 两个不重叠的切片同时可变借用
    left[0] = 10;
    right[0] = 50;
}

// 示例2: 迭代器与可变借用
fn iterator_with_mutable() {
    let mut vec = vec![1, 2, 3, 4, 5];

    // 获取迭代器
    let mut iter = vec.iter();

    // 同时可以修改其他元素
    vec.push(6);  // Tree Borrows: OK
}

// 示例3: 自引用结构
struct SelfReferential<'a> {
    data: String,
    ptr: &'a str,  // 指向 data
}
```

### 直观性提升

```rust
// 程序员直觉上认为合法的代码
fn intuitive_code() {
    let mut x = 0;
    let y = &mut x;

    // 使用 y 获取新的引用
    let z = &mut *y;
    *z = 1;

    // 重新使用 y
    *y = 2;  // Tree Borrows 认为这完全合法
}
```

---

## 🔄 迁移指南

### 测试代码兼容性

```bash
# 使用 Miri 测试 Tree Borrows
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 对比 Stacked Borrows
MIRIFLAGS="-Zmiri-stacked-borrows" cargo miri test
```

### 常见问题

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| 代码在新模型下 UB | 依赖旧的别名规则 | 重构借用模式 |
| 性能下降 | 额外的权限检查 | 等待编译器优化 |
| 不确定性 | 模型边界情况 | 避免模糊代码模式 |

---

## 🔗 参考资源

- [论文 PDF](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [Iris 形式化](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf)
- [Ralf Jung 博客](https://www.ralfj.de/blog/2025/07/07/tree-borrows-paper.html)
- [Miri Tree Borrows](https://github.com/rust-lang/miri)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: 🔄 学术前沿跟踪中
