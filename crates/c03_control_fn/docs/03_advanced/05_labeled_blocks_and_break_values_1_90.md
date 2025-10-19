# 05. 标记块与带值 break (Labeled Blocks & Break Values - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐  
> **预计阅读时间**：1小时  
> **前置知识**：循环结构、表达式求值

## 📖 内容概述

本文档深入阐述循环标签和带值 break 的强大表达能力，展示如何以更直观的方式实现"求值并提前返回"模式，以及标记块在复杂控制流中的应用。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 使用循环标签控制嵌套循环
- [ ] 通过 break 从循环返回值
- [ ] 使用标记块模拟局部求值
- [ ] 设计清晰的多层循环控制流
- [ ] 应用带值 break 简化代码逻辑

## 📚 目录

- [05. 标记块与带值 break (Labeled Blocks \& Break Values - Rust 1.90)](#05-标记块与带值-break-labeled-blocks--break-values---rust-190)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [5.1. 循环与标签](#51-循环与标签)
  - [带值 break 作为表达式](#带值-break-作为表达式)
  - [标记块（模拟“局部求值”）](#标记块模拟局部求值)

---

## 5.1. 循环与标签

```rust
fn find_first_even(nums: &[i32]) -> Option<i32> {
    'out: for &n in nums {
        if n % 2 == 0 { break 'out Some(n); }
    }
}
```

## 带值 break 作为表达式

```rust
fn index_of(hay: &[i32], needle: i32) -> Option<usize> {
    let res = 'search: loop {
        for (i, &x) in hay.iter().enumerate() {
            if x == needle { break 'search Some(i); }
        }
        break 'search None;
    };
    res
}
```

## 标记块（模拟“局部求值”）

```rust
fn compute() -> i32 {
    'blk: {
        if 1 + 1 == 2 { break 'blk 10; }
        0
    }
}
```

---

工程建议：

- 多层控制流用标签提升可读性；
- 带值 `break` 让“循环即表达式”的意图清晰；
- 标记块可替代临时变量/跳转实现局部求值。
