# 10. while let / if let 链 (While-let & If-let Chains - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐  
> **预计阅读时间**：1小时  
> **前置知识**：if let 基础、while let 基础、模式匹配

## 📖 内容概述

本文档系统化展示 if let 链、while let 流水式解构与守卫条件的高级用法，展示如何简化层层嵌套判断，提升代码可读性。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 使用 if let 链代替嵌套 if let
- [ ] 掌握 while let 的流水式解构
- [ ] 组合守卫条件简化逻辑
- [ ] 选择合适的模式匹配语法
- [ ] 重构嵌套条件判断

## 📚 目录

- [10. while let / if let 链 (While-let \& If-let Chains - Rust 1.90)](#10-while-let--if-let-链-while-let--if-let-chains---rust-190)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [10.1. if let 链](#101-if-let-链)
  - [while let 流水处理](#while-let-流水处理)

---

## 10.1. if let 链

```rust
fn parse(input: Option<Result<&str, &'static str>>) -> &'static str {
    if let Some(Ok(s)) = input {
        if s.is_empty() { "empty" } else { "ok" }
    } else if let Some(Err(_)) = input {
        "err"
    } else {
        "none"
    }
}
```

## while let 流水处理

```rust
fn drain_until_neg(mut v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::new();
    while let Some(x) = v.pop() {
        if x < 0 { break; }
        out.push(x);
    }
    out
}
```

---

工程建议：

- 链式 `if let` 适合“逐步缩小条件空间”的判断；
- 连续弹出/消费类逻辑优先 `while let`；
- 分支复杂时考虑改用 `match`。
