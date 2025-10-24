# 04. let-else 模式手册 (let-else Patterns - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐  
> **预计阅读时间**：45分钟  
> **前置知识**：模式匹配、控制流基础

## 📊 目录

- [04. let-else 模式手册 (let-else Patterns - Rust 1.90)](#04-let-else-模式手册-let-else-patterns---rust-190)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [4.1. 典型用法：参数校验 + 早退](#41-典型用法参数校验--早退)
  - [在循环中使用：继续/跳出](#在循环中使用继续跳出)

## 📖 内容概述

`let PATTERN = EXPR else { ... };` 语法允许在解构失败时立即执行 else 分支，常用于参数校验、早退、循环跳过等场景。本文档提供全面的用法指南和最佳实践。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 掌握 let-else 的语法和语义
- [ ] 在函数参数校验中使用 let-else
- [ ] 在循环中使用 let-else 提前跳过
- [ ] 理解 let-else vs if let 的选择
- [ ] 应用 let-else 简化错误处理

## 📚 目录

- [04. let-else 模式手册 (let-else Patterns - Rust 1.90)](#04-let-else-模式手册-let-else-patterns---rust-190)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [4.1. 典型用法：参数校验 + 早退](#41-典型用法参数校验--早退)
  - [在循环中使用：继续/跳出](#在循环中使用继续跳出)

---

## 4.1. 典型用法：参数校验 + 早退

```rust
fn get_port(s: &str) -> Result<u16, String> {
    let Some(rest) = s.strip_prefix("port=") else { return Err("missing".into()); };
    let Ok(n) = rest.parse::<u16>() else { return Err("nan".into()); };
    Ok(n)
}
```

## 在循环中使用：继续/跳出

```rust
fn collect_even(nums: &[i32]) -> Vec<i32> {
    let mut out = Vec::new();
    for &n in nums {
        let true = n % 2 == 0 else { continue };
        out.push(n);
    }
    out
}
```

---

工程建议：

- 将失败路径前置，保持主路径直行；
- `else` 内使用 `return/break/continue` 明确控制流；
- 与 `?` 互补：结构性检查（let-else）与错误传播（`?`）。
