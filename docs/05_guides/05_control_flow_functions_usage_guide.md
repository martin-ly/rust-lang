# 控制流与函数使用指南

> **Bloom 层级**: L3-L4 (应用/分析)

**模块**: C03 Control Flow & Functions
**创建日期**: 2026-05-12
**最后更新**: 2026-05-12
**Rust 版本**: 1.96.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [控制流与函数使用指南](#控制流与函数使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
  - [📊 核心功能](#-核心功能)
    - [1. 控制流模式](#1-控制流模式)
    - [2. 函数系统](#2-函数系统)
    - [3. 闭包](#3-闭包)
    - [4. 模式匹配](#4-模式匹配)
    - [5. if let guards (Rust 1.95)](#5-if-let-guards-rust-195)
    - [6. 协程与生成器](#6-协程与生成器)
  - [⚡ 性能优化](#-性能优化)
  - [🔧 错误处理](#-错误处理)
  - [🐛 常见问题与解决方案](#-常见问题与解决方案)
  - [🔗 相关文档](#-相关文档)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

---

## 📋 概述
>
> **[来源: Rust Official Docs]**

本指南对应 `crates/c03_control_fn`，涵盖 Rust 控制流、函数系统、闭包、模式匹配以及 Rust 1.95 的 `if let guards` 和协程/生成器前瞻。

**前置知识**: [knowledge/01_fundamentals/](../../knowledge/01_fundamentals/)
**速查卡**: [02_control_flow_functions_cheatsheet.md](../02_reference/quick_reference/02_control_flow_functions_cheatsheet.md)

---

## 🚀 快速开始
>
> **[来源: Rust Official Docs]**

```rust,ignore
use c03_control_fn::control_flow_patterns::{
    MatchPatterns, LetChainPatterns, LoopPatterns
};

fn main() {
    // 模式匹配示例
    let patterns = MatchPatterns::new();
    patterns.demonstrate_all();

    // let chains 示例
    let chains = LetChainPatterns::new();
    chains.demonstrate_let_chains();
}
```

---

## 📊 核心功能
>
> **[来源: Rust Official Docs]**

### 1. 控制流模式
>
> **[来源: Rust Official Docs]**

`control_flow_patterns/` 模块封装了 Rust 中所有控制流结构的高级用法：

| 模式 | 说明 |
|------|------|
| `MatchPatterns` | 穷尽匹配、守卫条件、绑定模式 |
| `LetChainPatterns` | `let-else`、`if let` 链式使用 |
| `LoopPatterns` | 带标签的循环、`break` 返回值 |

**示例：let chains**

```rust,ignore
use c03_control_fn::control_flow_patterns::LetChainPatterns;

fn process_nested_options() {
    let chains = LetChainPatterns::new();

    // Rust 1.95+: 链式 let 绑定简化嵌套 Option 处理
    chains.demonstrate_let_chains();

    // 等价于:
    // let Some(a) = opt_a else { return };
    // let Some(b) = opt_b else { return };
    // let Some(c) = opt_c else { return };
    // use(a, b, c);
}
```

### 2. 函数系统
>
> **[来源: Rust Official Docs]**

`control_struct/` 和 `items/` 模块展示函数定义的高级特性：

```rust,ignore
use c03_control_fn::control_struct::define::{ControlFlowBuilder, ConditionalExecutor};

// 构建复杂的条件执行链
fn conditional_execution() {
    let executor = ControlFlowBuilder::new()
        .add_condition(|x: i32| x > 0)
        .add_condition(|x| x < 100)
        .build();

    executor.execute(50, |x| println!("Valid: {}", x));
}
```

### 3. 闭包
>
> **[来源: Rust Official Docs]**

`closure/` 模块深入解析闭包的捕获机制与类型系统：

```rust,ignore
use c03_control_fn::closure::design::{ClosureDesigner, CaptureStrategy};

fn closure_patterns() {
    let designer = ClosureDesigner::new();

    // 按值捕获
    let move_closure = designer.create_move_closure();

    // 按引用捕获
    let ref_closure = designer.create_ref_closure();

    // 自定义捕获策略
    let custom = designer.create_with_strategy(CaptureStrategy::Mixed);
}
```

### 4. 模式匹配
>
> **[来源: Rust Official Docs]**

`pattern_matching/` 模块提供穷尽性检查和复杂模式：

```rust,ignore
use c03_control_fn::pattern_matching::define::{
    PatternMatcher, DestructuringPattern, GuardPattern
};

fn advanced_matching() {
    let matcher = PatternMatcher::new();

    // 解构嵌套结构
    matcher.match_nested_struct();

    // 带守卫的模式
    matcher.match_with_guard(|x| x > 10);
}
```

### 5. if let guards (Rust 1.95)
>
> **[来源: Rust Official Docs]**

`if_let_guards_deep_dive/` 模块是 Rust 1.95 核心特性的深度解析：

```rust,ignore
use c03_control_fn::if_let_guards_deep_dive::{
    IfLetGuardsSyntax, IfLetGuardsPatterns, IfLetGuardsMigrationGuide
};

fn demonstrate_if_let_guards() {
    let guide = IfLetGuardsMigrationGuide::new();
    guide.show_migration_path();

    // 新语法: match 守卫中支持 if let
    let syntax = IfLetGuardsSyntax::new();
    syntax.demonstrate_syntax();
}
```

**if let guards 核心用法:**

```rust,ignore
enum Message {
    Text(String),
    Image { url: String, size: u64 },
    Command { cmd: String, args: Vec<String> },
}

fn process_message(msg: Message, current_user: Option<User>) {
    match msg {
        Message::Text(text)
            if let Some(user) = current_user
            && user.can_read(&text) =>
        {
            println!("{}: {}", user.name, text);
        }
        Message::Image { url, size }
            if size < 1024 * 1024 =>
        {
            println!("Small image: {}", url);
        }
        _ => {}
    }
}
```

### 6. 协程与生成器
>
> **[来源: Rust Official Docs]**

`coroutine/` 和 `generator/` 模块提供异步控制流和生成器模式（部分为 nightly 特性）：

```rust,ignore
use c03_control_fn::coroutine::CoroutineExample;
use c03_control_fn::generator::GeneratorExample;

fn async_control_flow() {
    // 协程示例 (async/await)
    let coroutine = CoroutineExample::new();
    coroutine.demonstrate_await_points();

    // 生成器示例 (nightly-only, gen blocks)
    let gen = GeneratorExample::new();
    gen.demonstrate_yield();
}
```

---

## ⚡ 性能优化
>
> **[来源: Rust Official Docs]**

| 技术 | 说明 | 模块 |
|------|------|------|
| 尾递归优化 | 使用循环替代深度递归 | `control_flow_patterns/` |
| 短路求值 | `&&` / `||` 的懒加载特性 | `control_struct/` |
| 闭包内联 | `FnOnce` 避免重复调用开销 | `closure/` |
| 模式匹配优化 | 编译器生成跳转表 | `pattern_matching/` |

---

## 🔧 错误处理
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

`error_handling/` 模块提供控制流中的错误处理模式：

```rust,ignore
use c03_control_fn::error_handling::define::{
    ControlFlowResult, ErrorPropagation
};

fn robust_control_flow() -> ControlFlowResult<()> {
    let propagator = ErrorPropagation::new();

    propagator.try_chain(
        || step_one(),
        || step_two(),
        || step_three(),
    )
}
```

---

## 🐛 常见问题与解决方案
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| match 未穷尽 | 遗漏枚举变体 | 编译器警告，补全分支或使用 `_` |
| 闭包生命周期错误 | 捕获引用超出作用域 | 使用 `move` 关键字按值捕获 |
| if let guards 编译失败 | 语法位置错误 | 确保 `if let` 在 match arm 的守卫位置 |
| 递归栈溢出 | 深度过大 | 改用迭代或尾递归优化 |

---

## 🔗 相关文档
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- **速查卡**: [02_control_flow_functions_cheatsheet.md](../02_reference/quick_reference/02_control_flow_functions_cheatsheet.md)
- **学习教程**: [knowledge/02_intermediate/](../../knowledge/02_intermediate/)
- **异步指南**: [05_async_programming_usage_guide.md](./05_async_programming_usage_guide.md)
- **源码**: [crates/c03_control_fn/](../../crates/c03_control_fn/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [05_guides 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---
