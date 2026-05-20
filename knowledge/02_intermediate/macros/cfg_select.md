# `cfg_select!` 宏（Rust 1.95.0）

> **Bloom 层级**: 理解

> **稳定版本**: Rust 1.95.0 (2026-04-16)
> **Edition**: 2024
> **模块**: `core::macros`
> **权威来源**: [Rust 1.95 Release Notes](https://releases.rs/docs/1.95.0/), [core::macros::cfg_select](https://doc.rust-lang.org/core/macro.cfg_select.html), [rust-lang/rust#131038](https://github.com/rust-lang/rust/pull/131038)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 cfg_select 编译期条件选择语义来源标注 [来源: Authority Source Sprint Batch 8]

---

## 一、概念定义

`cfg_select!` 是 Rust 1.95.0 引入的标准宏 [来源: Rust 1.95 Release Notes / 2026; core::macros::cfg_select / Rust Standard Library 2025; 核心设计决策: 编译期根据 `cfg` 条件选择第一个满足条件的表达式，替代嵌套 `cfg!` 或 `#[cfg]` 属性]，用于在**编译期**根据 `cfg` 条件选择第一个满足条件的表达式。它是嵌套 `cfg!` 或 `#[cfg]` 属性的简洁替代方案。

### 语法
> **[来源: Rust Official Docs]**

```rust
cfg_select! {
    condition1 => expr1,
    condition2 => expr2,
    _ => fallback_expr,
}
```

### 与现有方案对比
> **[来源: Rust Official Docs]**

| 方案 | 适用层级 | 语法复杂度 | 默认分支 |
|------|---------|-----------|---------|
| `#[cfg]` | 项级别 (item) | 高（需重复定义） | ❌ 不支持 |
| `cfg!` | 表达式级别 | 中（嵌套 if） | ❌ 需显式 else |
| `cfg_select!` | 表达式级别 | 低（类 match） | ✅ `_ =>` |

---

## 二、基本用法
> **[来源: Rust Official Docs]**

### 2.1 平台特定常量
> **[来源: Rust Official Docs]**

```rust
const PAGE_SIZE: usize = cfg_select! {
    target_os = "macos" => 16384,
    target_os = "windows" => 4096,
    _ => 4096,
};
```

### 2.2 特性标志选择
> **[来源: Rust Official Docs]**

```rust
fn hasher_name() -> &'static str {
    cfg_select! {
        feature = "blake3" => "blake3",
        feature = "sha256" => "sha256",
        _ => "default",
    }
}
```

### 2.3 架构特定优化

```rust
fn simd_lanes() -> usize {
    cfg_select! {
        target_feature = "avx512f" => 16,
        target_feature = "avx2" => 8,
        target_feature = "sse2" => 4,
        _ => 1,
    }
}
```

---

## 三、应用场景

### 3.1 跨平台路径分隔符

```rust
const PATH_SEP: char = cfg_select! {
    target_os = "windows" => '\\',
    _ => '/',
};
```

### 3.2 嵌入式目标选择

```rust
fn max_priority() -> u8 {
    cfg_select! {
        target_arch = "arm" => 255,
        target_arch = "riscv32" => 7,
        _ => 127,
    }
}
```

---

## 四、限制与反例

### ❌ 不能用于模块/函数声明

```rust
// 错误：cfg_select! 是表达式级宏
cfg_select! {
    target_os = "linux" => mod linux_impl;
    _ => mod generic_impl;
}
```

### ❌ 所有分支类型必须一致

```rust
// 错误：分支类型不一致
let x = cfg_select! {
    target_os = "linux" => 42,
    _ => "fallback",  // 类型不匹配
};
```

### ❌ 运行时条件无效

```rust
let runtime_flag = true;
// 错误：runtime_flag 不是 cfg 条件
// cfg_select! { runtime_flag => ... }
```

---

## 五、决策树

```text
需要根据 cfg 条件选择代码？
├── 选择整个函数/结构体/模块？ → #[cfg]
├── 选择语句块内的不同实现？
│   ├── 条件简单（1-2个）→ cfg! + if/else
│   └── 条件复杂或多分支？ → cfg_select!
└── 需要表达式值？ → cfg_select!
```

---

### 模块 3: 概念依赖图

```mermaid
graph TD
    A[Conditional Compilation] --> B[#[cfg] Attribute]
    A --> C[cfg! Macro]
    C --> D[Runtime Branching]
    A --> E[cfg_select! Macro]
    E --> F[Compile-time Expression Selection]
    F --> G[Platform Abstraction]
    F --> H[Feature Flags]

    style E fill:#f9f,stroke:#333,stroke-width:2px
    style F fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **Macros** | `03_advanced/macros/declarative.md` | `cfg_select!` 是声明式宏 |
| **cfg** | `02_intermediate/cfg.md` | `cfg` 条件的基础语法 |
| **Conditional Compilation** | `01_fundamentals/conditional_compilation.md` | `#[cfg]` 属性 |

---

### 模块 7: 思维表征

### 表征: cfg 条件编译工具选择矩阵

| 需求 | `#[cfg]` | `cfg!` | `cfg_select!` |
|------|---------|--------|--------------|
| 条件编译整个函数/模块 | ✅ | ❌ | ❌ |
| 运行时检查条件 | ❌ | ✅ | ❌（编译期） |
| 表达式级值选择 | ❌ | ⚠️（需 if/else） | ✅ |
| 多分支选择 | ⚠️（重复定义） | ⚠️（嵌套 if） | ✅ |
| 默认/兜底分支 | ❌ | ⚠️ | ✅ |
| 代码简洁度 | 中 | 中 | **高** |

---

## 📚 模块 8: 国际化对齐

| 来源 | 类型 | 说明 |
|------|------|------|
| [Rust 1.95.0 Release](https://releases.rs/docs/1.95.0/) | 官方 | `cfg_select!` 稳定化公告 |
| [core::macros::cfg_select](https://doc.rust-lang.org/core/macro.cfg_select.html) | 官方 | API 文档 |

---

## ⚖️ 模块 9: 设计权衡

### 为什么需要 cfg_select!？

`#[cfg]` 只能作用于**项级别**（函数、结构体、模块），`cfg!` 只能在**表达式级别**返回布尔值。`cfg_select!` 填补了"表达式级多分支选择"的空白，使平台相关常量和函数体的编写更简洁。

限制：`cfg_select!` 是表达式级宏，不能用于声明项（如 `mod`、`fn` 签名）。

---

## 📝 模块 10: 自我检测

1. **`cfg_select!` 与 `#[cfg]` 的根本区别是什么？** 为什么 `cfg_select!` 不能用于条件编译整个函数？

2. **以下代码有什么问题？如何修复？**

```rust
let x = cfg_select! {
    target_os = "linux" => 42,
    target_os = "macos" => 100,
};
```

<details>
<summary>参考答案</summary>

**问题**: 缺少 `_ =>` 默认分支。如果目标 OS 既不是 linux 也不是 macos（如 Windows），编译会失败。

**修复**:

```rust
let x = cfg_select! {
    target_os = "linux" => 42,
    target_os = "macos" => 100,
    _ => 0,  // 默认分支
};
```

</details>

---

## 📚 权威来源索引

- [Rust 1.95 Release Notes](https://releases.rs/docs/1.95.0/) [来源: Rust Release Team / 2026]
- [core::macros::cfg_select](https://doc.rust-lang.org/core/macro.cfg_select.html) [来源: Rust Standard Library / 2025]
- [rust-lang/rust#131038](https://github.com/rust-lang/rust/pull/131038) [来源: Rust Core Team / 2025]

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
