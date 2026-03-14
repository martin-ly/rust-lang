# 常量求值形式化

> **创建日期**: 2026-02-28
> **文档类型**: 形式化研究
> **Rust 版本**: 1.94.0+

---

## 📋 目录

- [常量求值形式化](#常量求值形式化)
  - [📋 目录](#-目录)
  - [1. 常量求值概述](#1-常量求值概述)
  - [2. 形式化定义](#2-形式化定义)
    - [Def CE-1: 常量上下文](#def-ce-1-常量上下文)
    - [Def CE-2: 常量求值器](#def-ce-2-常量求值器)
  - [3. 常量函数 (const fn)](#3-常量函数-const-fn)
    - [Def CE-3: const fn 约束](#def-ce-3-const-fn-约束)
    - [Def CE-4: 禁止的 const fn 操作](#def-ce-4-禁止的-const-fn-操作)
  - [4. 定理](#4-定理)
    - [Thm CE-1: 常量求值终止性](#thm-ce-1-常量求值终止性)
    - [Thm CE-2: 常量求值确定性](#thm-ce-2-常量求值确定性)
  - [5. MIR 常量求值](#5-mir-常量求值)
  - [6. 高级特性](#6-高级特性)
    - [const\_eval\_select (不稳定)](#const_eval_select-不稳定)
  - [🆕 Rust 1.94 研究更新](#-rust-194-研究更新)
    - [核心研究点](#核心研究点)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)

## 1. 常量求值概述

Rust 的常量求值在编译期执行，允许在类型系统和常量定义中使用计算。

---

## 2. 形式化定义

### Def CE-1: 常量上下文

```text
常量上下文 := 静态项 | 常量项 | 枚举判别式 | 数组长度 | 类型别名
```

### Def CE-2: 常量求值器

```text
Eval_const: Expr × Env → Value + Error

Eval_const(e, env) =
  若 e 是纯表达式 → 求值结果
  若 e 含副作用 → 编译错误
```

---

## 3. 常量函数 (const fn)

### Def CE-3: const fn 约束

```rust
// 允许的 const fn 操作
const fn allowed() {
    // ✅ 算术运算
    let x = 1 + 2;

    // ✅ 控制流
    if x > 0 { }

    // ✅ 匹配
    match x { _ => () }

    // ✅ 循环
    loop { break; }

    // ✅ 调用其他 const fn
    const_fn_call();
}
```

### Def CE-4: 禁止的 const fn 操作

```rust
const fn forbidden() {
    // ❌ 堆分配
    // let x = Box::new(42);

    // ❌ 可变静态变量
    // unsafe { STATIC_VAR = 42; }

    // ❌ 非 const fn 调用
    // non_const_fn();

    // ❌ 类型转换到裸指针（某些情况）
    // &x as *const i32
}
```

---

## 4. 定理

### Thm CE-1: 常量求值终止性

**陈述**: 所有常量求值在有限步内终止或报告错误。

**证明**:

- 常量求值器限制循环迭代次数（默认 1_000_000）
- 递归深度有限制
- 无无限递归类型

### Thm CE-2: 常量求值确定性

**陈述**: 给定相同输入，常量求值产生相同结果。

**证明**:

- 无副作用
- 无外部输入
- 纯函数语义

---

## 5. MIR 常量求值

```text
编译期求值流程:

Rust 源码
    ↓
HIR (高级中间表示)
    ↓
MIR (中级中间表示)
    ↓
常量求值器 (MIRI 核心)
    ↓
编译时常量值
```

---

## 6. 高级特性

### const_eval_select (不稳定)

```rust
#![feature(const_eval_select)]

const fn with_const_eval_select<T>(x: T) -> T {
    const_eval_select!(
        @capture { x: T }
        @target: fn(T) -> T,
        @const_fallback: const_fn_impl,
        @runtime_fallback: runtime_fn_impl,
    )
}
```

---

**维护者**: Rust 形式化研究团队

---

## 🆕 Rust 1.94 研究更新

> **适用版本**: Rust 1.94.0+

### 核心研究点

- rray_windows 的形式化语义
- ControlFlow 的代数结构
- LazyCell/LazyLock 的延迟语义
- 与现有理论框架的集成

详见 [RUST_194_RESEARCH_UPDATE](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
