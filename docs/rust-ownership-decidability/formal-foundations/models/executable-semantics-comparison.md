# Rust 可执行语义形式化对比分析

> **覆盖**: KRust (2018), RustSEM (2024), Aeneas
> **框架**: K-Framework, Coq, 符号执行
> **难度**: 🔴 高级

---

## 目录

- [Rust 可执行语义形式化对比分析](#rust-可执行语义形式化对比分析)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言](#1-引言)
  - [2. KRust (2018)](#2-krust-2018)
    - [2.1 概述](#21-概述)
    - [2.2 K-Framework 实现](#22-k-framework-实现)
    - [2.3 覆盖的语言特性](#23-覆盖的语言特性)
    - [2.4 测试与验证](#24-测试与验证)
    - [2.5 局限性](#25-局限性)
  - [3. RustSEM (2024)](#3-rustsem-2024)
    - [3.1 概述](#31-概述)
    - [3.2 内存级形式化](#32-内存级形式化)
    - [3.3 覆盖范围](#33-覆盖范围)
    - [3.4 与 Rust 编译器的对比](#34-与-rust-编译器的对比)
    - [3.5 应用](#35-应用)
  - [4. Aeneas](#4-aeneas)
    - [4.1 概述](#41-概述)
    - [4.2 函数式翻译方法](#42-函数式翻译方法)
    - [4.3 LLBC 中间语言](#43-llbc-中间语言)
    - [4.4 验证流程](#44-验证流程)
  - [5. 对比分析](#5-对比分析)
    - [5.1 特性覆盖对比](#51-特性覆盖对比)
    - [5.2 验证能力对比](#52-验证能力对比)
    - [5.3 工具链集成对比](#53-工具链集成对比)
  - [6. 形式化方法对比](#6-形式化方法对比)
    - [6.1 操作语义风格](#61-操作语义风格)
    - [6.2 内存模型表示](#62-内存模型表示)
    - [6.3 所有权跟踪机制](#63-所有权跟踪机制)
  - [7. 实际应用建议](#7-实际应用建议)
    - [7.1 教育与学习](#71-教育与学习)
    - [7.2 运行时调试](#72-运行时调试)
    - [7.3 形式化验证](#73-形式化验证)
    - [7.4 语言研究](#74-语言研究)
  - [参考文献](#参考文献)
    - [KRust](#krust)
    - [RustSEM](#rustsem)
    - [Aeneas](#aeneas)
    - [K-Framework](#k-framework)

---

## 摘要

本文档对比分析三种主要的 Rust 可执行语义形式化方法：

| 项目 | 年份 | 框架 | 主要贡献 |
|------|------|------|----------|
| **KRust** | 2018 | K-Framework | 首个可执行 Rust 语义，覆盖核心特性 |
| **RustSEM** | 2024 | K-Framework | 内存级形式化，更大语言子集，700+ 测试验证 |
| **Aeneas** | 2022-24 | Coq | 函数式翻译，自动化验证，HOL4/F* 后端 |

---

## 1. 引言

可执行语义（Executable Semantics）是指可以被解释器直接执行的程序语言形式化定义。与纸面形式化相比，可执行语义允许：

1. **直接测试**：在形式化定义上运行真实程序
2. **自动化验证**：利用执行引擎进行模型检查
3. **错误检测**：识别程序中的未定义行为

Rust 的可执行语义形式化面临独特挑战：

- 复杂的所有权和借用系统
- 编译期与运行时的分离（零成本抽象）
- Unsafe 代码块的存在

---

## 2. KRust (2018)

### 2.1 概述

**KRust** 由上海科技大学研究人员开发，是首个在 K-Framework 中实现的 Rust 可执行语义。

**核心贡献**：

- 证明了 K-Framework 适用于系统级语言
- 为 Rust 形式化社区提供了基线
- 展示了可执行语义的调试和验证潜力

### 2.2 K-Framework 实现

K-Framework 是一种基于重写逻辑的语义框架：

```k
// KRust 中的语法定义示例（简化）
syntax Expr ::= Int
              | Expr "+" Expr  [strict]
              | "let" Id "=" Expr "in" Expr
              | "&" Expr       [strict]
              | "&mut" Expr    [strict]
              | "*" Expr       [strict]
```

**K-Framework 特性**：

- **模块化语法**：易于扩展
- **配置组织**：状态作为嵌套单元格
- **热图/冷图**：控制求值顺序

### 2.3 覆盖的语言特性

KRust 覆盖了 Rust 的核心特性：

| 类别 | 具体特性 |
|------|----------|
| **基础类型** | i32, i64, bool, char, () |
| **复合类型** | struct, array, Vec |
| **控制流** | if/else, while, for, loop |
| **函数** | 定义、调用、递归 |
| **所有权** | move, copy, 借用规则 |
| **借用** | 共享借用、可变借用、生命周期 |

**语法规则示例**（借用检查）：

```k
// 简化的借用规则
rule <k> borrow X => Reference(X, Tag, Mutable) ... </k>
     <env>... X |-> Loc ...</env>
     <borrow-stack> Stack => push(Stack, (Tag, Mutable, Loc)) </borrow-stack>
     <tag-counter> Tag => Tag + 1 </tag-counter>
     requires isValidBorrow(X, Mutable)
```

### 2.4 测试与验证

KRust 使用两组测试验证语义正确性：

1. **手工测试**：针对特定语言特性的测试用例
2. **Rust 官方测试套件**：兼容语法通过的测试

```
测试统计：
- 手工测试: ~100 个
- 官方测试子集: ~200 个
- 通过率: 支持语法范围内的测试 100% 通过
```

### 2.5 局限性

KRust 明确未实现的特性：

1. **带引用字段的结构体**
2. **模式匹配**（作为 switch-case 的泛化）
3. **Trait 对象**（类似 Java 接口）
4. **显式生命周期标注**
5. **复杂闭包**（捕获外部变量）
6. **并发**（多线程程序）
7. **Crates 和模块系统**
8. **Unsafe 代码块**

---

## 3. RustSEM (2024)

### 3.1 概述

**RustSEM** 由新加坡理工大学 Chen Zhe 等人开发，是一个内存级的 Rust 可执行操作语义。

**核心创新**：

- **内存级视角**：直接在内存布局上验证 OBS 不变量
- **更大语言子集**：比 KRust 覆盖更多构造
- **可复用性**：不绑定 Rust 特定构造，可移植到其他语言

### 3.2 内存级形式化

不同于在语言构造级别形式化 OBS，RustSEM 将类型系统的 OBS 不变量映射到内存布局：

```
语言级形式化 (KRust, RustBelt):
  Rust 代码 → 类型检查 → 借用检查 → 操作语义

内存级形式化 (RustSEM):
  Rust 代码 → 内存布局 → OBS 不变量检查 → 内存操作
```

**内存布局示例**：

```rust
struct Point {
    x: i32,  // offset 0
    y: i32,  // offset 4
}
```

```k
// RustSEM 中的内存表示
<Point> ::=
  <x> : i32  @ offset(0)
  <y> : i32  @ offset(4)
  invariant:
    - owner(Point) = owner(x) = owner(y)
    - lifetime(x) = lifetime(y) = lifetime(Point)
```

### 3.3 覆盖范围

RustSEM 覆盖的显著语言构造：

| 特性 | KRust | RustSEM |
|------|-------|---------|
| 基础类型 | ✅ | ✅ |
| 复合类型 | ✅ | ✅ |
| 控制流 | ✅ | ✅ |
| 函数 | ✅ | ✅ |
| 所有权/借用 | ✅ | ✅ |
| 模式匹配 | ❌ | ✅ |
| Trait 系统 | ❌ | 部分 |
| 闭包 | ❌ | 部分 |
| Unsafe 代码 | ❌ | 部分 |
| 混合 safe/unsafe | ❌ | ✅ |

### 3.4 与 Rust 编译器的对比

RustSEM 通过与 rustc 对比验证语义正确性：

```
评估方法：
1. 选取约 700 个测试用例
2. 分别在 rustc 和 RustSEM 上执行
3. 比较输出结果

结果：
- 语义正确性：与 rustc 行为一致
- 差异识别：发现编译器保守性导致的差异
- UB 检测：比 OBS 更强大的内存错误检测
```

### 3.5 应用

RustSEM 的潜在应用：

1. **运行时验证**：执行时检查内存安全
2. **形式化验证**：基于语义的自动证明
3. **教育**：帮助理解 OBS 与内存安全的关系
4. **跨语言复用**：OBS 机制移植到其他语言

---

## 4. Aeneas

### 4.1 概述

**Aeneas** 由 MSR (Microsoft Research) 的 Son Ho 和 Jonathan Protzenko 开发，采用不同的方法：将 Rust 翻译为纯函数式语言进行验证。

**核心思想**：

- 利用 Rust 的类型系统保证
- 将 imperative Rust 翻译为 functional 表示
- 使用成熟的函数式验证工具

### 4.2 函数式翻译方法

Aeneas 不是直接形式化 Rust 的操作语义，而是：

```
Rust 程序 → LLBC (Low-Level Borrow Calculus) → 纯函数式表示 → 验证
```

**翻译示例**：

```rust
// Rust 代码
fn sum(v: &Vec<i32>) -> i32 {
    let mut s = 0;
    for x in v {
        s += x;
    }
    s
}
```

```coq
(* Aeneas 生成的 Coq 代码（概念性） *)
Fixpoint sum (v: list i32) : i32 :=
  fold_left (fun acc x => acc + x) v 0.
```

### 4.3 LLBC 中间语言

LLBC 是 Aeneas 的中间表示，核心特性：

| 特性 | 说明 |
|------|------|
| **Borrow/Loan 显式化** | 将隐式借用转为显式构造 |
| **区域化** | 明确生命周期的开始和结束 |
| **符号化状态** | 使用符号值表示未知数据 |

**LLBC 语法示例**：

```llbc
// 借用表达式
let p = &mut x;  // 在 LLBC 中:
borrow_mut p from x;  // 创建借用
loan x to p;          // x 被冻结

// 使用借用
*p = 42;         // 在 LLBC 中:
write p 42;           // 通过借用写入

// 借用结束
// 隐式在作用域结束时
end_loan p;           // 恢复 x
```

### 4.4 验证流程

Aeneas 的完整验证流程：

```
┌─────────────┐    ┌─────────┐    ┌─────────────┐
│   Rust 源码  │───▶│  LLBC   │───▶│  函数式后端  │
└─────────────┘    └─────────┘    └─────────────┘
                                        │
                                        ▼
                              ┌─────────────────┐
                              │   Coq/HOL4/F*   │
                              │    定理证明器    │
                              └─────────────────┘
                                        │
                                        ▼
                              ┌─────────────────┐
                              │    验证属性      │
                              │  (功能正确性等)  │
                              └─────────────────┘
```

**支持的后端**：

- **Coq**: 交互式证明
- **HOL4**: 高阶逻辑
- **F***: 依赖类型，自动化验证

---

## 5. 对比分析

### 5.1 特性覆盖对比

| 特性 | KRust | RustSEM | Aeneas |
|------|-------|---------|--------|
| 基础语法 | ✅ | ✅ | ✅ |
| 所有权/借用 | ✅ | ✅ | ✅ |
| 模式匹配 | ❌ | ✅ | ✅ |
| Trait | ❌ | 部分 | 部分 |
| 闭包 | ❌ | 部分 | 部分 |
| Unsafe | ❌ | 部分 | ❌ |
| 并发 | ❌ | ❌ | ❌ |
| 宏 | ❌ | ❌ | ❌ |

### 5.2 验证能力对比

| 能力 | KRust | RustSEM | Aeneas |
|------|-------|---------|--------|
| 运行时验证 | ✅ | ✅ | ❌ |
| 模型检查 | ✅ | ✅ | ❌ |
| 功能正确性证明 | ❌ | 部分 | ✅ |
| 终止性证明 | ❌ | ❌ | ✅ |
| 自动化程度 | 中 | 中 | 高 |

### 5.3 工具链集成对比

| 方面 | KRust | RustSEM | Aeneas |
|------|-------|---------|--------|
| Cargo 集成 | ❌ | ❌ | ✅ |
| IDE 支持 | ❌ | ❌ | 部分 |
| CI/CD 集成 | ❌ | ❌ | ✅ |
| 学习曲线 | 陡峭 | 陡峭 | 中等 |

---

## 6. 形式化方法对比

### 6.1 操作语义风格

**KRust/RustSEM - 小步操作语义**：

```
〈e, σ, h〉→ 〈e', σ', h'〉
```

- 详细的逐步求值
- 显式状态转换
- 适合运行时验证

**Aeneas - 指称语义**：

```
〚e〛 : Env → Value
```

- 直接映射到数学对象
- 适合功能正确性证明
- 抽象程度更高

### 6.2 内存模型表示

| 项目 | 内存模型 | 所有权跟踪 |
|------|----------|------------|
| KRust | 抽象堆 | 借用栈 |
| RustSEM | 具体内存布局 | OBS 不变量 |
| Aeneas | 符号化状态 | Borrow/Loan 显式化 |

### 6.3 所有权跟踪机制

**KRust**：

```k
<borrow-stack>
  List<(Tag, Permission, Location)>
</borrow-stack>
```

**RustSEM**：

```k
<memory>
  Map<Location, (Value, Owner, Borrowers)>
</memory>
```

**Aeneas**：

```coq
State := Map<Place, Value>
BorrowState := Map<Place, LoanId>
```

---

## 7. 实际应用建议

### 7.1 教育与学习

**推荐**：RustSEM

- 可视化内存级 OBS 操作
- 理解 OBS 与内存安全的联系

### 7.2 运行时调试

**推荐**：Miri (基于 Tree Borrows)

- 检测真实 Rust 代码中的 UB
- 集成在 Cargo 工具链中

### 7.3 形式化验证

**推荐**：Aeneas

- 自动化程度高
- 生成可验证的函数式代码
- 活跃的开发和社区

### 7.4 语言研究

**推荐**：参考所有三个项目

- KRust 的基础方法
- RustSEM 的内存级视角
- Aeneas 的函数式翻译

---

## 参考文献

### KRust

1. **Wang, F., Song, F., Zhang, M., Zhu, X., & Zhang, J.** (2018). KRust: A Formal Executable Semantics of Rust. *TASE 2018*.

### RustSEM

1. **Chen, Z., et al.** (2024). Formally Understanding Rust's Ownership and Borrowing System at the Memory Level. *Formal Methods in System Design*.

### Aeneas

1. **Ho, S., & Protzenko, J.** (2022). Aeneas: Rust Verification by Functional Translation. *POPL '22*.

2. **Ho, S., Fromherz, A., & Protzenko, J.** (2024). Sound Borrow-Checking for Rust via Symbolic Semantics. *POPL '24*.

### K-Framework

1. **Roşu, G., & Şerbănută, T. F.** (2010). An overview of the K semantic framework. *Journal of Logic and Algebraic Programming*.

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*状态: 完成*
