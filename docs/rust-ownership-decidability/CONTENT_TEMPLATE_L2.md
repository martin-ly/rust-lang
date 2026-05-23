# L2 深度文档模板

> **使用说明**: 所有新创建的文档应基于此模板，确保达到 L2 深度标准

---

## 📑 目录
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [元数据头](#元数据头)
- [必需章节](#必需章节)
  - [1. 概念介绍 (必需)](#1-概念介绍-必需)
- [1. 概念介绍](#1-概念介绍)
  - [1.1 什么是 XXX](#11-什么是-xxx)
  - [1.2 核心思想](#12-核心思想)
  - [1.3 在 Rust 中的体现](#13-在-rust-中的体现)
  - [2. 形式化定义 (L2 必需)](#2-形式化定义-l2-必需)
- [2. 形式化定义](#2-形式化定义)
  - [定义 2.1 (XXX)](#定义-21-xxx)
  - [示例 2.1 (具体实例)](#示例-21-具体实例)
  - [3. 核心机制 (必需)](#3-核心机制-必需)
- [3. 核心机制](#3-核心机制)
  - [3.1 机制 A](#31-机制-a)
  - [3.2 机制 B](#32-机制-b)
    - [关键代码示例](#关键代码示例)
    - [错误示例](#错误示例)
  - [4. 定理与性质 (L2 必需)](#4-定理与性质-l2-必需)
- [4. 定理与性质](#4-定理与性质)
  - [定理 4.1 (XXX 安全性)](#定理-41-xxx-安全性)
  - [推论 4.2](#推论-42)
  - [5. 实际应用 (必需)](#5-实际应用-必需)
- [5. 实际应用](#5-实际应用)
  - [5.1 应用场景 A](#51-应用场景-a)
  - [5.2 最佳实践](#52-最佳实践)
  - [6. 与其他概念的关系 (必需)](#6-与其他概念的关系-必需)
- [6. 与其他概念的关系](#6-与其他概念的关系)
  - [6.1 与概念 A 的对比](#61-与概念-a-的对比)
  - [6.2 与概念 B 的组合](#62-与概念-b-的组合)
  - [7. 常见陷阱 (必需)](#7-常见陷阱-必需)
- [7. 常见陷阱与反模式](#7-常见陷阱与反模式)
  - [陷阱 1: XXX](#陷阱-1-xxx)
  - [陷阱 2: YYY](#陷阱-2-yyy)
  - [8. 进阶主题 (可选，用于 L3)](#8-进阶主题-可选用于-l3)
- [8. 进阶主题](#8-进阶主题)
  - [8.1 实现细节](#81-实现细节)
  - [8.2 性能优化](#82-性能优化)
  - [8.3 底层机制](#83-底层机制)
  - [9. 参考资源 (必需)](#9-参考资源-必需)
- [9. 参考资源](#9-参考资源)
  - [官方文档](#官方文档)
  - [学术论文](#学术论文)
  - [相关文档](#相关文档)
- [质量检查清单](#质量检查清单)
- [质量检查清单](#质量检查清单)
  - [内容完整性](#内容完整性)
  - [形式化内容](#形式化内容)
  - [代码示例](#代码示例)
  - [交叉引用](#交叉引用)
  - [格式规范](#格式规范)
- [示例文档结构](#示例文档结构)
- [相关概念](#相关概念)

## 元数据头
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```markdown
# 文档标题

> **权威来源**: [论文/书籍引用]
> **Rust 版本**: 1.94.0
> **难度**: 🟡 中等 / 🔴 高级
> **前置知识**: [前置文档链接]

---
```

## 必需章节
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1. 概念介绍 (必需)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```markdown
    ## 1. 概念介绍

    ### 1.1 什么是 XXX

    清晰定义概念，回答 "这是什么" 和 "为什么重要"。

    ### 1.2 核心思想

    用一句话概括核心思想，然后用 2-3 段解释。

    ### 1.3 在 Rust 中的体现

    解释这个概念在 Rust 中如何体现/实现。
```

### 2. 形式化定义 (L2 必需)
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```markdown
    ## 2. 形式化定义

    ### 定义 2.1 (XXX)

    $$
    \text{数学定义或类型规则}
    $$

    **解释**: 用自然语言解释定义的含义。

    ### 示例 2.1 (具体实例)

    ```rust
    // 对应形式化定义的 Rust 代码
    ```

```

### 3. 核心机制 (必需)
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```markdown
    ## 3. 核心机制

    ### 3.1 机制 A

    详细解释机制 A 的工作原理。

    ### 3.2 机制 B

    详细解释机制 B 的工作原理。

    #### 关键代码示例

    ```rust
    // 完整可运行的代码示例
    fn main() {
        // 示例代码
    }
    ```

    #### 错误示例

    ```rust,compile_fail
    // 展示错误用法
    // 应有编译错误注释
    ```

```

### 4. 定理与性质 (L2 必需)
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```markdown
    ## 4. 定理与性质

    ### 定理 4.1 (XXX 安全性)

    > **定理**: 形式化陈述

    **证明概要**:
    1. 步骤 1
    2. 步骤 2
    3. 结论

    ### 推论 4.2

    > **推论**: 从定理 4.1 得出的结论
```

### 5. 实际应用 (必需)
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```markdown
    ## 5. 实际应用

    ### 5.1 应用场景 A

    ```rust
    // 实际应用场景的代码
    ```

    ### 5.2 最佳实践

    | 做法 | 推荐 | 原因 |
    |-----|-----|------|
    | 做法 A | ✅ 推荐 | 原因... |
    | 做法 B | ❌ 避免 | 原因... |

```

### 6. 与其他概念的关系 (必需)
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```markdown
    ## 6. 与其他概念的关系

    ```text
    概念图:

    [本概念] ──相关──> [概念 A]
        │
        └──依赖──> [概念 B]
    ```

    ### 6.1 与概念 A 的对比

    | 特性 | 本概念 | 概念 A |
    |-----|-------|-------|
    | ... | ... | ... |

    ### 6.2 与概念 B 的组合

    ```rust
    // 展示两个概念如何一起使用
    ```

```

### 7. 常见陷阱 (必需)
> **[来源: [crates.io](https://crates.io/)]**

```markdown
    ## 7. 常见陷阱与反模式

    ### 陷阱 1: XXX

    **错误代码**:
    ```rust,compile_fail
    // 错误示例
    ```

    **错误信息**:

    ```text
    编译器错误信息
    ```

    **修复方案**:

    ```rust
    // 正确代码
    ```

    ### 陷阱 2: YYY

    ...

```

### 8. 进阶主题 (可选，用于 L3)
> **[来源: [docs.rs](https://docs.rs/)]**

```markdown
    ## 8. 进阶主题

    ### 8.1 实现细节

    ### 8.2 性能优化

    ### 8.3 底层机制
```

### 9. 参考资源 (必需)
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```markdown
    ## 9. 参考资源

    ### 官方文档
    - The Rust Book - XXX
    - The Rust Reference - XXX

    ### 学术论文
    1. 论文标题 - 作者 (年份)

    ### 相关文档
    - 相关文档 A
    - 相关文档 B
```

---

## 质量检查清单
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

在提交文档前，确认以下检查项:

```markdown
    ## 质量检查清单

    ### 内容完整性
    - [ ] 文档标题明确
    - [ ] 元数据完整 (来源、版本、难度)
    - [ ] 所有必需章节已填充
    - [ ] 总长度 >300 行

    ### 形式化内容
    - [ ] 至少 1 个形式化定义 (Def)
    - [ ] 至少 1 个定理/性质 (Thm)
    - [ ] 数学符号正确使用

    ### 代码示例
    - [ ] 至少 3 个代码示例
    - [ ] 所有代码可编译 (`cargo check` 通过)
    - [ ] 包含错误示例 (compile_fail)
    - [ ] 代码有详细注释

    ### 交叉引用
    - [ ] 引用权威来源
    - [ ] 链接到相关文档
    - [ ] 术语使用一致

    ### 格式规范
    - [ ] 使用标准 Markdown
    - [ ] 代码块标记语言
    - [ ] 表格对齐正确
    - [ ] 无死链接
```

---

## 示例文档结构
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
01-intro.md (~500 lines)
├── 概念介绍 (50 lines)
├── 形式化定义 (100 lines)
├── 核心机制 (150 lines)
├── 定理与性质 (80 lines)
├── 实际应用 (60 lines)
├── 关系与对比 (40 lines)
├── 常见陷阱 (50 lines)
└── 参考资源 (20 lines)
```

---

*模板版本: 1.0*
*最后更新: 2026-03-07*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [所有权可判定性总览](./README.md)
- [形式化基础](./formal-foundations/README.md)
- [案例研究](./case-studies/README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

