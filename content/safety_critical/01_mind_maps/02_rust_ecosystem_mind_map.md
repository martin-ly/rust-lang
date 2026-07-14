# Rust生态系统思维导图

**EN**: Rust Ecosystem Mind Map
**Summary**: Rust生态系统思维导图 Rust Ecosystem Mind Map.

> **权威来源**: 本文件为 `content/` 专题深度内容入口；通用 Rust 概念解释请见 [`concept/06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md`](../../../concept/06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md)。若 `concept/` 已覆盖相同主题，本文仅保留应用场景、案例与决策树，不重复概念推导。
> **Bloom 层级**: L4-L6
>
> 本文内容迁移自历史归档，已按 `AGENTS.md` 规则保留为安全关键领域专题实践。

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust生态系统思维导图](#rust生态系统思维导图)
  - [📑 目录](#-目录)
  - [思维导图说明](#思维导图说明)
    - [核心维度](#核心维度)
    - [核心安全保证](#核心安全保证)
    - [应用领域](#应用领域)
    - [认证工具链](#认证工具链)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 思维导图说明
>
> **[来源: Rust Official Docs]**

### 核心维度
>
> **[来源: Rust Official Docs]**

1. **学术理论基础**: Tree Borrows (PLDI 2025), Miri (POPL 2026)
2. **工具链与语言**: Rust 1.94/95, core库认证
3. **工业应用标准**: ISO 26262, IEC 61508, DO-178C
4. **国防航天应用**: NASA cFS, ESA空间系统
5. **教育体系**: Stanford CS110L, CMU 15-411

### 核心安全保证
>
> **[来源: Rust Official Docs]**

- 所有权系统
- 借用检查器
- 生命周期管理
- 类型安全
- 并发安全

### 应用领域
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- 汽车 (ASIL D)
- 航空航天 (DAL A-D)
- 医疗设备 (Class C)
- 工业控制 (SIL 4)
- 国防军事

### 认证工具链
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- Ferrocene (TÜV SÜD认证)
- AdaCore GNAT Pro
- High Assurance Rust

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: ISO 26262 - Functional Safety]**
> **[来源: IEC 61508 - Safety Standards]**
> **[来源: MISRA Rust Guidelines]**
> **[来源: Ferrocene Language Specification]**

---
