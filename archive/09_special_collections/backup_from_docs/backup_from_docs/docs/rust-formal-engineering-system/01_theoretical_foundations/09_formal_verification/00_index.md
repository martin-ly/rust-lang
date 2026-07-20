# 形式化验证（Formal Verification）索引


## 📊 目录

- [目的](#目的)
- [核心概念](#核心概念)
- [与 Rust 的关联](#与-rust-的关联)
- [术语（Terminology）](#术语terminology)
- [形式化与证明（Formalization）](#形式化与证明formalization)
- [实践与样例（Practice）](#实践与样例practice)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 介绍 Rust 形式化验证的理论基础与工具链。
- 提供形式化验证在 Rust 项目中的应用指南。

## 核心概念

- 形式化方法：数学方法证明程序正确性
- 模型检查：自动验证有限状态系统
- 定理证明：交互式证明系统
- 静态分析：编译时程序分析
- 契约编程：前置条件、后置条件、不变量

## 与 Rust 的关联

- 类型系统：编译时保证内存安全
- 借用检查：防止数据竞争和悬垂指针
- 形式化工具：Kani、Prusti、Creusot
- 属性测试：基于属性的随机测试

## 术语（Terminology）

- 形式化验证（Formal Verification）、模型检查（Model Checking）
- 定理证明（Theorem Proving）、静态分析（Static Analysis）
- 契约（Contract）、不变量（Invariant）
- 属性（Property）、规格（Specification）

## 形式化与证明（Formalization）

- 类型安全：`Γ ⊢ e : τ` 类型判断
- 内存安全：所有权不变式与借用规则
- 并发安全：数据竞争自由性
- 终止性：程序终止性证明

## 实践与样例（Practice）

- 形式化验证工具：参见 [crates/c04_generic](../../../crates/c04_generic/)
- 并发验证：[crates/c05_threads](../../../crates/c05_threads/)
- 异步验证：[crates/c06_async](../../../crates/c06_async/)

## 相关索引

- 类型系统：[`../01_type_system/00_index.md`](../01_type_system/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 研究议程：[`../../09_research_agenda/00_index.md`](../../09_research_agenda/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
