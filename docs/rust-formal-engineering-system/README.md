# Rust 形式化工程系统

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **说明**: 本目录为**单一索引层**，形式化理论内容已整合至 [研究笔记](../research_notes/) 及各 crates。子目录 README 仅为占位重定向，请以 [00_master_index.md](./00_master_index.md) 为完整导航入口。
> **docs 全结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.9

---

## 导航说明

本项目的 Rust 形式化理论与工程文档已整合至 **研究笔记系统**。请使用以下入口访问：

### 核心入口

| 模块 | 入口路径 | 说明 |
| :--- | :--- | :--- || **形式化方法** | [research_notes/formal_methods/](../research_notes/formal_methods/) | 所有权模型、借用检查器、生命周期、Pin、异步状态机 |
| **类型理论** | [research_notes/type_theory/](../research_notes/type_theory/) | 类型系统基础、Trait 形式化、型变理论、生命周期 |
| **主索引** | [00_master_index.md](./00_master_index.md) | 完整模块映射与导航 |

### 快速跳转

- [所有权与借用理论](../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
- [类型系统基础](../research_notes/type_theory/type_system_foundations.md)
- [Trait 系统形式化](../research_notes/type_theory/trait_system_formalization.md)
- [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)
- [型变理论](../research_notes/type_theory/variance_theory.md)
- [形式化验证工具](../research_notes/TOOLS_GUIDE.md)

---

## 相关文档

- [研究笔记主入口](../research_notes/README.md)
- [思维表征方式](../THINKING_REPRESENTATION_METHODS.md)
- [多维概念矩阵](../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)
