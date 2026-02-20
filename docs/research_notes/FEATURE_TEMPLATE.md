# Rust 特性精简模板

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **目标**: 为 92 项特性中非核心特性建立统一「概念→形式化引用→反例」精简模板

---

## 模板结构

除 [CORE_FEATURES_FULL_CHAIN](CORE_FEATURES_FULL_CHAIN.md) 所列 13 项核心特性外，其余特性采用以下**精简模板**：

| 列 | 必填 | 说明 |
| :--- | :--- | :--- |
| **概念** | 是 | 特性一句话定义；与 RUST_193 对应 |
| **形式化引用** | 若有 | 指向 formal_methods、type_theory、toolchain 等 Def/定理 |
| **反例** | 若有 | 违反后果；编译错误或 UB |

---

## 模板应用示例

### 示例 1：if/else（控制流族）

| 概念 | 形式化引用 | 反例 |
| :--- | :--- | :--- |
| 条件分支；表达式；必须返回同类型 | - | 分支类型不一致编译错误 |

### 示例 2：声明宏（宏族）

| 概念 | 形式化引用 | 反例 |
| :--- | :--- | :--- |
| 代码生成、DSL；macro_rules!、卫生宏 | - | 意外捕获、宏展开错误 |

### 示例 3：mod（模块族）

| 概念 | 形式化引用 | 反例 |
| :--- | :--- | :--- |
| 代码组织；mod、文件即模块 | [01_formal_composition](software_design_theory/04_compositional_engineering/01_formal_composition.md) Def 1.2 依赖 | 循环依赖编译失败 |

### 示例 4：const（常量族）

| 概念 | 形式化引用 | 反例 |
| :--- | :--- | :--- |
| 编译期常量；const X: T = ... | [advanced_types](type_theory/advanced_types.md) | 非常量表达式编译错误 |

---

## 与 RUST_193 的对应

[RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 中 92 项特性的表格列「动机」「设计决策」「形式化」「反例」与本模板一致：

- **概念** ← 动机 + 设计决策（合并为一句话）
- **形式化引用** ← 形式化列
- **反例** ← 反例列

**核心特性**（13 项）采用完整链，见 [CORE_FEATURES_FULL_CHAIN](CORE_FEATURES_FULL_CHAIN.md)。

**其余特性**（79 项）采用本精简模板，数据见 [RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 各表。

---

## 索引

| 文档 | 用途 |
| :--- | :--- |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 92 项特性完整表格 |
| [CORE_FEATURES_FULL_CHAIN](CORE_FEATURES_FULL_CHAIN.md) | 13 项核心特性完整链 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-12
