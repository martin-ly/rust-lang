> **Bloom 层级**: L2-L3 (理解/应用)
> **分级**: [C]

<!--
  Rust 学习项目 - 版本化文档模板
  使用说明:
  1. 复制此模板创建新文档
  2. 替换 {{变量}} 为实际内容
  3. 删除此注释
-->

# {{标题}}

> **Rust 版本**: {{ rust_version }}+ ({{ stability }})
> **Edition**: {{ edition }}
> **最后验证**: {{ validation_date }}
> **状态**: {{ status }}
> **历史版本**: [归档列表](../archive/2026_03_reorganization/VERSION_INDEX.md)

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [{{标题}}](#标题)
  - [📑 目录](#-目录)
  - [📋 版本标识](#-版本标识)
  - [📝 特性概述](#-特性概述)
    - [核心优势](#核心优势)
    - [使用场景](#使用场景)
  - [💻 代码示例](#-代码示例)
    - [基础用法](#基础用法)
    - [进阶用法](#进阶用法)
    - [生产级示例](#生产级示例)
  - [⚙️ 配置与选项](#配置与选项)
    - [Cargo.toml 配置](#cargotoml-配置)
    - [特性标志](#特性标志)
  - [📊 性能特征](#-性能特征)
    - [基准测试结果](#基准测试结果)
  - [🔄 版本变更](#-版本变更)
    - [迁移指南](#迁移指南)
  - [🔗 相关资源](#-相关资源)
    - [官方资源](#官方资源)
    - [项目内资源](#项目内资源)
    - [外部资源](#外部资源)
  - [⚠️ 注意事项](#注意事项)
    - [已知限制](#已知限制)
    - [常见陷阱](#常见陷阱)
    - [兼容性问题](#兼容性问题)
  - [🧪 测试用例](#-测试用例)
  - [📚 深入阅读](#-深入阅读)
    - [相关概念](#相关概念)
    - [设计模式](#设计模式)
  - [权威来源索引](#权威来源索引)

## 📋 版本标识
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```yaml
特性名称: {{ feature_name }}
引入版本: {{ introduced_version }}
稳定版本: {{ stable_version }}
废弃版本: {{ deprecated_version | default("N/A") }}
替代特性: {{ replacement | default("N/A") }}
```

---

## 📝 特性概述
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

{{ feature_description }}

### 核心优势

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- {{ advantage_1 }}
- {{ advantage_2 }}
- {{ advantage_3 }}

### 使用场景

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

{{ use_cases }}

---

## 💻 代码示例
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 基础用法

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

```rust,ignore
// 要求: Rust {{ rust_version }}+ | Edition {{ edition }}
// 文件: crates/{{ crate }}/src/rust_{{ version }}_features.rs

{{ basic_example }}
```

### 进阶用法

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

```rust,ignore
{{ advanced_example }}
```

### 生产级示例

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```rust,ignore
{{ production_example }}
```

---

## ⚙️ 配置与选项
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### Cargo.toml 配置

> **来源: [ACM](https://dl.acm.org/)**

```toml
[package]
name = "{{ package_name }}"
version = "{{ package_version }}"
rust-version = "{{ rust_version }}"  # 最低 Rust 版本要求
edition = "{{ edition }}"
```

### 特性标志
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```toml
[features]
default = []
{{ feature_flag }} = []
```

---

## 📊 性能特征
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 指标 | 数值 | 说明 |
|------|------|------|
| 编译时开销 | {{ compile_time }} | {{ compile_time_note }} |
| 运行时开销 | {{ runtime }} | {{ runtime_note }} |
| 内存占用 | {{ memory }} | {{ memory_note }} |

### 基准测试结果
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
{{ benchmark_results }}
```

---

## 🔄 版本变更
>
> **[来源: [crates.io](https://crates.io/)]**

| 版本 | 变更内容 | 影响级别 |
|------|----------|----------|
| {{ current_version }} | {{ current_change }} | {{ impact }} |
| {{ prev_version }} | {{ prev_change }} | {{ prev_impact }} |

### 迁移指南
>
> **[来源: [docs.rs](https://docs.rs/)]**

从 {{ prev_version }} 迁移到 {{ current_version }}:

```rust,ignore
// 旧代码 ({{ prev_version }})
{{ old_code }}

// 新代码 ({{ current_version }})
{{ new_code }}
```

---

## 🔗 相关资源
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 官方资源
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [Rust {{ rust_version }} 发布说明](https://blog.rust-lang.org/)
- [官方文档](https://doc.rust-lang.org/)
- RFC 文档: `{{ rfc_link }}`
- 跟踪 Issue: `{{ tracking_issue }}`

### 项目内资源
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [版本化索引](../archive/2026_03_reorganization/VERSION_INDEX.md)
- 历史版本归档: `../../crates/{{ crate }}/src/archive/`
- 相关 crate: `crates/{{ related_crate }}/`

### 外部资源
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- {{ external_resource_1 }}: `{{ external_link_1 }}`
- {{ external_resource_2 }}: `{{ external_link_2 }}`

---

## ⚠️ 注意事项
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 已知限制
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

{{ known_limitations }}

### 常见陷阱
>
> **[来源: [crates.io](https://crates.io/)]**

```rust,ignore
// ❌ 错误用法
{{ wrong_usage }}

// ✅ 正确用法
{{ correct_usage }}
```

### 兼容性问题
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 环境 | 兼容性 | 说明 |
|------|--------|------|
| 标准库 | {{ std_compat }} | {{ std_compat_note }} |
| no_std | {{ no_std_compat }} | {{ no_std_compat_note }} |
| WASM | {{ wasm_compat }} | {{ wasm_compat_note }} |

---

## 🧪 测试用例
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_{{ feature_name }}_basic() {
        {{ test_code }}
    }

    #[test]
    fn test_{{ feature_name }}_edge_cases() {
        {{ edge_case_test }}
    }
}
```

---

## 📚 深入阅读
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 相关概念
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- {{ related_concept_1 }}: `{{ concept_link_1 }}`
- {{ related_concept_2 }}: `{{ concept_link_2 }}`

### 设计模式
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- {{ pattern_1 }}: `../../crates/c09_design_pattern/src/`
- {{ pattern_2 }}: `../../crates/c09_design_pattern/src/`

---

<!-- 文档底部元数据 -->

---

**文档元数据**:

| 属性 | 值 |
|------|-----|
| 创建日期 | {{ created_date }} |
| 最后更新 | {{ updated_date }} |
| 维护者 | {{ maintainer }} |
| 审核状态 | {{ review_status }} |
| 版本标签 | {{ version_tags }} |

---

*本文档遵循 [Rust 学习项目版本化规范](../archive/2026_03_reorganization/VERSION_INDEX.md)*

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

---
