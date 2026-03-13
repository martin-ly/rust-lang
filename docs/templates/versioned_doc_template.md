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
> **历史版本**: [归档列表](../../VERSION_INDEX.md)

---

## 📋 版本标识

```yaml
特性名称: {{ feature_name }}
引入版本: {{ introduced_version }}
稳定版本: {{ stable_version }}
废弃版本: {{ deprecated_version | default("N/A") }}
替代特性: {{ replacement | default("N/A") }}
```

---

## 📝 特性概述

{{ feature_description }}

### 核心优势

- {{ advantage_1 }}
- {{ advantage_2 }}
- {{ advantage_3 }}

### 使用场景

{{ use_cases }}

---

## 💻 代码示例

### 基础用法

```rust
// 要求: Rust {{ rust_version }}+ | Edition {{ edition }}
// 文件: crates/{{ crate }}/src/rust_{{ version }}_features.rs

{{ basic_example }}
```

### 进阶用法

```rust
{{ advanced_example }}
```

### 生产级示例

```rust
{{ production_example }}
```

---

## ⚙️ 配置与选项

### Cargo.toml 配置

```toml
[package]
name = "{{ package_name }}"
version = "{{ package_version }}"
rust-version = "{{ rust_version }}"  # 最低 Rust 版本要求
edition = "{{ edition }}"
```

### 特性标志

```toml
[features]
default = []
{{ feature_flag }} = []
```

---

## 📊 性能特征

| 指标 | 数值 | 说明 |
|------|------|------|
| 编译时开销 | {{ compile_time }} | {{ compile_time_note }} |
| 运行时开销 | {{ runtime }} | {{ runtime_note }} |
| 内存占用 | {{ memory }} | {{ memory_note }} |

### 基准测试结果

```text
{{ benchmark_results }}
```

---

## 🔄 版本变更

| 版本 | 变更内容 | 影响级别 |
|------|----------|----------|
| {{ current_version }} | {{ current_change }} | {{ impact }} |
| {{ prev_version }} | {{ prev_change }} | {{ prev_impact }} |

### 迁移指南

从 {{ prev_version }} 迁移到 {{ current_version }}:

```rust
// 旧代码 ({{ prev_version }})
{{ old_code }}

// 新代码 ({{ current_version }})
{{ new_code }}
```

---

## 🔗 相关资源

### 官方资源

- [Rust {{ rust_version }} 发布说明](https://blog.rust-lang.org/)
- [官方文档](https://doc.rust-lang.org/)
- RFC 文档: `{{ rfc_link }}`
- 跟踪 Issue: `{{ tracking_issue }}`

### 项目内资源

- [版本化索引](../../VERSION_INDEX.md)
- 历史版本归档: `../../crates/{{ crate }}/src/archive/`
- 相关 crate: `crates/{{ related_crate }}/`

### 外部资源

- {{ external_resource_1 }}: `{{ external_link_1 }}`
- {{ external_resource_2 }}: `{{ external_link_2 }}`

---

## ⚠️ 注意事项

### 已知限制

{{ known_limitations }}

### 常见陷阱

```rust
// ❌ 错误用法
{{ wrong_usage }}

// ✅ 正确用法
{{ correct_usage }}
```

### 兼容性问题

| 环境 | 兼容性 | 说明 |
|------|--------|------|
| 标准库 | {{ std_compat }} | {{ std_compat_note }} |
| no_std | {{ no_std_compat }} | {{ no_std_compat_note }} |
| WASM | {{ wasm_compat }} | {{ wasm_compat_note }} |

---

## 🧪 测试用例

```rust
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

### 相关概念

- {{ related_concept_1 }}: `{{ concept_link_1 }}`
- {{ related_concept_2 }}: `{{ concept_link_2 }}`

### 设计模式

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

*本文档遵循 [Rust 学习项目版本化规范](../../VERSION_INDEX.md)*
