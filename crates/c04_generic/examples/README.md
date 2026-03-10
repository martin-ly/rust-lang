# C04 泛型与 Trait 示例

本目录包含 Rust 泛型编程和 Trait 系统的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `generics_basics.rs` | 泛型基础 | <T> 语法 |
| `traits_basics.rs` | Trait 基础 | trait 定义与实现 |
| `trait_bounds.rs` | Trait 约束 | where 子句 |
| `generic_functions.rs` | 泛型函数 | 单态化 |
| `generic_structs.rs` | 泛型结构体 | Vec<T>、Option<T> |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `advanced_generics.rs` | 高级泛型 | 关联类型、默认类型 |
| `trait_objects.rs` | Trait 对象 | dyn Trait |
| `generic_lifetimes.rs` | 泛型与生命周期 | T: 'a |
| `blanket_impls.rs` | 全覆盖实现 | impl<T> Trait for T |

### 高级示例 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `hrtb.rs` | 高阶 Trait 边界 | for<'a> |
| `specialization.rs` | 特化 | min_specialization |
| `gats.rs` | 泛型关联类型 | GAT |

---

## 🚀 快速开始

```bash
# 运行泛型基础示例
cargo run --example generics_basics

# 运行 Trait 示例
cargo run --example traits_basics

# 运行高级泛型示例
cargo run --example advanced_generics
```

---

## 🔗 相关文档

- [泛型与 Trait 指南](../docs/README.md)
- [泛型与 Trait 概念族谱](../../../docs/research_notes/GENERICS_TRAITS_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
