# C02 类型系统示例

本目录包含 Rust 类型系统的核心示例代码，从基础类型到高级类型特性。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `basic_types.rs` | 基础类型演示 | 标量类型、复合类型 |
| `type_inference.rs` | 类型推断 | 类型推导机制 |
| `custom_types.rs` | 自定义类型 | struct、enum |
| `pattern_matching.rs` | 模式匹配 | match、if let |
| `type_aliases.rs` | 类型别名 | type 关键字 |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `advanced_type_system.rs` | 高级类型特性 | 关联类型、类型别名 |
| `newtype_pattern.rs` | Newtype 模式 | 类型封装 |
| `phantom_types.rs` | 幽灵类型 | PhantomData |
| `exhaustiveness_checking.rs` | 穷尽性检查 | 编译期验证 |
| `never_type.rs` | Never 类型 | ! 类型 |

---

## 🚀 快速开始

```bash
# 运行基础类型示例
cargo run --example basic_types

# 运行模式匹配示例
cargo run --example pattern_matching

# 运行高级类型示例
cargo run --example advanced_type_system
```

---

## 📖 学习路径

1. **基础**：理解 Rust 的基础类型系统
2. **进阶**：掌握自定义类型和模式匹配
3. **高级**：学习类型系统的高级技巧

---

## 🔗 相关文档

- [类型系统基础](../docs/tier_01_foundations/)
- [类型系统概念族谱](../../../docs/research_notes/TYPE_SYSTEM_CONCEPT_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
