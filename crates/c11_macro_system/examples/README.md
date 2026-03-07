# C11 宏系统示例

本目录包含 Rust 宏编程的核心示例代码。

---

## 📚 示例列表

### 声明宏 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `declarative_basics.rs` | 声明宏基础 | macro_rules! |
| `vec_macro.rs` | vec! 宏实现 | 重复模式 |
| `println_impl.rs` | println! 实现 | 格式化 |

### 过程宏 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `derive_macro.rs` | 派生宏 | #[derive] |
| `attribute_macro.rs` | 属性宏 | #[attribute] |
| `function_macro.rs` | 函数式宏 | custom!() |

### 高级宏技巧 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `hygiene_demo.rs` | 卫生宏 | 作用域隔离 |
| `recursive_macros.rs` | 递归宏 | TT  muncher |
| `type_driven_macros.rs` | 类型驱动宏 | 编译期计算 |

---

## 🚀 快速开始

```bash
# 运行声明宏示例
cargo run --example declarative_basics

# 查看派生宏示例（在 proc_macro crate 中）
cargo expand --package c11_macro_system
```

---

## 🔗 相关文档

- [宏系统指南](../docs/)
- [宏系统概念族谱](../../../docs/research_notes/MACRO_SYSTEM_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
