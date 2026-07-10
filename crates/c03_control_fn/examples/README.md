# C03 控制流与函数示例

本目录包含 Rust 控制流和函数的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `control_flow_basics.rs` | 控制流基础 | if/else、loop、while、for |
| `functions_basics.rs` | 函数基础 | 定义、参数、返回值 |
| `closures_basics.rs` | 闭包基础 | \|x\| x + 1 |
| `iterators_basics.rs` | 迭代器基础 | iter()、next() |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `advanced_closures.rs` | 高级闭包 | Fn/FnMut/FnOnce |
| `iterator_adapters.rs` | 迭代器适配器 | map、filter、fold |
| `control_flow_patterns.rs` | 控制流模式 | ? 运算符、try 块 |
| `recursion_patterns.rs` | 递归模式 | 尾递归、迭代转换 |

---

## 🚀 快速开始

```bash
# 运行控制流示例
cargo run --example control_flow_basics

# 运行闭包示例
cargo run --example closures_basics

# 运行迭代器示例
cargo run --example iterator_adapters
```
---

## 🆕 Rust 1.95.0 特性示例

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `cfg_select_demo.rs` | `cfg_select!` 宏 | 编译期条件选择 | `cargo run --example cfg_select_demo` |

---

## 🔗 相关文档

- [控制流与函数指南](../docs/README.md)
- [Rust 1.95 特性速查表](../../../docs/02_reference/quick_reference/rust_195_features_cheatsheet.md)

---

*示例基于 Rust 1.97.0+，Edition 2024*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
