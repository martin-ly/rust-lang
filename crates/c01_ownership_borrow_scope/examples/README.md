# C01 所有权、借用与作用域示例

本目录包含所有权系统的核心示例代码，展示 Rust 最独特的内存安全机制。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `ownership_basics.rs` | 所有权基础规则 | 所有权转移、Copy trait |
| `borrow_checker_demo.rs` | 借用检查器演示 | 不可变/可变借用规则 |
| `scope_lifetime.rs` | 作用域与生命周期 | 词法作用域、NLL |
| `string_slice.rs` | String 与 &str | 堆分配 vs 切片 |
| `move_semantics.rs` | 移动语义详解 | Move、Clone、Copy |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `advanced_ownership_patterns.rs` | 高级所有权模式 | 内部可变性模式 |
| `lifetime_annotations.rs` | 显式生命周期标注 | 'a, 生命周期省略规则 |
| `reference_rules.rs` | 引用规则详解 | 借用检查器算法 |
| `drop_order.rs` | Drop 顺序演示 | RAII、析构顺序 |
| `rc_refcell_demo.rs` | Rc 和 RefCell | 运行时引用计数 |

### 高级示例 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `advanced_scope_examples.rs` | 高级作用域技巧 | 非词法生命周期 |
| `aeneas_first_intro.rs` | Aeneas 验证入门 | 形式化验证 |
| `ownership_verification.rs` | 所有权验证示例 | 定理证明 |

---

## 🚀 快速开始

```bash
# 运行基础示例
cargo run --example ownership_basics

# 运行借用检查器演示
cargo run --example borrow_checker_demo

# 运行生命周期示例
cargo run --example scope_lifetime
```

---

## 📖 学习路径

1. **初学者**：从 `ownership_basics.rs` 开始
2. **进阶**：学习 `borrow_checker_demo.rs` 理解借用规则
3. **高级**：研究 `advanced_ownership_patterns.rs`

---

## 🔗 相关文档

- [所有权系统详解](../docs/tier_02_guides/01_ownership_system_deep_dive.md)
- [借用检查器形式化证明](../../../docs/research_notes/formal_methods/borrow_checker_proof.md)
- [所有权概念族谱](../../../docs/research_notes/OWNERSHIP_CONCEPT_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
