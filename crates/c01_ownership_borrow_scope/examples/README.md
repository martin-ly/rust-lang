# C01 所有权、借用与作用域 - 示例中心

> **创建日期**: 2025-10-22
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 所有权系统是 Rust 最核心的特性，本示例集展示从基础规则到高级模式的完整所有权管理技术。

---

## 示例概览

本目录包含 **20+ 个核心示例**，涵盖所有权系统的所有重要概念：

- ✅ 所有权三大规则
- ✅ 借用检查器机制
- ✅ 生命周期管理
- ✅ 智能指针使用
- ✅ 内部可变性模式
- ✅ 形式化验证入门

---

## 示例分类导航

### 基础示例 ⭐

适合 Rust 初学者，理解核心概念。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `ownership_basics.rs` | 所有权基础规则 | 所有权转移、Copy trait | `cargo run --example ownership_basics` |
| `borrow_checker_demo.rs` | 借用检查器演示 | 不可变/可变借用规则 | `cargo run --example borrow_checker_demo` |
| `scope_lifetime.rs` | 作用域与生命周期 | 词法作用域、NLL | `cargo run --example scope_lifetime` |
| `string_slice.rs` | String 与 &str | 堆分配 vs 切片 | `cargo run --example string_slice` |
| `move_semantics.rs` | 移动语义详解 | Move、Clone、Copy | `cargo run --example move_semantics` |

### 进阶示例 ⭐⭐

适合有一定基础的开发者，深入理解借用规则。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `advanced_ownership_patterns.rs` | 高级所有权模式 | 内部可变性模式 | `cargo run --example advanced_ownership_patterns` |
| `lifetime_annotations.rs` | 显式生命周期标注 | 'a, 生命周期省略规则 | `cargo run --example lifetime_annotations` |
| `reference_rules.rs` | 引用规则详解 | 借用检查器算法 | `cargo run --example reference_rules` |
| `drop_order.rs` | Drop 顺序演示 | RAII、析构顺序 | `cargo run --example drop_order` |
| `rc_refcell_demo.rs` | Rc 和 RefCell | 运行时引用计数 | `cargo run --example rc_refcell_demo` |

### 高级示例 ⭐⭐⭐

适合高级开发者，掌握复杂模式。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `advanced_scope_examples.rs` | 高级作用域技巧 | 非词法生命周期 | `cargo run --example advanced_scope_examples` |
| `aeneas_first_intro.rs` | Aeneas 验证入门 | 形式化验证 | `cargo run --example aeneas_first_intro` |
| `ownership_verification.rs` | 所有权验证示例 | 定理证明 | `cargo run --example ownership_verification` |

### Rust 1.93.0 特性示例 ⭐ NEW

展示最新 Rust 版本的所有权相关改进。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rust_192_features_demo.rs` | Rust 1.93.0 特性演示 | MaybeUninit、原始引用 | `cargo run --example rust_192_features_demo` |
| `rust_191_features_demo.rs` | Rust 1.91 特性演示 | 借用检查优化 | `cargo run --example rust_191_features_demo` |
| `rust_190_rich_practical_examples.rs` | 丰富实战示例 | 综合案例 | `cargo run --example rust_190_rich_practical_examples` |

---

## 如何运行示例

### 基础运行

```bash
# 进入模块目录
cd crates/c01_ownership_borrow_scope

# 运行基础示例
cargo run --example ownership_basics

# 运行借用检查器演示
cargo run --example borrow_checker_demo

# 运行生命周期示例
cargo run --example scope_lifetime
```

### 运行测试

```bash
# 运行所有测试
cargo test -p c01_ownership_borrow_scope

# 运行特定示例测试
cargo test --example rust_190_rich_practical_examples

# 运行 Rust 1.93.0 特性测试
cargo test --test rust_192_comprehensive_tests
```

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench -p c01_ownership_borrow_scope

# 运行 Rust 1.93.0 特性基准测试
cargo bench --bench rust_192_benchmarks
```

---

## 学习建议

### 初学者路径 (第1-2周)

1. **从所有权基础开始**

   ```bash
   cargo run --example ownership_basics
   ```

   - 理解所有权三大规则
   - 学习 Copy vs Move
   - 掌握所有权转移

2. **学习借用规则**

   ```bash
   cargo run --example borrow_checker_demo
   ```

   - 不可变借用 (`&T`)
   - 可变借用 (`&mut T`)
   - 借用检查器原理

3. **理解生命周期**

   ```bash
   cargo run --example scope_lifetime
   cargo run --example lifetime_annotations
   ```

   - 词法作用域
   - 生命周期省略规则
   - 显式标注

### 进阶路径 (第3-4周)

1. **掌握智能指针**

   ```bash
   cargo run --example rc_refcell_demo
   ```

   - `Box<T>`
   - `Rc<T>` / `Arc<T>`
   - `RefCell<T>` / `Mutex<T>`

2. **学习高级模式**

   ```bash
   cargo run --example advanced_ownership_patterns
   cargo run --example advanced_scope_examples
   ```

   - 内部可变性
   - 自引用结构
   - 非词法生命周期

### 高级路径 (第5周+)

1. **形式化验证入门**

   ```bash
   cargo run --example aeneas_first_intro
   cargo run --example ownership_verification
   ```

   - Aeneas 验证工具
   - 定理证明基础
   - 形式化语义

2. **Rust 1.93.0 新特性**

   ```bash
   cargo run --example rust_192_features_demo
   ```

   - `MaybeUninit` 改进
   - 原始引用安全访问
   - 更好的错误提示

---

## 关键概念速查

### 所有权规则

```rust
// 规则1: 每个值都有一个所有者
let s = String::from("hello"); // s 是所有者

// 规则2: 只有一个所有者
let s2 = s; // s 的所有权转移到 s2，s 不再有效

// 规则3: 所有者离开作用域，值被释放
} // s2 在这里被释放
```

### 借用规则

```rust
// 可以有多个不可变借用
let r1 = &s;
let r2 = &s;

// 或一个可变借用
let r3 = &mut s;

// 但不能同时存在
```

### 生命周期标注

```rust
// 显式生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 结构体中的生命周期
struct ImportantExcerpt<'a> {
    part: &'a str,
}
```

---

## 相关文档

### 模块文档

- [模块主页](../README.md) - 完整学习指南
- [文档中心](../docs/README.md) - 详细文档导航
- [主索引](../docs/00_MASTER_INDEX.md) - 文档完整索引

### 理论文档

- [所有权系统详解](../docs/tier_02_guides/01_所有权系统详解.md)
- [借用检查器形式化证明](../../../docs/research_notes/formal_methods/borrow_checker_proof.md)
- [所有权概念族谱](../../../docs/research_notes/OWNERSHIP_CONCEPT_MINDMAP.md)

### 外部资源

- [The Rust Book - 所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rust  nomicon](https://doc.rust-lang.org/nomicon/)
- [Rust  by Example](https://doc.rust-lang.org/rust-by-example/scope.html)

---

## 常见问题

### Q: 为什么我的代码出现 "use of moved value" 错误？

A: 这意味着你尝试使用一个已经转移了所有权的值。考虑使用引用 (`&T`) 或克隆 (`Clone`)。

### Q: 如何解决 "cannot borrow as mutable more than once"？

A: Rust 不允许同时存在多个可变借用。重新设计代码结构，缩小借用范围。

### Q: 什么时候需要显式生命周期标注？

A: 当编译器无法推断生命周期关系时。通常涉及多个引用作为参数或返回值。

---

*示例基于 Rust 1.94+，Edition 2024*:

[返回模块主页](../README.md) | [返回上级](../README.md)
