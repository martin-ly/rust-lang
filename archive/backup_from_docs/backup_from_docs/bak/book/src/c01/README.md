# C01: 所有权、借用与作用域

> Rust 最核心、最独特的特性

---

## 📚 本模块内容

本模块深入讲解 Rust 的所有权系统，这是 Rust 实现内存安全和并发安全的基础。

### 主要主题

- **所有权 (Ownership)**: 每个值都有一个所有者
- **借用 (Borrowing)**: 临时使用而不获取所有权
- **作用域 (Scope)**: 变量的有效范围
- **生命周期 (Lifetimes)**: 引用的有效期

---

## 🎯 学习目标

学完本模块后，你将能够：

- ✅ 理解 Rust 的所有权系统
- ✅ 正确使用借用和引用
- ✅ 掌握可变和不可变借用规则
- ✅ 理解和标注生命周期
- ✅ 避免常见的所有权错误

---

## 📖 学习路径

推荐按以下顺序学习：

1. **[基础概念](./foundations.md)** - 理论基础
2. **[实践指南](./guides.md)** - 实用技巧
3. **[代码示例](./examples.md)** - 交互式示例 ⭐
4. **[知识图谱](./knowledge-graph.md)** - 概念关系

---

## 🚀 快速开始

### 第一个示例

理解所有权的基本规则：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权转移给 s2
    
    println!("{}", s2);  // 正确
    // println!("{}", s1);  // 编译错误！
}
```

**点击右上角的 "Run" 按钮运行这个示例！**

### 核心概念预览

**所有权三规则**:

1. Rust 中每个值都有一个所有者
2. 值在任一时刻只能有一个所有者
3. 当所有者离开作用域时，值被释放

**借用规则**:

- 同一时间可以有多个不可变引用
- 或者只有一个可变引用
- 引用必须总是有效的

---

## 💡 为什么重要？

### 内存安全

所有权系统在编译时保证内存安全，无需垃圾回收器：

- ✅ 无空指针解引用
- ✅ 无悬垂指针
- ✅ 无数据竞争
- ✅ 无双重释放

### 零成本抽象

所有权检查在编译时完成，运行时零开销：

- ✅ 无运行时开销
- ✅ 无垃圾回收暂停
- ✅ 可预测的性能

---

## 🎓 学习资源

### 本模块资源

- **[完整文档](../../crates/c01_ownership_borrow_scope/README.md)** - 详细文档
- **[代码示例集](../../crates/c01_ownership_borrow_scope/docs/tier_02_guides/06_代码示例集合.md)** - 102+ 示例
- **[知识图谱](../../crates/c01_ownership_borrow_scope/docs/theory/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)** - 概念关系

### 外部资源

- [Rust Book - 所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rust By Example - 作用域](https://doc.rust-lang.org/rust-by-example/scope.html)
- [Rustlings - 所有权练习](https://github.com/rust-lang/rustlings)

---

## 📊 模块统计

| 指标 | 数值 |
|------|------|
| **文档数量** | 160+ |
| **代码示例** | 14 个主题 |
| **练习题** | 20+ |
| **知识点** | 50+ |

---

## 🗺️ 后续学习

掌握本模块后，建议学习：

- **[C02: 类型系统](../c02/README.md)** - 构建类型安全的程序
- **[C03: 控制流与函数](../c03/README.md)** - 函数中的所有权
- **[C05: 多线程编程](../c05/README.md)** - 并发中的所有权

---

**开始学习吧！** 推荐从 [基础概念](./foundations.md) 开始 🚀
