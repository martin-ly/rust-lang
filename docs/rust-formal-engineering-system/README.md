# Rust 形式化工程系统

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **说明**: 本目录为**单一索引层**，形式化理论内容已整合至 [研究笔记](../research_notes/) 及各 crates。子目录 README 仅为占位重定向，请以 [00_master_index.md](./00_master_index.md) 为完整导航入口。
> **docs 全结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.9

---

## 导航说明

本项目的 Rust 形式化理论与工程文档已整合至 **研究笔记系统**。请使用以下入口访问：

### 核心入口

| 模块 | 入口路径 | 说明 |
| :--- | :--- | :--- |
| **形式化方法** | [research_notes/formal_methods/](../research_notes/formal_methods/) | 所有权模型、借用检查器、生命周期、Pin、异步状态机 |
| **类型理论** | [research_notes/type_theory/](../research_notes/type_theory/) | 类型系统基础、Trait 形式化、型变理论、生命周期 |
| **主索引** | [00_master_index.md](./00_master_index.md) | 完整模块映射与导航 |

### 快速跳转

- [所有权与借用理论](../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
- [类型系统基础](../research_notes/type_theory/type_system_foundations.md)
- [Trait 系统形式化](../research_notes/type_theory/trait_system_formalization.md)
- [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)
- [型变理论](../research_notes/type_theory/variance_theory.md)
- [形式化验证工具](../research_notes/TOOLS_GUIDE.md)

---

## 核心概念简介

### 1. 所有权系统

Rust 的所有权系统是其内存安全保证的核心：

```rust
// 所有权三规则的形式化理解
// 1. 每个值都有一个所有者
// 2. 同一时间只能有一个所有者
// 3. 当所有者离开作用域，值被丢弃

fn ownership_demo() {
    let s1 = String::from("hello");  // s1 拥有这个 String
    let s2 = s1;                      // 所有权转移到 s2
    // println!("{}", s1);            // 错误：s1 不再拥有该值

    let s3 = s2.clone();              // 克隆创建新的所有权
    println!("s2 = {}, s3 = {}", s2, s3);  // 两者都可用
}  // s2 和 s3 在这里被丢弃
```

### 2. 借用检查

借用检查器在编译时验证引用有效性：

```rust
// 借用规则的形式化表达
// ∀r: Reference, lifetime(r) ⊆ lifetime(pointee(r))
// ∀t: Time, has_mut_ref(l, t) → count_imm_refs(l, t) = 0

fn borrowing_demo() {
    let mut x = 5;

    // 可变借用
    let r1 = &mut x;
    *r1 += 1;
    // r1 在这里结束生命周期

    // 现在可以创建新的借用
    let r2 = &x;  // 不可变借用
    println!("{}", r2);
}
```

### 3. 类型系统

Rust 的类型系统基于 Hindley-Milner 类型推导：

```rust
// 类型系统的形式化基础
// - 结构类型 vs 名义类型
// - 参数多态（泛型）
// - 特设多态（Trait）

trait Drawable {
    fn draw(&self);
}

// 参数多态：T 可以是任何类型
fn identity<T>(x: T) -> T {
    x
}

// 约束多态：T 必须实现 Drawable
fn render<T: Drawable>(item: T) {
    item.draw();
}
```

---

## 形式化文档链接

### 核心研究笔记

| 主题 | 文档路径 | 内容概述 |
| :--- | :--- | :--- |
| **所有权模型** | [../research_notes/formal_methods/ownership_model.md](../research_notes/formal_methods/ownership_model.md) | 所有权系统的形式化定义与证明 |
| **借用检查器** | [../research_notes/formal_methods/borrow_checker_proof.md](../research_notes/formal_methods/borrow_checker_proof.md) | 借用检查的形式化正确性证明 |
| **生命周期** | [../research_notes/formal_methods/lifetime_formalization.md](../research_notes/formal_methods/lifetime_formalization.md) | 生命周期的形式化模型 |
| **类型系统** | [../research_notes/type_theory/type_system_foundations.md](../research_notes/type_theory/type_system_foundations.md) | 类型理论基础 |
| **Trait 系统** | [../research_notes/type_theory/trait_system_formalization.md](../research_notes/type_theory/trait_system_formalization.md) | Trait 系统的形式化 |
| **型变理论** | [../research_notes/type_theory/variance_theory.md](../research_notes/type_theory/variance_theory.md) | 型变规则与证明 |
| **证明索引** | [../research_notes/PROOF_INDEX.md](../research_notes/PROOF_INDEX.md) | 87+ 个形式化证明的完整索引 |
| **工具指南** | [../research_notes/TOOLS_GUIDE.md](../research_notes/TOOLS_GUIDE.md) | Prusti/Kani/Creusot 使用指南 |

---

## 相关文档

- [研究笔记主入口](../research_notes/README.md)
- [思维表征方式](../04_thinking/THINKING_REPRESENTATION_METHODS.md)
- [多维概念矩阵](../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)

---

## 研究笔记完整链接

| 研究笔记目录 | 路径 | 内容概述 |
| :--- | :--- | :--- |
| **formal_methods/** | [../research_notes/formal_methods/](../research_notes/formal_methods/) | 所有权模型、借用检查器、生命周期、异步状态机、Pin |
| **type_theory/** | [../research_notes/type_theory/](../research_notes/type_theory/) | 类型系统、Trait 系统、型变理论、类型推导 |
| **experiments/** | [../research_notes/experiments/](../research_notes/experiments/) | 性能实验、内存分析、编译器优化 |
| **PROOF_INDEX.md** | [../research_notes/PROOF_INDEX.md](../research_notes/PROOF_INDEX.md) | 形式化证明索引（87+ 个证明） |
| **TOOLS_GUIDE.md** | [../research_notes/TOOLS_GUIDE.md](../research_notes/TOOLS_GUIDE.md) | 形式化验证工具（Prusti、Kani、Creusot） |
| **SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md** | [../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) | 安全/非安全边界分析 |
