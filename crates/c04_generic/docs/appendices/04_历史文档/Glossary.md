# C04: 术语表 (Glossary)

> **文档定位**: 泛型编程相关术语的快速参考手册  
> **使用方式**: 查找不理解的术语，了解准确定义  
> **相关文档**: [泛型基础](./generic_fundamentals.md) | [主索引](./00_MASTER_INDEX.md)


## 📊 目录

- [📋 术语索引](#术语索引)
- [术语列表](#术语列表)
  - [泛型 (Generics)](#泛型-generics)
  - [参数化多态 (Parametric Polymorphism)](#参数化多态-parametric-polymorphism)
  - [单态化 (Monomorphization)](#单态化-monomorphization)
  - [Trait 约束 (Trait Bound)](#trait-约束-trait-bound)
  - [where 子句](#where-子句)
  - [关联类型 (Associated Type)](#关联类型-associated-type)
  - [动态多态 (Dynamic Polymorphism)](#动态多态-dynamic-polymorphism)
  - [Trait 对象 (Trait Object)](#trait-对象-trait-object)
  - [vtable (虚方法表)](#vtable-虚方法表)
  - [类型构造器 (Type Constructor)](#类型构造器-type-constructor)
  - [高阶类型 (Higher-Kinded Types, HKT)](#高阶类型-higher-kinded-types-hkt)
  - [GATs (Generic Associated Types)](#gats-generic-associated-types)
  - [RPITIT (Return Position Impl Trait In Traits)](#rpitit-return-position-impl-trait-in-traits)
- [📚 参考资源](#参考资源)


**最后更新**: 2025-10-19  
**适用版本**: Rust 1.0+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

本术语表收录了 Rust 泛型编程中的核心概念和术语。按字母顺序排列，方便快速查找。

---

## 术语列表

### 泛型 (Generics)

**定义**: 一种编程语言特性，允许在定义函数、结构体等实体时使用占位符类型（类型参数），从而编写能够适用于多种具体类型的通用代码。

**相关**: [泛型基础](./generic_fundamentals.md) | [01_introduction_to_generics](./01_introduction_to_generics.md)

---

### 参数化多态 (Parametric Polymorphism)

**定义**: 多态的一种形式，其中代码对一个或多个类型参数是通用的。这是 Rust 泛型所实现的多态类型。也称为静态多态。

**相关**: [多态](./05_advanced_topics.md#51-rust-中的多态-polymorphism)

---

### 单态化 (Monomorphization)

**定义**: Rust 编译器在编译时将泛型代码转换为非泛型代码的过程。编译器会为泛型代码的每一次具体类型实例化生成一份专门的代码，从而实现零成本抽象。

**相关**: [零成本抽象](./generic_fundamentals.md#零成本抽象)

---

### Trait 约束 (Trait Bound)

**定义**: 对泛型类型参数的一种约束，要求该类型必须实现一个或多个指定的 Trait。这保证了泛型类型具有某些特定的能力或行为。

**相关**: [Trait约束详解](./03_trait_bounds.md)

---

### where 子句

**定义**: 一种用于声明 Trait 约束的替代语法，当约束变得复杂或数量众多时，它能提供比行内约束更清晰的格式。

**相关**: [Trait约束](./03_trait_bounds.md)

---

### 关联类型 (Associated Type)

**定义**: 在 Trait 内部定义的一个占位符类型。它将一个类型与 Trait 本身关联起来，实现该 Trait 的类型必须为这个关联类型指定一个具体的类型。

**相关**: [关联类型详解](./04_associated_types.md)

---

### 动态多态 (Dynamic Polymorphism)

**定义**: 多态的一种形式，在运行时确定要调用的具体方法。在 Rust 中，这通过 Trait 对象 (`dyn Trait`) 实现，通常涉及 vtable 查找的开销。

**相关**: [多态](./05_advanced_topics.md#51-rust-中的多态-polymorphism)

---

### Trait 对象 (Trait Object)

**定义**: 一个指向实现了某个 Trait 的具体类型实例的指针（通常是 `&dyn Trait` 或 `Box<dyn Trait>`）。它是一个"胖指针"，同时包含数据指针和 vtable 指针。

**相关**: [动态多态](./05_advanced_topics.md#512-动态多态-dynamic-polymorphism)

---

### vtable (虚方法表)

**定义**: 一个函数指针表，用于在运行时查找动态分派的方法。每个实现了 Trait 的具体类型都有一个对应的 vtable。

**相关**: [Trait对象](./05_advanced_topics.md#512-动态多态-dynamic-polymorphism)

---

### 类型构造器 (Type Constructor)

**定义**: 一个在类型级别上运作的"函数"。它是一个泛型类型，接受一个或多个类型作为参数，并构造出一个新的具体类型。例如，`Vec` 是一个类型构造器。

**相关**: [类型构造器](./05_advanced_topics.md#52-类型构造器-type-constructors)

---

### 高阶类型 (Higher-Kinded Types, HKT)

**定义**: 一种高级的类型系统特性，允许泛化类型构造器本身。例如，能够编写一个对任何容器 `F<_>` 都通用的函数，而不管 `F` 是 `Vec`、`Option` 还是其他类型。

**当前状态**: Rust 目前不原生支持 HKT（截至2025年10月）。

**相关**: [HKT讨论](./05_advanced_topics.md#53-a-note-on-higher-kinded-types-hkt)

---

### GATs (Generic Associated Types)

**定义**: 泛型关联类型，允许在关联类型上使用泛型参数。这是Rust 1.65 (2022年11月) 稳定的重大特性。

**稳定版本**: Rust 1.65+

**相关**: [GATs详解](./05_advanced_topics.md#541-gats---generic-associated-types-已稳定) | [版本历史](./06_rust_features/RUST_VERSION_HISTORY_ACCURATE.md)

---

### RPITIT (Return Position Impl Trait In Traits)

**定义**: 允许在trait方法的返回位置使用 `impl Trait`，避免了 `Box<dyn Trait>` 的运行时开销。Rust 1.75 (2023年12月) 稳定。

**稳定版本**: Rust 1.75+

**相关**: [RPITIT详解](./05_advanced_topics.md#542-rpitit---return-position-impl-trait-in-traits-已稳定) | [版本历史](./06_rust_features/RUST_VERSION_HISTORY_ACCURATE.md)

---

## 📚 参考资源

* [泛型基础](./generic_fundamentals.md) - 系统学习泛型
* [主索引](./00_MASTER_INDEX.md) - 文档导航
* [实践指南](./PRACTICAL_GENERICS_GUIDE.md) - 实际应用

---

**最后审核**: 2025-10-19  
**维护**: 定期更新术语和链接
