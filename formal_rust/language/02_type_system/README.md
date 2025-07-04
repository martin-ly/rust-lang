# 第 2 章：Rust 类型系统

## 导读

欢迎来到 Rust 形式化理论的第二章。本章将深入探索 Rust 类型系统的核心，这是 Rust 得以保证内存安全、实现"零成本抽象"并提供强大表现力的基石。我们将从高级设计哲学出发，逐层深入到具体的类型构造、泛型与 Trait 机制，并最终落脚于类型转换和型变等深刻的理论概念。

本章旨在揭示 Rust 类型系统"为何如此设计"，而不仅仅是"如何使用"。通过结合形式化理论与哲学批判性分析，我们希望为读者构建一个关于 Rust 类型系统的完整、深刻且自洽的知识体系。

### 章节内容概览

- **[01. 导论与设计哲学](./01_introduction_and_philosophy.md)**: 探讨 Rust 类型系统的三大支柱（安全、性能、表现力），并从范畴论和类型论的视角鸟瞰其高级结构。

- **[02. 基础概念](./02_fundamental_concepts.md)**: 详细介绍 Rust 的基础类型构造，包括原始类型、代数数据类型（结构体与枚举）、序列和指针类型，并分析其形式化表示。

- **[03. 类型安全与推断](./03_type_safety_and_inference.md)**: 论述类型安全是如何作为 Rust 核心机制的一种"涌现"属性，并深入剖析其强大的类型推断引擎（类 Hindley-Milner）的工作原理与局限。

- **[04. 泛型与 Trait](./04_generics_and_traits.md)**: 这是本章的核心。我们将全面解析 Rust 实现抽象的两个关键工具——泛型（参数化多态）和 Trait（特设多态），并探讨其背后的单态化、动态/静态分派、孤儿规则等关键机制。

- **[05. 类型转换与强制](./05_type_casting_and_coercion.md)**: 厘清 Rust 中多种类型转换机制（`as`, `From/Into`, Deref 强制, 下转型）的差异、安全性和适用场景，并分析其背后的设计哲学。

- **[06. 型变 (Variance)](./06_variance.md)**: 深入探讨型变（协变、逆变、不变）这一深刻的理论概念，论证其对于保证生命周期和可变引用安全的必要性。

希望本章内容能帮助您更透彻地理解 Rust 的强大之处。
