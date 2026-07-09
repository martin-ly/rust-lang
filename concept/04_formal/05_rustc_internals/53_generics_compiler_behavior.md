> **内容分级**: [专家级]
> **本节关键术语**: 单态化 (Monomorphization) · 静态分发 (Static Dispatch) · 动态分发 (Dynamic Dispatch) · 类型擦除 (Type Erasure) · Fat Pointer · VTable — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
# 泛型编译器行为：单态化、分发与类型擦除
>
> **EN**: Generics Compiler Behavior
> **Summary**: How Rust compiles generic code: monomorphization, static vs dynamic dispatch, type erasure, fat pointers, and performance trade-offs.
> **受众**: [专家]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **定位**: 深入分析 Rust 泛型代码在编译期与运行时的行为差异，解释单态化如何实现零成本抽象，以及何时应退回到动态分发以优化代码体积。
> **前置概念**: [Generics](../../02_intermediate/01_generics/02_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Type System](../../01_foundation/02_type_system/04_type_system.md)
> **后置概念**: [Rustc Trait Solver](26_trait_solver_in_rustc.md) · [Type Layout](42_type_layout.md)

---

> **来源**: [Rust Reference — Generics](https://doc.rust-lang.org/reference/items/generics.html) · [Rustonomicon — Trait Objects](https://doc.rust-lang.org/nomicon/trait-objects.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

## 📑 目录

- [泛型编译器行为：单态化、分发与类型擦除](#泛型编译器行为单态化分发与类型擦除)
  - [📑 目录](#-目录)
  - [一、单态化 Monomorphization](#一单态化-monomorphization)
    - [优势与代价](#优势与代价)
  - [二、静态分发 vs 动态分发](#二静态分发-vs-动态分发)
  - [三、类型擦除与 Fat Pointer](#三类型擦除与-fat-pointer)
    - [VTable 结构](#vtable-结构)
  - [四、性能权衡与最佳实践](#四性能权衡与最佳实践)

---

## 一、单态化 Monomorphization

Rust 泛型在编译期为每个具体类型生成一份专用代码，称为**单态化**。

```rust
fn identity<T>(x: T) -> T { x }

fn main() {
    identity(5i32);     // 生成 identity_i32
    identity(3.14f64);  // 生成 identity_f64
}
```

### 优势与代价

| 优势 | 代价 |
| :--- | :--- |
| 零运行时开销 | 代码体积膨胀（code bloat） |
| 可内联优化 | 编译时间增加 |
| 类型错误在编译期捕获 | 跨 crate 边界重复实例化 |

---

## 二、静态分发 vs 动态分发

| 特性 | 静态分发 `impl Trait` / 泛型 | 动态分发 `dyn Trait` |
| :--- | :--- | :--- |
| 调用方式 | 直接调用，可内联 | 通过 VTable 间接调用 |
| 性能 | 高（零开销） | 低（间接跳转 + 无法内联） |
| 代码体积 | 可能膨胀 | 固定 |
| 同质集合 | 不便（每个元素类型不同） | 方便（`Vec<Box<dyn Trait>>`） |

---

## 三、类型擦除与 Fat Pointer

`dyn Trait` 使用**胖指针（fat pointer）**：数据指针 + VTable 指针。

```rust
let obj: &dyn Trait = &value;
// 内存布局: [data_ptr, vtable_ptr]
```

### VTable 结构

VTable 存储 trait 方法地址、析构函数、大小与对齐信息。

---

## 四、性能权衡与最佳实践

- **默认使用泛型/静态分发**：利用零成本抽象与内联。
- **代码体积敏感时考虑 `dyn Trait`**：如大量不同类型调用同一泛型函数。
- **泛型函数拆分为非泛型入口**：减少单态化膨胀。

```rust
// 减少膨胀：公共非泛型入口 + 小型泛型包装
pub fn process_value(value: &dyn MyTrait) {
    // 非泛型主体
}
```

---

> 本文档由原 `crates/c04_generic/docs/tier_03_references/05_compiler_behavior_reference.md` 按 AGENTS.md §6.4 迁移而来，是 `concept/` 中的权威页。
