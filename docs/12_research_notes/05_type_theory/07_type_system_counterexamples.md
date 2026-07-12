# 类型系统反例边界 {#类型系统反例边界}

<!-- canonical-normalized 2026-07-11 -->
> **权威来源（Canonical）**: 本文件为类型系统反例边界集（反例，独特内容）；通用 Rust 概念解释请以 concept 权威页为准：[`concept L2 类型系统`](../../../concept/01_foundation/02_type_system/01_type_system.md)
>
> 根据 AGENTS.md §2 Canonical 规则：本文仅保留本文独特内容（类型系统反例与边界（反例集，非概念正文）），不重复 concept/ 中的概念定义、规则与定理推导。

> **EN**: Type System Counterexamples
> **Summary**: 类型系统反例边界 Type System Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6
> **概念族**: 类型系统（Type System） / Trait / 反例边界
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [类型系统反例边界 {#类型系统反例边界}](#类型系统反例边界-类型系统反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. 型变误用：数组与 Vec 的协变差异 {#1-型变误用数组与-vec-的协变差异}](#1-型变误用数组与-vec-的协变差异-1-型变误用数组与-vec-的协变差异)
    - [现象 {#现象-6}](#现象-现象-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. 生命周期子类型误判 {#2-生命周期子类型误判}](#2-生命周期子类型误判-2-生命周期子类型误判)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [编译器错误 {#编译器错误-3}](#编译器错误-编译器错误-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. `dyn Trait` 对象大小不固定 {#3-dyn-trait-对象大小不固定}](#3-dyn-trait-对象大小不固定-3-dyn-trait-对象大小不固定)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [编译器错误 {#编译器错误-3}](#编译器错误-编译器错误-3-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. `impl Trait` 返回类型泄露限制 {#4-impl-trait-返回类型泄露限制}](#4-impl-trait-返回类型泄露限制-4-impl-trait-返回类型泄露限制)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [边界 {#边界-1}](#边界-边界-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. Orphan 规则冲突 {#5-orphan-规则冲突}](#5-orphan-规则冲突-5-orphan-规则冲突)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [编译器错误 {#编译器错误-3}](#编译器错误-编译器错误-3-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. 关联类型歧义 {#6-关联类型歧义}](#6-关联类型歧义-6-关联类型歧义)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [边界 {#边界-1}](#边界-边界-1-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. Copy / Drop 互斥 {#7-copy-drop-互斥}](#7-copy--drop-互斥-7-copy-drop-互斥)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [编译器错误 {#编译器错误-3}](#编译器错误-编译器错误-3-3)
    - [根因 {#根因}](#根因-根因)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 1. 型变误用：数组与 Vec 的协变差异 {#1-型变误用数组与-vec-的协变差异}

### 现象 {#现象-6}

```rust
fn takes_animals(animals: &[&Animal]) { /* ... */ }

let cats: &[&Cat] = &[&Cat];
takes_animals(cats); // ✅ &[&Cat] 可协变为 &[&Animal]
```

反例：误以为 `Vec<&Cat>` 可直接传给 `Vec<&Animal>`：

```rust
fn takes_animals_vec(animals: Vec<&Animal>) { /* ... */ }

let cats: Vec<&Cat> = vec![&Cat];
takes_animals_vec(cats); // ❌ Vec<T> 对 T 是协变，但这里生命周期/类型不匹配
```

### 修复方案 {#修复方案-6}

- 使用 `&[&Cat]` 切片（Slice），切片对元素是协变的。
- 或显式转换：`cats.into_iter().map(|c| c as &Animal).collect()`。

> **相关文档**: [06_variance_theory.md](06_variance_theory.md)

---

## 2. 生命周期子类型误判 {#2-生命周期子类型误判}

### 现象 {#现象-6}

```rust
fn assign<'a, 'b>(x: &'a str, y: &'b str) -> &'b str {
    x // ❌ 'a 不一定比 'b 长
}
```

### 编译器错误 {#编译器错误-3}

```text
error: lifetime may not live long enough
```

### 修复方案 {#修复方案-6}

```rust
fn assign<'a, 'b: 'a>(x: &'a str, y: &'b str) -> &'a str {
    x
}
```

或返回 `x` 本身并让生命周期统一。

---

## 3. `dyn Trait` 对象大小不固定 {#3-dyn-trait-对象大小不固定}

### 现象 {#现象-6}

```rust
fn take_trait(obj: dyn Trait) { /* ... */ }
```

### 编译器错误 {#编译器错误-3}

```text
error[E0277]: the size for values of type `dyn Trait` cannot be known at compilation time
```

### 修复方案 {#修复方案-6}

- 使用引用（Reference）/智能指针（Smart Pointer）：`&dyn Trait`、`Box<dyn Trait>`、`Rc<dyn Trait>`、`Arc<dyn Trait>`。
- 或改用泛型（Generics） `fn take<T: Trait>(obj: T)`。

---

## 4. `impl Trait` 返回类型泄露限制 {#4-impl-trait-返回类型泄露限制}

### 现象 {#现象-6}

```rust
trait Foo {}
fn make_foo() -> impl Foo { /* ... */ }

fn consumer() {
    let a = make_foo();
    let b = make_foo();
    // 无法判断 a 与 b 是否为同一具体类型
}
```

### 边界 {#边界-1}

- `impl Trait` 返回类型隐藏具体类型，调用者无法构造相同类型。
- 不能在不同返回点返回不同类型，即使都实现该 trait。

### 修复方案 {#修复方案-6}

- 需要多态返回时用 `Box<dyn Trait>`。
- 需要调用者构造同类型时，返回具体类型或泛型。

---

## 5. Orphan 规则冲突 {#5-orphan-规则冲突}

### 现象 {#现象-6}

```rust
// 在下游 crate 中试图为外部类型实现外部 trait
impl serde::Serialize for std::vec::Vec<u8> {
    // ...
}
```

### 编译器错误 {#编译器错误-3}

```text
error[E0117]: only traits defined in the current crate can be implemented for arbitrary types
```

### 修复方案 {#修复方案-6}

- 使用 newtype 模式包装外部类型：`struct MyBytes(Vec<u8>)`。
- 只在当前 crate 定义的类型上实现外部 trait，或为当前 trait 实现外部类型。

---

## 6. 关联类型歧义 {#6-关联类型歧义}

### 现象 {#现象-6}

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

fn process<I: Iterator>(it: &mut I) -> Option<I::Item> {
    it.next()
}

// 同时实现多个 Item 类型不可能，但调用者可能误以为可参数化
```

### 边界 {#边界-1}

- 一个类型对同一个 trait 只能有一种关联类型实现。
- 与泛型参数不同，关联类型由实现决定，调用方不能指定。

### 修复方案 {#修复方案-6}

- 若需参数化，使用泛型 trait：`trait Container<T>`。

---

## 7. Copy / Drop 互斥 {#7-copy-drop-互斥}

### 现象 {#现象-6}

```rust
#[derive(Copy)]
struct Resource {
    handle: *mut c_void,
}

impl Drop for Resource {
    fn drop(&mut self) { /* 释放资源 */ }
}
```

### 编译器错误 {#编译器错误-3}

```text
error[E0184]: the trait `Copy` may not be implemented for this type; the type implements `Drop`
```

### 根因 {#根因}

`Copy` 语义按位复制会产生多个相同资源句柄，与 `Drop` 单次释放语义冲突。

### 修复方案 {#修复方案-6}

- 移除 `Copy`，仅保留 `Clone`（若需深拷贝）。
- 使用 `Rc`/`Arc` 共享所有权（Ownership）。

---

## 总结 {#总结}

| 反例 | 涉及概念 | 典型错误码 | 修复方向 |
|------|----------|------------|----------|
| 型变误用 | 型变、子类型 | E0308 / E0623 | 切片（Slice）转换、显式收集 |
| 生命周期子类型误判 | 生命周期、子类型 | lifetime mismatch | 生命周期约束 `'b: 'a` |
| `dyn Trait` 大小不固定 | trait 对象 | E0277 | `Box<dyn Trait>` / 泛型（Generics） |
| `impl Trait` 类型隐藏 | 抽象返回类型 | — | `Box<dyn Trait>` / 具体类型 |
| Orphan 规则冲突 | trait 实现规则 | E0117 | newtype 模式 |
| 关联类型歧义 | 关联类型 | E0221 | 泛型 trait |
| Copy / Drop 互斥 | 资源语义 | E0184 | 移除 Copy / 使用 Rc/Arc |

> **权威来源**:
>
> [Rust Reference – Type System](https://doc.rust-lang.org/reference/type-system.html) |
> [Rust Reference – Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html) |
> [Rust Reference – Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) |
> [Rust Reference – Orphan Rules](https://doc.rust-lang.org/reference/items/implementations.html#orphan-rules) |
> [The Rust Programming Language – Ch 10](https://doc.rust-lang.org/book/ch10-00-generics.html) |
> [The Rust Programming Language – Ch 17](https://doc.rust-lang.org/book/ch17-00-oop.html) |
> [Rustonomicon – Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)
>

## 相关概念 {#相关概念}

- [类型系统基础](05_type_system_foundations.md)
- [Trait 系统形式化](04_trait_system_formalization.md)
- [型变理论](06_variance_theory.md)
- [生命周期形式化](03_lifetime_formalization.md)
- [通用反例汇编](../03_formal_proofs/08_counter_examples_compendium.md)
- [知识图谱索引](../06_concept_models/13_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../01_alignment_matrices/30_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 195: Associated items](https://rust-lang.github.io/rfcs/0195-associated-items.html)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Oxide](https://arxiv.org/abs/1903.00982)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
