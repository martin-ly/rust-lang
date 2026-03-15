# C04 高级泛型模式

> **模块**: C04 泛型编程
> **层级**: Tier 2 - 应用与实战
> **难度**: 高级
> **Rust 版本**: 1.94.0+

---

## 📋 目录

- [C04 高级泛型模式](#c04-高级泛型模式)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [💡 高级模式](#-高级模式)
    - [GAT (泛型关联类型)](#gat-泛型关联类型)
    - [类型族 (Type Families)](#类型族-type-families)
    - [HList (异构列表)](#hlist-异构列表)
  - [🔧 实战技巧](#-实战技巧)
    - [Builder 模式中的泛型](#builder-模式中的泛型)

---

## 🎯 概述

本文档深入探讨 Rust 泛型编程的高级模式，包括 GAT、类型族、HList 等高级特性。

---

## 💡 高级模式

### GAT (泛型关联类型)

泛型关联类型 (Generic Associated Types) 是 Rust 1.65+ 引入的重要特性，允许关联类型拥有泛型参数。

```rust
// 泛型关联类型
trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

// 实现：允许返回对自身的引用
struct WindowIter<'a, T> {
    slice: &'a [T],
    window_size: usize,
}

impl<'a, T> LendingIterator for WindowIter<'a, T> {
    type Item<'b> = &'b [T]
    where
        Self: 'b;

    fn next<'b>(&'b mut self) -> Option<Self::Item<'b>> {
        if self.slice.len() >= self.window_size {
            let window = &self.slice[..self.window_size];
            self.slice = &self.slice[1..];
            Some(window)
        } else {
            None
        }
    }
}
```

### 类型族 (Type Families)

```rust
// 类型族模式：根据类型参数返回不同类型

trait TypeFamily {
    type Output<T>;
}

struct VecFamily;
impl TypeFamily for VecFamily {
    type Output<T> = Vec<T>;
}

struct OptionFamily;
impl TypeFamily for OptionFamily {
    type Output<T> = Option<T>;
}
```

### HList (异构列表)

```rust
// 异构类型列表
struct HNil;
struct HCons<H, T> {
    head: H,
    tail: T,
}

trait HList {}
impl HList for HNil {}
impl<H, T: HList> HList for HCons<H, T> {}
```

---

## 🔧 实战技巧

### Builder 模式中的泛型

```rust
use std::marker::PhantomData;

struct NotSet;
struct Set<T>(T);

struct RequestBuilder<Url, Method, Body> {
    url: Url,
    method: Method,
    body: Body,
    headers: Vec<(String, String)>,
}
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
