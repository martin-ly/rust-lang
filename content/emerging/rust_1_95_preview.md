# Rust 1.95 预览特性

> **版本**: Rust 1.95.0 (Beta)
> **预计发布**: 2026年4月17日
> **状态**: 🧪 Beta 测试阶段

---

## 📋 目录

- [Rust 1.95 预览特性](#rust-195-预览特性)
  - [📋 目录](#-目录)
  - [🎯 版本概览](#-版本概览)
  - [🚀 主要新特性](#-主要新特性)
    - [1. Impl Trait in Associated Type (稳定)](#1-impl-trait-in-associated-type-稳定)
    - [2. 新的 API 稳定化](#2-新的-api-稳定化)
    - [3. 编译器性能改进](#3-编译器性能改进)
  - [📊 与 1.94 对比](#-与-194-对比)
  - [🔄 迁移指南](#-迁移指南)
    - [从手动 Future 类型到 impl Trait](#从手动-future-类型到-impl-trait)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 版本概览

Rust 1.95 主要聚焦于：

- **语言特性**: Impl Trait in Associated Type 的稳定化
- **API 扩展**: 更多标准库 API 稳定化
- **性能**: 编译器增量编译优化

---

## 🚀 主要新特性

### 1. Impl Trait in Associated Type (稳定)

**描述**: 允许在 trait 的关联类型中使用 `impl Trait`

```rust
// 定义异步迭代器 trait
trait AsyncIterator {
    type Item;
    // 使用 impl Trait 简化 Future 类型
    type NextFuture: Future<Output = Option<Self::Item>>;

    fn next(&mut self) -> Self::NextFuture;
}

// 实现示例
struct Counter {
    current: u32,
}

impl AsyncIterator for Counter {
    type Item = u32;
    // 编译器推断具体的 Future 类型
    type NextFuture = impl Future<Output = Option<u32>>;

    fn next(&mut self) -> Self::NextFuture {
        async move {
            if self.current < 10 {
                let val = self.current;
                self.current += 1;
                tokio::time::sleep(Duration::from_millis(100)).await;
                Some(val)
            } else {
                None
            }
        }
    }
}
```

**使用场景**:

- 简化复杂的 Future 类型签名
- 隐藏实现细节
- 更好的 API 封装

### 2. 新的 API 稳定化

```rust
// VecDeque::truncate_front
use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);
deque.truncate_front(2); // 从前端删除2个元素
assert_eq!(deque, [3, 4, 5]);

// RefCell::try_map (如果稳定)
use std::cell::RefCell;

let cell = RefCell::new(Some(5));
let mapped = RefCell::try_map(cell.borrow(), |opt| opt.as_ref());
```

### 3. 编译器性能改进

| 场景 | 1.94 | 1.95 | 提升 |
|------|------|------|------|
| 增量编译 | 基准 | 优化 | 10-15% |
| 泛型实例化 | 基准 | 缓存优化 | 5-10% |
| 宏扩展 | 基准 | 并行化 | 20-30% |

---

## 📊 与 1.94 对比

| 特性 | 1.94 | 1.95 | 影响 |
|------|------|------|------|
| array_windows | ✅ | ✅ | - |
| LazyCell/LazyLock 新方法 | ✅ | ✅ | - |
| Impl Trait in Assoc Type | ❌ | ✅ | **重大** |
| TOML 1.1 | ✅ | ✅ | - |
| 编译器性能 | 基准 | +10% | 中等 |

---

## 🔄 迁移指南

### 从手动 Future 类型到 impl Trait

```rust
// ❌ Rust 1.94: 需要显式指定复杂的 Future 类型
use std::pin::Pin;
use std::future::Future;

struct MyIter {
    future: Pin<Box<dyn Future<Output = Option<i32>> + Send>>,
}

// ✅ Rust 1.95: 使用 impl Trait 简化
trait MyAsyncTrait {
    type Future: Future<Output = i32>;
    fn compute(&self) -> Self::Future;
}

impl MyAsyncTrait for MyStruct {
    type Future = impl Future<Output = i32>;

    fn compute(&self) -> Self::Future {
        async move { 42 }
    }
}
```

---

## 🔗 参考资源

- [Rust 1.95 Release Notes (Draft)](https://releases.rs/docs/1.95.0/)
- [Tracking Issue: impl_trait_in_assoc_type](https://github.com/rust-lang/rust/issues/63063)

---

**最后更新**: 2026-03-15
**状态**: 🧪 Beta 预览
