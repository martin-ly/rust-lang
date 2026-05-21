# API 使用指南

> **最后更新**: 2026-04-10
> **版本**: Rust 1.96.0

---

## 📑 目录
>
- [API 使用指南](#api-使用指南)
  - [📑 目录](#-目录)
  - [快速开始](#快速开始)
    - [添加依赖](#添加依赖)
    - [基本使用](#基本使用)
  - [Crate API 概览](#crate-api-概览)
    - [c01\_ownership\_borrow\_scope](#c01_ownership_borrow_scope)
    - [c02\_type\_system](#c02_type_system)
    - [c04\_generic](#c04_generic)
    - [c05\_threads](#c05_threads)
    - [c06\_async](#c06_async)
    - [c08\_algorithms](#c08_algorithms)
  - [最佳实践](#最佳实践)
    - [错误处理](#错误处理)
    - [异步代码](#异步代码)
    - [并发控制](#并发控制)
  - [参考文档](#参考文档)
  - [相关概念](#相关概念)

## 快速开始
>
> **[来源: Rust Official Docs]**

### 添加依赖
>
> **[来源: Rust Official Docs]**

在 Cargo.toml 中添加需要的 crate:

```toml
[dependencies]
c01_ownership_borrow_scope = { path = "../crates/c01_ownership_borrow_scope" }
c02_type_system = { path = "../crates/c02_type_system" }
```

### 基本使用
>
> **[来源: Rust Official Docs]**

```rust
use c01_ownership_borrow_scope::smart_pointers::BoxExample;
use c02_type_system::collections::HashMapExample;

fn main() {
    let boxed = BoxExample::new(42);
    let map = HashMapExample::new();
}
```

---

## Crate API 概览

### c01_ownership_borrow_scope

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| ownership | OwnershipDemo | 所有权演示 |
| borrow | BorrowChecker | 借用检查示例 |
| smart_pointers | BoxDemo, RcDemo | 智能指针 |
| lifetime | LifetimeDemo | 生命周期 |

### c02_type_system

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| basic_types | TypeDemo | 基础类型 |
| collections | VecDemo, MapDemo | 集合类型 |
| generics | GenericDemo | 泛型基础 |
| traits | TraitDemo | Trait 系统 |

### c04_generic

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| traits | Displayable, Comparable | 常用 trait |
| generics | Container | 泛型容器 |
| gat | ContainerFamily | GAT 示例 |

### c05_threads

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| basic_threads | ThreadPool | 线程池 |
| synchronization | MutexWrapper | 互斥锁包装 |
| lock_free | LockFreeQueue | 无锁队列 |

### c06_async

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| async_basics | AsyncRuntime | 异步运行时 |
| streams | StreamProcessor | 流处理 |
| web_frameworks | AxumServer | Web 服务器 |

### c08_algorithms

| 模块 | 核心类型 | 描述 |
|------|----------|------|
| sorting | Sorter | 排序接口 |
| graph | Graph | 图结构 |
| tree | Tree | 树结构 |

---

## 最佳实践

### 错误处理

```rust
use common::Result;

fn do_something() -> Result<i32> {
    let value = may_fail()?;
    Ok(value * 2)
}
```

### 异步代码

```rust
use tokio;

#[tokio::main]
async fn main() {
    let result = async_operation().await;
}
```

### 并发控制

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

let data = Arc::new(Mutex::new(Vec::new()));
```

---

## 参考文档

- docs.rs - 在线文档
- examples/ - 示例代码
- tests/ - 测试用例

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [docs 目录](./README.md)
