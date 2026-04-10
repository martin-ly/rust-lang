# API 使用指南

> **最后更新**: 2026-04-10
> **版本**: Rust 1.96.0

---

## 快速开始

### 添加依赖

在 Cargo.toml 中添加需要的 crate:

```toml
[dependencies]
c01_ownership_borrow_scope = { path = "../crates/c01_ownership_borrow_scope" }
c02_type_system = { path = "../crates/c02_type_system" }
```

### 基本使用

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
