# 实践项目 14: 异步运行时原型
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c06 (异步)
> **预计时间**: 12-15小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 14: 异步运行时原型](#实践项目-14-异步运行时原型)
  - [📑 目录](#-目录)
  - [项目目标](#项目目标)
  - [功能需求](#功能需求)
  - [学习要点](#学习要点)
    - [自定义Future](#自定义future)
  - [参考实现](#参考实现)
  - [完整参考实现位于: `examples/async-runtime/`](#完整参考实现位于-examplesasync-runtime)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 项目目标
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

理解异步原理，创建简化版async运行时。

---

## 功能需求
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] Future trait实现
- [ ] 任务调度器
- [ ] Reactor模式
- [ ] Waker机制
- [ ] 基本TCP支持

---

## 学习要点
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 自定义Future
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    state: State,
}

impl Future for MyFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 实现poll逻辑
        Poll::Ready(())
    }
}
```

---

## 参考实现
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

完整参考实现位于: `examples/async-runtime/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [03_practice 目录](./README.md)
- [docs 索引](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
> **来源: [TRPL Ch. 17 - Async](https://doc.rust-lang.org/book/ch17-00-async-await.html)**
> **来源: [Tokio Documentation](https://tokio.rs/)**
> **来源: [RFC 2394 - Async/Await](https://rust-lang.github.io/rfcs/2394-2394-async_await.html)**

---
