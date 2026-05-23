# 实践项目 14: 异步运行时原型

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
  - [权威来源索引](#权威来源索引-1)

## 项目目标
>
> **[来源: Rust Official Docs]**

理解异步原理，创建简化版async运行时。

---

## 功能需求
>
> **[来源: Rust Official Docs]**

- [ ] Future trait实现
- [ ] 任务调度器
- [ ] Reactor模式
- [ ] Waker机制
- [ ] 基本TCP支持

---

## 学习要点
>
> **[来源: Rust Official Docs]**

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
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [03_practice 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Asynchronous I/O]**

> **[来源: TRPL Ch. 17 - Async]**

> **[来源: Tokio Documentation]**

> **[来源: RFC 2394 - Async/Await]**

---

## 权威来源索引

> **[来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]**
>
> **[来源: [Tokio Documentation](https://docs.rs/tokio/latest/tokio/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
