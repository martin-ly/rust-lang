# 实践项目 14: 异步运行时原型

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c06 (异步)
> **预计时间**: 12-15小时

---

## 项目目标

理解异步原理，创建简化版async运行时。

---

## 功能需求

- [ ] Future trait实现
- [ ] 任务调度器
- [ ] Reactor模式
- [ ] Waker机制
- [ ] 基本TCP支持

---

## 学习要点

### 自定义Future

```rust
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

完整参考实现位于: `examples/async-runtime/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
