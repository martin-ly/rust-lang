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
