
### 10.4 边界测试：Futures 的 `pin` 语义与堆分配需求（编译错误）

```rust,ignore
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    data: String,
}

impl Future for MyFuture {
    type Output = String;
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        // ❌ 编译错误: self 是 Pin<&mut Self>，不能直接获取 &mut self
        // 需要 unsafe { self.get_unchecked_mut() }
        Poll::Ready(self.data.clone())
    }
}

fn main() {}
```

> **修正**: **`Pin<&mut T>`** 是 Rust async 的核心：1) `Pin` 保证指针指向的数据在内存中不移动；2) `self: Pin<&mut Self>` 是 `Future::poll` 的签名要求；3) 自引用结构（如 `async fn` 编译后的状态机）必须 pinned，否则内部指针悬垂。获取 `&mut T`：1) `Pin::map_unchecked_mut`（安全，针对已知 `Unpin` 类型）；2) `unsafe { self.get_unchecked_mut() }`（不安全，需保证不移动数据）。自引用问题的根本：1) struct 包含指向自身的指针；2) 若 struct 被 move，内部指针悬垂；3) `Pin` 禁止 move，但需 unsafe 代码创建。这与 C++ 的 `std::pin`（无原生支持，需手动管理）或 Swift 的引用类型（始终堆分配，无 move 问题）不同——Rust 的 `Pin` 是零成本抽象（编译期约束），但使用复杂。[来源: [Pin API](https://doc.rust-lang.org/std/pin/)] · [来源: [Async Rust](https://rust-lang.github.io/async-book/)]
