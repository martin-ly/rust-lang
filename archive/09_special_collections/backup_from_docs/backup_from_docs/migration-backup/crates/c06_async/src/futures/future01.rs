/*
在 Rust 中，Future 的状态机和调度机制是理解异步编程的关键。
以下是对这两个概念的综合示例和解释。

Future 状态机

Future 的状态机模型允许异步操作在不同的状态之间转换。
每个 Future 可以处于以下几种状态：
Pending: 表示计算尚未完成，可能需要等待某些条件。
Ready: 表示计算已完成，并且可以返回结果。

调度机制
调度机制负责管理 Future 的执行。
Rust 的异步运行时（如 Tokio 或 async-std）会在适当的时候调用 poll 方法，
以检查 Future 的状态并决定何时继续执行。

*/

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

#[allow(unused)]
pub struct MyFuture {
    pub delay: Duration,
    pub state: State,
}

#[allow(unused)]
pub enum State {
    Pending,
    Ready(i32),
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();

        match this.state {
            State::Pending => {
                // 模拟异步操作
                cx.waker().wake_by_ref(); // 注册唤醒器
                this.state = State::Ready(42); // 更新状态为 Ready
                Poll::Pending // 返回 Pending
            }
            State::Ready(result) => {
                Poll::Ready(result) // 返回结果
            }
        }
    }
}
