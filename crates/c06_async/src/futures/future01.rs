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
                cx.waker().wake_by_ref(); // 通知调度器下一轮再 poll
                this.state = State::Ready(42); // 更新状态为 Ready
                Poll::Pending // 返回 Pending
            }
            State::Ready(result) => {
                Poll::Ready(result) // 返回结果
            }
        }
    }
}

/// 展示手写 Future 的用法
pub async fn demo_manual_future() -> i32 {
    // 这里只是演示状态切换；真实延时应交给运行时计时器
    MyFuture { delay: Duration::from_millis(1), state: State::Pending }.await
}

/// 展示与 tokio 计时器结合的 Future/Stream 组合子
pub async fn demo_future_combinators() -> i32 {
    use futures::{future, FutureExt};
    use tokio::time::sleep;

    // map/then 链式组合
    let f1 = async { 21 };
    let result = f1.map(|x| x * 2).await;

    // select 两个 future，先完成者返回
    let a = async {
        sleep(Duration::from_millis(10)).await;
        1
    };
    let b = async {
        sleep(Duration::from_millis(5)).await;
        2
    };
    futures::pin_mut!(a);
    futures::pin_mut!(b);
    let first_done = future::select(a, b).await;
    let faster_value = match first_done {
        future::Either::Left((va, _)) => va,
        future::Either::Right((vb, _)) => vb,
    };

    result + faster_value
}
