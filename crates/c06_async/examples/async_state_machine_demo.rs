//! Async 状态机示例 / Async state machine demo
//!
//! 演示如何用 enum + match 实现一个可持久化的异步任务状态机，
//! 并说明 async/await 编译器自动生成的 Future 状态机与此同构。
//!
//! 权威概念页（concept prose lives there, not here）：
//! - `concept/03_advanced/01_async/15_state_machine_semantics.md`
//! - `concept/03_advanced/01_async/01_async.md`
//!
//! 运行方式 / Run:
//!
//! ```bash
//! cargo run -p c06_async --example async_state_machine_demo
//! ```

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

/// 异步下载任务状态机 / Async download task state machine
#[derive(Debug)]
enum DownloadState {
    Idle { url: String },
    Connecting,
    Downloading { started: Instant },
    Completed { bytes: usize },
}

impl DownloadState {
    fn tick(&mut self) {
        *self = match std::mem::replace(self, DownloadState::Idle { url: String::new() }) {
            DownloadState::Idle { url } => {
                println!("[state] {url} -> Connecting");
                DownloadState::Connecting
            }
            DownloadState::Connecting => {
                println!("[state] -> Downloading");
                DownloadState::Downloading { started: Instant::now() }
            }
            DownloadState::Downloading { started } => {
                let elapsed = started.elapsed().as_millis();
                if elapsed > 10 {
                    println!("[state] -> Completed");
                    DownloadState::Completed { bytes: 1024 }
                } else {
                    DownloadState::Downloading { started }
                }
            }
            other => other,
        };
    }

}
struct DownloadFuture {
    state: DownloadState,
}

impl Future for DownloadFuture {
    type Output = Result<usize, String>;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.state.tick();
        match &self.state {
            DownloadState::Completed { bytes } => Poll::Ready(Ok(*bytes)),
            _ => Poll::Pending,
        }
    }
}

#[tokio::main]
async fn main() {
    let fut = DownloadFuture {
        state: DownloadState::Idle {
            url: "https://example.com/data".into(),
        },
    };

    // 手动驱动直到完成 / manually drive to completion
    tokio::time::sleep(Duration::from_millis(20)).await;
    let result = fut.await;
    println!("download result: {:?}", result);

    println!(
        "要点 / takeaway: async/await 的 Future 本质上就是状态机；详细语义见 \
         concept/03_advanced/01_async/15_state_machine_semantics.md 与 01_async.md"
    );
}
