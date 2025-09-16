//! 基础通道：标准库 `std::sync::mpsc`
//! 用法：
//! ```
//! use c05_threads::message_passing::channel::{channel, Sender, Receiver};
//! let (tx, rx): (Sender<i32>, Receiver<i32>) = channel();
//! tx.send(42).unwrap();
//! assert_eq!(rx.recv().unwrap(), 42);
//! ```

pub use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, TryRecvError, channel};
use std::time::Duration;

/// 尝试在超时内接收一条消息，映射 Err->None
pub fn try_recv_timeout<T>(rx: &Receiver<T>, timeout: Duration) -> Option<T> {
    rx.recv_timeout(timeout).ok()
}

/// 批量发送所有元素，遇到错误返回失败元素
pub fn send_all<T>(tx: &Sender<T>, items: impl IntoIterator<Item = T>) -> Result<(), T> {
    for item in items {
        tx.send(item).map_err(|e| e.0)?;
    }
    Ok(())
}

/// 拉取至多 n 条消息（非严格满）
pub fn drain_n<T>(rx: &Receiver<T>, n: usize) -> Vec<T> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        if let Ok(v) = rx.try_recv() {
            out.push(v);
        } else {
            break;
        }
    }
    out
}
