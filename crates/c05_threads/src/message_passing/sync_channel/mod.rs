//! 同步容量通道：标准库 `std::sync::mpsc::sync_channel`
//! 用法：
//! ```
//! use c05_threads::message_passing::sync_channel::{sync_channel, SyncSender, Receiver};
//! let (tx, rx): (SyncSender<i32>, Receiver<i32>) = sync_channel(1);
//! tx.send(1).unwrap();
//! assert_eq!(rx.recv().unwrap(), 1);
//! ```

pub use std::sync::mpsc::{sync_channel, Receiver, SyncSender, RecvTimeoutError, TryRecvError};
use std::time::Duration;

pub fn try_recv_timeout<T>(rx: &Receiver<T>, timeout: Duration) -> Option<T> {
    rx.recv_timeout(timeout).ok()
}

pub fn send_all<T>(tx: &SyncSender<T>, items: impl IntoIterator<Item = T>) -> Result<(), T> {
    for item in items { tx.send(item).map_err(|e| e.0)?; }
    Ok(())
}

pub fn drain_n<T>(rx: &Receiver<T>, n: usize) -> Vec<T> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n { if let Ok(v) = rx.try_recv() { out.push(v); } else { break; } }
    out
}
