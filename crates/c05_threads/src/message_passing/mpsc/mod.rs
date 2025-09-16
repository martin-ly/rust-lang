//! 多生产者-单/多消费者（MPSC/MPMC）通道：`crossbeam_channel`
//! 用法：
//! ```
//! use c05_threads::message_passing::mpsc::{unbounded, Sender, Receiver};
//! let (tx, rx): (Sender<i32>, Receiver<i32>) = unbounded();
//! tx.send(7).unwrap();
//! assert_eq!(rx.recv().unwrap(), 7);
//! ```

pub use crossbeam_channel::{
    Receiver, RecvTimeoutError, SendError, Sender, TryRecvError, TrySendError, bounded, unbounded,
};
use std::time::Duration;

pub fn try_recv_timeout<T>(rx: &Receiver<T>, timeout: Duration) -> Option<T> {
    rx.recv_timeout(timeout).ok()
}

pub fn send_all<T>(tx: &Sender<T>, items: impl IntoIterator<Item = T>) -> Result<(), T> {
    for item in items {
        tx.send(item).map_err(|e| e.into_inner())?;
    }
    Ok(())
}

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
