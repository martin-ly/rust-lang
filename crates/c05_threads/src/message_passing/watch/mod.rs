//! 简易同步 watch 通道：广播最新值的单生产者-多消费者模型（最小子集）。
//! 用法：
//! ```
//! use c05_threads::message_passing::watch;
//! let (tx, rx) = watch::channel(0u32);
//! tx.send(1);
//! assert_eq!(*rx.borrow(), 1);
//! ```

use std::sync::{Arc, Condvar, Mutex};

pub struct Sender<T> {
    inner: Arc<Inner<T>>,
}

#[derive(Clone)]
pub struct Receiver<T> {
    inner: Arc<Inner<T>>,
}

struct Inner<T> {
    state: Mutex<State<T>>,
    cv: Condvar,
}

struct State<T> {
    value: T,
    version: u64,
    closed: bool,
}

pub fn channel<T>(initial: T) -> (Sender<T>, Receiver<T>) {
    let inner = Arc::new(Inner {
        state: Mutex::new(State {
            value: initial,
            version: 0,
            closed: false,
        }),
        cv: Condvar::new(),
    });
    (
        Sender {
            inner: inner.clone(),
        },
        Receiver { inner },
    )
}

impl<T> Sender<T> {
    pub fn send(&self, value: T) {
        let mut guard = self.inner.state.lock().unwrap();
        if guard.closed {
            return;
        }
        guard.value = value;
        guard.version = guard.version.wrapping_add(1);
        self.inner.cv.notify_all();
    }

    pub fn close(&self) {
        let mut guard = self.inner.state.lock().unwrap();
        guard.closed = true;
        self.inner.cv.notify_all();
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut guard = self.inner.state.lock().unwrap();
        guard.closed = true;
        self.inner.cv.notify_all();
    }
}

impl<T: Clone> Receiver<T> {
    pub fn borrow(&self) -> T {
        let guard = self.inner.state.lock().unwrap();
        guard.value.clone()
    }

    pub fn changed(&self, last_seen: &mut u64) -> T {
        let mut guard = self.inner.state.lock().unwrap();
        while !guard.closed && *last_seen == guard.version {
            guard = self.inner.cv.wait(guard).unwrap();
        }
        *last_seen = guard.version;
        guard.value.clone()
    }

    pub fn try_changed(&self, last_seen: &mut u64) -> Option<T> {
        let guard = self.inner.state.lock().unwrap();
        if *last_seen != guard.version {
            *last_seen = guard.version;
            Some(guard.value.clone())
        } else {
            None
        }
    }

    pub fn is_closed(&self) -> bool {
        let guard = self.inner.state.lock().unwrap();
        guard.closed
    }

    /// 返回当前值并将 last_seen 更新为最新版本
    pub fn borrow_and_update(&self, last_seen: &mut u64) -> T {
        let guard = self.inner.state.lock().unwrap();
        *last_seen = guard.version;
        guard.value.clone()
    }

    /// 检查自 last_seen 以来是否有更新（不改变 last_seen）
    pub fn has_changed(&self, last_seen: u64) -> bool {
        let guard = self.inner.state.lock().unwrap();
        guard.version != last_seen
    }
}
