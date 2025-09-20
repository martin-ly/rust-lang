//! epoll/IOCP/kqueue 事件抽象（教学化占位实现）
//! - Linux: epoll (LT/ET)
//! - macOS/BSD: kqueue
//! - Windows: IOCP

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriggerMode {
    Level,
    Edge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interest {
    Readable,
    Writable,
    ReadWrite,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Event {
    pub fd: i32,
    pub readable: bool,
    pub writable: bool,
}

pub trait EventLoop {
    fn register(&mut self, fd: i32, interest: Interest, mode: TriggerMode) -> bool;
    fn reregister(&mut self, fd: i32, interest: Interest, mode: TriggerMode) -> bool;
    fn deregister(&mut self, fd: i32) -> bool;
    fn poll(&mut self, timeout_ms: i32) -> Vec<Event>;
}

/// 跨平台占位：Linux 使用 epoll，Windows 使用 IOCP，macOS 使用 kqueue。
/// 这里提供一个最简的可编译占位实现，方便上层编译通过与单元测试。
#[cfg(target_os = "linux")]
mod backend {
    use super::*;
    pub struct EventLoopImpl;
    impl EventLoopImpl {
        pub fn new() -> Self {
            Self
        }
    }
    impl EventLoop for EventLoopImpl {
        fn register(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn reregister(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn deregister(&mut self, _fd: i32) -> bool {
            true
        }
        fn poll(&mut self, _timeout_ms: i32) -> Vec<Event> {
            Vec::new()
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "openbsd"))]
mod backend {
    use super::*;
    pub struct EventLoopImpl;
    impl EventLoopImpl {
        pub fn new() -> Self {
            Self
        }
    }
    impl EventLoop for EventLoopImpl {
        fn register(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn reregister(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn deregister(&mut self, _fd: i32) -> bool {
            true
        }
        fn poll(&mut self, _timeout_ms: i32) -> Vec<Event> {
            Vec::new()
        }
    }
}

#[cfg(target_os = "windows")]
mod backend {
    use super::*;
    pub struct EventLoopImpl;
    impl Default for EventLoopImpl {
        fn default() -> Self {
            Self::new()
        }
    }

    impl EventLoopImpl {
        pub fn new() -> Self {
            Self
        }
    }
    impl EventLoop for EventLoopImpl {
        fn register(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn reregister(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn deregister(&mut self, _fd: i32) -> bool {
            true
        }
        fn poll(&mut self, _timeout_ms: i32) -> Vec<Event> {
            Vec::new()
        }
    }
}

#[cfg(not(any(
    target_os = "linux",
    target_os = "windows",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd"
)))]
mod backend {
    use super::*;
    pub struct EventLoopImpl;
    impl EventLoopImpl {
        pub fn new() -> Self {
            Self
        }
    }
    impl EventLoop for EventLoopImpl {
        fn register(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn reregister(&mut self, _fd: i32, _interest: Interest, _mode: TriggerMode) -> bool {
            true
        }
        fn deregister(&mut self, _fd: i32) -> bool {
            true
        }
        fn poll(&mut self, _timeout_ms: i32) -> Vec<Event> {
            Vec::new()
        }
    }
}

pub use backend::EventLoopImpl;

/// 最小事件循环 demo（跨平台占位）
pub fn minimal_demo() {
    let mut el = EventLoopImpl::new();
    let _ = el.register(0, Interest::Readable, TriggerMode::Level);
    let _events = el.poll(10);
}
