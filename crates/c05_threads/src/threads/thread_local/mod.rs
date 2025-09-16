//! 线程局部存储（TLS）示例
//! 1) std::thread_local!
//! 2) 初始化一次与每线程独立副本
//! 3) 结合线程使用（补充）

use std::cell::RefCell;

thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

pub fn tls_increment() -> u32 {
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        *c.borrow()
    })
}

/// 在线程里使用 TLS（3）
pub fn tls_in_threads() -> (u32, u32) {
    let h = std::thread::spawn(|| tls_increment());
    let a = tls_increment();
    let b = h.join().unwrap();
    (a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_tls_increment_is_thread_local() {
        let main_first = tls_increment();
        assert_eq!(main_first, 1);

        let handle = thread::spawn(|| tls_increment());
        let other = handle.join().unwrap();
        assert_eq!(other, 1);

        let main_second = tls_increment();
        assert_eq!(main_second, 2);
    }

    #[test]
    fn test_tls_in_threads() {
        let (a, b) = tls_in_threads();
        assert_eq!(a, 1);
        assert_eq!(b, 1);
    }
}
