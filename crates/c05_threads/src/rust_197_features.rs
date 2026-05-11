//! Rust 1.97 特性跟踪模块 —— 线程与并发
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::pin::pin!` 和 `Vec::pop_if` 在线程/并发场景中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `pin!` 在栈上固定线程局部数据
    pub fn pin_thread_local<T: Clone>(data: T) -> T {
        let pinned = std::pin::pin!(data);
        pinned.clone()
    }

    /// 使用 `Vec::pop_if` 从任务队列中条件性取出任务
    pub fn pop_high_priority_task(tasks: &mut Vec<(u32, String)>) -> Option<(u32, String)> {
        tasks.pop_if(|(priority, _)| *priority >= 10)
    }

    /// 模拟并发安全的缓冲区管理
    pub fn manage_buffer<T: Clone>(
        buffer: &mut Vec<T>,
        should_drain: impl FnOnce(&mut T) -> bool,
    ) -> Option<T> {
        buffer.pop_if(should_drain)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pin_thread_local() {
        assert_eq!(Rust197Features::pin_thread_local(42i32), 42);
        assert_eq!(
            Rust197Features::pin_thread_local("data".to_string()),
            "data"
        );
    }

    #[test]
    fn test_pop_high_priority_task() {
        let mut tasks = vec![(1, "low".to_string()), (15, "high".to_string())];
        assert_eq!(
            Rust197Features::pop_high_priority_task(&mut tasks),
            Some((15, "high".to_string()))
        );
        assert_eq!(tasks, vec![(1, "low".to_string())]);

        let mut tasks2 = vec![(1, "low".to_string())];
        assert_eq!(Rust197Features::pop_high_priority_task(&mut tasks2), None);
    }

    #[test]
    fn test_manage_buffer() {
        let mut buf = vec![1, 2, 3];
        assert_eq!(
            Rust197Features::manage_buffer(&mut buf, |x| *x == 3),
            Some(3)
        );
        assert_eq!(buf, vec![1, 2]);
    }
}
