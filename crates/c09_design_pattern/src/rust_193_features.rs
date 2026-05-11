//! Rust 1.93.0 设计模式 特性模块
#![allow(clippy::incompatible_msrv)]

use std::fmt;
use std::mem::MaybeUninit;

/// 使用 `fmt::from_fn` 实现动态格式化策略模式
pub fn dynamic_formatter(strategy: &str, value: i32) -> impl fmt::Display + use<'_> {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| match strategy {
        "hex" => write!(f, "0x{:X}", value),
        "bin" => write!(f, "0b{:b}", value),
        _ => write!(f, "{}", value),
    })
}

/// 使用 `MaybeUninit` 实现懒初始化模式（Lazy Init）
pub struct LazyInit<T> {
    slot: MaybeUninit<T>,
    initialized: bool,
}

impl<T> LazyInit<T> {
    pub fn new() -> Self {
        Self {
            slot: MaybeUninit::uninit(),
            initialized: false,
        }
    }

    pub fn get_or_init<F: FnOnce() -> T>(&mut self, f: F) -> &T {
        if !self.initialized {
            self.slot.write(f());
            self.initialized = true;
        }
        // SAFETY: initialized 为 true 时 slot 已被写入
        unsafe { self.slot.assume_init_ref() }
    }
}

impl<T> Drop for LazyInit<T> {
    fn drop(&mut self) {
        if self.initialized {
            // SAFETY: initialized 为 true 时 slot 包含有效值
            unsafe { self.slot.assume_init_drop() };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dynamic_formatter() {
        assert_eq!(format!("{}", dynamic_formatter("hex", 255)), "0xFF");
        assert_eq!(format!("{}", dynamic_formatter("bin", 5)), "0b101");
        assert_eq!(format!("{}", dynamic_formatter("dec", 42)), "42");
    }

    #[test]
    fn test_lazy_init() {
        let mut lazy = LazyInit::new();
        let counter = std::cell::Cell::new(0);
        let v1 = lazy.get_or_init(|| {
            counter.set(counter.get() + 1);
            counter.get()
        });
        assert_eq!(*v1, 1);
        let v2 = lazy.get_or_init(|| {
            counter.set(counter.get() + 1);
            counter.get()
        });
        assert_eq!(*v2, 1); // 不会再次初始化
    }

    #[test]
    fn test_lazy_init_drop() {
        let mut lazy: LazyInit<String> = LazyInit::new();
        lazy.get_or_init(|| String::from("test drop"));
        drop(lazy);
    }
}
