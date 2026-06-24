//! Unsafe 类型抽象：裸指针、`UnsafeCell` 与内部可变性。
//!
//! 这些示例展示如何在安全包装下使用 unsafe 原语。

/// 通过裸指针读取值。
///
/// # Safety
///
/// `r` 必须指向有效且未被释放的 `i32`。
pub unsafe fn read_via_raw_ptr(r: *const i32) -> i32 {
    // SAFETY: caller guarantees `r` is valid.
    unsafe { *r }
}

/// 通过裸指针修改值。
///
/// # Safety
///
/// `r` 必须指向可写的有效内存。
pub unsafe fn increment_raw_ptr(r: *mut i32) {
    // SAFETY: caller guarantees `r` points to writable memory.
    unsafe {
        *r += 1;
    }
}

/// 使用 `UnsafeCell` 实现的安全封装计数器。
pub struct UnsafeCounter {
    value: std::cell::UnsafeCell<i32>,
}

impl UnsafeCounter {
    /// 创建计数器。
    pub fn new(v: i32) -> Self {
        Self {
            value: std::cell::UnsafeCell::new(v),
        }
    }

    /// 读取当前值。
    pub fn get(&self) -> i32 {
        unsafe { *self.value.get() }
    }

    /// 增加指定数值。
    pub fn add(&self, n: i32) {
        unsafe {
            *self.value.get() += n;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_pointer_roundtrip() {
        let x = 42;
        assert_eq!(unsafe { read_via_raw_ptr(&x) }, 42);
    }

    #[test]
    fn raw_pointer_mutation() {
        let mut x = 10;
        unsafe {
            increment_raw_ptr(&mut x);
        }
        assert_eq!(x, 11);
    }

    #[test]
    fn unsafe_cell_counter() {
        let c = UnsafeCounter::new(0);
        c.add(5);
        c.add(3);
        assert_eq!(c.get(), 8);
    }
}
