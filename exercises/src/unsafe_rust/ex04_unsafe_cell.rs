//! # 练习 4: UnsafeCell 与内部可变性
//!
//! **难度**: Medium  
//! **考点**: `UnsafeCell<T>`、内部可变性、`*const`/`*mut` 转换、编译期 vs 运行期检查
//!
//! ## 题目描述
//!
//! `Cell<T>` 是 Rust 标准库中提供内部可变性的重要类型，它允许你在拥有 `&Cell<T>`
//! （不可变引用）的情况下修改内部值——代价是 `T` 不能存在指向自身的引用（即 `T: Copy`）。
//!
//! 请使用 `UnsafeCell<T>` 从零实现一个简化版的 `MyCell<T>`，支持：
//! - `new(value: T) -> MyCell<T>`
//! - `get(&self) -> T`（要求 `T: Copy`）
//! - `set(&self, value: T)`
//! - `replace(&self, value: T) -> T`
//!
//! ## 要求
//!
//! - 内部使用 `UnsafeCell<T>` 存储值
//! - `get` 和 `set` 使用原始指针进行读写
//! - 所有 unsafe 操作限制在方法内部
//! - 公开 API 是 safe 的
//!
//! ## 提示
//!
//! - `UnsafeCell::get()` 返回 `*mut T`
//! - 对于 `get()`，你需要 `T: Copy` 来避免返回引用导致的别名问题
//! - `ptr::read` 和 `ptr::write` 是关键操作
//! - `replace` 可以先读取旧值，再写入新值

use std::cell::UnsafeCell;

/// 简化版 Cell，基于 UnsafeCell 实现内部可变性
pub struct MyCell<T> {
    value: UnsafeCell<T>,
}

// SAFETY: MyCell 可以安全地在线程间传递（如果 T 可以）
// 但不像标准库 Cell，我们不实现 Sync，因为内部可变性 + 非原子操作 = 线程不安全
unsafe impl<T: Send> Send for MyCell<T> {}

impl<T> MyCell<T> {
    /// 创建一个新的 MyCell
    pub const fn new(value: T) -> MyCell<T> {
        MyCell {
            value: UnsafeCell::new(value),
        }
    }

    /// 获取内部值的副本（要求 T: Copy）
    ///
    /// # 为什么需要 Copy？
    ///
    /// 因为我们返回的是值的副本而非引用，避免创建与内部存储重叠的引用。
    pub fn get(&self) -> T
    where
        T: Copy,
    {
        // SAFETY: 我们持有 &self，且 UnsafeCell 保证内部数据有效
        // 由于 T: Copy，读取不会转移所有权
        unsafe { *self.value.get() }
    }

    /// 设置内部值
    pub fn set(&self, value: T) {
        // SAFETY: 我们持有 &self，拥有对内部数据的独占访问权
        // （从 Cell 的语义来看，set 操作不会与 get 并发，因为单线程）
        unsafe {
            *self.value.get() = value;
        }
    }

    /// 替换内部值，返回旧值
    pub fn replace(&self, value: T) -> T {
        // SAFETY: 读取旧值后立即写入新值，不会存在悬垂引用
        unsafe {
            let old = std::ptr::read(self.value.get());
            std::ptr::write(self.value.get(), value);
            old
        }
    }

    /// 获取内部原始指针（unsafe 原始操作出口）
    ///
    /// # Safety
    ///
    /// 调用者必须确保不会违反 Rust 的别名规则。
    pub const fn as_ptr(&self) -> *mut T {
        self.value.get()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_cell_new_and_get() {
        let cell = MyCell::new(42);
        assert_eq!(cell.get(), 42);
    }

    #[test]
    fn test_my_cell_set() {
        let cell = MyCell::new(10);
        cell.set(20);
        assert_eq!(cell.get(), 20);
    }

    #[test]
    fn test_my_cell_replace() {
        let cell = MyCell::new(100);
        let old = cell.replace(200);
        assert_eq!(old, 100);
        assert_eq!(cell.get(), 200);
    }

    #[test]
    fn test_my_cell_with_immutable_ref() {
        let cell = MyCell::new(1);
        let ref_to_cell = &cell;

        // 通过不可变引用修改内部值——这是内部可变性的核心
        ref_to_cell.set(2);
        assert_eq!(ref_to_cell.get(), 2);
    }

    #[test]
    fn test_my_cell_with_non_copy_type_replace() {
        // replace 不需要 Copy，因为它转移所有权
        let cell = MyCell::new(String::from("hello"));
        let old = cell.replace(String::from("world"));
        assert_eq!(old, "hello");
        // 注意：get() 需要 Copy，所以不能直接对 String 调用 get()
        // 但我们可以通过 replace 来操作
        let current = cell.replace(String::from("!"));
        assert_eq!(current, "world");
    }

    #[test]
    fn test_my_cell_multiple_refs() {
        let cell = MyCell::new(0i32);
        let r1 = &cell;
        let r2 = &cell;

        r1.set(1);
        r2.set(2);
        assert_eq!(r1.get(), 2);
        assert_eq!(r2.get(), 2);
    }
}
