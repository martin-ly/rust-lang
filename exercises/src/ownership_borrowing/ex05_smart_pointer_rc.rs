//! # 练习 5: Rc 智能指针共享所有权 / Exercise 5: Rc Smart Pointer for Shared Ownership
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: `Rc<T>`、引用计数、共享不可变数据
//!   `Rc<T>`, reference counting, shared immutable data
//!
//! ## 题目描述 / Problem Description
//!
//! 使用 `Rc<String>` 实现一个共享的配置项，
//! 让多个消费者共享同一个配置字符串。
//! Use `Rc<String>` to implement a shared configuration item,
//! allowing multiple consumers to share the same configuration string.

use std::rc::Rc;

/// 创建一个共享的配置项
/// Creates a shared configuration item
pub fn create_shared_config(value: &str) -> Rc<String> {
    Rc::new(String::from(value))
}

/// 获取当前引用计数
/// Gets the current reference count
pub fn get_ref_count(config: &Rc<String>) -> usize {
    Rc::strong_count(config)
}

/// 克隆共享配置（增加引用计数）
/// Clones the shared config (increments reference count)
pub fn clone_config(config: &Rc<String>) -> Rc<String> {
    Rc::clone(config)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_config() {
        let config = create_shared_config("debug=true");
        assert_eq!(get_ref_count(&config), 1);

        let config2 = clone_config(&config);
        assert_eq!(get_ref_count(&config), 2);
        assert_eq!(*config2, "debug=true");

        let _config3 = clone_config(&config);
        assert_eq!(get_ref_count(&config), 3);
    }

    #[test]
    fn test_rc_equality() {
        let c1 = create_shared_config("production");
        let c2 = clone_config(&c1);
        assert!(Rc::ptr_eq(&c1, &c2));
    }
}
