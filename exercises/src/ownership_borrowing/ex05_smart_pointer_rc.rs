//! # 练习 5: Rc 智能指针共享所有权
//!
//! **难度**: Medium  
//! **考点**: Rc<T>、引用计数、共享不可变数据
//!
//! ## 题目描述
//!
//! 使用 `Rc<String>` 实现一个共享的配置项，
//! 让多个消费者共享同一个配置字符串。

use std::rc::Rc;

/// 创建一个共享的配置项
pub fn create_shared_config(value: &str) -> Rc<String> {
    Rc::new(String::from(value))
}

/// 获取当前引用计数
pub fn get_ref_count(config: &Rc<String>) -> usize {
    Rc::strong_count(config)
}

/// 克隆共享配置（增加引用计数）
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
