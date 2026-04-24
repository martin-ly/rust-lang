//! # 练习 2: 派生宏框架
//!
//! **难度**: Hard  
//! **考点**: 过程宏概念、proc_macro2、quote
//!
//! ## 题目描述
//!
//! 本练习为概念性框架，展示如何为结构体生成 `Describe` 特质实现。
//! 由于过程宏需要单独的 proc-macro crate，本文件提供核心逻辑 stub。
//!
//! ## 实际实现步骤
//!
//! 1. 创建 `exercises/macros_derive/` proc-macro crate
//! 2. 实现 `#[derive(Describe)]`
//! 3. 生成 `fn describe(&self) -> String`

/// Describe 特质：为类型提供自我描述
pub trait Describe {
    fn describe(&self) -> String;
}

/// 手动实现 Describe 的示例
#[derive(Debug)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Describe for Point {
    fn describe(&self) -> String {
        format!("Point {{ x: {}, y: {} }}", self.x, self.y)
    }
}

/// 为简单枚举手动实现
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Status {
    Active,
    Inactive,
    Pending,
}

impl Describe for Status {
    fn describe(&self) -> String {
        match self {
            Status::Active => "状态: 活跃".to_string(),
            Status::Inactive => "状态: 非活跃".to_string(),
            Status::Pending => "状态: 待定".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_describe() {
        let p = Point { x: 1.0, y: 2.0 };
        assert_eq!(p.describe(), "Point { x: 1, y: 2 }");
    }

    #[test]
    fn test_status_describe() {
        assert_eq!(Status::Active.describe(), "状态: 活跃");
        assert_eq!(Status::Pending.describe(), "状态: 待定");
    }
}
