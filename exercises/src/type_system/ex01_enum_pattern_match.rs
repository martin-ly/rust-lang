//! # 练习 1: 枚举与模式匹配
//!
//! **难度**: Easy  
//! **考点**: 枚举定义、Option<T>、match 表达式
//!
//! ## 题目描述
//!
//! 定义一个 `TrafficLight` 枚举，包含红、黄、绿三种状态。
//! 实现函数返回每种灯持续的时间（秒）。
//! 同时实现一个函数，使用 `Option<u8>` 来描述可能缺失的年龄。

/// 交通信号灯
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TrafficLight {
    Red,
    Yellow,
    Green,
}

/// 返回每种灯的持续时间（秒）
pub fn duration(light: TrafficLight) -> u8 {
    match light {
        TrafficLight::Red => 30,
        TrafficLight::Yellow => 5,
        TrafficLight::Green => 45,
    }
}

/// 如果年龄大于 0 且小于 150，返回 Some(age)，否则返回 None
pub fn validate_age(age: i32) -> Option<u8> {
    if age > 0 && age < 150 {
        Some(age as u8)
    } else {
        None
    }
}

/// 对 Option 值进行加倍，如果是 None 则返回 None
pub fn double_option(x: Option<i32>) -> Option<i32> {
    x.map(|v| v * 2)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_traffic_light_duration() {
        assert_eq!(duration(TrafficLight::Red), 30);
        assert_eq!(duration(TrafficLight::Yellow), 5);
        assert_eq!(duration(TrafficLight::Green), 45);
    }

    #[test]
    fn test_validate_age_valid() {
        assert_eq!(validate_age(25), Some(25));
    }

    #[test]
    fn test_validate_age_invalid() {
        assert_eq!(validate_age(-1), None);
        assert_eq!(validate_age(150), None);
    }

    #[test]
    fn test_double_option() {
        assert_eq!(double_option(Some(5)), Some(10));
        assert_eq!(double_option(None), None);
    }
}
