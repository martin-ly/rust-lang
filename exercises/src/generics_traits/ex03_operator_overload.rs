//! # 练习 3: 运算符重载 / Exercise 3: Operator Overloading
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: std::ops 特质、运算符重载
//!   std::ops traits, operator overloading
//!
//! ## 题目描述 / Problem Description
//!
//! 实现一个简单的二维向量类型，支持加法和减法运算。
//! Implement a simple 2D vector type supporting addition and subtraction.

use std::ops::{Add, Sub};

/// 二维向量 / 2D vector
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Vec2 {
    pub x: f64,
    pub y: f64,
}

impl Vec2 {
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// 计算长度
    /// Calculates the magnitude
    pub fn magnitude(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }

    /// 点积
    /// Computes the dot product
    pub fn dot(self, other: Self) -> f64 {
        self.x * other.x + self.y * other.y
    }
}

impl Add for Vec2 {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::new(self.x + other.x, self.y + other.y)
    }
}

impl Sub for Vec2 {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::new(self.x - other.x, self.y - other.y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec2_add() {
        let a = Vec2::new(1.0, 2.0);
        let b = Vec2::new(3.0, 4.0);
        assert_eq!(a + b, Vec2::new(4.0, 6.0));
    }

    #[test]
    fn test_vec2_sub() {
        let a = Vec2::new(5.0, 5.0);
        let b = Vec2::new(2.0, 3.0);
        assert_eq!(a - b, Vec2::new(3.0, 2.0));
    }

    #[test]
    fn test_vec2_magnitude() {
        let v = Vec2::new(3.0, 4.0);
        assert!((v.magnitude() - 5.0).abs() < 0.0001);
    }

    #[test]
    fn test_vec2_dot() {
        let a = Vec2::new(1.0, 2.0);
        let b = Vec2::new(3.0, 4.0);
        assert!((a.dot(b) - 11.0).abs() < 0.0001);
    }
}
