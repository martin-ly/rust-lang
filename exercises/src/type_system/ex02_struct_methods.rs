//! # 练习 2: 结构体与方法
//!
//! **难度**: Easy  
//! **考点**: struct、impl、关联函数、方法
//!
//! ## 题目描述
//!
//! 实现一个 `Rectangle` 结构体，包含宽度和高度。
//! 提供计算面积、判断是否为正方形、以及缩放的方法。

/// 矩形
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Rectangle {
    /// 创建一个新的矩形
    pub fn new(width: f64, height: f64) -> Self {
        Self { width, height }
    }

    /// 计算面积
    pub fn area(&self) -> f64 {
        self.width * self.height
    }

    /// 判断是否为正方形
    pub fn is_square(&self) -> bool {
        (self.width - self.height).abs() < f64::EPSILON
    }

    /// 按倍数缩放矩形（修改自身）
    pub fn scale(&mut self, factor: f64) {
        self.width *= factor;
        self.height *= factor;
    }

    /// 返回缩放后的新矩形（不修改自身）
    pub fn scaled(&self, factor: f64) -> Self {
        Self::new(self.width * factor, self.height * factor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rectangle_area() {
        let rect = Rectangle::new(3.0, 4.0);
        assert_eq!(rect.area(), 12.0);
    }

    #[test]
    fn test_is_square() {
        assert!(Rectangle::new(5.0, 5.0).is_square());
        assert!(!Rectangle::new(3.0, 4.0).is_square());
    }

    #[test]
    fn test_scale() {
        let mut rect = Rectangle::new(2.0, 3.0);
        rect.scale(2.0);
        assert_eq!(rect.width, 4.0);
        assert_eq!(rect.height, 6.0);
    }

    #[test]
    fn test_scaled() {
        let rect = Rectangle::new(2.0, 3.0);
        let new_rect = rect.scaled(3.0);
        assert_eq!(new_rect.area(), 54.0); // (2*3) * (3*3) = 54
        assert_eq!(rect.area(), 6.0); // 原矩形不变
    }
}
