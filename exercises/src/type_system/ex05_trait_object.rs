//! # 练习 5: 特质对象
//!
//! **难度**: Medium  
//! **考点**: trait、dyn Trait、动态分发
//!
//! ## 题目描述
//!
//! 定义一个 `Shape` 特质，为 Circle 和 Rectangle 实现它，
//! 然后使用特质对象进行多态调用。

use std::f64::consts::PI;

/// 可绘制的形状
pub trait Shape {
    /// 计算面积
    fn area(&self) -> f64;
    /// 返回形状名称
    fn name(&self) -> &'static str;
}

/// 圆形
#[derive(Debug, Clone, Copy)]
pub struct Circle {
    pub radius: f64,
}

/// 矩形
#[derive(Debug, Clone, Copy)]
pub struct Rect {
    pub width: f64,
    pub height: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        PI * self.radius * self.radius
    }

    fn name(&self) -> &'static str {
        "Circle"
    }
}

impl Shape for Rect {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn name(&self) -> &'static str {
        "Rectangle"
    }
}

/// 计算所有形状的总面积
pub fn total_area(shapes: &[Box<dyn Shape>]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

/// 返回面积最大的形状名称
pub fn largest_shape_name(shapes: &[Box<dyn Shape>]) -> Option<&'static str> {
    shapes.iter().max_by(|a, b| a.area().total_cmp(&b.area())).map(|s| s.name())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circle_area() {
        let c = Circle { radius: 1.0 };
        assert!((c.area() - PI).abs() < 0.0001);
    }

    #[test]
    fn test_rect_area() {
        let r = Rect { width: 3.0, height: 4.0 };
        assert_eq!(r.area(), 12.0);
    }

    #[test]
    fn test_total_area() {
        let shapes: Vec<Box<dyn Shape>> = vec![
            Box::new(Circle { radius: 1.0 }),
            Box::new(Rect { width: 2.0, height: 3.0 }),
        ];
        let expected = PI + 6.0;
        assert!((total_area(&shapes) - expected).abs() < 0.0001);
    }

    #[test]
    fn test_largest_shape() {
        let shapes: Vec<Box<dyn Shape>> = vec![
            Box::new(Circle { radius: 1.0 }),
            Box::new(Rect { width: 10.0, height: 10.0 }),
        ];
        assert_eq!(largest_shape_name(&shapes), Some("Rectangle"));
    }
}
