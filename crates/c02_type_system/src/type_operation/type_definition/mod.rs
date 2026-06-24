//! 类型定义：用 `struct`、`enum`、`type` 创建新类型。

/// 二维点。
pub struct Point {
    pub x: f64,
    pub y: f64,
}

/// 形状：圆或矩形。
pub enum Shape {
    Circle {
        center: Point,
        radius: f64,
    },
    Rectangle {
        top_left: Point,
        bottom_right: Point,
    },
}

/// 三维点类型别名。
pub type Point3D = (f64, f64, f64);

/// 计算 [`Shape`] 的面积。
pub fn area(shape: &Shape) -> f64 {
    match shape {
        Shape::Circle { radius, .. } => std::f64::consts::PI * radius * radius,
        Shape::Rectangle {
            top_left,
            bottom_right,
        } => {
            let width = (bottom_right.x - top_left.x).abs();
            let height = (bottom_right.y - top_left.y).abs();
            width * height
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circle_area() {
        let circle = Shape::Circle {
            center: Point { x: 0.0, y: 0.0 },
            radius: 1.0,
        };
        assert!((area(&circle) - std::f64::consts::PI).abs() < 1e-10);
    }

    #[test]
    fn test_rectangle_area() {
        let rect = Shape::Rectangle {
            top_left: Point { x: 0.0, y: 0.0 },
            bottom_right: Point { x: 2.0, y: 3.0 },
        };
        assert!((area(&rect) - 6.0).abs() < 1e-10);
    }

    #[test]
    fn test_point3d_alias() {
        let p: Point3D = (1.0, 2.0, 3.0);
        assert_eq!(p.2, 3.0);
    }
}
