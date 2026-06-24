//! 类型组合：积类型（struct / tuple）与和类型（enum）。

/// 姓名 Newtype。
pub struct Name(pub String);

/// 年龄 Newtype。
pub struct Age(pub u8);

/// 人：两个积类型的组合。
pub struct Person {
    pub name: Name,
    pub age: Age,
}

impl Person {
    /// 构造一个 [`Person`]。
    pub fn new(name: &str, age: u8) -> Self {
        Self {
            name: Name(name.to_string()),
            age: Age(age),
        }
    }
}

/// 左或右：和类型。
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// 可计算面积的形状接口。
pub trait Shape {
    /// 计算面积。
    fn area(&self) -> f64;
}

/// 圆。
pub struct Circle(pub f64);

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.0 * self.0
    }
}

/// 矩形。
pub struct Rectangle(pub f64, pub f64);

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.0 * self.1
    }
}

/// 对任意形状引用切片求总面积。
pub fn total_area(shapes: &[&dyn Shape]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_person_composition() {
        let p = Person::new("Ada", 30);
        assert_eq!(p.name.0, "Ada");
        assert_eq!(p.age.0, 30);
    }

    #[test]
    fn test_sum_type() {
        let e: Either<i32, &str> = Either::Left(42);
        assert!(matches!(e, Either::Left(42)));
    }

    #[test]
    fn test_total_area() {
        let circle = Circle(1.0);
        let rect = Rectangle(2.0, 3.0);
        let shapes: &[&dyn Shape] = &[&circle, &rect];
        let area = total_area(shapes);
        assert!((area - (std::f64::consts::PI + 6.0)).abs() < 1e-10);
    }
}
