//! 类型等价：同构与不同构。
//!
//! Rust 使用**名义类型系统**（nominal typing）：字段结构相同但名字不同的类型
//! 在类型系统中并不等价。Newtype 与底层类型也不等价，但可以通过显式函数建立同构。

/// 点别名。
pub type Point = (f64, f64);

/// 与 [`Point`] 字段结构相同但名称不同的类型。
pub struct Coordinate {
    /// x 坐标。
    pub x: f64,
    /// y 坐标。
    pub y: f64,
}

impl Coordinate {
    /// 转换为同构的元组。
    pub fn to_tuple(&self) -> Point {
        (self.x, self.y)
    }
}

/// 米：Newtype，与 `f64` 不同构于类型系统。
#[derive(Debug, PartialEq)]
pub struct Meters(pub f64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nominal_types_are_distinct() {
        let c = Coordinate { x: 1.0, y: 2.0 };
        let p: Point = c.to_tuple();
        assert_eq!(p, (1.0, 2.0));
    }

    #[test]
    fn newtype_distinct_from_underlying() {
        let m = Meters(10.0);
        // 必须显式取出底层值，不能直接当作 f64 使用。
        assert_eq!(m.0 + 5.0, 15.0);
    }
}
