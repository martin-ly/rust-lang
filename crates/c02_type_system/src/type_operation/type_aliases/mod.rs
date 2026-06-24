//! 类型别名：`type` 关键字、泛型别名、与 Newtype 的区别。

/// 二维点别名（积类型）。
pub type Point = (f64, f64);

/// 由点组成的向量。
pub type Vector = Vec<Point>;

/// 用户 ID 别名：语义不同，但类型系统上与 `u32` 完全等价。
pub type UserId = u32;

/// 产品 ID 别名。
pub type ProductId = u32;

/// 可发送同步的错误对象。
pub type BoxedError = Box<dyn std::error::Error + Send + Sync>;

/// 本模块默认的 [`Result`] 别名。
pub type Result<T> = std::result::Result<T, BoxedError>;

/// 计算两点距离。
pub fn distance(a: Point, b: Point) -> f64 {
    let dx = a.0 - b.0;
    let dy = a.1 - b.1;
    (dx * dx + dy * dy).sqrt()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alias_is_interchangeable() {
        let uid: UserId = 1;
        let pid: ProductId = uid; // 别名与 u32 完全等价
        assert_eq!(pid, 1);
    }

    #[test]
    fn test_distance() {
        let a: Point = (0.0, 0.0);
        let b: Point = (3.0, 4.0);
        assert!((distance(a, b) - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_result_alias() -> Result<()> {
        let v: Result<i32> = Ok(42);
        assert_eq!(v?, 42);
        Ok(())
    }
}
