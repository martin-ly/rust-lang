//! 引用类型：`&T`、`&mut T`、切片、`dyn Trait`。
//!
//! 引用本身总是 `Sized`（指针大小），但指向的值可能是 `?Sized`。

/// 返回引用指向值的大小（对于 trait object / 切片是“胖指针”指向内容的大小）。
pub fn referent_size<T: ?Sized>(_r: &T) -> usize {
    std::mem::size_of_val(_r)
}

/// 对切片求和。
pub fn slice_sum(s: &[i32]) -> i32 {
    s.iter().sum()
}

/// 通过 trait object 进行动态分派。
pub fn trait_object_to_string(x: &dyn std::fmt::Display) -> String {
    format!("{}", x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slice_sum() {
        assert_eq!(slice_sum(&[1, 2, 3, 4]), 10);
    }

    #[test]
    fn test_trait_object() {
        assert_eq!(trait_object_to_string(&42), "42");
        assert_eq!(trait_object_to_string(&"hello"), "hello");
    }

    #[test]
    fn test_referent_size() {
        let arr = [1_i32, 2, 3];
        let slice: &[i32] = &arr;
        assert_eq!(referent_size(slice), 12);
    }
}
