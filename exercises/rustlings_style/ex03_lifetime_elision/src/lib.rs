// 练习: 显式生命周期标注
// 目标: 为函数添加正确的生命周期参数
// 考点: 返回引用时必须显式标注生命周期

pub fn first_or_default(a: &str, b: &str) -> &str {
    if a.is_empty() {
        b
    } else {
        a
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_or_default() {
        assert_eq!(first_or_default("hello", "world"), "hello");
        assert_eq!(first_or_default("", "world"), "world");
    }
}
