// 练习: 泛型参数使用错误
// 目标: 修复 make_pair 函数
// 考点: 泛型参数声明后必须在参数列表中使用

pub fn make_pair(a: T, b: T) -> (T, T) {
    (a, b)
}

pub fn use_pair() {
    let pair = make_pair(1, 2); // 错误: T 未定义
    assert_eq!(pair.0, 1);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_use_pair() {
        use_pair();
    }
}
