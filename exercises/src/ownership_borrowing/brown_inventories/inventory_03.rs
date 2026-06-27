//! # Brown University CRP Ownership Inventory — Program 03
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 悬垂引用 / Dangling References
//!
//! ## 学习目标 / Learning Goal
//!
//! 识别并避免返回指向局部变量或临时值的引用。
//! Identify and avoid returning references to local variables or temporary values.
//!
//! ## TODO
//!
//! 1. 下面的 `get_longest_bad` 试图返回局部变量的引用。预测编译错误信息。
//! 2. 将其实现为 `get_longest_good`，通过返回 owned String 避免悬垂引用。
//! 3. 什么时候返回 `&str` 是安全的？（提示：输入参数的生命周期）

// 错误版本：返回局部变量的引用，导致悬垂引用。
// Broken version: returns a reference to a local variable, creating a dangling reference.
//
// TODO: 取消注释并观察编译错误，然后实现下方的正确版本。
// pub fn get_longest_bad(a: &str, b: &str) -> &str {
//     let longest = if a.len() > b.len() { a } else { b };
//     longest
// }

/// 正确版本：返回拥有所有权的 String，而不是局部引用。
/// Correct version: returns an owned String instead of a local reference.
pub fn get_longest_good(a: &str, b: &str) -> String {
    // TODO: 如果 a 更长返回 a 的拷贝，否则返回 b 的拷贝。
    if a.len() > b.len() {
        a.to_string()
    } else {
        b.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_longest_good() {
        let x = "short";
        let y = "loooooong";
        let result = get_longest_good(x, y);
        assert_eq!(result, "loooooong");
    }

    #[test]
    fn test_get_longest_equal() {
        let x = "rust";
        let y = "safe";
        let result = get_longest_good(x, y);
        // 长度相等时返回 b
        assert_eq!(result, "safe");
    }
}
