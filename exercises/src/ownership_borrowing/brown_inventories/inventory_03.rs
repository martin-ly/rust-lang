//! # Brown University CRP Ownership Inventory — Program 03
//!
//! **EN**: Avoiding Dangling References
//! **Summary**: Learn to return owned data instead of references to local variables or
//! temporary values.
//! **Key Terms**: 悬垂引用 (dangling reference), 生命周期 (lifetime), 返回值 (return value),
//! 拥有所有权 (owned), 局部变量 (local variable), 临时值 (temporary value).
//! **Related Concepts**:
//! [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md).
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 悬垂引用 / Dangling References
//!
//! ## 学习目标 / Learning Goal
//!
//! 识别并避免返回指向局部变量或临时值的引用。
//! Identify and avoid returning references to local variables or temporary values.
//!
//! ## TODO / Tasks
//!
//! 1. 下面的 `get_longest_bad` 试图返回局部变量的引用。预测编译错误信息。
//!    The `get_longest_bad` function below tries to return a reference to a local variable.
//!    Predict the compiler error message.
//! 2. 将其实现为 `get_longest_good`，通过返回 owned String 避免悬垂引用。
//!    Implement `get_longest_good` by returning an owned `String` to avoid dangling.
//! 3. 什么时候返回 `&str` 是安全的？（提示：输入参数的生命周期）
//!    When is it safe to return `&str`? (Hint: lifetimes of the input parameters.)

// 错误版本：返回局部变量的引用，导致悬垂引用。
// Broken version: returns a reference to a local variable, creating a dangling reference.
//
// TODO: 取消注释并观察编译错误，然后实现下方的正确版本。
// TODO: Uncomment and observe the compile error, then implement the correct version below.
// pub fn get_longest_bad(a: &str, b: &str) -> &str {
//     let longest = if a.len() > b.len() { a } else { b };
//     longest
// }

/// 正确版本：返回拥有所有权的 String，而不是局部引用。
/// Correct version: returns an owned String instead of a local reference.
pub fn get_longest_good(a: &str, b: &str) -> String {
    // TODO: 如果 a 更长返回 a 的拷贝，否则返回 b 的拷贝。
    // TODO: Return a copy of `a` if it is longer, otherwise a copy of `b`.
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
