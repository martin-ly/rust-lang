//! # Brown University CRP Ownership Inventory — Program 01
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 移动语义 vs. Copy 语义 / Move Semantics vs. Copy Semantics
//!
//! ## 学习目标 / Learning Goal
//!
//! 判断哪些类型在赋值时会发生所有权转移（move），哪些会被按位复制（Copy）。
//! Identify which types move ownership on assignment and which are bitwise copied (Copy).
//!
//! ## TODO
//!
//! 1. 在修复 `analyze_ownership` 之前，先预测哪些行会编译失败。
//! 2. 修改函数体（不要改签名），使其在保持原值可用的前提下返回长度之和。
//! 3. 解释为什么 `i32` 不会 move，而 `String` 会 move。

/// 返回两个数字和两个字符串长度的总和。
/// Returns the sum of lengths of two numbers (as string) and two strings.
///
/// TODO: 当前实现会导致 String 的 move 错误。请使用借用修复。
pub fn analyze_ownership(a: i32, b: i32, s1: String, s2: String) -> usize {
    // i32 实现 Copy，因此 a 和 b 可以继续使用。
    let _sum_numbers = a + b;

    // String 不实现 Copy，默认发生 move。
    // TODO: 请改用借用，避免拿走 s1 和 s2 的所有权。
    let len1 = s1.len();
    let len2 = s2.len();

    // 返回后 s1 和 s2 仍然有效。
    len1 + len2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analyze_ownership() {
        let x = 42;
        let y = 7;
        let hello = String::from("hello");
        let world = String::from("world");

        let total = analyze_ownership(x, y, hello, world);

        assert_eq!(total, 10);
        // TODO: 如果上面把 String move 走了，下面两行就无法通过。
        // 请确认修复后 x、y、hello、world 都仍然可用。
        assert_eq!(x + y, 49);
        // 注意：测试中此处没有再次使用 hello/world，因为函数参数已按值传入。
        // 但在实际调用点，调用者仍希望保留原变量可用。
    }
}
