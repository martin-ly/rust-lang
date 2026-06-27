//! # Brown University CRP Ownership Inventory — Program 02
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 可变借用规则 / Mutable Borrowing Rules
//!
//! ## 学习目标 / Learning Goal
//!
//! 理解 Rust 的核心借用规则：在同一作用域内，不能同时存在对同一数据的可变引用与不可变引用。
//! Understand Rust's core borrowing rule: mutable and immutable references to the same data
//! cannot coexist in the same scope.
//!
//! ## TODO
//!
//! 1. 解释为什么同时存在 `&data` 和 `&mut data` 会导致编译错误。
//! 2. 重新排列或缩小借用范围，使代码通过编译。
//! 3. 思考：如果编译器允许这样做，会产生什么内存安全问题？

/// 先打印数据，再原地修改数据。
/// Prints the data first, then mutates it in place.
///
/// TODO: 当前实现试图同时持有不可变借用和可变借用。请修复。
pub fn print_then_append(data: &mut String, suffix: &str) {
    // 不可变借用：读取当前内容
    let current = &*data;
    println!("before: {}", current);

    // TODO: 下面这行需要可变借用，但它与上面的 current 重叠了。
    // 请在完成所有读取后再获取可变借用。
    data.push_str(suffix);

    println!("after: {}", data);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print_then_append() {
        let mut s = String::from("hello");
        print_then_append(&mut s, " world");
        assert_eq!(s, "hello world");
    }
}
