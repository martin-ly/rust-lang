//! # 练习 12: 循环中的所有权 / Exercise 12: Ownership in Loops
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 在循环中构建 `Vec<String>` 时的移动与借用
//!   Moves and borrows when building a `Vec<String>` in a loop
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `build_greetings`，接收一个名字列表 `&[&str]`，
//! 为每个名字生成问候语 `String`（如 `"Hello, Alice!"`），并收集到 `Vec<String>` 返回。
//!
//! 注意：`String` 不实现 `Copy`，每次 `format!` 都会生成新的 `String`，
//! 可以直接移入 `Vec`。
//!
//! ## 提示 / Hints
//!
//! - 使用 `names.iter().map(...).collect()`
//! - `format!("Hello, {}!", name)` 创建新的 `String`

/// 为每个名字生成问候语并返回 Vec<String>
/// Generates a greeting for each name and returns a Vec<String>
pub fn build_greetings(names: &[&str]) -> Vec<String> {
    names
        .iter()
        .map(|name| format!("Hello, {}!", name))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_greetings() {
        let names = vec!["Alice", "Bob", "Carol"];
        let greetings = build_greetings(&names.iter().copied().collect::<Vec<_>>());
        assert_eq!(
            greetings,
            vec!["Hello, Alice!", "Hello, Bob!", "Hello, Carol!"]
        );
    }

    #[test]
    fn test_build_greetings_empty() {
        let names: Vec<&str> = vec![];
        let greetings = build_greetings(&names);
        assert!(greetings.is_empty());
    }

    #[test]
    fn test_names_still_usable() {
        let names = vec!["Ada", "Grace"];
        let _greetings = build_greetings(&names);
        // names 仍可用，因为 build_greetings 接收的是 &[&str]
        assert_eq!(names, vec!["Ada", "Grace"]);
    }
}
