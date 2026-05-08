//! # 控制流模式与惯用法
//!
//! 本模块展示 Rust 中各种控制流结构的高级用法和最佳实践，
//! 帮助开发者写出更地道、更高效的 Rust 代码。

/// 展示 `match` 的高级模式
///
/// 包括守卫、绑定、解构、范围匹配等技巧。
pub struct MatchPatterns;

impl MatchPatterns {
    /// 使用 match 进行多条件分支
    pub fn classify_number(n: i32) -> &'static str {
        match n {
            0 => "zero",
            1 | 2 | 3 => "small",
            4..=10 => "medium",
            n if n < 0 => "negative",
            n if n > 100 => "large",
            _ => "other",
        }
    }

    /// 使用 @ 绑定同时匹配和捕获值
    pub fn binding_at_patterns(msg: &str) -> String {
        match msg.split(':').collect::<Vec<_>>().as_slice() {
            ["ERROR", code @ "404"] => format!("Not found: {}", code),
            ["ERROR", code @ "500"] => format!("Server error: {}", code),
            ["ERROR", code] => format!("Other error: {}", code),
            ["INFO", content] => format!("Info: {}", content),
            _ => "Unknown format".to_string(),
        }
    }

    /// 匹配嵌套结构
    pub fn match_nested(option_result: Option<Result<i32, ()>>) -> i32 {
        match option_result {
            Some(Ok(n)) if n > 0 => n * 2,
            Some(Ok(n)) => n,
            Some(Err(())) => -1,
            None => 0,
        }
    }
}

/// 展示 `if let` / `while let` 链式用法
///
/// Rust 1.95+ 支持更灵活的 let 链（let chains），
/// 本模块展示如何优雅地处理嵌套 Option/Result。
pub struct LetChainPatterns;

impl LetChainPatterns {
    /// 多条件 let 链（概念展示，实际使用需 Rust 1.95+ let_chains）
    pub fn process_user_data(data: Option<&str>) -> Option<String> {
        let trimmed = data?.trim();
        if trimmed.is_empty() {
            return None;
        }
        Some(trimmed.to_uppercase())
    }

    /// while let 遍历迭代器
    pub fn sum_even_numbers(mut iter: impl Iterator<Item = i32>) -> i32 {
        let mut sum = 0;
        while let Some(n) = iter.next() {
            if n % 2 == 0 {
                sum += n;
            }
        }
        sum
    }
}

/// 展示 `loop` 标签和 break 返回值
///
/// Rust 的 `loop` 可以作为表达式返回值，配合标签实现多层跳出。
pub struct LoopPatterns;

impl LoopPatterns {
    /// 使用 break 返回值
    pub fn find_first_positive(numbers: &[i32]) -> Option<i32> {
        let result = numbers.iter().find(|&&n| n > 0);
        result.copied()
    }

    /// 使用 loop 标签跳出嵌套循环
    pub fn find_pair_sum(target: i32, arr: &[i32]) -> Option<(usize, usize)> {
        'outer: for (i, &a) in arr.iter().enumerate() {
            for (j, &b) in arr.iter().enumerate().skip(i + 1) {
                if a + b == target {
                    return Some((i, j));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_number() {
        assert_eq!(MatchPatterns::classify_number(0), "zero");
        assert_eq!(MatchPatterns::classify_number(2), "small");
        assert_eq!(MatchPatterns::classify_number(7), "medium");
        assert_eq!(MatchPatterns::classify_number(-5), "negative");
        assert_eq!(MatchPatterns::classify_number(200), "large");
        assert_eq!(MatchPatterns::classify_number(50), "other");
    }

    #[test]
    fn test_binding_at_patterns() {
        assert_eq!(
            MatchPatterns::binding_at_patterns("ERROR:404"),
            "Not found: 404"
        );
        assert_eq!(
            MatchPatterns::binding_at_patterns("INFO:hello"),
            "Info: hello"
        );
    }

    #[test]
    fn test_match_nested() {
        assert_eq!(MatchPatterns::match_nested(Some(Ok(5))), 10);
        assert_eq!(MatchPatterns::match_nested(Some(Ok(-3))), -3);
        assert_eq!(MatchPatterns::match_nested(Some(Err(()))), -1);
        assert_eq!(MatchPatterns::match_nested(None), 0);
    }

    #[test]
    fn test_process_user_data() {
        assert_eq!(
            LetChainPatterns::process_user_data(Some("  hello  ")),
            Some("HELLO".to_string())
        );
        assert_eq!(LetChainPatterns::process_user_data(None), None);
        assert_eq!(
            LetChainPatterns::process_user_data(Some("   ")),
            None
        );
    }

    #[test]
    fn test_sum_even_numbers() {
        let nums = vec![1, 2, 3, 4, 5, 6];
        assert_eq!(
            LetChainPatterns::sum_even_numbers(nums.into_iter()),
            12
        );
    }

    #[test]
    fn test_find_pair_sum() {
        let arr = vec![1, 2, 3, 4, 5];
        let result = LoopPatterns::find_pair_sum(7, &arr);
        // 多个正确答案: (1,4)=2+5=7 或 (2,3)=3+4=7
        assert!(result.is_some());
        let (i, j) = result.unwrap();
        assert!(i < j);
        assert_eq!(arr[i] + arr[j], 7);

        assert_eq!(
            LoopPatterns::find_pair_sum(100, &arr),
            None
        );
    }
}
