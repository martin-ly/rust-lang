//! # Rust 1.96.0 特性 — 控制流与函数
//!
//! Rust 1.96.0 为控制流和函数编程带来的核心稳定特性：
//!
//! - **`std::assert_matches`**: `assert_matches!` 宏用于在测试中断言模式匹配
//! - **`core::range`**: `Range` / `RangeInclusive` / `RangeFrom` / `RangeToInclusive`
//!   类型字段公开，支持直接构造和重用
//! - **never type (`!`) 强制转换**: 发散表达式在控制流中强制转换为任意目标类型

// ==================== assert_matches! 在控制流测试中的应用 ====================

/// 使用 assert_matches! 测试控制流结果
///
/// `assert_matches!(expr, pattern)` 是 Rust 1.96 引入的标准断言宏，
/// 支持可选的 `if guard`，但不支持 `=> { block }` 语法。
pub fn classify_status(code: u16) -> Result<&'static str, &'static str> {
    match code {
        200..=299 => Ok("success"),
        300..=399 => Ok("redirect"),
        400..=499 => Ok("client_error"),
        500..=599 => Ok("server_error"),
        _ => Err("unknown status"),
    }
}

/// 使用 assert_matches! 测试 Option 控制流
pub fn maybe_process(input: Option<i32>) -> Option<i32> {
    if let Some(n) = input {
        if n > 0 { Some(n * 2) } else { None }
    } else {
        None
    }
}

// ==================== core::range 在循环边界中的应用 ====================

/// 使用 core::range::Range 实现可复用的循环边界
///
/// `core::range::Range` 实现了 `Copy`，可以在多次循环中重复使用。
pub fn sum_in_range(items: &[i32], bounds: core::range::Range<usize>) -> i32 {
    let core::range::Range { start, end } = bounds;
    let mut sum = 0;
    for i in start..end {
        if let Some(&val) = items.get(i) {
            sum += val;
        }
    }
    sum
}

/// 使用 core::range::RangeInclusive 实现包含边界的循环
pub fn product_in_range(items: &[i32], bounds: core::range::RangeInclusive<usize>) -> i32 {
    let core::range::RangeInclusive { start, last } = bounds;
    let mut product = 1;
    for i in start..=last {
        if let Some(&val) = items.get(i) {
            product *= val;
        }
    }
    product
}

/// 使用 core::range::RangeFrom 实现从起始位置到末尾的遍历
pub fn collect_from(items: &[i32], from: core::range::RangeFrom<usize>) -> Vec<i32> {
    let core::range::RangeFrom { start } = from;
    items.iter().skip(start).copied().collect()
}

/// 使用 core::range::RangeToInclusive 实现范围上限检查
///
/// 注意：`RangeToInclusive` 不实现 `IntoIterator`，但可直接用于边界判断。
pub fn is_within_inclusive_limit(
    index: usize,
    limit: core::range::RangeToInclusive<usize>,
) -> bool {
    let core::range::RangeToInclusive { last } = limit;
    index <= last
}

// ==================== never type 在控制流中的强制转换 ====================

/// never type 强制转换在控制流中的应用
///
/// 发散表达式（如 `panic!`、`return`、`break`、`continue`）的类型为 `!`，
/// `!` 可强制转换为任何类型。在控制流中，包含发散分支的表达式
/// 可与正常分支统一为同一类型。
pub fn fetch_or_timeout(timeout: bool) -> (i32, String) {
    if timeout {
        abort_request() // `!` 强制转换为 `(i32, String)`
    } else {
        (42, String::from("ok"))
    }
}

/// 必然发散的控制流分支
fn abort_request() -> ! {
    panic!("request timed out")
}

/// 在 match 控制流中利用发散分支统一返回类型
///
/// 当某个 match arm 发散时，`!` 自动强制转换为该 match 表达式的目标类型。
pub fn unify_with_diverge(opt: Option<i32>) -> i32 {
    match opt {
        Some(v) => v,
        None => panic!("required value missing"), // `!` -> `i32`
    }
}

/// 在 if-else 控制流中混合正常值与发散分支
///
/// `break` 的类型为 `!`，可强制转换为与循环体匹配的任何类型。
pub fn find_first_positive(values: &[i32]) -> Option<i32> {
    let mut result = None;
    for &v in values {
        if v > 0 {
            result = Some(v);
            break; // `!` 强制转换为 `()`，与赋值语句兼容
        }
    }
    result
}

// ==================== 演示函数 ====================

/// 演示 Rust 1.96 控制流特性
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 控制流特性演示");
    println!("========================================\n");

    println!("--- assert_matches! 测试 ---");
    let status = classify_status(200);
    println!("status(200) = {:?}", status);

    println!("\n--- core::range 循环边界 ---");
    let items = vec![10, 20, 30, 40, 50];
    let range = core::range::Range { start: 1, end: 4 };
    println!("sum_in_range [1..4] = {}", sum_in_range(&items, range));
    // Range 是 Copy 的，可以再次使用
    println!(
        "sum_in_range [1..4] again = {}",
        sum_in_range(&items, range)
    );

    let inc_range = core::range::RangeInclusive { start: 0, last: 2 };
    println!(
        "product_in_range [0..=2] = {}",
        product_in_range(&items, inc_range)
    );

    let from_range = core::range::RangeFrom { start: 2 };
    println!(
        "collect_from [2..] = {:?}",
        collect_from(&items, from_range)
    );

    let to_inc = core::range::RangeToInclusive { last: 3 };
    println!(
        "is_within_inclusive_limit(3, ..=3) = {}",
        is_within_inclusive_limit(3, to_inc)
    );

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 Rust 1.96 特性信息
pub fn get_rust_196_info() -> String {
    "Rust 1.96.0 控制流特性:\n- assert_matches! 宏用于模式匹配断言\n- core::range \
     类型字段公开，支持直接构造\n- never type (!) 强制转换统一发散分支与正常分支类型"
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use super::*;

    #[test]
    fn test_classify_status() {
        assert_eq!(classify_status(200), Ok("success"));
        assert_eq!(classify_status(404), Ok("client_error"));
        assert_eq!(classify_status(500), Ok("server_error"));
        assert_eq!(classify_status(999), Err("unknown status"));
    }

    #[test]
    fn test_assert_matches_on_result() {
        let ok_result: Result<i32, &str> = Ok(42);
        assert_matches!(ok_result, Ok(_));
        assert_matches!(ok_result, Ok(42));
        assert_matches!(ok_result, Ok(n) if n == 42);

        let err_result: Result<i32, &str> = Err("fail");
        assert_matches!(err_result, Err("fail"));
    }

    #[test]
    fn test_assert_matches_on_option() {
        let some_val: Option<i32> = Some(10);
        assert_matches!(some_val, Some(10));
        assert_matches!(some_val, Some(n) if n > 5);

        let none_val: Option<i32> = None;
        assert_matches!(none_val, None);
    }

    #[test]
    fn test_maybe_process() {
        assert_eq!(maybe_process(Some(5)), Some(10));
        assert_eq!(maybe_process(Some(-1)), None);
        assert_eq!(maybe_process(None), None);
    }

    #[test]
    fn test_sum_in_range() {
        let items = vec![10, 20, 30, 40, 50];
        let range = core::range::Range { start: 1, end: 4 };
        assert_eq!(sum_in_range(&items, range), 90); // 20 + 30 + 40
    }

    #[test]
    fn test_range_copy_reusable() {
        let items = vec![1, 2, 3, 4, 5];
        let range = core::range::Range { start: 0, end: 3 };
        let first = sum_in_range(&items, range);
        let second = sum_in_range(&items, range); // Copy 语义允许重用
        assert_eq!(first, second);
    }

    #[test]
    fn test_product_in_range() {
        let items = vec![2, 3, 4, 5];
        let bounds = core::range::RangeInclusive { start: 0, last: 2 };
        assert_eq!(product_in_range(&items, bounds), 24); // 2 * 3 * 4
    }

    #[test]
    fn test_collect_from() {
        let items = vec![10, 20, 30, 40];
        let from = core::range::RangeFrom { start: 2 };
        assert_eq!(collect_from(&items, from), vec![30, 40]);
    }

    #[test]
    fn test_is_within_inclusive_limit() {
        let limit = core::range::RangeToInclusive { last: 5 };
        assert!(is_within_inclusive_limit(3, limit));
        assert!(is_within_inclusive_limit(5, limit));
        assert!(!is_within_inclusive_limit(6, limit));
    }

    #[test]
    fn test_unify_with_diverge() {
        assert_eq!(unify_with_diverge(Some(100)), 100);
    }

    #[test]
    fn test_find_first_positive() {
        assert_eq!(find_first_positive(&[-1, -2, 5, 10]), Some(5));
        assert_eq!(find_first_positive(&[-1, -2, -3]), None);
    }

    #[test]
    fn test_get_rust_196_info() {
        let info = get_rust_196_info();
        assert!(info.contains("assert_matches!"));
        assert!(info.contains("core::range"));
    }
}
