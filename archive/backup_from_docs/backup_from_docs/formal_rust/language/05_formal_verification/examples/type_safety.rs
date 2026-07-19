// 类型安全与进展/保持定理示例
// 工程意义：演示Rust类型系统如何在编译期消除未定义行为，适用于Prusti/Creusot等工具验证

/// 前置条件：b != 0
/// 后置条件：返回 Some(a / b) 或 None（避免除零错误）
fn safe_divide(a: i32, b: i32) -> Option<i32> {
    if b != 0 {
        Some(a / b)
    } else {
        None
    }
}

fn main() {
    assert_eq!(safe_divide(10, 2), Some(5));
    assert_eq!(safe_divide(10, 0), None);
}

// 形式化注释：
// {b != 0} safe_divide(a, b) {result = Some(a / b)}
// {b == 0} safe_divide(a, b) {result = None}
// 工具建议：Prusti #[requires(b != 0)] #[ensures(result.is_some())] 