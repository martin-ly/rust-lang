// Kani 基础示例
// 演示如何使用 Kani 进行有界模型检查
//
// ## 使用说明
//
// 1. 安装 Kani：
//    ```bash
//    cargo install --locked kani-verifier
//    cargo kani setup
//    ```
//
// 2. 验证代码：
//    ```bash
//    cargo kani
//    ```
//
// 3. 验证特定函数：
//    ```bash
//    cargo kani --harness verify_safe_div
//    ```
//
// 4. 正常运行示例：
//    ```bash
//    cargo run --example kani_basic
//    ```
//
// ## 关于 Kani
//
// Kani 是 AWS 开源的 Rust 模型检查工具，使用符号执行技术验证代码的正确性。
// 特点：
// - 不需要额外的依赖，通过 #[cfg(kani)] 条件编译
// - 支持验证所有可能的输入组合（有界）
// - 可以发现溢出、panic、断言失败等问题

/// 安全的整数除法
/// 避免除零和溢出
fn safe_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 {
        None
    } else if a == i32::MIN && b == -1 {
        None  // 防止溢出：i32::MIN / -1 会溢出
    } else {
        Some(a / b)
    }
}

/// Kani 验证：整数除法不会溢出或 panic
#[cfg(kani)]
#[kani::proof]
fn verify_safe_div() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    
    match safe_div(a, b) {
        Some(result) => {
            // 验证结果在有效范围内
            assert!(result >= i32::MIN && result <= i32::MAX);
            // 验证结果的正确性（考虑整数除法的特性）
            if b != 0 && !(a == i32::MIN && b == -1) {
                let quotient = a / b;
                assert_eq!(result, quotient);
            }
        }
        None => {
            // 验证 None 只在除数为 0 或会溢出时返回
            assert!(b == 0 || (a == i32::MIN && b == -1));
        }
    }
}

/// 数组查找函数
fn find_element(arr: &[i32], target: i32) -> Option<usize> {
    for (i, &item) in arr.iter().enumerate() {
        if item == target {
            return Some(i);
        }
    }
    None
}

/// Kani 验证：数组查找的正确性
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(10)]  // 设置循环展开次数
fn verify_find_element() {
    let arr: [i32; 5] = kani::any();
    let target: i32 = kani::any();
    
    match find_element(&arr, target) {
        Some(index) => {
            // 如果找到，索引必须有效且元素匹配
            assert!(index < arr.len());
            assert_eq!(arr[index], target);
        }
        None => {
            // 如果未找到，数组中不应存在该元素
            for &item in arr.iter() {
                assert_ne!(item, target);
            }
        }
    }
}

/// 带检查的无符号整数加法
fn checked_add_u32(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

/// Kani 验证：无符号整数加法的属性
#[cfg(kani)]
#[kani::proof]
fn verify_checked_add() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    
    match checked_add_u32(a, b) {
        Some(result) => {
            // 结果必须大于等于两个操作数
            assert!(result >= a);
            assert!(result >= b);
            // 验证没有溢出
            assert!(result as u64 == a as u64 + b as u64);
        }
        None => {
            // None 只在会溢出时返回
            assert!(a as u64 + b as u64 > u32::MAX as u64);
        }
    }
}

/// 字符串反转函数
fn reverse_string(s: &str) -> String {
    s.chars().rev().collect()
}

/// Kani 验证：字符串反转的幂等性
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(20)]
fn verify_reverse_idempotent() {
    let len: usize = kani::any();
    kani::assume(len <= 10);  // 限制长度以提高性能
    
    let mut chars = Vec::new();
    for _ in 0..len {
        let c: char = kani::any();
        // 限制为 ASCII 字符以提高性能
        kani::assume(c.is_ascii());
        chars.push(c);
    }
    
    let s: String = chars.into_iter().collect();
    let reversed = reverse_string(&s);
    let double_reversed = reverse_string(&reversed);
    
    // 验证：两次反转应该得到原字符串
    assert_eq!(s, double_reversed);
    // 验证：反转后长度不变
    assert_eq!(s.len(), reversed.len());
}

/// 安全的数组访问
fn safe_array_access(arr: &[i32], index: usize) -> Option<i32> {
    if index < arr.len() {
        Some(arr[index])
    } else {
        None
    }
}

/// Kani 验证：数组访问安全性
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn verify_safe_array_access() {
    let arr: [i32; 3] = kani::any();
    let index: usize = kani::any();
    
    match safe_array_access(&arr, index) {
        Some(value) => {
            // 索引必须在有效范围内
            assert!(index < arr.len());
            // 返回的值必须等于数组中的值
            assert_eq!(value, arr[index]);
        }
        None => {
            // None 只在索引越界时返回
            assert!(index >= arr.len());
        }
    }
}

/// 计算两个数的最大值
fn max_i32(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

/// Kani 验证：最大值函数的性质
#[cfg(kani)]
#[kani::proof]
fn verify_max_properties() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    
    let result = max_i32(a, b);
    
    // 结果必须大于等于两个输入
    assert!(result >= a);
    assert!(result >= b);
    // 结果必须等于其中一个输入
    assert!(result == a || result == b);
}

/// 饱和减法（不会下溢）
fn saturating_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}

/// Kani 验证：饱和减法的性质
#[cfg(kani)]
#[kani::proof]
fn verify_saturating_sub() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    
    let result = saturating_sub(a, b);
    
    // 结果不会超过 a
    assert!(result <= a);
    // 如果 a >= b，结果应该是 a - b
    if a >= b {
        assert_eq!(result, a - b);
    } else {
        // 否则结果应该是 0
        assert_eq!(result, 0);
    }
}

fn main() {
    println!("=== Kani 有界模型检查示例 ===\n");
    
    // 安全除法示例
    println!("➗ 安全除法:");
    let div_tests = [(10, 2), (10, 0), (i32::MIN, -1), (7, 3)];
    for (a, b) in div_tests {
        match safe_div(a, b) {
            Some(result) => println!("  {} / {} = {}", a, b, result),
            None => println!("  {} / {} = None (除零或溢出)", a, b),
        }
    }
    
    // 数组查找示例
    println!("\n🔍 数组查找:");
    let arr = [1, 2, 3, 4, 5];
    for target in [3, 10] {
        match find_element(&arr, target) {
            Some(idx) => println!("  在 {:?} 中找到 {} at index {}", arr, target, idx),
            None => println!("  在 {:?} 中未找到 {}", arr, target),
        }
    }
    
    // 无符号加法示例
    println!("\n➕ 带检查的加法:");
    let add_tests = [(100, 200), (u32::MAX, 1), (u32::MAX - 10, 5)];
    for (a, b) in add_tests {
        match checked_add_u32(a, b) {
            Some(result) => println!("  {} + {} = {}", a, b, result),
            None => println!("  {} + {} = None (溢出)", a, b),
        }
    }
    
    // 字符串反转示例
    println!("\n🔄 字符串反转:");
    let strings = ["Hello", "Rust", "世界", ""];
    for s in strings {
        let reversed = reverse_string(s);
        let double_reversed = reverse_string(&reversed);
        println!("  原始: '{}' → 反转: '{}' → 双重反转: '{}'", s, reversed, double_reversed);
        println!("    幂等性验证: {}", s == double_reversed);
    }
    
    // 安全数组访问示例
    println!("\n🎯 安全数组访问:");
    let arr = [10, 20, 30];
    for index in [0, 1, 2, 5] {
        match safe_array_access(&arr, index) {
            Some(value) => println!("  arr[{}] = {}", index, value),
            None => println!("  arr[{}] = None (越界)", index),
        }
    }
    
    // 最大值示例
    println!("\n⬆️  最大值计算:");
    let max_tests = [(5, 10), (-5, -10), (0, 0), (i32::MIN, i32::MAX)];
    for (a, b) in max_tests {
        println!("  max({}, {}) = {}", a, b, max_i32(a, b));
    }
    
    // 饱和减法示例
    println!("\n⬇️  饱和减法:");
    let sub_tests = [(10, 5), (5, 10), (0, 1), (u32::MAX, 1)];
    for (a, b) in sub_tests {
        println!("  {} - {} = {} (饱和)", a, b, saturating_sub(a, b));
    }
    
    println!("\n{}", "=".repeat(50));
    println!("💡 提示:");
    println!("  - 当前以普通模式运行");
    println!("  - 要启用 Kani 形式化验证，请:");
    println!("    1. 安装: cargo install --locked kani-verifier");
    println!("    2. 设置: cargo kani setup");
    println!("    3. 验证所有: cargo kani");
    println!("    4. 验证单个: cargo kani --harness verify_safe_div");
    println!("\n  Kani 会验证所有可能的输入组合（有界），发现：");
    println!("    • 整数溢出");
    println!("    • 数组越界");
    println!("    • panic 和断言失败");
    println!("    • 除零错误");
    println!("{}", "=".repeat(50));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_safe_div() {
        assert_eq!(safe_div(10, 2), Some(5));
        assert_eq!(safe_div(10, 0), None);
        assert_eq!(safe_div(i32::MIN, -1), None);
        assert_eq!(safe_div(7, 3), Some(2));
    }
    
    #[test]
    fn test_find_element() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(find_element(&arr, 3), Some(2));
        assert_eq!(find_element(&arr, 10), None);
        assert_eq!(find_element(&arr, 1), Some(0));
    }
    
    #[test]
    fn test_checked_add_u32() {
        assert_eq!(checked_add_u32(100, 200), Some(300));
        assert_eq!(checked_add_u32(u32::MAX, 1), None);
        assert_eq!(checked_add_u32(0, 0), Some(0));
    }
    
    #[test]
    fn test_reverse_string() {
        assert_eq!(reverse_string("hello"), "olleh");
        assert_eq!(reverse_string(""), "");
        assert_eq!(reverse_string("a"), "a");
        
        // 测试幂等性
        let s = "Rust";
        let reversed = reverse_string(s);
        let double_reversed = reverse_string(&reversed);
        assert_eq!(s, double_reversed);
    }
    
    #[test]
    fn test_safe_array_access() {
        let arr = [10, 20, 30];
        assert_eq!(safe_array_access(&arr, 0), Some(10));
        assert_eq!(safe_array_access(&arr, 2), Some(30));
        assert_eq!(safe_array_access(&arr, 5), None);
    }
    
    #[test]
    fn test_max_i32() {
        assert_eq!(max_i32(5, 10), 10);
        assert_eq!(max_i32(10, 5), 10);
        assert_eq!(max_i32(5, 5), 5);
        assert_eq!(max_i32(i32::MIN, i32::MAX), i32::MAX);
    }
    
    #[test]
    fn test_saturating_sub() {
        assert_eq!(saturating_sub(10, 5), 5);
        assert_eq!(saturating_sub(5, 10), 0);
        assert_eq!(saturating_sub(0, 1), 0);
        assert_eq!(saturating_sub(u32::MAX, 1), u32::MAX - 1);
    }
}
