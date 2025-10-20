// Kani 基础示例
// 演示如何使用Kani进行有界模型检查

/// 安全的整数除法
fn safe_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 {
        None
    } else if a == i32::MIN && b == -1 {
        None  // 防止溢出
    } else {
        Some(a / b)
    }
}

/// 验证：整数除法不会溢出或panic
#[cfg(kani)]
#[kani::proof]
fn verify_safe_div() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    
    match safe_div(a, b) {
        Some(result) => {
            // 验证结果在有效范围内
            assert!(result >= i32::MIN && result <= i32::MAX);
            // 验证 a = result * b (大致相等，考虑整数除法)
            if b != 0 {
                assert!((result as i64 * b as i64).abs() <= a.abs() as i64 + b.abs() as i64);
            }
        }
        None => {
            // 验证None只在除数为0或会溢出时返回
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

/// 验证：数组查找的正确性
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(10)]
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

/// 无符号整数加法
fn checked_add_u32(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

/// 验证：无符号整数加法的属性
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
            // None只在会溢出时返回
            assert!(a as u64 + b as u64 > u32::MAX as u64);
        }
    }
}

/// 字符串反转函数
fn reverse_string(s: &str) -> String {
    s.chars().rev().collect()
}

/// 验证：字符串反转的幂等性
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(20)]
fn verify_reverse_idempotent() {
    let len: usize = kani::any();
    kani::assume(len <= 10);  // 限制长度以提高性能
    
    let mut chars = Vec::new();
    for _ in 0..len {
        chars.push(kani::any::<char>());
    }
    
    let s: String = chars.into_iter().collect();
    let reversed = reverse_string(&s);
    let double_reversed = reverse_string(&reversed);
    
    // 验证：两次反转应该得到原字符串
    assert_eq!(s, double_reversed);
}

fn main() {
    // 示例用法
    println!("Safe division: {:?}", safe_div(10, 2));
    println!("Safe division by zero: {:?}", safe_div(10, 0));
    
    let arr = [1, 2, 3, 4, 5];
    println!("Find 3: {:?}", find_element(&arr, 3));
    println!("Find 10: {:?}", find_element(&arr, 10));
    
    println!("Checked add: {:?}", checked_add_u32(100, 200));
    println!("Checked add overflow: {:?}", checked_add_u32(u32::MAX, 1));
    
    let text = "Hello";
    println!("Reversed: {}", reverse_string(text));
    
    println!("\n运行 'cargo kani' 进行验证");
    println!("运行 'cargo kani --harness verify_safe_div' 验证特定函数");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_safe_div() {
        assert_eq!(safe_div(10, 2), Some(5));
        assert_eq!(safe_div(10, 0), None);
        assert_eq!(safe_div(i32::MIN, -1), None);
    }
    
    #[test]
    fn test_find_element() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(find_element(&arr, 3), Some(2));
        assert_eq!(find_element(&arr, 10), None);
    }
    
    #[test]
    fn test_reverse_string() {
        assert_eq!(reverse_string("hello"), "olleh");
        assert_eq!(reverse_string(""), "");
        assert_eq!(reverse_string("a"), "a");
    }
}

