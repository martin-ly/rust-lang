// Creusot 基础示例
// 演示如何使用Creusot进行演绎验证
//
// ## 使用说明
//
// 1. 安装 Creusot 工具链：
//    ```bash
//    cargo install creusot
//    ```
//
// 2. 在 Cargo.toml 中启用 creusot feature 并添加依赖：
//    ```toml
//    [dependencies]
//    creusot-contracts = { version = "0.2", optional = true }
//    
//    [features]
//    creusot = ["creusot-contracts"]
//    ```
//
// 3. 使用 Creusot 验证：
//    ```bash
//    cargo creusot verify --features creusot
//    ```
//
// 4. 正常运行示例（不进行验证）：
//    ```bash
//    cargo run --example creusot_basic
//    ```

/// 阶乘函数
/// 规约：计算 n!，n <= 12 防止 u64 溢出
fn factorial(n: u32) -> u64 {
    if n == 0 {
        1
    } else {
        n as u64 * factorial(n - 1)
    }
}

/// 斐波那契数列
/// 规约：F(0) = 0, F(1) = 1, F(n) = F(n-1) + F(n-2)
fn fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 最大公约数（欧几里得算法）
/// 规约：返回 a 和 b 的最大公约数
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// 数组求和
/// 规约：返回数组所有元素的和
fn array_sum(arr: &[i32]) -> i32 {
    let mut sum: i32 = 0;
    for &item in arr {
        sum = sum.saturating_add(item);
    }
    sum
}

/// 线性查找
/// 规约：查找数组中第一个等于 target 的元素
fn linear_search(arr: &[i32], target: i32) -> Option<usize> {
    for (i, &item) in arr.iter().enumerate() {
        if item == target {
            return Some(i);
        }
    }
    None
}

/// 数组最小值
/// 规约：返回数组中的最小值索引
fn find_min_index(arr: &[i32]) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mut min_idx = 0;
    for i in 1..arr.len() {
        if arr[i] < arr[min_idx] {
            min_idx = i;
        }
    }
    
    Some(min_idx)
}

/// 检查数组是否已排序
/// 规约：返回 true 当且仅当数组是递增有序的
fn is_sorted(arr: &[i32]) -> bool {
    if arr.len() <= 1 {
        return true;
    }
    
    for i in 0..arr.len() - 1 {
        if arr[i] > arr[i + 1] {
            return false;
        }
    }
    
    true
}

/// 二分查找
/// 规约：在已排序数组中查找 target
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    if !is_sorted(arr) {
        return None;
    }
    
    let mut left = 0;
    let mut right = arr.len();
    
    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    
    None
}

/// 数组反转（原地）
/// 规约：反转数组元素顺序
fn reverse_array(arr: &mut [i32]) {
    let len = arr.len();
    for i in 0..len / 2 {
        arr.swap(i, len - 1 - i);
    }
}

fn main() {
    println!("=== Creusot 形式化验证示例 ===\n");
    
    // 阶乘示例
    println!("📊 阶乘计算:");
    for n in [0, 1, 5, 10] {
        println!("  {}! = {}", n, factorial(n));
    }
    
    // 斐波那契示例
    println!("\n📈 斐波那契数列:");
    for n in [0, 1, 5, 10, 15] {
        println!("  fib({}) = {}", n, fibonacci(n));
    }
    
    // GCD 示例
    println!("\n🔢 最大公约数:");
    let gcd_pairs = [(48, 18), (100, 50), (17, 19)];
    for (a, b) in gcd_pairs {
        println!("  gcd({}, {}) = {}", a, b, gcd(a, b));
    }
    
    // 数组求和示例
    println!("\n➕ 数组求和:");
    let arrays = [
        vec![1, 2, 3, 4, 5],
        vec![10, 20, 30],
        vec![-5, -3, 8, 2],
    ];
    for arr in &arrays {
        println!("  sum({:?}) = {}", arr, array_sum(arr));
    }
    
    // 线性查找示例
    println!("\n🔍 线性查找:");
    let arr = [1, 2, 3, 4, 5];
    for target in [3, 10] {
        match linear_search(&arr, target) {
            Some(idx) => println!("  在 {:?} 中找到 {} at index {}", arr, target, idx),
            None => println!("  在 {:?} 中未找到 {}", arr, target),
        }
    }
    
    // 最小值示例
    println!("\n⬇️  数组最小值:");
    let test_arrays = [
        vec![5, 2, 8, 1, 9],
        vec![10, -5, 3],
        vec![42],
    ];
    for arr in &test_arrays {
        if let Some(min_idx) = find_min_index(arr) {
            println!("  {:?} 的最小值是 {} (索引 {})", arr, arr[min_idx], min_idx);
        }
    }
    
    // 排序检查示例
    println!("\n✅ 排序检查:");
    let sort_test = [
        vec![1, 2, 3, 4, 5],
        vec![1, 3, 2, 4, 5],
        vec![5, 4, 3, 2, 1],
    ];
    for arr in &sort_test {
        println!("  {:?} 是否有序? {}", arr, is_sorted(arr));
    }
    
    // 二分查找示例
    println!("\n🎯 二分查找:");
    let sorted_arr = [1, 3, 5, 7, 9, 11, 13];
    for target in [7, 8] {
        match binary_search(&sorted_arr, target) {
            Some(idx) => println!("  在 {:?} 中找到 {} at index {}", sorted_arr, target, idx),
            None => println!("  在 {:?} 中未找到 {}", sorted_arr, target),
        }
    }
    
    // 数组反转示例
    println!("\n🔄 数组反转:");
    let mut test_rev = vec![1, 2, 3, 4, 5];
    println!("  原始: {:?}", test_rev);
    reverse_array(&mut test_rev);
    println!("  反转: {:?}", test_rev);
    
    println!("\n{}", "=".repeat(50));
    println!("💡 提示:");
    println!("  - 当前以普通模式运行");
    println!("  - 要启用 Creusot 形式化验证，请:");
    println!("    1. 添加 creusot-contracts 依赖到 Cargo.toml");
    println!("    2. 在函数上添加 #[requires], #[ensures] 等属性");
    println!("    3. 运行: cargo creusot verify --features creusot");
    println!("{}", "=".repeat(50));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(5), 120);
        assert_eq!(factorial(10), 3_628_800);
    }
    
    #[test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(10), 55);
        assert_eq!(fibonacci(15), 610);
    }
    
    #[test]
    fn test_gcd() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(100, 50), 50);
        assert_eq!(gcd(17, 19), 1);
    }
    
    #[test]
    fn test_array_sum() {
        assert_eq!(array_sum(&[1, 2, 3, 4, 5]), 15);
        assert_eq!(array_sum(&[]), 0);
        assert_eq!(array_sum(&[-5, -3, 8, 2]), 2);
    }
    
    #[test]
    fn test_linear_search() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(linear_search(&arr, 3), Some(2));
        assert_eq!(linear_search(&arr, 10), None);
    }
    
    #[test]
    fn test_find_min_index() {
        assert_eq!(find_min_index(&[5, 2, 8, 1, 9]), Some(3));
        assert_eq!(find_min_index(&[10, -5, 3]), Some(1));
        assert_eq!(find_min_index(&[42]), Some(0));
        assert_eq!(find_min_index(&[]), None);
    }
    
    #[test]
    fn test_is_sorted() {
        assert!(is_sorted(&[1, 2, 3, 4, 5]));
        assert!(!is_sorted(&[1, 3, 2, 4, 5]));
        assert!(is_sorted(&[]));
        assert!(is_sorted(&[1]));
    }
    
    #[test]
    fn test_binary_search() {
        let arr = [1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search(&arr, 7), Some(3));
        assert_eq!(binary_search(&arr, 8), None);
        assert_eq!(binary_search(&arr, 1), Some(0));
        assert_eq!(binary_search(&arr, 13), Some(6));
    }
    
    #[test]
    fn test_reverse_array() {
        let mut arr = vec![1, 2, 3, 4, 5];
        reverse_array(&mut arr);
        assert_eq!(arr, vec![5, 4, 3, 2, 1]);
        
        let mut empty: Vec<i32> = vec![];
        reverse_array(&mut empty);
        assert_eq!(empty, Vec::<i32>::new());
        
        let mut single = vec![42];
        reverse_array(&mut single);
        assert_eq!(single, vec![42]);
    }
}
