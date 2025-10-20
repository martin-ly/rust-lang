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
//    creusot-contracts = "0.2"
//    
//    [features]
//    creusot = ["creusot-contracts"]
//    ```
//
// 3. 使用 Creusot 验证：
//    ```bash
//    cargo creusot verify
//    ```
//
// 注意：本示例使用条件编译，在没有 creusot-contracts 依赖时也能正常编译运行

#[cfg(feature = "creusot")]
use creusot_contracts::*;

// 在没有 creusot feature 时，这些属性宏不会被处理，但代码仍能编译
// 我们只需要确保使用的泛型函数（如 forall）有备用定义
#[cfg(not(feature = "creusot"))]
fn forall<F>(_f: F) -> bool
where
    F: Fn(usize) -> bool,
{
    // Stub 实现：在没有验证时总是返回 true
    true
}

/// 阶乘函数
/// 规约：计算 n!
#[requires(n <= 12)]  // 防止u64溢出
#[ensures(result > 0)]
#[ensures(n == 0 ==> result == 1)]
#[variant(n)]
fn factorial(n: u32) -> u64 {
    if n == 0 {
        1
    } else {
        n as u64 * factorial(n - 1)
    }
}

/// 斐波那契数列
/// 规约：F(0) = 0, F(1) = 1, F(n) = F(n-1) + F(n-2)
#[requires(n <= 20)]  // 防止溢出
#[ensures(n == 0 ==> result == 0)]
#[ensures(n == 1 ==> result == 1)]
#[variant(n)]
fn fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 最大公约数（欧几里得算法）
/// 规约：返回a和b的最大公约数
#[requires(b > 0)]
#[ensures(result > 0)]
#[ensures(a % result == 0)]
#[ensures(b % result == 0)]
#[variant(b)]
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// 数组求和
/// 规约：返回数组所有元素的和
#[ensures(result == sum_spec(arr))]
fn array_sum(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    
    #[invariant(i <= arr.len())]
    #[invariant(sum == sum_spec(&arr[0..i]))]
    while i < arr.len() {
        sum = sum + arr[i];
        i += 1;
    }
    
    sum
}

/// 规约函数：定义数组求和的语义
#[logic]
#[variant(arr.len())]
fn sum_spec(arr: &[i32]) -> i32 {
    if arr.is_empty() {
        0
    } else {
        arr[0] + sum_spec(&arr[1..])
    }
}

/// 线性查找
/// 规约：查找数组中第一个等于target的元素
#[ensures(match result {
    Some(idx) => idx < arr.len() && arr[idx] == target,
    None => forall(|i: usize| i < arr.len() ==> arr[i] != target),
})]
fn linear_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut i = 0;
    
    #[invariant(i <= arr.len())]
    #[invariant(forall(|j: usize| j < i ==> arr[j] != target))]
    while i < arr.len() {
        if arr[i] == target {
            return Some(i);
        }
        i += 1;
    }
    
    None
}

/// 数组最小值
/// 规约：返回数组中的最小值索引
#[requires(arr.len() > 0)]
#[ensures(result < arr.len())]
#[ensures(forall(|i: usize| i < arr.len() ==> arr[result] <= arr[i]))]
fn find_min_index(arr: &[i32]) -> usize {
    let mut min_idx = 0;
    let mut i = 1;
    
    #[invariant(i <= arr.len())]
    #[invariant(min_idx < arr.len())]
    #[invariant(forall(|j: usize| j < i ==> arr[min_idx] <= arr[j]))]
    while i < arr.len() {
        if arr[i] < arr[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    
    min_idx
}

/// 检查数组是否已排序
/// 规约：返回true当且仅当数组是递增有序的
#[ensures(result ==> is_sorted_spec(arr))]
fn is_sorted(arr: &[i32]) -> bool {
    if arr.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    
    #[invariant(i < arr.len())]
    #[invariant(forall(|j: usize, k: usize| 
        j < k && k <= i ==> arr[j] <= arr[k]
    ))]
    while i < arr.len() - 1 {
        if arr[i] > arr[i + 1] {
            return false;
        }
        i += 1;
    }
    
    true
}

/// 规约函数：定义有序数组的语义
#[predicate]
fn is_sorted_spec(arr: &[i32]) -> bool {
    forall(|i: usize, j: usize| 
        i < j && j < arr.len() ==> arr[i] <= arr[j]
    )
}

fn main() {
    // 阶乘示例
    println!("5! = {}", factorial(5));
    
    // 斐波那契示例
    println!("fib(10) = {}", fibonacci(10));
    
    // GCD示例
    println!("gcd(48, 18) = {}", gcd(48, 18));
    
    // 数组求和示例
    let arr = [1, 2, 3, 4, 5];
    println!("sum([1,2,3,4,5]) = {}", array_sum(&arr));
    
    // 线性查找示例
    match linear_search(&arr, 3) {
        Some(idx) => println!("Found 3 at index {}", idx),
        None => println!("3 not found"),
    }
    
    // 最小值示例
    let arr2 = [5, 2, 8, 1, 9];
    let min_idx = find_min_index(&arr2);
    println!("Minimum value {} at index {}", arr2[min_idx], min_idx);
    
    // 排序检查示例
    println!("Is [1,2,3,4,5] sorted? {}", is_sorted(&[1, 2, 3, 4, 5]));
    println!("Is [1,3,2,4,5] sorted? {}", is_sorted(&[1, 3, 2, 4, 5]));
    
    println!("\n运行 'cargo creusot verify' 进行验证");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(5), 120);
    }
    
    #[test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(10), 55);
    }
    
    #[test]
    fn test_gcd() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(100, 50), 50);
    }
    
    #[test]
    fn test_array_sum() {
        assert_eq!(array_sum(&[1, 2, 3, 4, 5]), 15);
        assert_eq!(array_sum(&[]), 0);
    }
    
    #[test]
    fn test_is_sorted() {
        assert!(is_sorted(&[1, 2, 3, 4, 5]));
        assert!(!is_sorted(&[1, 3, 2, 4, 5]));
        assert!(is_sorted(&[]));
        assert!(is_sorted(&[1]));
    }
}

