// Prusti 基础示例
// 演示如何使用 Prusti 进行基本的形式化验证
//
// ## 使用说明
//
// 1. 安装 Prusti：
//    ```bash
//    cargo install prusti-cli
//    ```
//
// 2. 在 Cargo.toml 中启用 prusti feature 并添加依赖：
//    ```toml
//    [dependencies]
//    prusti-contracts = { version = "0.2", optional = true }
//    
//    [features]
//    prusti = ["prusti-contracts"]
//    ```
//
// 3. 使用 Prusti 验证：
//    ```bash
//    cargo prusti --features prusti
//    ```
//
// 4. 正常运行示例（不进行验证）：
//    ```bash
//    cargo run --example prusti_basic
//    ```

/// 确保向量非空
/// 如果向量为空，则添加一个元素
fn keep_non_empty(v: &mut Vec<i32>) {
    if v.is_empty() {
        v.push(0);
    }
}

/// 安全的数组访问
/// 在边界检查后访问元素
fn safe_get(v: &[i32], index: usize) -> Option<i32> {
    if index < v.len() {
        Some(v[index])
    } else {
        None
    }
}

/// 向量追加元素
/// 在不溢出的情况下添加元素
fn safe_push(v: &mut Vec<i32>, elem: i32) -> Result<(), &'static str> {
    if v.len() >= usize::MAX - 1 {
        Err("Vector capacity exceeded")
    } else {
        v.push(elem);
        Ok(())
    }
}

/// 查找最大值
/// 在非空向量中查找最大元素
fn find_max(v: &[i32]) -> Option<i32> {
    if v.is_empty() {
        return None;
    }
    
    let mut max = v[0];
    for &item in v.iter().skip(1) {
        if item > max {
            max = item;
        }
    }
    
    Some(max)
}

/// 查找最小值
/// 在非空向量中查找最小元素
fn find_min(v: &[i32]) -> Option<i32> {
    if v.is_empty() {
        return None;
    }
    
    let mut min = v[0];
    for &item in v.iter().skip(1) {
        if item < min {
            min = item;
        }
    }
    
    Some(min)
}

/// 范围检查的数组切片
/// 返回数组的安全切片
fn safe_slice(v: &[i32], start: usize, end: usize) -> Option<&[i32]> {
    if start <= end && end <= v.len() {
        Some(&v[start..end])
    } else {
        None
    }
}

/// 安全的整数除法
/// 避免除零和溢出
fn safe_div(a: i32, b: i32) -> Option<i32> {
    if b == 0 {
        None
    } else if a == i32::MIN && b == -1 {
        None  // 防止溢出
    } else {
        Some(a / b)
    }
}

/// 向量元素求和（带溢出检查）
/// 使用饱和加法防止溢出
fn safe_sum(v: &[i32]) -> i32 {
    v.iter().fold(0, |acc, &x| acc.saturating_add(x))
}

/// 检查向量是否包含元素
/// 线性搜索检查元素是否存在
fn contains(v: &[i32], elem: i32) -> bool {
    v.iter().any(|&x| x == elem)
}

/// 移除向量中的第一个匹配元素
/// 找到并移除第一个等于指定值的元素
fn remove_first(v: &mut Vec<i32>, elem: i32) -> bool {
    if let Some(pos) = v.iter().position(|&x| x == elem) {
        v.remove(pos);
        true
    } else {
        false
    }
}

fn main() {
    println!("=== Prusti 形式化验证示例 ===\n");
    
    // 保持非空示例
    println!("📦 保持向量非空:");
    let mut v1 = vec![1, 2, 3];
    println!("  原始: {:?}", v1);
    keep_non_empty(&mut v1);
    println!("  处理后: {:?} (长度: {})", v1, v1.len());
    
    let mut v2: Vec<i32> = vec![];
    println!("  空向量: {:?}", v2);
    keep_non_empty(&mut v2);
    println!("  处理后: {:?} (长度: {})", v2, v2.len());
    
    // 安全访问示例
    println!("\n🔍 安全数组访问:");
    let v = vec![10, 20, 30, 40, 50];
    for i in [0, 2, 5, 10] {
        match safe_get(&v, i) {
            Some(value) => println!("  v[{}] = {}", i, value),
            None => println!("  v[{}] = 越界", i),
        }
    }
    
    // 安全追加示例
    println!("\n➕ 安全追加元素:");
    let mut v = vec![1, 2, 3];
    println!("  原始: {:?}", v);
    match safe_push(&mut v, 4) {
        Ok(_) => println!("  追加 4 成功: {:?}", v),
        Err(e) => println!("  追加失败: {}", e),
    }
    
    // 查找最大值示例
    println!("\n⬆️  查找最大值:");
    let test_cases = [
        vec![3, 1, 4, 1, 5, 9, 2, 6],
        vec![-10, -5, -20],
        vec![42],
        vec![],
    ];
    for v in &test_cases {
        match find_max(v) {
            Some(max) => println!("  {:?} 的最大值: {}", v, max),
            None => println!("  {:?} 为空，无最大值", v),
        }
    }
    
    // 查找最小值示例
    println!("\n⬇️  查找最小值:");
    for v in &test_cases {
        match find_min(v) {
            Some(min) => println!("  {:?} 的最小值: {}", v, min),
            None => println!("  {:?} 为空，无最小值", v),
        }
    }
    
    // 安全切片示例
    println!("\n✂️  安全切片:");
    let v = vec![1, 2, 3, 4, 5];
    let slices = [(0, 3), (2, 5), (3, 10), (5, 3)];
    for (start, end) in slices {
        match safe_slice(&v, start, end) {
            Some(slice) => println!("  v[{}..{}] = {:?}", start, end, slice),
            None => println!("  v[{}..{}] = 无效范围", start, end),
        }
    }
    
    // 安全除法示例
    println!("\n➗ 安全除法:");
    let div_tests = [(10, 2), (10, 0), (i32::MIN, -1), (15, 3)];
    for (a, b) in div_tests {
        match safe_div(a, b) {
            Some(result) => println!("  {} / {} = {}", a, b, result),
            None => println!("  {} / {} = 错误 (除零或溢出)", a, b),
        }
    }
    
    // 安全求和示例
    println!("\n🧮 安全求和:");
    let sum_tests = [
        vec![1, 2, 3, 4, 5],
        vec![i32::MAX, 1],  // 会溢出
        vec![-10, -20, 30],
    ];
    for v in &sum_tests {
        println!("  sum({:?}) = {}", v, safe_sum(v));
    }
    
    // 包含检查示例
    println!("\n🔎 元素包含检查:");
    let v = vec![1, 2, 3, 4, 5];
    for elem in [3, 10] {
        println!("  {:?} 包含 {}? {}", v, elem, contains(&v, elem));
    }
    
    // 移除元素示例
    println!("\n🗑️  移除元素:");
    let mut v = vec![1, 2, 3, 2, 4];
    println!("  原始: {:?}", v);
    if remove_first(&mut v, 2) {
        println!("  移除第一个 2: {:?}", v);
    }
    if !remove_first(&mut v, 10) {
        println!("  移除 10 失败 (不存在)");
    }
    
    println!("\n{}", "=".repeat(50));
    println!("💡 提示:");
    println!("  - 当前以普通模式运行");
    println!("  - 要启用 Prusti 形式化验证，请:");
    println!("    1. 安装: cargo install prusti-cli");
    println!("    2. 添加 prusti-contracts 依赖到 Cargo.toml");
    println!("    3. 在函数上添加 #[requires], #[ensures] 等属性");
    println!("    4. 运行: cargo prusti --features prusti");
    println!("{}", "=".repeat(50));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_keep_non_empty() {
        let mut v = vec![1];
        keep_non_empty(&mut v);
        assert!(!v.is_empty());
        
        let mut empty: Vec<i32> = vec![];
        keep_non_empty(&mut empty);
        assert!(!empty.is_empty());
    }
    
    #[test]
    fn test_safe_get() {
        let v = vec![10, 20, 30];
        assert_eq!(safe_get(&v, 1), Some(20));
        assert_eq!(safe_get(&v, 5), None);
    }
    
    #[test]
    fn test_safe_push() {
        let mut v = vec![1, 2, 3];
        assert!(safe_push(&mut v, 4).is_ok());
        assert_eq!(v, vec![1, 2, 3, 4]);
    }
    
    #[test]
    fn test_find_max() {
        let v = vec![3, 1, 4, 1, 5, 9, 2, 6];
        assert_eq!(find_max(&v), Some(9));
        
        let empty: Vec<i32> = vec![];
        assert_eq!(find_max(&empty), None);
    }
    
    #[test]
    fn test_find_min() {
        let v = vec![3, 1, 4, 1, 5, 9, 2, 6];
        assert_eq!(find_min(&v), Some(1));
        
        let empty: Vec<i32> = vec![];
        assert_eq!(find_min(&empty), None);
    }
    
    #[test]
    fn test_safe_slice() {
        let v = vec![1, 2, 3, 4, 5];
        assert_eq!(safe_slice(&v, 0, 3), Some(&[1, 2, 3][..]));
        assert_eq!(safe_slice(&v, 2, 5), Some(&[3, 4, 5][..]));
        assert_eq!(safe_slice(&v, 3, 10), None);
        assert_eq!(safe_slice(&v, 5, 3), None);
    }
    
    #[test]
    fn test_safe_div() {
        assert_eq!(safe_div(10, 2), Some(5));
        assert_eq!(safe_div(10, 0), None);
        assert_eq!(safe_div(i32::MIN, -1), None);
    }
    
    #[test]
    fn test_safe_sum() {
        assert_eq!(safe_sum(&[1, 2, 3, 4, 5]), 15);
        assert_eq!(safe_sum(&[i32::MAX, 1]), i32::MAX);  // 饱和加法
    }
    
    #[test]
    fn test_contains() {
        let v = vec![1, 2, 3, 4, 5];
        assert!(contains(&v, 3));
        assert!(!contains(&v, 10));
    }
    
    #[test]
    fn test_remove_first() {
        let mut v = vec![1, 2, 3, 2, 4];
        assert!(remove_first(&mut v, 2));
        assert_eq!(v, vec![1, 3, 2, 4]);
        assert!(!remove_first(&mut v, 10));
    }
}
