// Prusti 基础示例
// 演示如何使用Prusti进行基本的形式化验证

// 注意：此文件需要prusti-contracts依赖才能编译
// 添加到Cargo.toml: prusti-contracts = "0.2"

use prusti_contracts::*;

/// 验证：向量总是非空的
#[requires(v.len() > 0)]
#[ensures(v.len() > 0)]
fn keep_non_empty(v: &mut Vec<i32>) {
    if v.is_empty() {
        v.push(0);
    }
}

/// 验证：数组访问安全
#[requires(index < v.len())]
#[ensures(result == old(v[index]))]
fn safe_get(v: &Vec<i32>, index: usize) -> i32 {
    v[index]
}

/// 验证：向量追加元素
#[requires(v.len() < usize::MAX)]
#[ensures(v.len() == old(v.len()) + 1)]
#[ensures(v[old(v.len())] == elem)]
fn safe_push(v: &mut Vec<i32>, elem: i32) {
    v.push(elem);
}

/// 验证：最大值查找
#[requires(v.len() > 0)]
#[ensures(forall(|i: usize| i < v.len() ==> v[i] <= result))]
#[ensures(exists(|i: usize| i < v.len() && v[i] == result))]
fn find_max(v: &Vec<i32>) -> i32 {
    let mut max = v[0];
    let mut i = 1;
    
    #[invariant(i <= v.len())]
    #[invariant(forall(|j: usize| j < i ==> v[j] <= max))]
    #[invariant(exists(|j: usize| j < i && v[j] == max))]
    while i < v.len() {
        if v[i] > max {
            max = v[i];
        }
        i += 1;
    }
    
    max
}

fn main() {
    // 基本测试
    let mut v = vec![1, 2, 3];
    keep_non_empty(&mut v);
    println!("Vector length: {}", v.len());
    
    let value = safe_get(&v, 0);
    println!("First element: {}", value);
    
    safe_push(&mut v, 4);
    println!("After push: {:?}", v);
    
    let max = find_max(&v);
    println!("Max value: {}", max);
    
    println!("运行 'cargo prusti' 进行验证");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_keep_non_empty() {
        let mut v = vec![1];
        keep_non_empty(&mut v);
        assert!(v.len() > 0);
    }
    
    #[test]
    fn test_safe_get() {
        let v = vec![10, 20, 30];
        assert_eq!(safe_get(&v, 1), 20);
    }
    
    #[test]
    fn test_find_max() {
        let v = vec![3, 1, 4, 1, 5, 9, 2, 6];
        assert_eq!(find_max(&v), 9);
    }
}

