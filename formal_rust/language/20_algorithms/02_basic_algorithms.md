# Rust基础算法：形式化定义与实现原理

**版本**: 1.0.0  
**日期**: 2025-01-27  
**状态**: 重构完成

## 📋 目录

1. [排序算法](#1-排序算法)
2. [搜索算法](#2-搜索算法)
3. [字符串算法](#3-字符串算法)
4. [数值算法](#4-数值算法)
5. [算法分析](#5-算法分析)
6. [实现示例](#6-实现示例)

## 1. 排序算法

### 1.1 比较排序算法

#### 1.1.1 快速排序 (Quick Sort)

**定义 1.1** (快速排序)
快速排序是一种分治排序算法，通过选择基准元素将数组分为两部分。

**算法描述**:
```rust
fn quicksort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quicksort(&mut arr[..pivot_index]);
    quicksort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let pivot = arr.len() - 1;
    let mut i = 0;
    
    for j in 0..pivot {
        if arr[j] <= arr[pivot] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot);
    i
}
```

**复杂度分析**:
- **时间复杂度**: 
  - 最好情况: $O(n \log n)$
  - 平均情况: $O(n \log n)$
  - 最坏情况: $O(n^2)$
- **空间复杂度**: $O(\log n)$ (递归栈深度)

**定理 1.1** (快速排序平均复杂度)
快速排序的平均时间复杂度为 $O(n \log n)$。

**证明**:
设 $T(n)$ 为快速排序的平均时间复杂度，则：
$$T(n) = \frac{1}{n} \sum_{i=0}^{n-1} (T(i) + T(n-i-1)) + O(n)$$

通过数学归纳法可以证明 $T(n) = O(n \log n)$。

#### 1.1.2 归并排序 (Merge Sort)

**定义 1.2** (归并排序)
归并排序是一种稳定的分治排序算法，将数组分为两半，递归排序后合并。

**算法描述**:
```rust
fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    let (left, right) = arr.split_at_mut(mid);
    
    merge_sort(left);
    merge_sort(right);
    merge(arr, left, right);
}

fn merge<T: Ord + Clone>(arr: &mut [T], left: &[T], right: &[T]) {
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i].clone();
            i += 1;
        } else {
            arr[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }
    
    // 复制剩余元素
    while i < left.len() {
        arr[k] = left[i].clone();
        i += 1;
        k += 1;
    }
    
    while j < right.len() {
        arr[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}
```

**复杂度分析**:
- **时间复杂度**: $O(n \log n)$ (所有情况)
- **空间复杂度**: $O(n)$

**定理 1.2** (归并排序最优性)
归并排序的时间复杂度达到了比较排序的理论下界。

**证明**:
通过决策树模型，比较排序的决策树高度至少为 $\log(n!)$，而 $\log(n!) = \Omega(n \log n)$。

#### 1.1.3 堆排序 (Heap Sort)

**定义 1.3** (堆排序)
堆排序利用堆数据结构的特性进行排序。

**算法描述**:
```rust
fn heap_sort<T: Ord>(arr: &mut [T]) {
    // 构建最大堆
    for i in (0..arr.len() / 2).rev() {
        heapify(arr, i);
    }
    
    // 逐个提取最大值
    for i in (1..arr.len()).rev() {
        arr.swap(0, i);
        heapify(&mut arr[..i], 0);
    }
}

fn heapify<T: Ord>(arr: &mut [T], root: usize) {
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;
    
    if left < arr.len() && arr[left] > arr[largest] {
        largest = left;
    }
    
    if right < arr.len() && arr[right] > arr[largest] {
        largest = right;
    }
    
    if largest != root {
        arr.swap(root, largest);
        heapify(arr, largest);
    }
}
```

**复杂度分析**:
- **时间复杂度**: $O(n \log n)$ (所有情况)
- **空间复杂度**: $O(1)$

### 1.2 非比较排序算法

#### 1.2.1 计数排序 (Counting Sort)

**定义 1.4** (计数排序)
计数排序是一种非比较排序算法，适用于已知范围的整数排序。

**算法描述**:
```rust
fn counting_sort(arr: &[u32], max_value: u32) -> Vec<u32> {
    let mut count = vec![0; (max_value + 1) as usize];
    let mut output = vec![0; arr.len()];
    
    // 计数
    for &x in arr {
        count[x as usize] += 1;
    }
    
    // 累加计数
    for i in 1..count.len() {
        count[i] += count[i - 1];
    }
    
    // 构建输出数组
    for &x in arr.iter().rev() {
        let index = count[x as usize] - 1;
        output[index] = x;
        count[x as usize] -= 1;
    }
    
    output
}
```

**复杂度分析**:
- **时间复杂度**: $O(n + k)$，其中 $k$ 是数据范围
- **空间复杂度**: $O(n + k)$

## 2. 搜索算法

### 2.1 线性搜索

**定义 2.1** (线性搜索)
线性搜索逐个检查数组中的每个元素。

**算法描述**:
```rust
fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (i, item) in arr.iter().enumerate() {
        if item == target {
            return Some(i);
        }
    }
    None
}
```

**复杂度分析**:
- **时间复杂度**: $O(n)$
- **空间复杂度**: $O(1)$

### 2.2 二分搜索

**定义 2.2** (二分搜索)
二分搜索在有序数组中查找目标元素。

**算法描述**:
```rust
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();
    
    while left < right {
        let mid = left + (right - left) / 2;
        
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    
    None
}
```

**复杂度分析**:
- **时间复杂度**: $O(\log n)$
- **空间复杂度**: $O(1)$

**定理 2.1** (二分搜索最优性)
二分搜索的时间复杂度达到了有序数组搜索的理论下界。

**证明**:
通过信息论，需要至少 $\log n$ 位信息来区分 $n$ 个元素。

### 2.3 插值搜索

**定义 2.3** (插值搜索)
插值搜索是二分搜索的改进版本，使用线性插值估计目标位置。

**算法描述**:
```rust
fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len() - 1;
    
    while left <= right && target >= arr[left] && target <= arr[right] {
        if left == right {
            return if arr[left] == target { Some(left) } else { None };
        }
        
        let pos = left + (((right - left) as f64 * (target - arr[left]) as f64) 
                         / (arr[right] - arr[left]) as f64) as usize;
        
        match arr[pos].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(pos),
            std::cmp::Ordering::Less => left = pos + 1,
            std::cmp::Ordering::Greater => right = pos - 1,
        }
    }
    
    None
}
```

**复杂度分析**:
- **时间复杂度**: 
  - 最好情况: $O(\log \log n)$ (均匀分布)
  - 最坏情况: $O(n)$
- **空间复杂度**: $O(1)$

## 3. 字符串算法

### 3.1 字符串匹配

#### 3.1.1 KMP算法

**定义 3.1** (KMP算法)
KMP算法是一种高效的字符串匹配算法，利用部分匹配表避免重复比较。

**算法描述**:
```rust
fn kmp_search(text: &str, pattern: &str) -> Option<usize> {
    let pattern_bytes = pattern.as_bytes();
    let text_bytes = text.as_bytes();
    let lps = compute_lps(pattern_bytes);
    
    let mut i = 0; // text索引
    let mut j = 0; // pattern索引
    
    while i < text_bytes.len() {
        if pattern_bytes[j] == text_bytes[i] {
            i += 1;
            j += 1;
        }
        
        if j == pattern_bytes.len() {
            return Some(i - j);
        } else if i < text_bytes.len() && pattern_bytes[j] != text_bytes[i] {
            if j != 0 {
                j = lps[j - 1];
            } else {
                i += 1;
            }
        }
    }
    
    None
}

fn compute_lps(pattern: &[u8]) -> Vec<usize> {
    let mut lps = vec![0; pattern.len()];
    let mut len = 0;
    let mut i = 1;
    
    while i < pattern.len() {
        if pattern[i] == pattern[len] {
            len += 1;
            lps[i] = len;
            i += 1;
        } else {
            if len != 0 {
                len = lps[len - 1];
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
    }
    
    lps
}
```

**复杂度分析**:
- **时间复杂度**: $O(m + n)$，其中 $m$ 是模式长度，$n$ 是文本长度
- **空间复杂度**: $O(m)$

#### 3.1.2 Boyer-Moore算法

**定义 3.2** (Boyer-Moore算法)
Boyer-Moore算法是一种高效的字符串匹配算法，从右到左比较。

**算法描述**:
```rust
fn boyer_moore_search(text: &str, pattern: &str) -> Option<usize> {
    let pattern_bytes = pattern.as_bytes();
    let text_bytes = text.as_bytes();
    let bad_char_table = build_bad_char_table(pattern_bytes);
    let good_suffix_table = build_good_suffix_table(pattern_bytes);
    
    let mut i = pattern_bytes.len() - 1;
    
    while i < text_bytes.len() {
        let mut j = pattern_bytes.len() - 1;
        let mut k = i;
        
        while j > 0 && pattern_bytes[j] == text_bytes[k] {
            j -= 1;
            k -= 1;
        }
        
        if j == 0 && pattern_bytes[0] == text_bytes[k] {
            return Some(k);
        }
        
        let bad_char_shift = bad_char_table.get(&text_bytes[k]).unwrap_or(&pattern_bytes.len());
        let good_suffix_shift = good_suffix_table[j];
        
        i += std::cmp::max(*bad_char_shift, good_suffix_shift);
    }
    
    None
}
```

### 3.2 字符串编辑距离

**定义 3.3** (编辑距离)
编辑距离是将一个字符串转换为另一个字符串所需的最少操作次数。

**算法描述**:
```rust
fn edit_distance(s1: &str, s2: &str) -> usize {
    let s1_bytes = s1.as_bytes();
    let s2_bytes = s2.as_bytes();
    let m = s1_bytes.len();
    let n = s2_bytes.len();
    
    let mut dp = vec![vec![0; n + 1]; m + 1];
    
    // 初始化
    for i in 0..=m {
        dp[i][0] = i;
    }
    for j in 0..=n {
        dp[0][j] = j;
    }
    
    // 填充DP表
    for i in 1..=m {
        for j in 1..=n {
            if s1_bytes[i - 1] == s2_bytes[j - 1] {
                dp[i][j] = dp[i - 1][j - 1];
            } else {
                dp[i][j] = 1 + std::cmp::min(
                    dp[i - 1][j],     // 删除
                    std::cmp::min(
                        dp[i][j - 1], // 插入
                        dp[i - 1][j - 1] // 替换
                    )
                );
            }
        }
    }
    
    dp[m][n]
}
```

**复杂度分析**:
- **时间复杂度**: $O(mn)$
- **空间复杂度**: $O(mn)$

## 4. 数值算法

### 4.1 素数算法

#### 4.1.1 埃拉托斯特尼筛法

**定义 4.1** (埃拉托斯特尼筛法)
埃拉托斯特尼筛法是一种高效的素数生成算法。

**算法描述**:
```rust
fn sieve_of_eratosthenes(n: usize) -> Vec<bool> {
    let mut is_prime = vec![true; n + 1];
    is_prime[0] = false;
    is_prime[1] = false;
    
    let sqrt_n = (n as f64).sqrt() as usize;
    
    for i in 2..=sqrt_n {
        if is_prime[i] {
            for j in (i * i..=n).step_by(i) {
                is_prime[j] = false;
            }
        }
    }
    
    is_prime
}
```

**复杂度分析**:
- **时间复杂度**: $O(n \log \log n)$
- **空间复杂度**: $O(n)$

#### 4.1.2 素数测试

**定义 4.2** (Miller-Rabin素数测试)
Miller-Rabin是一种概率性素数测试算法。

**算法描述**:
```rust
fn miller_rabin(n: u64, k: u32) -> bool {
    if n <= 1 || n == 4 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    
    let mut d = n - 1;
    let mut r = 0;
    
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    
    for _ in 0..k {
        if !miller_rabin_test(n, d, r) {
            return false;
        }
    }
    
    true
}

fn miller_rabin_test(n: u64, d: u64, r: u32) -> bool {
    let a = 2 + (rand::random::<u64>() % (n - 4));
    let mut x = mod_pow(a, d, n);
    
    if x == 1 || x == n - 1 {
        return true;
    }
    
    for _ in 1..r {
        x = (x * x) % n;
        if x == n - 1 {
            return true;
        }
        if x == 1 {
            return false;
        }
    }
    
    false
}

fn mod_pow(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1;
    base %= modulus;
    
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exp /= 2;
    }
    
    result
}
```

### 4.2 最大公约数

**定义 4.3** (欧几里得算法)
欧几里得算法计算两个数的最大公约数。

**算法描述**:
```rust
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

// 扩展欧几里得算法
fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (gcd, x, y) = extended_gcd(b, a % b);
        (gcd, y, x - (a / b) * y)
    }
}
```

**复杂度分析**:
- **时间复杂度**: $O(\log \min(a, b))$
- **空间复杂度**: $O(1)$

## 5. 算法分析

### 5.1 正确性证明

**定理 5.1** (快速排序正确性)
快速排序算法能够正确排序任意输入数组。

**证明**:
通过数学归纳法：
1. **基础情况**: 长度为0或1的数组已经有序
2. **归纳步骤**: 假设子数组排序正确，则合并后数组也正确

### 5.2 复杂度分析

**定理 5.2** (排序算法下界)
任何基于比较的排序算法的最坏情况时间复杂度为 $\Omega(n \log n)$。

**证明**:
通过决策树模型，比较排序的决策树高度至少为 $\log(n!)$，而 $\log(n!) = \Omega(n \log n)$。

### 5.3 稳定性分析

**定义 5.1** (排序稳定性)
排序算法是稳定的，当且仅当相等元素的相对顺序在排序后保持不变。

**稳定性分析**:
- **稳定算法**: 归并排序、插入排序、冒泡排序
- **不稳定算法**: 快速排序、堆排序、选择排序

## 6. 实现示例

### 6.1 完整排序实现

```rust
use std::cmp::Ord;

pub trait Sortable {
    fn sort(&mut self);
    fn is_sorted(&self) -> bool;
}

impl<T: Ord + Clone> Sortable for Vec<T> {
    fn sort(&mut self) {
        quicksort(self);
    }
    
    fn is_sorted(&self) -> bool {
        self.windows(2).all(|w| w[0] <= w[1])
    }
}

// 测试框架
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quicksort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        arr.sort();
        assert!(arr.is_sorted());
    }
    
    #[test]
    fn test_binary_search() {
        let arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(binary_search(&arr, &5), Some(4));
        assert_eq!(binary_search(&arr, &10), None);
    }
}
```

## 🔗 交叉引用

### 相关概念
- [理论基础](01_theoretical_foundations.md) - 理论背景
- [数据结构算法](03_data_structure_algorithms.md) - 数据结构相关算法
- [高级算法](04_advanced_algorithms.md) - 高级算法技术

### 外部资源
- [Rust标准库排序](https://doc.rust-lang.org/std/primitive.slice.html#method.sort)
- [算法可视化](https://visualgo.net/)
- [排序算法比较](https://www.toptal.com/developers/sorting-algorithms)

## 📚 参考文献

1. **算法导论** - Thomas H. Cormen (2009)
2. **编程珠玑** - Jon Bentley (2000)
3. **字符串算法** - Dan Gusfield (1997)
4. **数值算法** - William H. Press (2007)

---

**维护者**: Rust语言形式化理论团队  
**最后更新**: 2025-01-27  
**版本**: 1.0.0 