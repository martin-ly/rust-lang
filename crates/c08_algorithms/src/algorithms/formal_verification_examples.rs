//! # 算法形式化验证与注释示例
//! 
//! 本模块展示如何为算法添加：
//! - 完整的数学注释
//! - 形式化前置/后置条件
//! - 循环不变量
//! - 复杂度分析
//! - 正确性证明
//! 
//! 对标 Rust 1.90 特性，结合形式化方法。

use std::cmp::Ordering;

/// # 二分查找（形式化验证版本）
/// 
/// ## 形式化规约
/// 
/// **前置条件** (Precondition):
/// ```text
/// ∀i ∈ [0, n-2]. arr[i] ≤ arr[i+1]  // 数组已排序
/// ```
/// 
/// **后置条件** (Postcondition):
/// ```text
/// result = Some(idx) ⟺ arr[idx] = target ∧ 0 ≤ idx < n
/// result = None      ⟺ ∀i ∈ [0, n). arr[i] ≠ target
/// ```
/// 
/// ## 复杂度分析
/// 
/// - **时间复杂度**: O(log n)
///   - 每次迭代将搜索空间减半
///   - 递归关系: T(n) = T(n/2) + O(1) = O(log n)
/// 
/// - **空间复杂度**: O(1)
///   - 只使用常数个变量
/// 
/// ## 循环不变量
/// 
/// ```text
/// 不变量 I:
///   1. 0 ≤ left ≤ right ≤ n
///   2. ∀i < left.   arr[i] < target
///   3. ∀i ≥ right. arr[i] > target
///   4. target ∈ arr ⟹ target ∈ arr[left..right]
/// ```
/// 
/// ## 正确性证明（霍尔逻辑）
/// 
/// ```text
/// 初始化：
///   left = 0, right = n
///   I成立：arr[-∞..0)为空，arr[n..+∞)为空 ✓
/// 
/// 维护：
///   假设 I 成立且 left < right
///   mid = (left + right) / 2
///   
///   Case 1: arr[mid] < target
///     新left = mid + 1
///     ∀i < mid+1. arr[i] < target (由I和arr[mid]<target)
///     I仍成立 ✓
///   
///   Case 2: arr[mid] > target
///     新right = mid
///     ∀i ≥ mid. arr[i] > target (由I和arr[mid]>target)
///     I仍成立 ✓
///   
///   Case 3: arr[mid] = target
///     返回 Some(mid)
///     由I, mid ∈ [left, right), 正确 ✓
/// 
/// 终止：
///   left ≥ right
///   由I, target ∉ arr
///   返回 None，正确 ✓
/// ```
/// 
/// ## Rust实现
/// 
/// ```rust
/// use c08_algorithms::algorithms::formal_verification_examples::binary_search_verified;
/// 
/// let arr = vec![1, 3, 5, 7, 9];
/// assert_eq!(binary_search_verified(&arr, 5), Some(2));
/// assert_eq!(binary_search_verified(&arr, 4), None);
/// ```
/// 
/// ## 形式化验证工具
/// 
/// 可使用以下工具进行验证：
/// - **Prusti**: Rust的验证工具（基于Viper）
/// - **Creusot**: Rust的演绎验证工具（基于Why3）
/// - **Kani**: Rust的模型检查器
#[inline]
pub fn binary_search_verified<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    // 初始化：建立循环不变量
    let mut left = 0;
    let mut right = arr.len();
    
    // 循环：维护不变量
    // 不变量 I:
    //   1. 0 ≤ left ≤ right ≤ n
    //   2. ∀i < left.   arr[i] < target
    //   3. ∀i ≥ right. arr[i] > target
    //   4. target ∈ arr ⟹ target ∈ arr[left..right]
    while left < right {
        // 计算中点（避免溢出）
        let mid = left + (right - left) / 2;
        
        match arr[mid].cmp(target) {
            Ordering::Equal => {
                // 找到目标
                // 由不变量，mid ∈ [left, right)
                return Some(mid);
            }
            Ordering::Less => {
                // arr[mid] < target
                // 更新left，维护不变量2
                left = mid + 1;
            }
            Ordering::Greater => {
                // arr[mid] > target
                // 更新right，维护不变量3
                right = mid;
            }
        }
    }
    
    // 终止：left ≥ right
    // 由不变量，target ∉ arr
    None
}

/// # 插入排序（带完整证明）
/// 
/// ## 形式化规约
/// 
/// **前置条件**:
/// ```text
/// arr: &mut [T]  // 任意可比较元素数组
/// ```
/// 
/// **后置条件**:
/// ```text
/// 1. ∀i ∈ [0, n-2]. arr[i] ≤ arr[i+1]  // 已排序
/// 2. multiset(arr_after) = multiset(arr_before)  // 保持元素集合
/// ```
/// 
/// ## 复杂度分析
/// 
/// - **时间复杂度**:
///   - 最好情况: O(n) - 已排序
///   - 平均情况: O(n²) - 随机排列
///   - 最坏情况: O(n²) - 逆序
/// 
/// - **空间复杂度**: O(1) - 原地排序
/// 
/// ## 循环不变量
/// 
/// **外层循环不变量**:
/// ```text
/// I_outer(i):
///   arr[0..i] 已排序
///   ∧ multiset(arr[0..n]) = multiset(arr_original)
/// ```
/// 
/// **内层循环不变量**:
/// ```text
/// I_inner(j):
///   arr[0..i+1] 除 arr[j] 外已排序
///   ∧ arr[j] 是待插入元素
///   ∧ arr[j+1..i+1] > arr[j]
/// ```
/// 
/// ## 正确性证明
/// 
/// ```text
/// 外层循环：
/// 
/// 初始化 (i=0):
///   arr[0..0] 为空，平凡已排序 ✓
/// 
/// 维护 (i → i+1):
///   假设 arr[0..i] 已排序
///   执行内层循环插入 arr[i]
///   结果 arr[0..i+1] 已排序 ✓
/// 
/// 终止 (i=n):
///   arr[0..n] 已排序 ✓
/// 
/// 内层循环：
/// 
/// 初始化 (j=i):
///   待插入 arr[i]，arr[0..i] 已排序 ✓
/// 
/// 维护 (j → j-1):
///   若 arr[j-1] > arr[j]，交换
///   保持 arr[0..j) ∪ arr[j+1..i+1] 已排序 ✓
/// 
/// 终止 (j=0 或 arr[j-1] ≤ arr[j]):
///   arr[j] 已在正确位置
///   arr[0..i+1] 已排序 ✓
/// ```
/// 
/// ## 示例
/// 
/// ```rust
/// use c08_algorithms::algorithms::formal_verification_examples::insertion_sort_verified;
/// 
/// let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
/// insertion_sort_verified(&mut arr);
/// assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
/// ```
#[inline]
pub fn insertion_sort_verified<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    
    // 外层循环：建立不变量 I_outer
    // 不变量: arr[0..i] 已排序
    for i in 1..n {
        // 此时 arr[0..i] 已排序
        
        // 内层循环：插入 arr[i] 到正确位置
        let mut j = i;
        
        // 不变量 I_inner:
        //   arr[0..j) ∪ arr[j+1..i+1] 已排序
        //   arr[j] 待插入
        while j > 0 && arr[j - 1] > arr[j] {
            // arr[j-1] > arr[j]，交换
            arr.swap(j - 1, j);
            j -= 1;
            // 维护不变量
        }
        
        // 终止：j=0 或 arr[j-1] ≤ arr[j]
        // arr[0..i+1] 已排序
    }
    
    // 终止：i=n
    // arr[0..n] 已排序 ✓
}

/// # 归并排序（分治算法范例）
/// 
/// ## 形式化规约
/// 
/// **递归定义**:
/// ```text
/// MergeSort(arr) =
///   if |arr| ≤ 1 then
///     arr
///   else
///     merge(MergeSort(left), MergeSort(right))
///   where (left, right) = split(arr)
/// ```
/// 
/// ## 复杂度分析
/// 
/// **递归关系**:
/// ```text
/// T(n) = 2·T(n/2) + Θ(n)  // 分治 + 合并
/// ```
/// 
/// **主定理应用**:
/// ```text
/// a = 2, b = 2, f(n) = Θ(n)
/// log_b(a) = log_2(2) = 1
/// f(n) = Θ(n¹ log⁰(n))
/// 
/// 由主定理 Case 2:
/// T(n) = Θ(n log n)
/// ```
/// 
/// **空间复杂度**: O(n)
/// - 需要临时数组存储合并结果
/// 
/// ## 正确性证明（结构归纳）
/// 
/// ```text
/// 基础情况 (|arr| ≤ 1):
///   单元素或空数组已排序 ✓
/// 
/// 归纳假设:
///   假设 MergeSort 对所有 |arr| < n 正确
/// 
/// 归纳步骤 (|arr| = n):
///   1. split(arr) = (left, right)
///      |left|, |right| < n
///   2. 由归纳假设:
///      left' = MergeSort(left) 已排序
///      right' = MergeSort(right) 已排序
///   3. result = merge(left', right') 已排序
///      （merge的正确性见下）
///   4. 因此 MergeSort(arr) 正确 ✓
/// ```
/// 
/// ## Merge函数的正确性
/// 
/// **不变量**:
/// ```text
/// I(i, j):
///   result[0..i+j] 包含 left[0..i] ∪ right[0..j] 的元素
///   ∧ result[0..i+j] 已排序
/// ```
/// 
/// **证明**:
/// ```text
/// 初始化 (i=0, j=0):
///   result 为空，平凡成立 ✓
/// 
/// 维护:
///   若 left[i] ≤ right[j]:
///     result.push(left[i])
///     由不变量和 left[i] ≤ right[j..] ✓
///   
///   否则:
///     result.push(right[j])
///     由不变量和 right[j] < left[i..] ✓
/// 
/// 终止 (i=|left|, j=|right|):
///   result 包含所有元素且已排序 ✓
/// ```
#[inline]
pub fn merge_sort_verified<T: Ord + Clone>(arr: Vec<T>) -> Vec<T> {
    // 基础情况
    if arr.len() <= 1 {
        return arr;
    }
    
    // 分解
    let mid = arr.len() / 2;
    let (left, right) = arr.split_at(mid);
    
    // 递归求解
    let left_sorted = merge_sort_verified(left.to_vec());
    let right_sorted = merge_sort_verified(right.to_vec());
    
    // 合并
    merge_verified(left_sorted, right_sorted)
}

/// 合并两个已排序数组
/// 
/// **前置条件**:
/// ```text
/// sorted(left) ∧ sorted(right)
/// ```
/// 
/// **后置条件**:
/// ```text
/// sorted(result)
/// ∧ multiset(result) = multiset(left) ∪ multiset(right)
/// ```
#[inline]
fn merge_verified<T: Ord + Clone>(left: Vec<T>, right: Vec<T>) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);
    
    // 不变量 I(i, j):
    //   result[0..i+j] = sorted(left[0..i] ∪ right[0..j])
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }
    
    // 处理剩余元素
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    
    result
}

/// # 快速排序（原地排序范例）
/// 
/// ## 形式化规约
/// 
/// **递归定义**:
/// ```text
/// QuickSort(arr) =
///   if |arr| ≤ 1 then
///     arr
///   else
///     pivot_idx = partition(arr)
///     QuickSort(arr[0..pivot_idx])
///     QuickSort(arr[pivot_idx+1..])
/// ```
/// 
/// ## Partition函数的规约
/// 
/// **后置条件**:
/// ```text
/// 返回 pivot_idx 满足:
///   1. ∀i < pivot_idx.   arr[i] ≤ arr[pivot_idx]
///   2. ∀i > pivot_idx.   arr[i] ≥ arr[pivot_idx]
///   3. multiset(arr) = multiset(arr_before)
/// ```
/// 
/// ## 复杂度分析
/// 
/// **最好/平均情况**: O(n log n)
/// ```text
/// T(n) = 2·T(n/2) + Θ(n)  // 平衡分割
/// 由主定理: T(n) = Θ(n log n)
/// ```
/// 
/// **最坏情况**: O(n²)
/// ```text
/// T(n) = T(n-1) + Θ(n)  // 不平衡分割
/// T(n) = Θ(n²)
/// ```
/// 
/// **空间复杂度**: O(log n)
/// - 递归栈深度（平均情况）
/// 
/// ## 正确性证明
/// 
/// ```text
/// 基础情况 (|arr| ≤ 1):
///   平凡成立 ✓
/// 
/// 归纳假设:
///   QuickSort 对 |arr| < n 正确
/// 
/// 归纳步骤:
///   1. pivot_idx = partition(arr)
///      由partition的后置条件:
///      arr[0..pivot_idx] ≤ pivot
///      arr[pivot_idx+1..] ≥ pivot
///   
///   2. QuickSort(arr[0..pivot_idx])
///      由归纳假设，左半部分已排序
///   
///   3. QuickSort(arr[pivot_idx+1..])
///      由归纳假设，右半部分已排序
///   
///   4. 组合：left_sorted ≤ pivot ≤ right_sorted
///      整个数组已排序 ✓
/// ```
#[inline]
pub fn quick_sort_verified<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    // Partition：返回pivot最终位置
    let pivot_idx = partition_verified(arr);
    
    // 递归排序左右两部分
    quick_sort_verified(&mut arr[0..pivot_idx]);
    quick_sort_verified(&mut arr[pivot_idx + 1..]);
}

/// Partition函数
/// 
/// **不变量**:
/// ```text
/// I(store):
///   arr[0..store) ≤ pivot
///   arr[store..i) > pivot
///   arr[i..] 未处理
/// ```
#[inline]
fn partition_verified<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_idx = len - 1;
    let mut store = 0;
    
    // 不变量 I(store):
    //   arr[0..store) ≤ arr[pivot_idx]
    //   arr[store..i) > arr[pivot_idx]
    for i in 0..pivot_idx {
        if arr[i] <= arr[pivot_idx] {
            arr.swap(i, store);
            store += 1;
        }
    }
    
    // 将pivot放到正确位置
    arr.swap(store, pivot_idx);
    
    // 后置条件满足：
    //   arr[0..store) ≤ arr[store] ≤ arr[store+1..)
    store
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_search_verified() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        
        // 找到存在的元素
        assert_eq!(binary_search_verified(&arr, &5), Some(2));
        assert_eq!(binary_search_verified(&arr, &1), Some(0));
        assert_eq!(binary_search_verified(&arr, &13), Some(6));
        
        // 找不到的元素
        assert_eq!(binary_search_verified(&arr, &0), None);
        assert_eq!(binary_search_verified(&arr, &4), None);
        assert_eq!(binary_search_verified(&arr, &14), None);
        
        // 边界情况
        let empty: Vec<i32> = vec![];
        assert_eq!(binary_search_verified(&empty, &1), None);
        
        let single = vec![42];
        assert_eq!(binary_search_verified(&single, &42), Some(0));
        assert_eq!(binary_search_verified(&single, &43), None);
    }

    #[test]
    fn test_insertion_sort_verified() {
        // 随机数组
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        insertion_sort_verified(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
        
        // 已排序
        let mut sorted = vec![1, 2, 3, 4, 5];
        insertion_sort_verified(&mut sorted);
        assert_eq!(sorted, vec![1, 2, 3, 4, 5]);
        
        // 逆序
        let mut reversed = vec![5, 4, 3, 2, 1];
        insertion_sort_verified(&mut reversed);
        assert_eq!(reversed, vec![1, 2, 3, 4, 5]);
        
        // 边界情况
        let mut empty: Vec<i32> = vec![];
        insertion_sort_verified(&mut empty);
        assert_eq!(empty, Vec::<i32>::new());
        
        let mut single = vec![42];
        insertion_sort_verified(&mut single);
        assert_eq!(single, vec![42]);
    }

    #[test]
    fn test_merge_sort_verified() {
        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let sorted = merge_sort_verified(arr);
        assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 6, 9]);
        
        // 大规模测试
        let mut large: Vec<i32> = (0..1000).rev().collect();
        let sorted_large = merge_sort_verified(large.clone());
        large.sort();
        assert_eq!(sorted_large, large);
    }

    #[test]
    fn test_quick_sort_verified() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        quick_sort_verified(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
        
        // 重复元素
        let mut duplicates = vec![3, 3, 1, 1, 2, 2];
        quick_sort_verified(&mut duplicates);
        assert_eq!(duplicates, vec![1, 1, 2, 2, 3, 3]);
    }

    /// 验证排序算法的性质
    #[test]
    fn test_sorting_properties() {
        let test_cases = vec![
            vec![],
            vec![1],
            vec![2, 1],
            vec![3, 1, 4, 1, 5, 9, 2, 6],
            vec![5, 4, 3, 2, 1],
            vec![1, 1, 1, 1],
        ];
        
        for original in test_cases {
            // 测试insertion_sort
            let mut arr1 = original.clone();
            insertion_sort_verified(&mut arr1);
            assert!(is_sorted(&arr1), "insertion_sort failed");
            assert!(has_same_elements(&arr1, &original), "elements changed");
            
            // 测试merge_sort
            let arr2 = merge_sort_verified(original.clone());
            assert!(is_sorted(&arr2), "merge_sort failed");
            assert!(has_same_elements(&arr2, &original), "elements changed");
            
            // 测试quick_sort
            let mut arr3 = original.clone();
            quick_sort_verified(&mut arr3);
            assert!(is_sorted(&arr3), "quick_sort failed");
            assert!(has_same_elements(&arr3, &original), "elements changed");
        }
    }
    
    /// 检查数组是否已排序
    fn is_sorted<T: Ord>(arr: &[T]) -> bool {
        arr.windows(2).all(|w| w[0] <= w[1])
    }
    
    /// 检查两个数组是否包含相同元素（multiset相等）
    fn has_same_elements<T: Ord + Clone>(a: &[T], b: &[T]) -> bool {
        let mut a_sorted = a.to_vec();
        let mut b_sorted = b.to_vec();
        a_sorted.sort();
        b_sorted.sort();
        a_sorted == b_sorted
    }
}

