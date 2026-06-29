//! # 排序练习 / Sorting Exercises
//!
//! 本模块包含经典排序算法的实现与练习：
//! - 快速排序 (Quick Sort)
//! - 归并排序 (Merge Sort)
//! - 堆排序 (Heap Sort)
//! - 桶排序 (Bucket Sort)
//! - 计数排序 (Counting Sort)
//! - 荷兰国旗问题 (Dutch National Flag / Sort Colors)

/// 快速排序：原地分治，平均时间复杂度 O(n log n)，空间 O(log n)。
pub fn quick_sort(arr: &mut [i32]) {
    if arr.len() <= 1 {
        return;
    }
    quick_sort_helper(arr, 0, arr.len() - 1);
}

fn quick_sort_helper(arr: &mut [i32], low: usize, high: usize) {
    if low >= high {
        return;
    }
    let pivot_index = partition(arr, low, high);
    if pivot_index > 0 {
        quick_sort_helper(arr, low, pivot_index - 1);
    }
    quick_sort_helper(arr, pivot_index + 1, high);
}

fn partition(arr: &mut [i32], low: usize, high: usize) -> usize {
    // 选择最右侧元素作为 pivot
    let pivot = arr[high];
    let mut i = low;
    for j in low..high {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, high);
    i
}

/// 归并排序：稳定排序，时间复杂度 O(n log n)，空间 O(n)。
pub fn merge_sort(arr: &mut [i32]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    let mut aux = arr.to_vec();
    merge_sort_recursive(arr, &mut aux, 0, len);
}

fn merge_sort_recursive(arr: &mut [i32], aux: &mut [i32], start: usize, end: usize) {
    if end - start <= 1 {
        return;
    }
    let mid = start + (end - start) / 2;
    merge_sort_recursive(arr, aux, start, mid);
    merge_sort_recursive(arr, aux, mid, end);
    merge(arr, aux, start, mid, end);
}

fn merge(arr: &mut [i32], aux: &mut [i32], start: usize, mid: usize, end: usize) {
    aux[start..end].copy_from_slice(&arr[start..end]);
    let mut i = start;
    let mut j = mid;
    let mut k = start;
    while i < mid && j < end {
        if aux[i] <= aux[j] {
            arr[k] = aux[i];
            i += 1;
        } else {
            arr[k] = aux[j];
            j += 1;
        }
        k += 1;
    }
    while i < mid {
        arr[k] = aux[i];
        i += 1;
        k += 1;
    }
    while j < end {
        arr[k] = aux[j];
        j += 1;
        k += 1;
    }
}

/// 堆排序：原地排序，时间复杂度 O(n log n)，空间 O(1)。
pub fn heap_sort(arr: &mut [i32]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    // 构建大顶堆
    for i in (0..len / 2).rev() {
        sift_down(arr, i, len);
    }
    // 逐个取出最大值
    for end in (1..len).rev() {
        arr.swap(0, end);
        sift_down(arr, 0, end);
    }
}

fn sift_down(arr: &mut [i32], mut root: usize, end: usize) {
    loop {
        let left = 2 * root + 1;
        let right = 2 * root + 2;
        let mut largest = root;
        if left < end && arr[left] > arr[largest] {
            largest = left;
        }
        if right < end && arr[right] > arr[largest] {
            largest = right;
        }
        if largest == root {
            break;
        }
        arr.swap(root, largest);
        root = largest;
    }
}

/// 桶排序：对均匀分布在 [0, 1) 区间的浮点数排序。
/// 时间复杂度平均 O(n + k)，k 为桶数量。
pub fn bucket_sort(arr: &mut [f64]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    // 确认数据在 [0, 1) 区间
    assert!(
        arr.iter().all(|&x| (0.0..1.0).contains(&x)),
        "bucket_sort requires all elements in [0, 1)"
    );

    let bucket_count = n.max(2);
    let mut buckets: Vec<Vec<f64>> = vec![Vec::new(); bucket_count];

    for &value in arr.iter() {
        let idx = (value * bucket_count as f64).min(bucket_count as f64 - 1.0) as usize;
        buckets[idx].push(value);
    }

    for bucket in buckets.iter_mut() {
        bucket.sort_by(|a, b| a.partial_cmp(b).unwrap());
    }

    let mut idx = 0;
    for bucket in buckets {
        for value in bucket {
            arr[idx] = value;
            idx += 1;
        }
    }
}

/// 计数排序：对非负整数排序，稳定，时间复杂度 O(n + max_val)。
pub fn counting_sort(arr: &mut [u32]) {
    if arr.is_empty() {
        return;
    }
    let max = *arr.iter().max().unwrap() as usize;
    let mut count = vec![0usize; max + 1];
    for &value in arr.iter() {
        count[value as usize] += 1;
    }
    let mut idx = 0;
    for (value, &cnt) in count.iter().enumerate() {
        for _ in 0..cnt {
            arr[idx] = value as u32;
            idx += 1;
        }
    }
}

/// 荷兰国旗问题：将数组中的 0、1、2 按颜色分类排序。
/// 时间复杂度 O(n)，空间 O(1)。
pub fn sort_colors(arr: &mut [u8]) {
    let mut low = 0usize;
    let mut mid = 0usize;
    let mut high = arr.len();

    while mid < high {
        match arr[mid] {
            0 => {
                arr.swap(low, mid);
                low += 1;
                mid += 1;
            }
            1 => {
                mid += 1;
            }
            2 => {
                high -= 1;
                arr.swap(mid, high);
            }
            _ => panic!("sort_colors only accepts 0, 1, 2"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quick_sort_basic() {
        let mut arr = vec![3, 6, 8, 10, 1, 2, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 6, 8, 10]);
    }

    #[test]
    fn test_quick_sort_empty_and_single() {
        let mut empty: Vec<i32> = vec![];
        quick_sort(&mut empty);
        assert!(empty.is_empty());

        let mut single = vec![42];
        quick_sort(&mut single);
        assert_eq!(single, vec![42]);
    }

    #[test]
    fn test_quick_sort_duplicates_and_negatives() {
        let mut arr = vec![-3, -1, -3, 0, 5, 5, 2];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![-3, -3, -1, 0, 2, 5, 5]);
    }

    #[test]
    fn test_merge_sort_basic() {
        let mut arr = vec![38, 27, 43, 3, 9, 82, 10];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![3, 9, 10, 27, 38, 43, 82]);
    }

    #[test]
    fn test_merge_sort_stability() {
        // i32 本身不可区分稳定性，这里验证结果正确
        let mut arr = vec![1, 1, 1, 1];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 1, 1]);
    }

    #[test]
    fn test_heap_sort_basic() {
        let mut arr = vec![4, 10, 3, 5, 1];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![1, 3, 4, 5, 10]);
    }

    #[test]
    fn test_heap_sort_large() {
        let mut arr: Vec<i32> = (0..100).rev().collect();
        heap_sort(&mut arr);
        assert_eq!(arr, (0..100).collect::<Vec<i32>>());
    }

    #[test]
    fn test_bucket_sort_basic() {
        let mut arr = vec![0.78, 0.17, 0.39, 0.26, 0.72, 0.94, 0.21, 0.12, 0.23, 0.68];
        bucket_sort(&mut arr);
        let expected = vec![0.12, 0.17, 0.21, 0.23, 0.26, 0.39, 0.68, 0.72, 0.78, 0.94];
        assert_eq!(arr.len(), expected.len());
        for (a, e) in arr.iter().zip(expected.iter()) {
            assert!((a - e).abs() < 1e-9, "{} != {}", a, e);
        }
    }

    #[test]
    fn test_bucket_sort_empty_and_single() {
        let mut empty: Vec<f64> = vec![];
        bucket_sort(&mut empty);
        assert!(empty.is_empty());

        let mut single = vec![0.5];
        bucket_sort(&mut single);
        assert_eq!(single, vec![0.5]);
    }

    #[test]
    fn test_counting_sort_basic() {
        let mut arr = vec![4, 2, 2, 8, 3, 3, 1];
        counting_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 2, 3, 3, 4, 8]);
    }

    #[test]
    fn test_counting_sort_zeros() {
        let mut arr = vec![0, 0, 0, 0];
        counting_sort(&mut arr);
        assert_eq!(arr, vec![0, 0, 0, 0]);
    }

    #[test]
    fn test_sort_colors_basic() {
        let mut arr = vec![2, 0, 2, 1, 1, 0];
        sort_colors(&mut arr);
        assert_eq!(arr, vec![0, 0, 1, 1, 2, 2]);
    }

    #[test]
    fn test_sort_colors_all_same() {
        let mut arr = vec![1, 1, 1];
        sort_colors(&mut arr);
        assert_eq!(arr, vec![1, 1, 1]);
    }
}
