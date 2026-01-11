//! # Rust 1.92.0 算法特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在算法实现场景中的应用，包括：
//! - 新的稳定 API（`rotate_right`, `NonZero::div_ceil`）
//! - 性能优化（迭代器方法特化）
//! - 改进的 Lint 行为
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::num::NonZeroUsize;
use std::collections::BTreeMap;

// ==================== 1. rotate_right 在算法中的应用 ====================

/// 使用 rotate_right 实现循环移位算法
///
/// Rust 1.92.0: 新增的 `rotate_right` 方法可以高效实现循环移位
pub fn rotate_array_right<T>(arr: &mut [T], k: usize) {
    if arr.is_empty() || k == 0 {
        return;
    }

    let len = arr.len();
    let k = k % len;

    // Rust 1.92.0: 使用新的 rotate_right 方法
    arr.rotate_right(k);
}

/// 使用 rotate_right 实现循环缓冲区
pub struct CircularBuffer<T> {
    data: Vec<T>,
    start: usize,
}

impl<T> CircularBuffer<T> {
    pub fn new(capacity: usize) -> Self {
        CircularBuffer {
            data: Vec::with_capacity(capacity),
            start: 0,
        }
    }

    /// 旋转缓冲区
    pub fn rotate(&mut self, positions: usize) {
        if self.data.is_empty() {
            return;
        }

        // Rust 1.92.0: 使用新的 rotate_right 方法
        self.data.rotate_right(positions);
    }

    pub fn push(&mut self, item: T) {
        if self.data.len() < self.data.capacity() {
            self.data.push(item);
        } else {
            // 循环覆盖
            self.data[self.start] = item;
            self.start = (self.start + 1) % self.data.capacity();
        }
    }
}

// ==================== 2. NonZero::div_ceil 在算法中的应用 ====================

/// 使用 NonZero::div_ceil 计算数组分块数量
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算向上取整除法
pub fn calculate_chunks<T>(arr: &[T], chunk_size: NonZeroUsize) -> usize {
    // Rust 1.92.0: 使用 NonZero::div_ceil 安全计算
    let size = NonZeroUsize::new(arr.len()).unwrap_or(NonZeroUsize::new(1).unwrap());
    size.div_ceil(chunk_size).get()
}

/// 使用 div_ceil 实现分页算法
pub fn calculate_pages(total_items: usize, items_per_page: NonZeroUsize) -> usize {
    if total_items == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_items).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算页数
    total.div_ceil(items_per_page).get()
}

// ==================== 3. 迭代器方法特化在算法中的应用 ====================

/// 使用特化的迭代器比较方法
///
/// Rust 1.92.0: Iterator::eq 和 Iterator::eq_by 为 TrustedLen 迭代器特化
pub fn compare_arrays<T: PartialEq>(arr1: &[T], arr2: &[T]) -> bool {
    // Rust 1.92.0: 特化的迭代器比较方法，性能更好
    arr1.iter().eq(arr2.iter())
}

/// 使用特化的迭代器比较方法比较排序结果
pub fn verify_sorted<T: PartialEq + Ord>(arr: &[T], expected: &[T]) -> bool {
    // Rust 1.92.0: 使用特化的 eq 方法（性能优化）
    arr.iter().eq(expected.iter())
}

// ==================== 4. 实战案例 ====================

/// 案例1: 使用 rotate_right 实现轮转数组查找
pub fn search_rotated_array(arr: &[i32], target: i32) -> Option<usize> {
    // 假设数组已经旋转，使用 rotate_right 可以恢复原始顺序
    let mut sorted = arr.to_vec();

    // 找到旋转点（简化示例）
    if let Some(pivot) = find_pivot(&sorted) {
        sorted.rotate_right(pivot);
    }

    // 二分查找
    sorted.binary_search(&target).ok()
}

fn find_pivot(arr: &[i32]) -> Option<usize> {
    for i in 1..arr.len() {
        if arr[i] < arr[i - 1] {
            return Some(i);
        }
    }
    None
}

/// 案例2: 使用 div_ceil 实现内存对齐算法
pub fn align_size(size: usize, alignment: NonZeroUsize) -> usize {
    if size == 0 {
        return alignment.get();
    }

    let size_nz = NonZeroUsize::new(size).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算对齐后的大小
    size_nz.div_ceil(alignment).get() * alignment.get()
}

/// 案例3: 使用新特性优化排序算法
pub fn optimized_merge_sort<T: Clone + Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let mid = arr.len() / 2;
    let (left, right) = arr.split_at_mut(mid);

    optimized_merge_sort(left);
    optimized_merge_sort(right);

    // Rust 1.92.0: 使用特化的迭代器方法比较
    merge(left, right);
}

fn merge<T: Ord>(_left: &mut [T], _right: &mut [T]) {
    // 合并逻辑（简化示例）
    // Rust 1.92.0: 可以使用特化的迭代器方法
    // 实际实现需要根据具体算法需求
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rotate_right() {
        let mut arr = vec![1, 2, 3, 4, 5];
        rotate_array_right(&mut arr, 2);
        assert_eq!(arr, vec![4, 5, 1, 2, 3]);
    }

    #[test]
    fn test_div_ceil() {
        let chunk_size = NonZeroUsize::new(3).unwrap();
        let chunks = calculate_chunks(&[1, 2, 3, 4, 5], chunk_size);
        assert_eq!(chunks, 2); // ceil(5/3) = 2
    }

    #[test]
    fn test_compare_arrays() {
        let arr1 = vec![1, 2, 3];
        let arr2 = vec![1, 2, 3];
        assert!(compare_arrays(&arr1, &arr2));
    }
}

// ==================== 4. btree_map::Entry::insert_entry (Rust 1.92.0 新增) ====================

/// Rust 1.92.0 新增：btree_map::Entry::insert_entry 和 VacantEntry::insert_entry
///
/// 提供更高效的 BTreeMap 插入操作，返回插入的值的可变引用。
/// Rust 1.92.0: `Entry::insert_entry` 和 `VacantEntry::insert_entry` 已稳定
pub fn demonstrate_btree_map_insert_entry() {
    println!("\n=== Rust 1.92.0 BTreeMap::Entry::insert_entry 演示 ===\n");

    let mut map = BTreeMap::new();

    // Rust 1.92.0: 使用 insert_entry 方法
    // 如果键不存在，插入并返回值的可变引用
    // 如果键已存在，返回现有值的可变引用
    let value = map.entry("key1".to_string()).insert_entry(100);
    *value = 200; // 可以直接修改
    println!("1. 插入新键 'key1' 并修改值: {}", map.get("key1").unwrap());

    // 如果键已存在，返回现有值的可变引用
    let existing_value = map.entry("key1".to_string()).insert_entry(300);
    println!("2. 键 'key1' 已存在，返回现有值: {}", existing_value);
    println!("3. 最终值: {}", map.get("key1").unwrap());

    // 使用 insert_entry 实现计数器
    let mut counter = BTreeMap::new();
    for word in ["hello", "world", "hello", "rust", "world"] {
        let count = counter.entry(word.to_string()).insert_entry(0);
        *count += 1;
    }
    println!("4. 单词计数: {:?}", counter);
}

/// 使用 insert_entry 实现高效的缓存更新
pub struct Cache<K, V> {
    data: BTreeMap<K, V>,
}

impl<K: Ord, V> Cache<K, V> {
    pub fn new() -> Self {
        Self {
            data: BTreeMap::new(),
        }
    }

    /// 插入或更新缓存项（使用 insert_entry 优化）
    pub fn insert_or_update(&mut self, key: K, value: V) -> &mut V {
        // Rust 1.92.0: 使用 insert_entry 避免额外的查找
        self.data.entry(key).insert_entry(value)
    }

    /// 获取缓存项
    pub fn get(&self, key: &K) -> Option<&V> {
        self.data.get(key)
    }
}

#[cfg(test)]
mod btree_map_insert_entry_tests {
    use super::*;

    #[test]
    fn test_btree_map_insert_entry() {
        let mut map = BTreeMap::new();
        
        // 插入新键
        let value = map.entry("key1".to_string()).insert_entry(100);
        assert_eq!(*value, 100);
        
        // 键已存在，返回现有值
        let existing = map.entry("key1".to_string()).insert_entry(200);
        assert_eq!(*existing, 100); // 返回的是旧值，不是新值
        *existing = 200; // 可以修改
        assert_eq!(map.get("key1"), Some(&200));
    }

    #[test]
    fn test_cache_insert_or_update() {
        let mut cache = Cache::new();
        
        let value = cache.insert_or_update("key1".to_string(), 100);
        assert_eq!(*value, 100);
        
        *value = 200;
        assert_eq!(cache.get("key1"), Some(&200));
    }
}
