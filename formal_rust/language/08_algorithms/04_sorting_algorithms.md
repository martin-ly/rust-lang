# 排序算法实现

## 1. 比较排序

- 快速排序、归并排序、堆排序、插入/冒泡/选择排序
- 理论下界：任意比较排序最坏$\Omega(n \log n)$

### 1.1 快速排序

```rust
pub fn quicksort<T: Ord>(arr: &mut [T]) { /* ... */ }
```

### 1.2 归并排序

```rust
pub fn merge_sort<T: Ord + Clone>(arr: &mut [T]) { /* ... */ }
```

### 1.3 堆排序

```rust
pub fn heap_sort<T: Ord>(arr: &mut [T]) { /* ... */ }
```

## 2. 非比较排序

- 计数排序、基数排序、桶排序，适用于整数/有限域

### 2.1 计数排序

```rust
pub fn counting_sort(arr: &mut [usize], max_val: usize) { /* ... */ }
```

### 2.2 基数排序

```rust
pub fn radix_sort(arr: &mut [u32]) { /* ... */ }
```

### 2.3 桶排序

```rust
pub fn bucket_sort(arr: &mut [f64]) { /* ... */ }
```

## 3. 稳定性与工程实践

- 归并/计数/基数/桶排序稳定，快速/堆排序不稳定
- Rust标准库sort/sort_unstable区分稳定性

## 4. 批判性分析与未来值值值展望

- 排序算法工程实现需关注缓存友好、并行化与数据分布
- 未来值值值可探索自适应排序与AI驱动排序策略

"

---
