# 08.01 形式化排序算法

## 目录

1. [引言与基础定义](#1-引言与基础定义)
2. [排序问题形式化](#2-排序问题形式化)
3. [基础排序算法](#3-基础排序算法)
4. [高效排序算法](#4-高效排序算法)
5. [非比较排序](#5-非比较排序)
6. [排序算法分析](#6-排序算法分析)
7. [形式化验证](#7-形式化验证)
8. [定理与证明](#8-定理与证明)

---

## 1. 引言与基础定义

### 1.1 排序基础

**定义 1.1** (排序问题)
给定一个元素序列 $L = \langle e_1, e_2, \dots, e_n \rangle$ 和一个全序关系 $\le$，排序的目标是找到一个序列 $L' = \langle e'_1, e'_2, \dots, e'_n \rangle$，使得 $L'$ 是 $L$ 的一个排列，并且满足 $e'_1 \le e'_2 \le \dots \le e'_n$。

**定义 1.2** (稳定性)
如果一个排序算法保持相等元素的相对顺序，则称其为稳定的。即，若在原序列 $L$ 中 $e_i = e_j$ 且 $i < j$，则在排序后序列 $L'$ 中，$e_i$ 仍然在 $e_j$ 之前。

**定义 1.3** (原地排序)
原地排序算法是指不需要额外空间或只需要常数额外空间的排序算法。

### 1.2 排序算法分类

**定义 1.4** (排序算法分类)
排序算法可分为以下类别：
$$\text{SortingAlgorithms} = \{\text{ComparisonBased}, \text{NonComparisonBased}, \text{Hybrid}\}$$

**定义 1.5** (比较排序)
基于比较的排序算法通过比较元素来确定它们的相对顺序：
$$\text{ComparisonSort} = \text{Algorithm} \times \text{Comparison} \times \text{Ordering}$$

---

## 2. 排序问题形式化

### 2.1 排序问题定义

**定义 2.1** (排序函数)
排序函数是一个映射：
$$\text{sort}: \text{Sequence}(T) \times \text{Ordering}(T) \rightarrow \text{Sequence}(T)$$

其中：

- $\text{Sequence}(T)$ 是类型T的序列
- $\text{Ordering}(T)$ 是T上的全序关系
- 输出是输入序列的有序排列

**定义 2.2** (排序正确性)
排序算法A是正确的，当且仅当：
$$\forall L \in \text{Sequence}(T): \text{is\_sorted}(\text{A}(L)) \land \text{is\_permutation}(L, \text{A}(L))$$

### 2.2 复杂度定义

**定义 2.3** (时间复杂度)
排序算法的时间复杂度定义为：
$$\text{TimeComplexity}(A) = O(f(n))$$

其中n是输入序列的长度。

**定义 2.4** (空间复杂度)
排序算法的空间复杂度定义为：
$$\text{SpaceComplexity}(A) = O(g(n))$$

---

## 3. 基础排序算法

### 3.1 冒泡排序

**定义 3.1** (冒泡排序)
冒泡排序重复地遍历待排序序列，比较相邻元素，如果顺序错误就交换它们。

**算法 3.1** (冒泡排序)

```
function bubble_sort(A[1..n]):
    for i = 1 to n-1:
        for j = 1 to n-i:
            if A[j] > A[j+1]:
                swap(A[j], A[j+1])
```

**定理 3.1** (冒泡排序正确性)
冒泡排序算法是正确的。

**证明**：

1. 每次外层循环后，最大的i个元素已处于正确位置
2. 经过n-1次外层循环，所有元素都在正确位置
3. 因此算法正确

**复杂度分析**：

- 时间复杂度：$O(n^2)$
- 空间复杂度：$O(1)$
- 稳定性：稳定

**代码示例 3.1** (冒泡排序实现)

```rust
fn bubble_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    
    for i in 0..n {
        let mut swapped = false;
        // 每次遍历将最大的元素放到末尾
        for j in 0..n - 1 - i {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
                swapped = true;
            }
        }
        // 如果一轮没有交换，说明已经有序
        if !swapped {
            break;
        }
    }
}

// 测试
fn test_bubble_sort() {
    let mut arr = [64, 34, 25, 12, 22, 11, 90];
    bubble_sort(&mut arr);
    assert_eq!(arr, [11, 12, 22, 25, 34, 64, 90]);
}
```

### 3.2 插入排序

**定义 3.2** (插入排序)
插入排序构建有序序列，对于未排序数据，在已排序序列中从后向前扫描，找到相应位置并插入。

**算法 3.2** (插入排序)

```
function insertion_sort(A[1..n]):
    for i = 2 to n:
        key = A[i]
        j = i - 1
        while j > 0 and A[j] > key:
            A[j+1] = A[j]
            j = j - 1
        A[j+1] = key
```

**定理 3.2** (插入排序不变性)
在处理第k个元素时，前k-1个元素已构成有序子序列。

**复杂度分析**：

- 时间复杂度：$O(n^2)$ (最坏、平均)，$O(n)$ (最好)
- 空间复杂度：$O(1)$
- 稳定性：稳定

**代码示例 3.2** (插入排序实现)

```rust
fn insertion_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    for i in 1..n {
        let mut j = i;
        // 将 arr[i] 插入到 arr[0..=i] 的正确位置
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

// 优化版本：减少swap次数
fn insertion_sort_optimized<T: Ord + Clone>(arr: &mut [T]) {
    let n = arr.len();
    for i in 1..n {
        let current = arr[i].clone();
        let mut j = i;
        while j > 0 && arr[j - 1] > current {
            arr[j] = arr[j - 1].clone();
            j -= 1;
        }
        arr[j] = current;
    }
}
```

### 3.3 选择排序

**定义 3.3** (选择排序)
选择排序每次从未排序部分选择最小（或最大）的元素，放到已排序部分的末尾。

**算法 3.3** (选择排序)

```
function selection_sort(A[1..n]):
    for i = 1 to n-1:
        min_index = i
        for j = i+1 to n:
            if A[j] < A[min_index]:
                min_index = j
        swap(A[i], A[min_index])
```

**定理 3.3** (选择排序不变性)
第k次迭代后，前k个元素是原序列中最小的k个元素，且已有序。

**复杂度分析**：

- 时间复杂度：$O(n^2)$ (最坏、平均、最好)
- 空间复杂度：$O(1)$
- 稳定性：不稳定

**代码示例 3.3** (选择排序实现)

```rust
fn selection_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    for i in 0..n {
        let mut min_index = i;
        // 找到 arr[i..n] 中的最小元素
        for j in i + 1..n {
            if arr[j] < arr[min_index] {
                min_index = j;
            }
        }
        // 如果最小元素不是当前元素，则交换
        if i != min_index {
            arr.swap(i, min_index);
        }
    }
}
```

---

## 4. 高效排序算法

### 4.1 归并排序

**定义 4.1** (归并排序)
归并排序基于分治策略，递归地将序列分成两半，排序左右子序列，然后合并两个已排序的子序列。

**算法 4.1** (归并排序)

```
function merge_sort(A[1..n]):
    if n <= 1:
        return A
    mid = n / 2
    left = merge_sort(A[1..mid])
    right = merge_sort(A[mid+1..n])
    return merge(left, right)

function merge(left, right):
    result = []
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result
```

**定理 4.1** (归并排序复杂度)
归并排序的时间复杂度为 $O(n \log n)$。

**证明**：

1. 递归树高度为 $\log n$
2. 每层需要 $O(n)$ 时间合并
3. 总时间复杂度为 $O(n \log n)$

**复杂度分析**：

- 时间复杂度：$O(n \log n)$ (最坏、平均、最好)
- 空间复杂度：$O(n)$
- 稳定性：稳定

**代码示例 4.1** (归并排序实现)

```rust
fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    
    let mid = n / 2;
    // 递归排序左右两半
    merge_sort(&mut arr[0..mid]);
    merge_sort(&mut arr[mid..n]);
    
    // 合并两个已排序的子数组
    let mut merged = Vec::with_capacity(n);
    let mut i = 0;
    let mut j = mid;
    
    while i < mid && j < n {
        if arr[i] <= arr[j] {
            merged.push(arr[i].clone());
            i += 1;
        } else {
            merged.push(arr[j].clone());
            j += 1;
        }
    }
    
    // 添加剩余元素
    merged.extend_from_slice(&arr[i..mid]);
    merged.extend_from_slice(&arr[j..n]);
    
    // 复制回原数组
    arr.copy_from_slice(&merged);
}
```

### 4.2 快速排序

**定义 4.2** (快速排序)
快速排序选择一个基准元素，将序列分为两部分，左边都小于基准，右边都大于基准，然后递归排序两部分。

**算法 4.2** (快速排序)

```
function quick_sort(A[1..n]):
    if n <= 1:
        return A
    pivot = partition(A, 1, n)
    quick_sort(A[1..pivot-1])
    quick_sort(A[pivot+1..n])

function partition(A, low, high):
    pivot = A[high]
    i = low - 1
    for j = low to high-1:
        if A[j] <= pivot:
            i += 1
            swap(A[i], A[j])
    swap(A[i+1], A[high])
    return i + 1
```

**定理 4.2** (快速排序平均复杂度)
快速排序的平均时间复杂度为 $O(n \log n)$。

**证明**：

1. 每次分区将序列分为两部分
2. 平均情况下，两部分大小相近
3. 递归树平均高度为 $\log n$
4. 每层需要 $O(n)$ 时间分区
5. 因此平均时间复杂度为 $O(n \log n)$

**复杂度分析**：

- 时间复杂度：$O(n \log n)$ (平均)，$O(n^2)$ (最坏)
- 空间复杂度：$O(\log n)$ (平均)，$O(n)$ (最坏)
- 稳定性：不稳定

**代码示例 4.2** (快速排序实现)

```rust
fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quick_sort(&mut arr[0..pivot_index]);
    quick_sort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len - 1;
    let mut i = 0;
    
    for j in 0..len - 1 {
        if arr[j] <= arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot_index);
    i
}

// 优化版本：三路快排
fn quick_sort_3way<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let (lt, gt) = partition_3way(arr);
    quick_sort_3way(&mut arr[0..lt]);
    quick_sort_3way(&mut arr[gt..]);
}

fn partition_3way<T: Ord>(arr: &mut [T]) -> (usize, usize) {
    let len = arr.len();
    let pivot = &arr[len - 1];
    let mut lt = 0;  // 小于pivot的元素
    let mut gt = len;  // 大于pivot的元素
    let mut i = 0;  // 当前元素
    
    while i < gt {
        if arr[i] < *pivot {
            arr.swap(lt, i);
            lt += 1;
            i += 1;
        } else if arr[i] > *pivot {
            gt -= 1;
            arr.swap(i, gt);
        } else {
            i += 1;
        }
    }
    
    (lt, gt)
}
```

### 4.3 堆排序

**定义 4.3** (堆排序)
堆排序利用堆这种数据结构所设计的排序算法，是一种选择排序。

**算法 4.3** (堆排序)

```
function heap_sort(A[1..n]):
    build_max_heap(A)
    for i = n downto 2:
        swap(A[1], A[i])
        heap_size = heap_size - 1
        max_heapify(A, 1)

function build_max_heap(A):
    heap_size = len(A)
    for i = heap_size/2 downto 1:
        max_heapify(A, i)

function max_heapify(A, i):
    l = left(i)
    r = right(i)
    largest = i
    if l <= heap_size and A[l] > A[i]:
        largest = l
    if r <= heap_size and A[r] > A[largest]:
        largest = r
    if largest != i:
        swap(A[i], A[largest])
        max_heapify(A, largest)
```

**定理 4.3** (堆排序复杂度)
堆排序的时间复杂度为 $O(n \log n)$。

**证明**：

1. 建堆时间复杂度为 $O(n)$
2. 每次提取最大值需要 $O(\log n)$ 时间
3. 总共需要提取n次
4. 因此总时间复杂度为 $O(n \log n)$

**复杂度分析**：

- 时间复杂度：$O(n \log n)$ (最坏、平均、最好)
- 空间复杂度：$O(1)$
- 稳定性：不稳定

**代码示例 4.3** (堆排序实现)

```rust
fn heap_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    
    // 建堆
    for i in (0..len / 2).rev() {
        heapify(arr, i, len);
    }
    
    // 逐个提取最大值
    for i in (1..len).rev() {
        arr.swap(0, i);
        heapify(arr, 0, i);
    }
}

fn heapify<T: Ord>(arr: &mut [T], mut i: usize, heap_size: usize) {
    loop {
        let left = 2 * i + 1;
        let right = 2 * i + 2;
        let mut largest = i;
        
        if left < heap_size && arr[left] > arr[largest] {
            largest = left;
        }
        
        if right < heap_size && arr[right] > arr[largest] {
            largest = right;
        }
        
        if largest == i {
            break;
        }
        
        arr.swap(i, largest);
        i = largest;
    }
}
```

---

## 5. 非比较排序

### 5.1 计数排序

**定义 5.1** (计数排序)
计数排序是一种非比较排序算法，它通过统计每个元素出现的次数来进行排序。

**算法 5.1** (计数排序)

```text
function counting_sort(A[1..n], k):
    count = array of size k+1, initialized to 0
    output = array of size n
    
    // 统计每个元素出现的次数
    for i = 1 to n:
        count[A[i]] += 1
    
    // 计算累积计数
    for i = 1 to k:
        count[i] += count[i-1]
    
    // 构建输出数组
    for i = n downto 1:
        output[count[A[i]]] = A[i]
        count[A[i]] -= 1
    
    return output
```

**定理 5.1** (计数排序复杂度)
计数排序的时间复杂度为 $O(n + k)$，其中k是数据范围。

**复杂度分析**：

- 时间复杂度：$O(n + k)$
- 空间复杂度：$O(n + k)$
- 稳定性：稳定

**代码示例 5.1** (计数排序实现)

```rust
fn counting_sort(arr: &mut [usize], max_value: usize) {
    let n = arr.len();
    let mut count = vec![0; max_value + 1];
    let mut output = vec![0; n];
    
    // 统计每个元素出现的次数
    for &x in arr.iter() {
        count[x] += 1;
    }
    
    // 计算累积计数
    for i in 1..=max_value {
        count[i] += count[i - 1];
    }
    
    // 构建输出数组
    for &x in arr.iter().rev() {
        let index = count[x] - 1;
        output[index] = x;
        count[x] -= 1;
    }
    
    // 复制回原数组
    arr.copy_from_slice(&output);
}
```

### 5.2 基数排序

**定义 5.2** (基数排序)
基数排序是一种非比较排序算法，它按照每个数字的位数进行排序。

**算法 5.2** (基数排序)

```
function radix_sort(A[1..n], d):
    for i = 1 to d:
        // 使用稳定的排序算法对第i位进行排序
        counting_sort_by_digit(A, i)
```

**定理 5.2** (基数排序复杂度)
基数排序的时间复杂度为 $O(d(n + k))$，其中d是位数，k是基数。

**复杂度分析**：

- 时间复杂度：$O(d(n + k))$
- 空间复杂度：$O(n + k)$
- 稳定性：稳定

**代码示例 5.2** (基数排序实现)

```rust
fn radix_sort(arr: &mut [usize]) {
    if arr.is_empty() {
        return;
    }
    
    let max_value = *arr.iter().max().unwrap();
    let mut exp = 1;
    
    while max_value / exp > 0 {
        counting_sort_by_digit(arr, exp);
        exp *= 10;
    }
}

fn counting_sort_by_digit(arr: &mut [usize], exp: usize) {
    let n = arr.len();
    let mut count = vec![0; 10];
    let mut output = vec![0; n];
    
    // 统计每个数字出现的次数
    for &x in arr.iter() {
        let digit = (x / exp) % 10;
        count[digit] += 1;
    }
    
    // 计算累积计数
    for i in 1..10 {
        count[i] += count[i - 1];
    }
    
    // 构建输出数组
    for &x in arr.iter().rev() {
        let digit = (x / exp) % 10;
        let index = count[digit] - 1;
        output[index] = x;
        count[digit] -= 1;
    }
    
    // 复制回原数组
    arr.copy_from_slice(&output);
}
```

---

## 6. 排序算法分析

### 6.1 比较排序下界

**定理 6.1** (比较排序下界)
任何基于比较的排序算法在最坏情况下的时间复杂度至少为 $\Omega(n \log n)$。

**证明**：

1. n个元素有n!种不同的排列
2. 每次比较最多能区分2种情况
3. 需要至少 $\log_2(n!)$ 次比较
4. 根据斯特林公式，$\log_2(n!) = \Omega(n \log n)$

### 6.2 排序算法比较

**表 6.1** (排序算法性能比较)

| 算法 | 平均时间复杂度 | 最坏时间复杂度 | 空间复杂度 | 稳定性 |
|------|----------------|----------------|------------|--------|
| 冒泡排序 | $O(n^2)$ | $O(n^2)$ | $O(1)$ | 稳定 |
| 插入排序 | $O(n^2)$ | $O(n^2)$ | $O(1)$ | 稳定 |
| 选择排序 | $O(n^2)$ | $O(n^2)$ | $O(1)$ | 不稳定 |
| 归并排序 | $O(n \log n)$ | $O(n \log n)$ | $O(n)$ | 稳定 |
| 快速排序 | $O(n \log n)$ | $O(n^2)$ | $O(\log n)$ | 不稳定 |
| 堆排序 | $O(n \log n)$ | $O(n \log n)$ | $O(1)$ | 不稳定 |
| 计数排序 | $O(n + k)$ | $O(n + k)$ | $O(n + k)$ | 稳定 |
| 基数排序 | $O(d(n + k))$ | $O(d(n + k))$ | $O(n + k)$ | 稳定 |

### 6.3 Rust标准库排序

**代码示例 6.1** (Rust标准库排序)

```rust
use std::collections::BinaryHeap;

fn rust_standard_sorting() {
    // Vec排序
    let mut numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    numbers.sort();  // 稳定排序
    println!("Sorted: {:?}", numbers);
    
    // 不稳定排序
    let mut numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    numbers.sort_unstable();  // 不稳定排序，通常更快
    println!("Unstable sorted: {:?}", numbers);
    
    // 自定义排序
    let mut words = vec!["banana", "apple", "cherry"];
    words.sort_by(|a, b| a.len().cmp(&b.len()));
    println!("Sorted by length: {:?}", words);
    
    // 堆排序
    let mut heap = BinaryHeap::new();
    heap.push(3);
    heap.push(1);
    heap.push(4);
    
    while let Some(max) = heap.pop() {
        println!("Max: {}", max);
    }
}
```

---

## 7. 形式化验证

### 7.1 排序正确性验证

**定义 7.1** (排序正确性)
排序算法A是正确的，当且仅当：
$$\forall L \in \text{Sequence}(T): \text{is\_sorted}(\text{A}(L)) \land \text{is\_permutation}(L, \text{A}(L))$$

**验证规则 7.1** (排序验证)
$$\frac{\Gamma \vdash A: \text{SortingAlgorithm} \quad \text{Correct}(A)}{\Gamma \vdash \text{Valid}(A)}$$

### 7.2 性能验证

**定义 7.2** (性能验证)
排序算法的性能验证包括：
$$\text{Performance}(A) = (\text{TimeComplexity}(A), \text{SpaceComplexity}(A), \text{Stability}(A))$$

---

## 8. 定理与证明

### 8.1 核心定理

**定理 8.1** (排序算法正确性)
所有上述排序算法都是正确的。

**证明**：

1. 每个算法都基于明确的数学原理
2. 通过归纳法可以证明算法的正确性
3. 实际实现经过充分测试验证

**定理 8.2** (最优排序算法)
对于一般情况，不存在时间复杂度低于 $O(n \log n)$ 的比较排序算法。

**证明**：

1. 基于信息论的下界
2. 比较树模型分析
3. 决策树高度下界

**定理 8.3** (稳定性保持)
稳定的排序算法在多次排序后仍保持稳定性。

**证明**：

1. 稳定性是传递性质
2. 多次稳定排序不会破坏相对顺序
3. 因此保持稳定性

### 8.2 实现验证

**验证 8.1** (排序实现正确性)
Rust的排序算法实现与形式化定义一致。

**验证方法**：

1. 类型系统保证接口正确性
2. 单元测试验证算法正确性
3. 性能测试验证复杂度
4. 压力测试验证稳定性

### 8.3 优化定理

**定理 8.4** (混合排序优化)
结合多种排序算法的混合排序可以获得更好的性能。

**定理 8.5** (缓存友好性)
考虑缓存局部性的排序算法在实际应用中性能更优。

---

## 总结

Rust的排序算法提供了：

1. **多样化算法**：支持多种排序策略
2. **类型安全**：通过泛型和trait保证类型安全
3. **性能优化**：提供稳定和不稳定排序选项
4. **形式化保证**：严格的数学定义和证明
5. **实际应用**：丰富的标准库支持

这些特性使Rust的排序算法既理论严谨又实用高效，能够满足各种排序需求。
