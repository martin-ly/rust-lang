# Rust算法实现：分类、原理与形式化分析

## 目录

- [Rust算法实现：分类、原理与形式化分析](#rust算法实现分类原理与形式化分析)
  - [目录](#目录)
  - [1. 引言：算法、数据结构体体体与Rust](#1-引言算法数据结构体体体与rust)
  - [2. 基础排序算法](#2-基础排序算法)
    - [2.1 排序问题定义](#21-排序问题定义)
    - [2.2 冒泡排序 (Bubble Sort)](#22-冒泡排序-bubble-sort)
    - [2.3 插入排序 (Insertion Sort)](#23-插入排序-insertion-sort)
    - [2.4 选择排序 (Selection Sort)](#24-选择排序-selection-sort)
  - [3. 高效排序算法](#3-高效排序算法)
    - [3.1 归并排序 (Merge Sort)](#31-归并排序-merge-sort)
    - [3.2 快速排序 (Quick Sort)](#32-快速排序-quick-sort)
    - [3.3 堆排序 (Heap Sort)](#33-堆排序-heap-sort)
    - [3.4 Rust标准库排序](#34-rust标准库排序)
  - [4. 搜索算法](#4-搜索算法)
    - [4.1 搜索问题定义](#41-搜索问题定义)
    - [4.2 线性搜索 (Linear Search)](#42-线性搜索-linear-search)
    - [4.3 二分搜索 (Binary Search)](#43-二分搜索-binary-search)
    - [4.4 哈希表查找](#44-哈希表查找)
  - [5. 图算法](#5-图算法)
    - [5.1 图的基本定义与表示](#51-图的基本定义与表示)
    - [5.2 图遍历：广度优先搜索 (BFS)](#52-图遍历广度优先搜索-bfs)
    - [5.3 图遍历：深度优先搜索 (DFS)](#53-图遍历深度优先搜索-dfs)
    - [5.4 最短路径：Dijkstra算法](#54-最短路径dijkstra算法)
    - [5.5 最小生成树：Prim/Kruskal](#55-最小生成树primkruskal)
  - [6. 字符串算法](#6-字符串算法)
    - [6.1 字符串匹配问题](#61-字符串匹配问题)
    - [6.2 KMP算法](#62-kmp算法)
  - [7. 算法设计策略](#7-算法设计策略)
    - [7.1 分治法 (Divide and Conquer)](#71-分治法-divide-and-conquer)
    - [7.2 动态规划 (Dynamic Programming)](#72-动态规划-dynamic-programming)
    - [7.3 贪心算法 (Greedy Algorithms)](#73-贪心算法-greedy-algorithms)
  - [8. 数据结构体体体与算法的交互](#8-数据结构体体体与算法的交互)
    - [8.1 数组/向量 (Vec)](#81-数组向量-vec)
    - [8.2 链表 (LinkedList)](#82-链表-linkedlist)
    - [8.3 哈希表 (HashMap/HashSet)](#83-哈希表-hashmaphashset)
    - [8.4 树 (BTreeMap/BTreeSet, BinaryHeap)](#84-树-btreemapbtreeset-binaryheap)
  - [9. Rust特征对算法实现的影响](#9-rust特征对算法实现的影响)
    - [9.1 所有权与借用](#91-所有权与借用)
    - [9.2 泛型与Trait](#92-泛型与trait)
    - [9.3 迭代器](#93-迭代器)
    - [9.4 安全与`unsafe`](#94-安全与unsafe)
  - [10. 复杂性理论简介](#10-复杂性理论简介)
    - [10.1 时间与空间复杂度](#101-时间与空间复杂度)
    - [10.2 P vs NP 问题](#102-p-vs-np-问题)
  - [11. 结论：Rust中的算法实践](#11-结论rust中的算法实践)
  - [12. 思维导图](#12-思维导图)

## 1. 引言：算法、数据结构体体体与Rust

算法是解决特定问题的一系列明确指令或步骤。数据结构体体体是组织和存储数据的方式。两者紧密相连，高效的算法往往依赖于合适的数据结构体体体。Rust作为一门注重性能、安全和并发的系统编程语言，为实现各种算法提供了强大的工具和独特的视角。其类型系统、所有权模型和丰富的标准库对算法的具体实现方式产生了显著影响。

本篇将梳理常见的算法分类，探讨其核心原理、形式化定义（如适用）、复杂度分析，并展示如何在Rust中实现它们，同时关注Rust语言特征带来的优势和挑战。

## 2. 基础排序算法

### 2.1 排序问题定义

**定义 2.1.1 (排序问题)** 给定一个元素序列 \( L = \langle e_1, e_2, \dots, e_n \rangle \) 和一个全序关系 \( \le \)，排序的目标是找到一个序列 \( L' = \langle e'_1, e'_2, \dots, e'_n \rangle \)，使得 \( L' \) 是 \( L \) 的一个排列，并且满足 \( e'_1 \le e'_2 \le \dots \le e'_n \)。

**定义 2.1.2 (稳定性 Stable Sort)** 如果一个排序算法保持相等元素的相对顺序，则称其为稳定的。即，若在原序列 \( L \) 中 \( e_i = e_j \) 且 \( i < j \)，则在排序后序列 \( L' \) 中，\( e_i \) 仍然在 \( e_j \) 之前。

### 2.2 冒泡排序 (Bubble Sort)

- **原理**：重复地遍历待排序序列，比较相邻元素，如果顺序错误就交换它们。每次遍历至少将一个元素“冒泡”到其最终位置。
- **形式化性质**：
  - **不变性 (Invariant)**：第 \( k \) 次遍历后，序列末尾的 \( k \) 个元素已处于其最终排序位置。
- **复杂度**：
  - 时间：\( O(n^2) \) （最坏、平均），\( O(n) \) （最好，如果已排序且有优化）
  - 空间：\( O(1) \) （原地排序）
- **稳定性**：稳定。
- **Rust示例**：

```rust
fn bubble_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    for i in 0..n {
        let mut swapped = false;
        // 每次遍历将最大的元素放到末尾，所以内层循环作用域可以减小
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
```

- **原理解释**：简单直观，易于实现，但效率低下，主要用于教学或小规模数据。

### 2.3 插入排序 (Insertion Sort)

- **原理**：构建有序序列，对于未排序数据，在已排序序列中从后向前扫描，找到相应位置并插入。
- **形式化性质**：
  - **不变性 (Invariant)**：在处理第 \( k \) 个元素时，前 \( k-1 \) 个元素已构成有序子序列。
- **复杂度**：
  - 时间：\( O(n^2) \) （最坏、平均），\( O(n) \) （最好，如果已排序）
  - 空间：\( O(1) \) （原地排序）
- **稳定性**：稳定。
- **Rust示例**：

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
        let current = arr[i].clone(); // 需要Clone
        let mut j = i;
        while j > 0 && arr[j - 1] > current {
            // 将元素后移，而不是每次都swap
            arr[j] = arr[j - 1].clone(); // 需要Clone
            j -= 1;
        }
        arr[j] = current;
    }
}
```

- **原理解释**：对于小规模或部分有序的数据效率较高。常用于其他排序算法（如TimSort）的子过程。

### 2.4 选择排序 (Selection Sort)

- **原理**：每次从未排序部分选择最小（或最大）的元素，放到已排序部分的末尾。
- **形式化性质**：
  - **不变性 (Invariant)**：第 \( k \) 次迭代后，前 \( k \) 个元素是原序列中最小的 \( k \) 个元素，且已有序。
- **复杂度**：
  - 时间：\( O(n^2) \) （最坏、平均、最好）
  - 空间：\( O(1) \) （原地排序）
- **稳定性**：不稳定（取决于交换实现，标准实现不稳定）。
- **Rust示例**：

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

- **原理解释**：实现简单，交换次数少（最多n-1次），但在比较次数上没有优势。

## 3. 高效排序算法

### 3.1 归并排序 (Merge Sort)

- **原理**：基于分治策略。递归地将序列分成两半，排序左右子序列，然后合并两个已排序的子序列。
- **形式化定义 (合并操作 Merge)**：输入两个已排序序列 \( A, B \)，输出一个包含 \( A \) 和 \( B \) 所有元素的已排序序列 \( C \)。可以通过比较 \( A, B \) 的首元素，将较小的元素移入 \( C \) 并重复此过程来完成。
- **复杂度**：
  - 时间：\( O(n \log n) \) （最坏、平均、最好）
  - 空间：\( O(n) \) （需要额外空间进行合并），或 \( O(\log n) \) （原地归并，但复杂且效率较低）
- **稳定性**：稳定。
- **Rust示例 (需要额外空间)**：

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
    let mut left = 0;
    let mut right = mid;

    while left < mid && right < n {
        if arr[left] <= arr[right] {
            merged.push(arr[left].clone()); // 需要Clone
            left += 1;
        } else {
            merged.push(arr[right].clone()); // 需要Clone
            right += 1;
        }
    }
    // 将剩余的元素加入merged
    merged.extend_from_slice(&arr[left..mid]);
    merged.extend_from_slice(&arr[right..n]);

    // 将合并后的结果复制回原数组
    arr.clone_from_slice(&merged);
}
```

- **原理解释**：性能稳定，保证 \( O(n \log n) \) 时间复杂度，且是稳定排序，常用于外部排序或需要稳定性的场景。

### 3.2 快速排序 (Quick Sort)

- **原理**：基于分治策略。选择一个“基准”元素(pivot)，将序列分区(partition)成两部分：小于基准的元素和大于等于基准的元素。然后递归地对两个子序列进行排序。
- **形式化定义 (分区操作 Partition)**：对序列 \( A[p..r] \)，选择基准 \( x = A[k] \)。重新排列 \( A[p..r] \)，使得存在一个索引 \( q \)，满足 \( p \le q \le r \)，并且对于所有 \( i \) 使得 \( p \le i < q \)，有 \( A[i] \le x \)，对于所有 \( j \) 使得 \( q \le j \le r \)，有 \( A[j] \ge x \)。返回索引 \( q \)。常用Lomuto或Hoare分区方案。
- **复杂度**：
  - 时间：\( O(n \log n) \) （平均、最好），\( O(n^2) \) （最坏，取决于基准选择）
  - 空间：\( O(\log n) \) （平均，递归栈深度），\( O(n) \) （最坏）
- **稳定性**：不稳定。
- **Rust示例 (Lomuto Partition)**：

```rust
fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot_index = partition(arr);
    // 递归排序左右分区
    quick_sort(&mut arr[0..pivot_index]);
    // 注意：基准元素已在正确位置，不需要包含在递归调用中
    // 但索引需要调整
    if pivot_index + 1 < arr.len() {
         quick_sort(&mut arr[pivot_index + 1..]);
    }
}

// Lomuto分区方案，选择最后一个元素作为基准
fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let n = arr.len();
    let pivot_index = n - 1; // 选择最后一个元素为基准
    let mut i = 0; // i 是小于基准的区域的右边界
    for j in 0..pivot_index {
        if arr[j] <= arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }
    // 将基准元素放到正确的位置
    arr.swap(i, pivot_index);
    i // 返回基准元素的最终索引
}
```

- **原理解释**：实践中平均性能非常好，常数因子小。但最坏情况性能差，需要优化基准选择策略（如三数取中、随机化）来避免。

### 3.3 堆排序 (Heap Sort)

- **原理**：利用堆（通常是最大堆）这种数据结构体体体进行排序。首先将输入序列构建成一个最大堆。然后重复地将堆顶（最大元素）与堆末尾元素交换，并调整堆的大小，重新维护堆的性质。
- **形式化定义 (堆 Heap)**：一个数组 \( A \) 可以被视为一个近似完整的二叉树，如果它满足堆性质（父节点 \( \ge \) 子节点（最大堆）或父节点 \( \le \) 子节点（最小堆）），则称为堆。
- **形式化定义 (建堆 Build-Heap)**：将一个无序数组 \( A \) 转换成满足堆性质的数组。通常通过从最后一个非叶子节点开始向上调用 `heapify` 完成。
- **形式化定义 (维护堆性质 Heapify)**：给定一个节点 \( i \) 和它的左右子树（假设它们已满足堆性质），调整 \( A[i] \) 的位置，使得以 \( i \) 为根的子树满足堆性质。
- **复杂度**：
  - 时间：\( O(n \log n) \) （最坏、平均、最好）
  - 空间：\( O(1) \) （原地排序）
- **稳定性**：不稳定。
- **Rust示例**：

```rust
fn heap_sort<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    // 1. 构建最大堆
    // 从最后一个非叶子节点开始，向上调整
    for i in (0..n / 2).rev() {
        heapify(arr, n, i);
    }

    // 2. 排序阶段
    // 重复将堆顶元素（最大）与末尾元素交换，并重新调整堆
    for i in (1..n).rev() {
        arr.swap(0, i); // 将最大元素放到数组末尾
        heapify(arr, i, 0); // 调整剩余元素，保持堆性质 (堆大小减1)
    }
}

// 维护最大堆性质 (子树根节点为 i, 堆大小为 n)
fn heapify<T: Ord>(arr: &mut [T], n: usize, i: usize) {
    let mut largest = i; // 假设根是最大的
    let left = 2 * i + 1;
    let right = 2 * i + 2;

    // 如果左子节点存在且大于根
    if left < n && arr[left] > arr[largest] {
        largest = left;
    }

    // 如果右子节点存在且大于当前最大值
    if right < n && arr[right] > arr[largest] {
        largest = right;
    }

    // 如果最大值不是根节点
    if largest != i {
        arr.swap(i, largest);
        // 递归地调整受影响的子树
        heapify(arr, n, largest);
    }
}
```

- **原理解释**：保证 \( O(n \log n) \) 时间复杂度，且是原地排序。但实际性能常数因子通常比快速排序大。

### 3.4 Rust标准库排序

- **`Vec::sort()` / `slice::sort()`**：这是不稳定的排序，目前实现通常是基于**模式击败快速排序 (Pattern-defeating Quicksort, pdqsort)**，这是一种快速排序的变种，能抵抗某些导致 \( O(n^2) \) 性能的输入模式，性能非常好。
- **`Vec::sort_unstable()` / `slice::sort_unstable()`**：同上。
- **`Vec::sort_by()` / `slice::sort_by()`**：根据自定义比较函数进行不稳定排序。
- **`Vec::sort_unstable_by()` / `slice::sort_unstable_by()`**：同上。
- **`Vec::sort_by_key()` / `slice::sort_by_key()`**：根据从元素提取的键进行不稳定排序。
- **`Vec::sort_unstable_by_key()` / `slice::sort_unstable_by_key()`**：同上。
- **`slice::sort_stable()`**：(需要启用 nightly 功能或等待稳定) 提供稳定的排序，可能基于归并排序或TimSort的变种。

**原理说明**：标准库的选择反映了对实践性能的重视。Pdqsort 在各种数据分布下都表现出优秀的性能，是现代不依赖稳定性的通用排序首选。

## 4. 搜索算法

### 4.1 搜索问题定义

**定义 4.1.1 (搜索问题)** 给定一个数据集 \( S \) 和一个目标元素 \( x \)，确定 \( x \) 是否在 \( S \) 中。如果存在，通常还需要返回其位置或相关信息。

### 4.2 线性搜索 (Linear Search)

- **原理**：按顺序检查数据集中的每个元素，直到找到目标或遍历完整个数据集。
- **复杂度**：
  - 时间：\( O(n) \) （最坏、平均），\( O(1) \) （最好）
  - 空间：\( O(1) \)
- **Rust示例**：

```rust
fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (index, element) in arr.iter().enumerate() {
        if element == target {
            return Some(index);
        }
    }
    None // 未找到
}

// 使用迭代器方法更简洁
fn linear_search_idiomatic<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    arr.iter().position(|element| element == target)
}
```

- **原理解释**：最简单的搜索算法，适用于无序数据或小数据集。

### 4.3 二分搜索 (Binary Search)

- **原理**：要求数据集**必须是有序的**。通过比较目标元素与数据集的中间元素，将搜索作用域缩小一半。重复此过程，直到找到目标或搜索作用域为空。
- **形式化性质**：
  - **不变性 (Invariant)**：在每次迭代开始时，如果目标元素存在，则它必定在当前的搜索作用域 `[low..high]` 内。
- **复杂度**：
  - 时间：\( O(\log n) \) （最坏、平均、最好）
  - 空间：\( O(1) \) （迭代实现），\( O(\log n) \) （递归实现，栈空间）
- **Rust示例 (迭代)**：

```rust
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut low = 0;
    let mut high = arr.len(); // 使用开区间 [low, high)

    while low < high {
        let mid = low + (high - low) / 2; // 防止溢出
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Less => low = mid + 1,
            std::cmp::Ordering::Greater => high = mid,
            std::cmp::Ordering::Equal => return Some(mid),
        }
    }
    None // 未找到
}

// 标准库提供了更强大的版本
// slice::binary_search(&target) -> Result<usize, usize>
```

- **原理解释**：效率极高，是对数时间复杂度。但前提是数据必须有序。

### 4.4 哈希表查找

- **原理**：利用哈希函数将键映射到存储桶（通常是数组索引）。理想情况下，查找、插入、删除操作接近常数时间。
- **形式化定义 (哈希函数 Hash Function)**：一个函数 \( h: U \to \{0, 1, \dots, m-1\} \)，将全域键空间 \( U \) 映射到大小为 \( m \) 的哈希表槽位。
- **定义 (碰撞 Collision)**：当 \( k_1 \ne k_2 \) 但 \( h(k_1) = h(k_2) \) 时，发生碰撞。需要解决碰撞（如链地址法、开放地址法）。
- **复杂度**：
  - 时间：\( O(1) \) （平均，假设哈希函数良好且负载因子适中），\( O(n) \) （最坏，所有元素哈希到同一位置）
  - 空间：\( O(n) \)
- **Rust示例 (使用 `std::collections::HashMap`)**：

```rust
use std::collections::HashMap;

fn hash_table_example() {
    let mut map = HashMap::new();
    map.insert("apple", 1);
    map.insert("banana", 2);

    // 查找
    match map.get("apple") {
        Some(&value) => println!("Found apple: {}", value), // 通常 O(1)
        None => println!("Apple not found"),
    }

    // 检查是否存在
    if map.contains_key("banana") { // 通常 O(1)
        println!("Banana exists");
    }
}
```

- **原理解释**：提供了平均 \( O(1) \) 的查找性能，非常常用。性能依赖于哈希函数的质量和碰撞处理策略。

## 5. 图算法

### 5.1 图的基本定义与表示

**定义 5.1.1 (图 Graph)** 图 \( G = (V, E) \) 由顶点集合 \( V \) 和边集合 \( E \) 组成。边连接顶点对。图可以是无向的或有向的，带权的或无权的。

**Rust表示**：

- **邻接列表 (Adjacency List)**：使用 `Vec<Vec<usize>>` 或 `HashMap<NodeId, Vec<EdgeInfo>>`。空间效率高，适合稀疏图。
- **邻接矩阵 (Adjacency Matrix)**：使用二维数组 `Vec<Vec<Option<Weight>>>`。空间 \( O(|V|^2) \)，适合稠密图，判断边是否存在快。
- **边列表 (Edge List)**：`Vec<(NodeId, NodeId, Option<Weight>)>`。

选择哪种表示取决于图的特征和所需操作。使用 `petgraph` 等库可以简化图操作。

### 5.2 图遍历：广度优先搜索 (BFS)

- **原理**：从源顶点开始，逐层探索图。先访问所有距离源顶点为1的邻居，然后是距离为2的，依此类推。使用队列实现。
- **形式化性质**：
  - **定理 (BFS最短路径)**：在无权图中，BFS找到的从源顶点到所有可达顶点的路径是最短路径（边数最少）。
- **复杂度**：
  - 时间：\( O(|V| + |E|) \) （邻接列表），\( O(|V|^2) \) （邻接矩阵）
  - 空间：\( O(|V|) \) （存储队列和访问状态）
- **Rust示例 (概念，使用邻接列表)**：

```rust
use std::collections::{VecDeque, HashSet};

// 假设 graph 是 Vec<Vec<usize>> 表示的邻接列表
fn bfs(graph: &Vec<Vec<usize>>, start_node: usize) -> HashSet<usize> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();

    visited.insert(start_node);
    queue.push_back(start_node);

    while let Some(node) = queue.pop_front() {
        println!("Visiting node: {}", node); // 处理节点

        for &neighbor in &graph[node] {
            if visited.insert(neighbor) { // 如果邻居未访问过
                queue.push_back(neighbor);
            }
        }
    }
    visited // 返回所有访问过的节点
}
```

- **原理解释**：适用于查找无权图最短路径、层序遍历等。

### 5.3 图遍历：深度优先搜索 (DFS)

- **原理**：从源顶点开始，尽可能深地探索图的分支。当一个分支探索到底（或遇到已访问节点）时，回溯到上一个节点，继续探索其他未访问分支。使用栈（递归或显式）实现。
- **形式化性质**：
  - **定理 (括号定理 Parenthesis Theorem)**：在DFS遍历中，一个顶点 \( v \) 的发现时间 `d[v]` 和完成时间 `f[v]` 形成的区间 `[d[v], f[v]]`，对于任意两个顶点 \( u, v \)，这两个区间要么完全不相交，要么一个完全包含另一个。
- **复杂度**：
  - 时间：\( O(|V| + |E|) \) （邻接列表），\( O(|V|^2) \) （邻接矩阵）
  - 空间：\( O(|V|) \) （存储访问状态和递归栈）
- **Rust示例 (递归)**：

```rust
use std::collections::HashSet;

// 假设 graph 是 Vec<Vec<usize>> 表示的邻接列表
fn dfs(graph: &Vec<Vec<usize>>, start_node: usize) -> HashSet<usize> {
    let mut visited = HashSet::new();
    dfs_recursive(graph, start_node, &mut visited);
    visited
}

fn dfs_recursive(graph: &Vec<Vec<usize>>, node: usize, visited: &mut HashSet<usize>) {
    visited.insert(node);
    println!("Visiting node: {}", node); // 处理节点

    for &neighbor in &graph[node] {
        if !visited.contains(&neighbor) {
            dfs_recursive(graph, neighbor, visited);
        }
    }
}
```

- **原理解释**：适用于拓扑排序、查找连通分量、查找环等。

### 5.4 最短路径：Dijkstra算法

- **原理**：用于查找带**非负**权重的图中，从单一源点到所有其他顶点的最短路径。维护一个距离集合，从未确定最短路径的顶点中选择距离源点最近的顶点，更新其邻居的距离。通常使用优先队列（最小堆）优化。
- **形式化定义 (松弛 Relaxation)**：对于边 \( (u, v) \) 权重为 \( w(u, v) \)，如果当前估计的到 \( v \) 的距离 `dist[v]` 大于通过 \( u \) 到达 \( v \) 的距离 `dist[u] + w(u, v)`，则更新 `dist[v]`。
- **复杂度**：
  - 时间：\( O(|E| \log |V|) \) （使用二叉堆优先队列），\( O(|E| + |V| \log |V|) \) （使用斐波那契堆）
  - 空间：\( O(|V|) \) （存储距离和优先队列）
- **Rust示例 (概念，需要优先队列)**：

```rust
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    cost: usize,
    position: usize,
}

// 让BinaryHeap成为最小堆
impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost) // 注意反转比较
            .then_with(|| self.position.cmp(&other.position))
    }
}
impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// 假设 graph 是 HashMap<usize, Vec<(usize, usize)>> (邻接列表，节点->(邻居, 权重))
fn dijkstra(graph: &HashMap<usize, Vec<(usize, usize)>>, start_node: usize) -> HashMap<usize, usize> {
    let mut dist: HashMap<usize, usize> = HashMap::new();
    let mut pq = BinaryHeap::new();

    dist.insert(start_node, 0);
    pq.push(State { cost: 0, position: start_node });

    while let Some(State { cost, position }) = pq.pop() {
        // 如果找到更短的路径，则忽略
        if cost > *dist.get(&position).unwrap_or(&usize::MAX) {
            continue;
        }

        // 遍历邻居
        if let Some(neighbors) = graph.get(&position) {
            for &(neighbor, weight) in neighbors {
                let next = State { cost: cost + weight, position: neighbor };

                if next.cost < *dist.get(&neighbor).unwrap_or(&usize::MAX) {
                    pq.push(next);
                    dist.insert(neighbor, next.cost);
                }
            }
        }
    }
    dist
}
```

- **原理解释**：经典的单源最短路径算法，但不能处理负权边。

### 5.5 最小生成树：Prim/Kruskal

**定义 5.5.1 (最小生成树 Minimum Spanning Tree, MST)**：对于一个连通的、无向的、带权图 \( G = (V, E, w) \)，MST 是一个子图 \( T = (V, E') \)，其中 \( E' \subseteq E \)，\( T \) 是一棵树且连接所有顶点，并且 \( T \) 的边的总权重 \( \sum_{e \in E'} w(e) \) 最小。

- **Prim算法原理**：贪心策略。从任意顶点开始，逐步扩展树。每次选择连接树内顶点和树外顶点中权重最小的边，并将对应的树外顶点加入树中，直到所有顶点都加入。通常使用优先队列优化。
  - 复杂度：\( O(|E| \log |V|) \) (二叉堆)
- **Kruskal算法原理**：贪心策略。将所有边按权重排序。依次考虑权重最小的边，如果该边连接的两个顶点尚未连通（使用并查集判断），则将该边加入MST。
  - 复杂度：\( O(|E| \log |E|) \) 或 \( O(|E| \log |V|) \) (主要取决于排序和并查集操作)

- **原理解释**：两种算法都基于贪心策略，证明其正确性需要用到**切割性质 (Cut Property)**：对于图的任意切割（将顶点分成两部分），连接两部分的权重最小的边一定属于某个MST。

## 6. 字符串算法

### 6.1 字符串匹配问题

**定义 6.1.1 (字符串匹配)**：给定一个文本串 \( T \) 和一个模式串 \( P \)，查找 \( P \) 在 \( T \) 中所有出现的位置。

### 6.2 KMP算法

- **原理**：利用模式串本身的性质（前后缀匹配信息）来避免在匹配失败时不必要的回溯。构建一个“部分匹配表”（next数组），记录当匹配在模式串的第 \( j \) 个字符失败时，应该将模式串向右滑动多少位（等价于将模式串的指针移到 `next[j]`）。
- **形式化定义 (next数组)**：`next[j]` 是模式串 \( P[0..j-1] \) 的最长真前缀，同时也是其后缀的长度。
- **复杂度**：
  - 时间：\( O(|T| + |P|) \) （预处理next数组 \( O(|P|) \)，匹配 \( O(|T|) \)）
  - 空间：\( O(|P|) \) （存储next数组）
- **Rust示例 (概念)**：

```rust
fn kmp_search(text: &str, pattern: &str) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    if m == 0 { return vec![]; }
    if n < m { return vec![]; }

    let next = compute_next(pattern);
    let mut matches = Vec::new();
    let text_bytes = text.as_bytes();
    let pattern_bytes = pattern.as_bytes();

    let mut j = 0; // pattern 中的索引
    for i in 0..n { // text 中的索引
        // 如果字符不匹配，使用 next 数组调整 j
        while j > 0 && text_bytes[i] != pattern_bytes[j] {
            j = next[j - 1];
        }
        // 如果字符匹配，增加 j
        if text_bytes[i] == pattern_bytes[j] {
            j += 1;
        }
        // 如果 j 到达模式串末尾，说明找到匹配
        if j == m {
            matches.push(i - m + 1);
            // 继续查找下一个匹配，使用 next 数组调整 j
            j = next[j - 1];
        }
    }
    matches
}

// 计算 KMP 的 next 数组 (部分匹配表)
fn compute_next(pattern: &str) -> Vec<usize> {
    let m = pattern.len();
    let mut next = vec![0; m];
    let pattern_bytes = pattern.as_bytes();
    let mut length = 0; // 当前匹配的前后缀长度
    let mut i = 1; // 从第二个字符开始计算

    while i < m {
        if pattern_bytes[i] == pattern_bytes[length] {
            length += 1;
            next[i] = length;
            i += 1;
        } else {
            if length != 0 {
                // 回溯到上一个可能匹配的前后缀长度
                length = next[length - 1];
            } else {
                // 没有更短的前后缀可以匹配
                next[i] = 0;
                i += 1;
            }
        }
    }
    next
}
```

- **原理解释**：经典的线性时间字符串匹配算法，通过预处理模式串避免了朴素算法的低效回溯。

## 7. 算法设计策略

### 7.1 分治法 (Divide and Conquer)

- **原理**：将问题分解成若干个规模较小、相互独立的相同子问题；递归地解决这些子问题；将子问题的解合并成原问题的解。
- **适用条件**：问题可以分解，子问题独立，合并步骤可高效完成。
- **例子**：归并排序、快速排序、二分搜索。
- **形式化分析 (主定理 Master Theorem)**：常用于分析分治算法的时间复杂度，形如 \( T(n) = aT(n/b) + f(n) \)。

### 7.2 动态规划 (Dynamic Programming)

- **原理**：将问题分解成相互重叠的子问题。通过存储子问题的解（通常在表格中），避免重复计算。适用于具有最优子结构体体体和重叠子问题性质的问题。
- **实现方式**：
  - **自顶向下 (Top-Down with Memoization)**：递归求解，使用缓存存储已解决的子问题。
  - **自底向上 (Bottom-Up Tabulation)**：按子问题规模从小到大顺序计算并填表。
- **例子**：斐波那契数列、最长公共子序列、背包问题。
- **Rust示例 (斐波那契 - Bottom-Up)**：

```rust
fn fibonacci_dp(n: usize) -> u64 {
    if n == 0 { return 0; }
    if n == 1 { return 1; }

    let mut dp = vec![0u64; n + 1];
    dp[1] = 1;

    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    dp[n]
}
```

### 7.3 贪心算法 (Greedy Algorithms)

- **原理**：在每一步选择中都采取当前状态下最好或最优（即最贪心）的选择，从而希望能导致全局最好或最优解。
- **适用条件**：问题具有贪心选择性质（局部最优能导致全局最优）和最优子结构体体体。
- **例子**：Dijkstra算法、Prim算法、Kruskal算法、霍夫曼编码。
- **证明**：贪心算法的正确性通常需要数学证明，如使用归纳法或反证法证明其满足贪心选择性质。

## 8. 数据结构体体体与算法的交互

### 8.1 数组/向量 (Vec)

- **特征**：连续内存，\( O(1) \) 索引访问。
- **适用算法**：需要随机访问的算法（如二分搜索、快速排序分区）、需要缓存友好的算法。
- **Rust `Vec<T>`**：动态大小的数组，摊销 \( O(1) \) push/pop。

### 8.2 链表 (LinkedList)

- **特征**：非连续内存，节点包含数据和指向下一（或上一）节点的指针。\( O(1) \) 插入/删除（给定节点引用），\( O(n) \) 查找。
- **适用算法**：需要频繁插入/删除元素的算法，不需要随机访问。
- **Rust `std::collections::LinkedList`**：双向链表。由于所有权和借用规则，在Rust中使用链表通常比C/C++更复杂。

### 8.3 哈希表 (HashMap/HashSet)

- **特征**：基于哈希函数实现键值对存储。平均 \( O(1) \) 查找/插入/删除。
- **适用算法**：需要快速查找、去重、缓存（备忘录）。
- **Rust `std::collections::HashMap/HashSet`**：默认使用SipHash（防哈希洪水攻击），可配置其他哈希器。

### 8.4 树 (BTreeMap/BTreeSet, BinaryHeap)

- **`BTreeMap/BTreeSet`**：
  - 特征：基于B树的有序映射/集合。\( O(\log n) \) 查找/插入/删除。保持元素有序。
  - 适用算法：需要有序遍历、作用域查询、或对数时间复杂度保证的操作。
- **`BinaryHeap`**：
  - 特征：基于二叉堆的优先队列。\( O(\log n) \) 插入/删除最大（或最小）元素，\( O(1) \) 查看最大（或最小）元素。
  - 适用算法：堆排序、Dijkstra、Prim、任何需要优先队列的场景。

## 9. Rust特征对算法实现的影响

### 9.1 所有权与借用

- **影响**：
  - 天然防止数据竞争，有助于并发算法的正确性。
  - 对需要修改输入数据的原地算法（如排序）友好，通过可变借用 `&mut` 实现。
  - 对需要复杂指针操作（如图算法、某些树操作、链表）可能增加实现难度，有时需要 `Rc`, `RefCell` 或 `unsafe`。
  - 移动语义可以优化某些算法的资源传递。

### 9.2 泛型与Trait

- **影响**：
  - 允许编写通用的、类型无关的算法实现，通过Trait约束（如 `Ord`, `PartialOrd`, `Clone`, `Copy`, `Hash`, `Eq`）。
  - Trait提供了类似接口的功能，便于抽象和扩展（如自定义图节点/边类型）。

### 9.3 迭代器

- **影响**：
  - 提供了强大、高效、惯用的序列处理方式。
  - 许多算法（如搜索、映射、过滤）可以用简洁的迭代器链实现。
  - 惰性求值特征可以优化某些算法的性能。

### 9.4 安全与`unsafe`

- **影响**：
  - 默认情况下，Rust编译器保证内存安全和线程安全。
  - 对于性能极致优化或需要直接内存操作的底层算法/数据结构体体体实现，可能需要使用 `unsafe` 块，但需要开发者承担安全保证责任。
  - 标准库和核心库内部使用 `unsafe` 来构建安全的高级抽象。

## 10. 复杂性理论简介

### 10.1 时间与空间复杂度

- **定义 (大O符号 Big O Notation)**：描述算法运行时间或空间消耗随输入规模 \( n \) 增长的**上界**。\( f(n) = O(g(n)) \) 意为存在正常数 \( c \) 和 \( n_0 \)，使得对所有 \( n \ge n_0 \)，有 \( 0 \le f(n) \le c g(n) \)。
- **常见复杂度类别**：\( O(1) \), \( O(\log n) \), \( O(n) \), \( O(n \log n) \), \( O(n^2) \), \( O(2^n) \), \( O(n!) \)。
- **分析**：通常关注最坏情况、平均情况和最好情况复杂度。

### 10.2 P vs NP 问题

- **定义 (P类问题)**：能在多项式时间内由确定性图灵机解决的判定问题集合。
- **定义 (NP类问题)**：能在多项式时间内由非确定性图灵机解决的判定问题集合。等价地，一个解能在多项式时间内被确定性图灵机验证的判定问题集合。
- **P vs NP 问题**：是否 \( P = NP \)？这是理论计算机科学中最核心的未解问题之一。
- **NP完全问题 (NP-Complete)**：属于NP类，并且任何其他NP问题都可以在多项式时间内归约到它的问题。（例如：旅行商问题、布尔可满足性问题SAT）。如果任何一个NP完全问题能在多项式时间内解决，则 \( P = NP \)。

## 11. 结论：Rust中的算法实践

Rust为算法实现提供了一个独特而强大的环境。其强类型系统、泛型和Trait机制支持编写通用、可复用且类型安全的算法代码。所有权和借用系统在提供内存安全的同时，也对某些需要复杂指针操作的算法实现提出了挑战。Rust的迭代器模型则为序列处理算法提供了简洁高效的表达方式。

虽然Rust的安全检查和底层控制可能使得某些算法的初步实现比动态语言更复杂，但它能在编译时捕获大量错误，并允许开发者在需要时通过`unsafe`进行底层优化。标准库提供了高效且经过良好测试的基础算法实现（如排序、搜索、集合操作），开发者通常应优先使用标准库。对于更复杂的算法（如图算法），社区提供了如`petgraph`等高质量库。

最终，Rust不仅是实现已知算法的工具，其特征也可能启发新的算法设计思路，特别是在并发和安全敏感的领域。

## 12. 思维导图

```text
Rust算法梳理
│
├── 1. 基础排序算法
│   ├── 冒泡排序 (O(n^2), Stable)
│   ├── 插入排序 (O(n^2), Stable, O(n) best)
│   └── 选择排序 (O(n^2), Unstable)
│
├── 2. 高效排序算法
│   ├── 归并排序 (O(n log n), Stable, O(n) space)
│   ├── 快速排序 (O(n log n) avg, Unstable, O(log n) space avg)
│   ├── 堆排序 (O(n log n), Unstable, O(1) space)
│   └── Rust标准库 (pdqsort, unstable default)
│
├── 3. 搜索算法
│   ├── 线性搜索 (O(n))
│   ├── 二分搜索 (O(log n), requires sorted)
│   └── 哈希表查找 (O(1) avg)
│
├── 4. 图算法
│   ├── 图表示 (邻接列表/矩阵)
│   ├── 遍历
│   │   ├── BFS (O(V+E), 无权最短路径)
│   │   └── DFS (O(V+E), 拓扑排序, 连通分量)
│   ├── 最短路径 (Dijkstra, O(E log V), 非负权)
│   └── 最小生成树 (Prim/Kruskal, O(E log V))
│
├── 5. 字符串算法
│   ├── 字符串匹配 (KMP, O(T+P))
│   └── (其他: Rabin-Karp, Boyer-Moore...)
│
├── 6. 算法设计策略
│   ├── 分治法 (Merge/Quick Sort, Binary Search)
│   ├── 动态规划 (Fibonacci, LCS, Knapsack)
│   └── 贪心算法 (Dijkstra, Prim, Kruskal)
│
├── 7. 数据结构体体体关联
│   ├── Vec (随机访问)
│   ├── LinkedList (插入/删除)
│   ├── HashMap/HashSet (快速查找)
│   └── Trees (BTree: 有序; BinaryHeap: 优先队列)
│
├── 8. Rust特征影响
│   ├── 所有权/借用 (安全, 指针复杂性)
│   ├── 泛型/Trait (通用性, 约束)
│   ├── 迭代器 (序列处理)
│   └── 安全/unsafe (默认安全, 可选优化)
│
└── 9. 复杂性理论
    ├── 时间/空间复杂度 (Big O)
    └── P vs NP (理论边界)
```

"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 概述
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


