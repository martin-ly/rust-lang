//! # 算法选择决策树
//!
//! 本模块提供了各种算法选择的决策树，帮助开发者根据问题特征选择最合适的算法。
//!
//! 每个决策树以结构体形式组织，通过关联函数返回详细的决策指南（Markdown + ASCII 图表）。
//!
//! ## 决策树列表
//!
//! | 结构体 | 覆盖领域 |
//! |--------|----------|
//! | `SortingDecisionTree` | 排序算法选择 |
//! | `SearchingDecisionTree` | 搜索算法选择 |
//! | `GraphAlgorithmDecisionTree` | 图算法选择 |
//! | `DynamicProgrammingDecisionTree` | 动态规划 vs 贪心 |
//! | `ConcurrencyAlgorithmDecisionTree` | 并发与并行策略 |

// ============================================================
// 排序算法决策树
// ============================================================

/// 排序算法决策树
///
/// 根据数据规模、稳定性需求、内存限制和键类型，选择最合适的排序算法。
pub struct SortingDecisionTree;

impl SortingDecisionTree {
    /// 快速排序 (QuickSort) 使用指南
    pub fn quicksort_guide() -> &'static str {
        r#"# QuickSort 决策指南

## 适用场景
- 通用排序需求（默认首选）
- 内存受限，需要原地排序
- 平均性能要求高，可接受最坏情况 O(n²)

## 决策流程
```
是否需要原地排序?
├── 是 → 数据是否基本有序?
│   ├── 是 → 考虑 InsertionSort 或随机化 QuickSort
│   └── 否 → QuickSort ✅
└── 否 → 考虑 MergeSort
```

## 复杂度
| 情况 | 时间 | 空间 |
|------|------|------|
| 最优 | O(n log n) | O(log n) |
| 平均 | O(n log n) | O(log n) |
| 最坏 | O(n²) | O(log n) |

## Rust 示例
```rust
let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
data.sort_unstable(); // 底层为 Pattern-defeating QuickSort (pdqsort)
```

## 关键提醒
- **不稳定**：相等元素可能改变相对顺序
- **最坏情况**：已排序数据 + 固定枢轴 → 随机化或三数取中
- **缓存友好**：原地操作，局部性良好
"#
    }

    /// 归并排序 (MergeSort) 使用指南
    pub fn mergesort_guide() -> &'static str {
        r#"# MergeSort 决策指南

## 适用场景
- **稳定性是必须的**（相等元素保持原顺序）
- 需要 **保证 O(n log n)** 最坏情况
- **外部排序**：数据太大无法装入内存
- 链表排序（无需随机访问）

## 决策流程
```
是否需要稳定排序?
├── 是 → 内存是否充足?
│   ├── 是 → MergeSort ✅
│   └── 否 → 考虑 TimSort (Rust std::vec::Vec::sort)
└── 否 → 考虑 QuickSort 或 HeapSort
```

## 复杂度
| 情况 | 时间 | 空间 |
|------|------|------|
| 所有情况 | O(n log n) | O(n) |

## Rust 示例
```rust
let mut data = vec![(3, "a"), (1, "b"), (3, "c")];
data.sort_by_key(|k| k.0); // 稳定排序，基于 Timsort
// 结果: [(1, "b"), (3, "a"), (3, "c")]
```

## 关键提醒
- **稳定排序**：相等元素相对顺序不变
- **空间开销**：需要额外 O(n) 缓冲区
- **链表友好**：仅需顺序访问，无需随机访问
- **外部排序**：可分段排序后多路归并
"#
    }

    /// 堆排序 (HeapSort) 使用指南
    pub fn heapsort_guide() -> &'static str {
        r#"# HeapSort 决策指南

## 适用场景
- **严格限制额外内存**（O(1) 辅助空间）
- 需要 **保证 O(n log n)** 最坏时间
- 优先级队列类问题
- 只需要部分有序（如 Top-K）

## 决策流程
```
内存是否极度受限?
├── 是 → 是否需要稳定性?
│   ├── 是 → 无法兼顾，考虑 MergeSort
│   └── 否 → HeapSort ✅
└── 否 → 考虑 QuickSort 或 MergeSort
```

## 复杂度
| 情况 | 时间 | 空间 |
|------|------|------|
| 所有情况 | O(n log n) | O(1) |

## Rust 示例
```rust
use std::collections::BinaryHeap;

let mut heap = BinaryHeap::from(vec![3, 1, 4, 1, 5, 9, 2, 6]);
let mut sorted = Vec::with_capacity(heap.len());
while let Some(x) = heap.pop() {
    sorted.push(x);
}
sorted.reverse(); // BinaryHeap 是大根堆
```

## 关键提醒
- **不稳定**：堆调整会破坏相等元素顺序
- **缓存不友好**：随机访问堆中节点，cache miss 高
- **常数较大**：实际速度通常慢于 QuickSort
- **部分排序优势**：找 Top-K 只需 O(n log k)
"#
    }

    /// 计数排序 / 基数排序 (CountingSort / RadixSort) 使用指南
    pub fn counting_radix_sort_guide() -> &'static str {
        r#"# CountingSort / RadixSort 决策指南

## 适用场景
- **整数键** 或 **固定长度字符串**
- 键的 **取值范围小**（CountingSort: k << n）
- 需要 **线性时间** O(n + k) 或 O(d × (n + k))
- 数据分布均匀（RadixSort 对位数敏感）

## 决策流程
```
键是否为整数或定长字符串?
├── 是 → 范围是否很小 (k <= 10^6)?
│   ├── 是 → CountingSort ✅  O(n + k)
│   └── 否 → 位数 d 是否较小?
│       ├── 是 → RadixSort ✅  O(d * (n + k))
│       └── 否 → 考虑 QuickSort / MergeSort
└── 否 → 考虑比较排序
```

## 复杂度对比
| 算法 | 时间 | 空间 | 稳定性 |
|------|------|------|--------|
| CountingSort | O(n + k) | O(k) | 稳定 |
| RadixSort (LSD) | O(d × (n + k)) | O(n + k) | 稳定 |
| RadixSort (MSD) | O(d × (n + k)) | O(n + k) | 稳定 |

## Rust 示例（CountingSort）
```rust
fn counting_sort(arr: &mut [u32], max_val: u32) {
    let mut count = vec![0usize; (max_val + 1) as usize];
    for &x in arr.iter() {
        count[x as usize] += 1;
    }
    let mut idx = 0;
    for (val, &cnt) in count.iter().enumerate() {
        for _ in 0..cnt {
            arr[idx] = val as u32;
            idx += 1;
        }
    }
}
```

## 关键提醒
- **非比较排序**：打破 O(n log n) 下界
- **范围敏感**：k 太大时空间爆炸
- **稳定实现**：LSD RadixSort 天然稳定
- **浮点数**：需特定位拆解（如按 u32 重新解释）
"#
    }

    /// 插入排序 (InsertionSort) 使用指南
    pub fn insertion_sort_guide() -> &'static str {
        r#"# InsertionSort 决策指南

## 适用场景
- **数据量很小**（n < 20~50）
- **数据基本有序**（逆序对很少）
- **在线排序**：数据流逐个到达
- **递归基例**：Timsort / IntroSort 的 fallback

## 决策流程
```
n < 20?
├── 是 → InsertionSort ✅
└── 否 → 数据是否基本有序?
    ├── 是 → InsertionSort ✅（或 Timsort）
    └── 否 → 考虑 QuickSort / MergeSort
```

## 复杂度
| 情况 | 时间 | 空间 |
|------|------|------|
| 最优（已有序） | O(n) | O(1) |
| 平均 | O(n²) | O(1) |
| 最坏 | O(n²) | O(1) |

## Rust 示例
```rust
fn insertion_sort<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}
```

## 关键提醒
- **自适应**：对已排序数据极快
- **稳定**：相等元素不交换
- **常数极小**：小数据下比 O(n log n) 算法更快
- **写操作多**：每次插入伴随多次 swap
"#
    }

    /// Rust `sort` vs `sort_unstable` 决策
    pub fn rust_sort_decision() -> &'static str {
        r#"# Rust `sort` vs `sort_unstable` 决策

## 快速决策表
| 条件 | 推荐方法 | 底层算法 |
|------|----------|----------|
| 需要稳定性 | `sort` / `sort_by` | Timsort (自适应归并排序) |
| 不需要稳定性 | `sort_unstable` / `sort_unstable_by` | Pattern-defeating QuickSort (pdqsort) |
| 基本类型数组 | `sort_unstable` | pdqsort（更快） |
| 自定义结构体，关心顺序 | `sort` | Timsort |

## 性能对比（典型场景）
```
随机数据：  sort_unstable ≈ 1.2x ~ 1.5x faster than sort
已排序：    sort 更快（Timsort 自适应 O(n)）
重复键多：  sort_unstable 的 pdqsort  partitioning 优势明显
```

## Rust 示例
```rust
let mut v1 = vec![3, 1, 4, 1, 5];
v1.sort_unstable();               // 更快，不稳定

let mut v2 = vec![(3, "a"), (1, "b"), (3, "c")];
v2.sort_by_key(|k| k.0);          // 稳定，保留原始相对顺序
```

## 关键提醒
- `sort` = Timsort (O(n) 最优情况，稳定，需 O(n) 辅助空间)
- `sort_unstable` = pdqsort (O(n log n) 保证，不稳定，O(log n) 栈空间)
- 对 `Copy` 类型或简单值类型，**优先 `sort_unstable`**
"#
    }
}

// ============================================================
// 搜索算法决策树
// ============================================================

/// 搜索算法决策树
///
/// 根据数据是否有序、访问模式、键类型选择搜索策略。
pub struct SearchingDecisionTree;

impl SearchingDecisionTree {
    /// 线性搜索 vs 二分搜索 vs 插值搜索
    pub fn linear_vs_binary_vs_interpolation() -> &'static str {
        r#"# 线性搜索 vs 二分搜索 vs 插值搜索

## 决策流程
```
数据是否有序?
├── 否 → 线性搜索 ✅（或先排序）
└── 是 → 数据分布是否均匀?
    ├── 是 → 插值搜索 ✅（键为数值）
    └── 否 → 二分搜索 ✅
```

## 对比表
| 算法 | 前提条件 | 时间 | 空间 | 适用数据 |
|------|----------|------|------|----------|
| 线性搜索 | 无 | O(n) | O(1) | 任意 |
| 二分搜索 | 有序 + 随机访问 | O(log n) | O(1) | 数组、Vec |
| 插值搜索 | 有序 + 均匀分布 | O(log log n) ~ O(n) | O(1) | 整数/浮点数组 |

## Rust 示例
```rust
let arr = [1, 3, 5, 7, 9, 11, 13];

// 线性搜索
let found = arr.iter().position(|&x| x == 7); // Some(3)

// 二分搜索
let found = arr.binary_search(&7);            // Ok(3)

// 插值搜索（手动实现）
fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = arr.len().saturating_sub(1);
    while low <= high && target >= arr[low] && target <= arr[high] {
        if low == high {
            return if arr[low] == target { Some(low) } else { None };
        }
        let pos = low + ((target - arr[low]) as usize * (high - low))
                        / (arr[high] - arr[low]) as usize;
        match arr[pos].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(pos),
            std::cmp::Ordering::Less => low = pos + 1,
            std::cmp::Ordering::Greater => high = pos - 1,
        }
    }
    None
}
```

## 关键提醒
- **二分搜索**：最稳健的有序数据搜索，标准库直接支持
- **插值搜索**：分布不均匀时退化到 O(n)，谨慎使用
- **线性搜索**：小数组（n < 32）可能比二分搜索更快（缓存 + 分支预测）
"#
    }

    /// 哈希表查找 vs 树查找
    pub fn hash_vs_tree_lookup() -> &'static str {
        r#"# 哈希表查找 vs 树查找

## 决策流程
```
是否需要维护顺序?
├── 是 → 树结构 ✅（BTreeMap / BTreeSet）
└── 否 → 键是否能有效哈希?
    ├── 是 → 哈希表 ✅（HashMap / HashSet）
    └── 否 → 树结构 或 线性搜索
```

## 对比表
| 特性 | HashMap | BTreeMap |
|------|---------|----------|
| 查找 | O(1) 平均 | O(log n) |
| 插入 | O(1) 平均 | O(log n) |
| 有序遍历 | 不支持 | 支持 |
| 范围查询 | 不支持 | 支持 |
| 最小/最大 | 不支持 | O(log n) |
| 内存 | 通常更多 | 通常更少 |
| 最坏情况 | O(n)（哈希冲突） | O(log n) 保证 |

## Rust 示例
```rust
use std::collections::{HashMap, BTreeMap};

// 哈希表：快速点查
let mut hash = HashMap::new();
hash.insert("key", 42);
assert_eq!(hash.get("key"), Some(&42));

// B树：有序 + 范围查询
let mut btree = BTreeMap::new();
btree.insert(10, "a");
btree.insert(20, "b");
btree.insert(30, "c");
for (k, v) in btree.range(15..=25) {
    println!("{} -> {}", k, v); // 20 -> b
}
```

## 关键提醒
- **DoS 防护**：Rust HashMap 默认使用 SipHash，抗碰撞攻击
- **自定义哈希**：若知道键分布，可用 `BuildHasherDefault<FxHasher>` 提速
- **内存碎片**：HashMap 扩容时重新分配全部桶；BTreeMap 更稳定
"#
    }

    /// 预处理（排序+二分） vs 线性扫描
    pub fn preprocess_vs_linear_scan() -> &'static str {
        r#"# 预处理 vs 线性扫描

## 决策流程
```
查询次数 q 是多少?
├── q = 1 → 线性扫描 ✅（排序开销不划算）
└── q > 1 → 数据是否变化频繁?
    ├── 是 → 线性扫描 或 哈希表
    └── 否 → 排序 + 二分搜索 ✅
```

## 成本分析
| 策略 | 预处理 | 单次查询 | q 次查询总成本 |
|------|--------|----------|----------------|
| 线性扫描 | 0 | O(n) | O(q × n) |
| 排序 + 二分 | O(n log n) | O(log n) | O(n log n + q × log n) |
| 哈希表 | O(n) | O(1) | O(n + q) |

## 盈亏平衡点
```
排序 + 二分 优于 线性扫描 当:
    n log n + q log n < q × n
    => q > n log n / (n - log n) ≈ log n (当 n 很大时)

即：只要查询次数 > ~log₂(n)，预处理就划算
```

## Rust 示例
```rust
// 单次查询：线性扫描更快
fn exists_once(arr: &[i32], target: i32) -> bool {
    arr.iter().any(|&x| x == target)
}

// 多次查询：预处理
fn build_sorted_index(mut arr: Vec<i32>) -> Vec<i32> {
    arr.sort_unstable();
    arr
}
fn exists_many(sorted: &[i32], target: i32) -> bool {
    sorted.binary_search(&target).is_ok()
}
```

## 关键提醒
- **动态数据**：若频繁插入/删除，维护有序状态成本高，考虑 BTreeMap
- **读多写少**：排序 + 二分是最简单高效的方案
- **空间换时间**：哈希表 O(n) 空间，查询 O(1)，预处理最简单
"#
    }

    /// 字符串匹配：朴素 vs KMP vs Boyer-Moore vs Rabin-Karp
    pub fn string_matching_guide() -> &'static str {
        r#"# 字符串匹配算法决策

## 决策流程
```
模式串长度 m vs 文本长度 n?
├── m 很小 (<= 4) → 朴素算法 ✅（常数低）
└── m 较大 → 是否需要多模式匹配?
    ├── 是 → Aho-Corasick ✅
    └── 否 → 字母表大小?
        ├── 小字母表（如 DNA 'ACGT'）→ KMP ✅
        ├── 大字母表（如 Unicode 文本）→ Boyer-Moore / Horspool ✅
        └── 需要模糊/滚动哈希 → Rabin-Karp ✅
```

## 对比表
| 算法 | 预处理 | 匹配时间 | 空间 | 最佳场景 |
|------|--------|----------|------|----------|
| 朴素 (Naive) | O(1) | O(n × m) | O(1) | 极短模式串 |
| KMP | O(m) | O(n) | O(m) | 小字母表、需要确定性保证 |
| Boyer-Moore | O(m + σ) | O(n/m) ~ O(n×m) | O(σ) | 大字母表、长模式串 |
| Rabin-Karp | O(m) | O(n) 平均 | O(1) | 多模式、滚动哈希、 plagiarism 检测 |

## Rust 示例
```rust
// 1. 标准库（朴素 / 内部优化）
let text = "hello world";
assert!(text.contains("world"));

// 2. KMP 风格：利用标准库 Iterator
fn kmp_like_find(text: &str, pattern: &str) -> Option<usize> {
    text.find(pattern) // Rust 内部使用高效算法
}

// 3. Rabin-Karp（滚动哈希）
fn rabin_karp(text: &[u8], pattern: &[u8]) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    if m == 0 || m > n { return vec![]; }
    let base: u64 = 256;
    let modu: u64 = 1_000_000_007;
    let mut pattern_hash = 0u64;
    let mut window_hash = 0u64;
    let mut h = 1u64;
    for _ in 0..m - 1 {
        h = (h * base) % modu;
    }
    for i in 0..m {
        pattern_hash = (pattern_hash * base + pattern[i] as u64) % modu;
        window_hash = (window_hash * base + text[i] as u64) % modu;
    }
    let mut results = vec![];
    for i in 0..=n - m {
        if pattern_hash == window_hash && &text[i..i + m] == pattern {
            results.push(i);
        }
        if i < n - m {
            window_hash = (window_hash + modu
                - (text[i] as u64 * h) % modu) % modu;
            window_hash = (window_hash * base + text[i + m] as u64) % modu;
        }
    }
    results
}
```

## 关键提醒
- **实际工程**：Rust `str::find` / `str::contains` 已经高度优化，优先使用标准库
- **Boyer-Moore**：实际常用简化版 Horspool（仅需坏字符规则，代码更短）
- **Rabin-Karp**：哈希冲突需二次确认（逐字符比较）
"#
    }
}

// ============================================================
// 图算法决策树
// ============================================================

/// 图算法决策树
///
/// 根据图的类型（稀疏/稠密、有向/无向、权重特征）选择图算法。
pub struct GraphAlgorithmDecisionTree;

impl GraphAlgorithmDecisionTree {
    /// BFS vs DFS 决策
    pub fn bfs_vs_dfs() -> &'static str {
        r#"# BFS vs DFS 决策指南

## 决策流程
```
目标是什么?
├── 最短路径（无权图） → BFS ✅
├── 连通性 / 拓扑排序 / 回溯 → DFS ✅
├── 层次遍历 / 最近邻居 → BFS ✅
└── 寻找所有解 / 迷宫探测 → DFS ✅
```

## 对比表
| 特性 | BFS | DFS |
|------|-----|-----|
| 数据结构 | 队列 (Queue) | 栈 (Stack) 或递归 |
| 空间复杂度 | O(V)（最坏） | O(V)（递归栈） |
| 最短路径（无权） | ✅ 保证 | ❌ 不保证 |
| 是否适合深图 | ❌ 队列爆炸 | ⚠️ 栈溢出风险 |
| 是否适合宽图 | ✅ 更稳定 | ❌ 递归深度大 |
| 实现复杂度 | 迭代即可 | 递归简洁，迭代需显式栈 |

## Rust 示例
```rust
use std::collections::VecDeque;

fn bfs(graph: &[Vec<usize>], start: usize) -> Vec<usize> {
    let mut visited = vec![false; graph.len()];
    let mut queue = VecDeque::new();
    let mut order = vec![];
    queue.push_back(start);
    visited[start] = true;
    while let Some(node) = queue.pop_front() {
        order.push(node);
        for &neighbor in &graph[node] {
            if !visited[neighbor] {
                visited[neighbor] = true;
                queue.push_back(neighbor);
            }
        }
    }
    order
}

fn dfs(graph: &[Vec<usize>], start: usize) -> Vec<usize> {
    let mut visited = vec![false; graph.len()];
    let mut order = vec![];
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if visited[node] { continue; }
        visited[node] = true;
        order.push(node);
        for &neighbor in graph[node].iter().rev() {
            if !visited[neighbor] {
                stack.push(neighbor);
            }
        }
    }
    order
}
```

## 关键提醒
- **BFS**：求无权图单源最短路径的最优选择
- **DFS**：检测环、生成拓扑序、寻找强连通分量 (Tarjan/Kosaraju)
- **递归深度**：图很大时，DFS 递归可能导致栈溢出，改用显式栈
"#
    }

    /// 最短路径：Dijkstra vs Bellman-Ford vs Floyd-Warshall
    pub fn shortest_path_decision() -> &'static str {
        r#"# 最短路径算法决策

## 决策流程
```
图中是否有负权边?
├── 是 → 是否有负权环?
│   ├── 是 → 问题无解（或需特殊处理）
│   └── 否 → Bellman-Ford ✅
└── 否 → 需要全源最短路径?
    ├── 是 → Floyd-Warshall ✅
    └── 否 → Dijkstra ✅
```

## 对比表
| 算法 | 权重限制 | 时间 | 空间 | 用途 |
|------|----------|------|------|------|
| Dijkstra | 非负 | O((V+E) log V) | O(V) | 单源最短路径 |
| Bellman-Ford | 可负 | O(V × E) | O(V) | 单源、检测负环 |
| Floyd-Warshall | 可负 | O(V³) | O(V²) | 全源最短路径 |
| SPFA | 可负 | O(E) 平均 | O(V) | Bellman-Ford 优化版 |

## Rust 示例（Dijkstra）
```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

fn dijkstra(adj: &[Vec<(usize, u64)>], start: usize) -> Vec<u64> {
    let n = adj.len();
    let mut dist = vec![u64::MAX; n];
    let mut heap = BinaryHeap::new();
    dist[start] = 0;
    heap.push(Reverse((0u64, start)));
    while let Some(Reverse((d, u))) = heap.pop() {
        if d > dist[u] { continue; }
        for &(v, w) in &adj[u] {
            let nd = d + w;
            if nd < dist[v] {
                dist[v] = nd;
                heap.push(Reverse((nd, v)));
            }
        }
    }
    dist
}
```

## 关键提醒
- **Dijkstra**：要求权重非负；优先队列实现效率最高
- **Bellman-Ford**：V-1 轮松弛，第 V 轮还能松弛则说明有负环
- **Floyd-Warshall**：基于动态规划，适合密集图且需要任意两点距离
- **0-1 BFS**：边权仅为 0 或 1 时，用双端队列替代优先队列，O(V + E)
"#
    }

    /// 最小生成树：Prim vs Kruskal
    pub fn mst_decision() -> &'static str {
        r#"# MST: Prim vs Kruskal 决策

## 决策流程
```
图是稀疏还是稠密?
├── 稀疏 (E ≈ V) → Kruskal ✅（排序边 + Union-Find）
└── 稠密 (E ≈ V²) → Prim ✅（优先队列或邻接矩阵）
```

## 对比表
| 特性 | Prim | Kruskal |
|------|------|---------|
| 核心思想 | 扩展树顶点集合 | 按权重贪心选边 |
| 时间（二叉堆） | O(E log V) | O(E log E) |
| 时间（稠密图优化） | O(V²) | — |
| 数据结构 | 优先队列 + 访问标记 | Union-Find (并查集) |
| 适合图类型 | 稠密图 | 稀疏图 |
| 是否需全局排序边 | 否 | 是 |

## Rust 示例（Kruskal + Union-Find）
```rust
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self { parent: (0..n).collect(), rank: vec![0; n] }
    }
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    fn union(&mut self, x: usize, y: usize) -> bool {
        let (rx, ry) = (self.find(x), self.find(y));
        if rx == ry { return false; }
        if self.rank[rx] < self.rank[ry] {
            self.parent[rx] = ry;
        } else if self.rank[rx] > self.rank[ry] {
            self.parent[ry] = rx;
        } else {
            self.parent[ry] = rx;
            self.rank[rx] += 1;
        }
        true
    }
}

fn kruskal(n: usize, mut edges: Vec<(u64, usize, usize)>) -> u64 {
    edges.sort_unstable_by_key(|e| e.0);
    let mut uf = UnionFind::new(n);
    let mut total = 0u64;
    let mut count = 0;
    for (w, u, v) in edges {
        if uf.union(u, v) {
            total += w;
            count += 1;
            if count == n - 1 { break; }
        }
    }
    total
}
```

## 关键提醒
- **Prim**：类似 Dijkstra，从起点逐步扩展；稠密图可用数组找最小边，O(V²)
- **Kruskal**：边排序是主要开销；并查集路径压缩后几乎 O(1)
- **唯一 MST**：若边权互不相同，MST 唯一；否则可能有多个
"#
    }

    /// 拓扑排序：Kahn vs DFS-based
    pub fn topological_sort_decision() -> &'static str {
        r#"# 拓扑排序：Kahn 算法 vs DFS-based

## 决策流程
```
是否需要检测环并输出字典序最小拓扑序?
├── 是 → Kahn + 优先队列 ✅
└── 否 → 两种皆可
    ├── 需要显式入度信息 → Kahn ✅
    └── 代码最短 → DFS-based ✅
```

## 对比表
| 特性 | Kahn 算法 | DFS-based |
|------|-----------|-----------|
| 核心思想 | 不断移除入度为 0 的节点 | DFS 后序遍历的逆序 |
| 数据结构 | 队列 + 入度数组 | 递归栈 + 访问标记 |
| 环检测 | 自然（最终节点数 < V） | 需额外检测回边（灰节点） |
| 输出顺序 | 靠近源点的先输出 | 靠近汇点的先输出 |
| 空间 | O(V) | O(V) |

## Rust 示例（Kahn）
```rust
use std::collections::VecDeque;

fn kahn_topological_sort(graph: &[Vec<usize>], n: usize) -> Option<Vec<usize>> {
    let mut in_degree = vec![0; n];
    for neighbors in graph {
        for &v in neighbors {
            in_degree[v] += 1;
        }
    }
    let mut queue = VecDeque::new();
    for i in 0..n {
        if in_degree[i] == 0 {
            queue.push_back(i);
        }
    }
    let mut order = vec![];
    while let Some(u) = queue.pop_front() {
        order.push(u);
        for &v in &graph[u] {
            in_degree[v] -= 1;
            if in_degree[v] == 0 {
                queue.push_back(v);
            }
        }
    }
    if order.len() == n { Some(order) } else { None } // None = 有环
}
```

## 关键提醒
- **Kahn**：更易理解，天然支持按字典序输出（改用 `BinaryHeap`）
- **DFS-based**：代码更短，但需三种颜色标记（白/灰/黑）才能检测环
- **应用场景**：任务调度、编译依赖、课程选修计划
"#
    }
}

// ============================================================
// 动态规划决策树
// ============================================================

/// 动态规划决策树
///
/// 帮助判断问题是否适合 DP，以及选择实现方式。
pub struct DynamicProgrammingDecisionTree;

impl DynamicProgrammingDecisionTree {
    /// 判断 DP 是否适用
    pub fn when_dp_applies() -> &'static str {
        r#"# 动态规划适用性判断

## 两个必要条件

```
问题是否具有最优子结构?
└── 是 → 子问题是否重叠?
    └── 是 → DP 适用 ✅
    └── 否 → 分治法即可
└── 否 → 尝试贪心或暴力枚举
```

## 识别信号
| 信号 | 说明 |
|------|------|
| 求最值 | 最大/最小/最长/最短 |
| 求方案数 | 计数问题（组合） |
| 可行性判断 | 是否存在满足条件的解 |
| 状态转移 | 当前状态由有限个子状态推导 |

## 经典 DP 问题模式
| 模式 | 例子 |
|------|------|
| 线性 DP | 最长递增子序列 (LIS)、最大子数组和 |
| 背包 DP | 0-1 背包、完全背包、多重背包 |
| 区间 DP | 矩阵链乘、石子合并、回文分割 |
| 树形 DP | 树上最大独立集、树直径 |
| 状态压缩 DP | 旅行商问题 (TSP)、棋盘覆盖 |
| 数位 DP | 统计满足条件的数字个数 |

## Rust 示例（Fibonacci —— 最简 DP）
```rust
fn fibonacci(n: usize) -> u64 {
    if n <= 1 { return n as u64; }
    let mut dp = vec![0u64; n + 1];
    dp[1] = 1;
    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    dp[n]
}
```

## 关键提醒
- **最优子结构**：全局最优解包含子问题的最优解
- **重叠子问题**：递归时重复计算相同子问题
- **无后效性**：未来状态只与当前状态有关，与到达路径无关
"#
    }

    /// 自顶向下 (记忆化) vs 自底向上 (填表)
    pub fn top_down_vs_bottom_up() -> &'static str {
        r#"# Top-Down (记忆化) vs Bottom-Up (填表)

## 决策流程
```
是否需要访问所有子问题?
├── 否 → Top-Down 记忆化 ✅（只计算必要状态）
└── 是 → Bottom-Up 填表 ✅（无递归开销）
```

## 对比表
| 特性 | Top-Down (Memoization) | Bottom-Up (Tabulation) |
|------|------------------------|------------------------|
| 实现方式 | 递归 + HashMap/数组缓存 | 迭代填表 |
| 思维难度 | 更接近问题定义 | 需设计状态顺序 |
| 栈溢出风险 | 有（状态多/递归深） | 无 |
| 常数因子 | 略大（函数调用开销） | 更小 |
| 可剪枝 | ✅ 容易 | ❌ 较难 |
| 空间优化 | 需保留全部记忆化表 | 更容易滚动数组优化 |

## Rust 示例对比

### Top-Down（记忆化）
```rust
use std::collections::HashMap;

fn fib_memo(n: usize, memo: &mut HashMap<usize, u64>) -> u64 {
    if n <= 1 { return n as u64; }
    if let Some(&v) = memo.get(&n) { return v; }
    let v = fib_memo(n - 1, memo) + fib_memo(n - 2, memo);
    memo.insert(n, v);
    v
}
```

### Bottom-Up（填表）
```rust
fn fib_tab(n: usize) -> u64 {
    if n <= 1 { return n as u64; }
    let mut dp = vec![0u64; n + 1];
    dp[1] = 1;
    for i in 2..=n {
        dp[i] = dp[i - 1] + dp[i - 2];
    }
    dp[n]
}
```

## 关键提醒
- **Top-Down**：适合状态空间稀疏（很多子问题不会被访问到）
- **Bottom-Up**：适合递归深度大或需要极致性能的场景
- **Rust 递归**：默认栈大小有限（通常 ~8MB），大规模 DP 建议 Bottom-Up
"#
    }

    /// 空间优化技巧（滚动数组）
    pub fn space_optimization() -> &'static str {
        r#"# DP 空间优化：滚动数组

## 核心思想
若 `dp[i]` 只依赖前 `k` 个状态，则无需保存整个数组，只需保留最近 `k` 个值。

## 适用场景
| 依赖范围 | 原始空间 | 优化后空间 | 方法 |
|----------|----------|------------|------|
| 前一个状态 | O(n) | O(1) | 单个变量滚动 |
| 前两个状态 | O(n) | O(2) | 双变量交替 |
| 前 m 个状态 | O(n) | O(m) | 循环队列 / 取模索引 |
| 二维只依赖上一行 | O(n²) | O(n) | 两行交替 |

## Rust 示例

### 一维滚动（斐波那契）
```rust
fn fib_rolling(n: usize) -> u64 {
    if n <= 1 { return n as u64; }
    let (mut prev, mut curr) = (0u64, 1u64);
    for _ in 2..=n {
        let next = prev + curr;
        prev = curr;
        curr = next;
    }
    curr
}
```

### 二维滚动（0-1 背包）
```rust
fn knapsack_rolling(weights: &[usize], values: &[u64], cap: usize) -> u64 {
    let mut dp = vec![0u64; cap + 1];
    for (&w, &v) in weights.iter().zip(values) {
        for c in (w..=cap).rev() {
            dp[c] = dp[c].max(dp[c - w] + v);
        }
    }
    dp[cap]
}
```

## 关键提醒
- **倒序遍历**：0-1 背包必须倒序，避免物品被重复选取
- **正序遍历**：完全背包可正序（因为允许重复）
- **空间换时间**：滚动数组可能丢失回溯路径，若需输出方案，需额外记录
"#
    }

    /// 贪心 vs DP
    pub fn greedy_vs_dp() -> &'static str {
        r#"# 贪心 vs 动态规划

## 核心区别
| 特性 | 贪心 (Greedy) | 动态规划 (DP) |
|------|---------------|---------------|
| 决策方式 | 每一步做局部最优选择 | 枚举所有子问题，综合决策 |
| 正确性保证 | 需证明贪心选择性质 | 只要满足最优子结构+重叠子问题 |
| 时间复杂度 | 通常 O(n log n) 或 O(n) | 通常 O(n²) 或更高 |
| 适用问题 | 活动选择、哈夫曼编码、MST | 背包、最短路、LIS、编辑距离 |

## 决策流程
```
问题是否满足贪心选择性质?
（局部最优能推出全局最优）
├── 是 → 贪心 ✅（更快更简单）
└── 否 → DP ✅（更通用）
```

## 经典对比
| 问题 | 贪心 | DP |
|------|------|-----|
| 活动选择（最多场次） | ✅ 正确 | 也能做，但没必要 |
| 0-1 背包 | ❌ 错误 | ✅ 正确 |
| 分数背包 | ✅ 正确 | 也能做 |
| 最短路径（非负权） | Dijkstra（贪心） | ✅ 正确但慢 |
| 找零钱（硬币无限） | 某些币制下正确 | ✅ 通用正确 |

## Rust 示例（活动选择 —— 贪心正确）
```rust
fn activity_selection(mut activities: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    // 按结束时间排序
    activities.sort_by_key(|&(_, end)| end);
    let mut selected = vec![];
    let mut last_end = 0;
    for (start, end) in activities {
        if start >= last_end {
            selected.push((start, end));
            last_end = end;
        }
    }
    selected
}
```

## 关键提醒
- **证明贪心**：通常用“交换论证”或“拟阵”理论
- **保险策略**：不确定时先用 DP，确认贪心性质后再优化
- **经典反例**：0-1 背包用贪心按价值密度排序会得到次优解
"#
    }
}

// ============================================================================
// AlgorithmSkeletons — 可运行的算法骨架实现
// ============================================================================

/// 常见算法的简洁 Rust 实现骨架
///
/// 这些实现侧重于清晰度和教学价值，而非极致性能。
/// 每个算法都包含完整注释，说明关键不变量和边界条件。
pub struct AlgorithmSkeletons;

impl AlgorithmSkeletons {
    /// 二分查找（迭代版）
    ///
    /// # 前提条件
    /// - `arr` 必须是有序的（升序）
    ///
    /// # 复杂度
    /// - 时间: O(log n)
    /// - 空间: O(1)
    pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
        let mut left = 0usize;
        let mut right = arr.len();

        while left < right {
            let mid = left + (right - left) / 2;
            match arr[mid].cmp(&target) {
                std::cmp::Ordering::Equal => return Some(mid),
                std::cmp::Ordering::Less => left = mid + 1,
                std::cmp::Ordering::Greater => right = mid,
            }
        }
        None
    }

    /// 快速排序（原地）
    ///
    /// # 复杂度
    /// - 平均时间: O(n log n)
    /// - 最坏时间: O(n²)
    /// - 空间: O(log n) 递归栈
    pub fn quick_sort(arr: &mut [i32]) {
        if arr.len() <= 1 {
            return;
        }
        let pivot_idx = AlgorithmSkeletons::partition(arr);
        let (left, right) = arr.split_at_mut(pivot_idx);
        AlgorithmSkeletons::quick_sort(left);
        AlgorithmSkeletons::quick_sort(&mut right[1..]);
    }

    fn partition(arr: &mut [i32]) -> usize {
        let len = arr.len();
        let pivot = arr[len - 1];
        let mut i = 0;
        for j in 0..len - 1 {
            if arr[j] <= pivot {
                arr.swap(i, j);
                i += 1;
            }
        }
        arr.swap(i, len - 1);
        i
    }

    /// BFS 图遍历
    ///
    /// # 参数
    /// - `n`: 节点数（0..n-1）
    /// - `edges`: 无向边列表
    /// - `start`: 起始节点
    ///
    /// # 返回
    /// 遍历顺序
    pub fn bfs_traversal(n: usize, edges: &[(usize, usize)], start: usize) -> Vec<usize> {
        let mut adj = vec![vec![]; n];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }

        let mut visited = vec![false; n];
        let mut queue = std::collections::VecDeque::new();
        let mut order = Vec::new();

        visited[start] = true;
        queue.push_back(start);

        while let Some(node) = queue.pop_front() {
            order.push(node);
            for &neighbor in &adj[node] {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }
        order
    }
}

// ============================================================
// 并发算法决策树
// ============================================================

/// 并发算法决策树
///
/// 根据问题特征选择并行策略、同步原语和向量化方案。
pub struct ConcurrencyAlgorithmDecisionTree;

impl ConcurrencyAlgorithmDecisionTree {
    /// 顺序 vs 并行：何时并行化有帮助
    pub fn sequential_vs_parallel() -> &'static str {
        r#"# 顺序 vs 并行：何时并行化

## Amdahl 定律
```
加速比 = 1 / ((1 - P) + P / N)
其中 P = 可并行比例, N = 处理器数量
```
即使 N → ∞，最大加速比 = 1 / (1 - P)。

## 决策流程
```
数据量是否足够大?
├── 否 (< 1万) → 顺序 ✅（线程开销 > 收益）
└── 是 → 可并行比例 P 是否 > 80%?
    ├── 否 → 顺序 或 重新设计算法
    └── 是 → 并行 ✅
```

## 并行化收益评估表
| 场景 | 顺序 | 并行 | 建议 |
|------|------|------|------|
| 小数组排序 (< 10K) | O(n log n) | 更慢 | 顺序 |
| 大数组排序 (> 1M) | 慢 | O((n log n)/N) | `rayon::sort` |
| 简单映射（无依赖） | O(n) | O(n/N) | `par_iter` |
| 频繁同步/共享状态 | O(n) | 更慢 | 顺序或重新设计 |
| I/O 密集型 | 阻塞 | 重叠 I/O | 异步 (async) |

## Rust 示例（Rayon）
```rust
use rayon::prelude::*;

// 数据量小时：顺序
let small: Vec<i32> = (0..1000).map(|x| x * x).collect();

// 数据量大时：并行
let large: Vec<i32> = (0..10_000_000)
    .into_par_iter()
    .map(|x| x * x)
    .collect();
```

## 关键提醒
- **线程开销**：创建线程、任务分发、结果合并都有成本
- **缓存效应**：多核竞争同一缓存行（false sharing）会严重退化性能
- **内存带宽**：CPU 核心数超过内存带宽承载能力时，并行收益饱和
"#
    }

    /// 数据并行 vs 任务并行
    pub fn data_vs_task_parallelism() -> &'static str {
        r#"# 数据并行 vs 任务并行

## 定义对比
| 特性 | 数据并行 (Data Parallelism) | 任务并行 (Task Parallelism) |
|------|-----------------------------|-----------------------------|
| 拆分对象 | 同一数据集 | 不同任务/函数 |
| 同步需求 | 通常少（SIMD / MapReduce） | 通常多（流水线、依赖图） |
| 典型模式 | `par_iter`, SIMD, GPU | `spawn`, `join`, actor |
| 负载均衡 | 数据均匀则易均衡 | 任务粒度决定 |

## 决策流程
```
问题结构是什么?
├── 同一操作作用于大量数据 → 数据并行 ✅
│   └── 向量加法、图像处理、矩阵乘法
└── 多个独立/半独立任务 → 任务并行 ✅
    └──  Web 服务器、编译管道、游戏引擎
```

## Rust 示例对比

### 数据并行（Rayon）
```rust
use rayon::prelude::*;

fn vector_add(a: &[f64], b: &[f64], c: &mut [f64]) {
    c.par_iter_mut()
        .zip(a.par_iter().zip(b.par_iter()))
        .for_each(|(c, (a, b))| *c = a + b);
}
```

### 任务并行（Rayon join / spawn）
```rust
use rayon::{join, spawn};

fn task_parallel() {
    join(
        || compute_physics(),
        || render_frame(),
    );
}
```

## 关键提醒
- **数据并行**：最易实现，优先尝试 `rayon::prelude::*`
- **任务并行**：注意任务间依赖，避免死锁
- **混合模式**：大规模系统常同时采用两种并行（如游戏引擎）
"#
    }

    /// 锁 vs 无锁：决策因素
    pub fn lock_vs_lock_free() -> &'static str {
        r#"# 锁 (Lock-based) vs 无锁 (Lock-free)

## 决策流程
```
争用是否激烈?
├── 否（读多写少） → RwLock / Mutex ✅（简单）
└── 是（高并发写） → 考虑无锁结构
    ├── 只需计数/累加 → Atomic ✅
    ├── 队列/栈 → lock-free 数据结构 ✅
    └── 复杂状态机 → Mutex + 优化 或 Actor 模型
```

## 对比表
| 特性 | Mutex / RwLock | Lock-Free |
|------|----------------|-----------|
| 实现难度 | 低 | 高（需内存序理解） |
| 最坏延迟 | 可能阻塞（优先级反转） | 有界（系统级进度保证） |
| 吞吐量（低争用） | 优秀 | 略差（CAS 重试） |
| 吞吐量（高争用） | 差（上下文切换） | 更好 |
| 内存序要求 | 无（编译器处理） | 必须手动指定 |

## Rust 示例

### 锁方案
```rust
use std::sync::{Arc, Mutex};

let counter = Arc::new(Mutex::new(0));
let c = Arc::clone(&counter);
std::thread::spawn(move || {
    let mut num = c.lock().unwrap();
    *num += 1;
}).join().unwrap();
```

### 无锁方案
```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);
counter.fetch_add(1, Ordering::Relaxed);
```

## 关键提醒
- **Rust 优势**：`Mutex<T>` 将数据与锁绑定，编译时防止数据竞争
- **内存序**：无锁编程需理解 `Relaxed` / `Acquire` / `Release` / `SeqCst`
- **ABA 问题**：无锁数据结构需用 Tagging / Hazard Pointer 解决
- **建议**：除非性能测试证明锁是瓶颈，否则优先使用锁
"#
    }

    /// SIMD 适用性判断
    pub fn simd_applicability() -> &'static str {
        r#"# SIMD 适用性判断

## 前提条件
```
1. 数据布局是否连续?（SoA > AoS）
2. 操作是否统一?（同一指令处理所有元素）
3. 数据量是否足够?（向量寄存器宽度 × 数倍）
4. 算法是否有条件分支?（分支多 → SIMD 效率低）
```

## 决策流程
```
数据是否为连续数组?
├── 否（链表、树） → SIMD 不适用 ❌
└── 是 → 操作是否统一且无复杂分支?
    ├── 是 → SIMD ✅
    └── 否 → 考虑其他优化
```

## SIMD 友好 vs 不友好
| 友好 ✅ | 不友好 ❌ |
|---------|-----------|
| 数组逐元素加法 | 链表遍历 |
| 矩阵乘法 | 图的 BFS/DFS |
| 图像卷积 | 快速排序（分支多） |
| 字符串批量比较 | 哈希表查找 |
| 数组求和/点积 | 带复杂条件的循环 |

## Rust 示例（自动向量化提示）
```rust
// 编译器可自动 SIMD 向量化
fn array_add(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] + b[i]; // 无分支、连续内存 → LLVM auto-vectorize
    }
}

// 阻碍向量化的代码（条件分支）
fn conditional_add(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        if a[i] > 0.0 {
            c[i] = a[i] + b[i];
        } else {
            c[i] = a[i] - b[i];
        }
    }
}
// 优化：可用 select / blend 替代 if
```

## 关键提醒
- **SoA vs AoS**：Structure of Arrays 比 Array of Structures 更易 SIMD
- **对齐**：`#[repr(align(64))]` 可帮助缓存行对齐
- **稳定 Rust**：标准库暂无稳定 `std::simd`；可用 `packed_simd` 或编译器自动向量化
- **portable_simd**： nightly 特性，跨平台抽象
"#
    }
}

// ============================================================
// Tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---------------- SortingDecisionTree ----------------

    #[test]
    fn test_quicksort_guide() {
        let s = SortingDecisionTree::quicksort_guide();
        assert!(!s.is_empty());
        assert!(s.contains("QuickSort"));
        assert!(s.contains("O(n log n)"));
        assert!(s.contains("sort_unstable"));
    }

    #[test]
    fn test_mergesort_guide() {
        let s = SortingDecisionTree::mergesort_guide();
        assert!(!s.is_empty());
        assert!(s.contains("MergeSort"));
        assert!(s.contains("稳定"));
        assert!(s.contains("Timsort"));
    }

    #[test]
    fn test_heapsort_guide() {
        let s = SortingDecisionTree::heapsort_guide();
        assert!(!s.is_empty());
        assert!(s.contains("HeapSort"));
        assert!(s.contains("O(1)"));
        assert!(s.contains("BinaryHeap"));
    }

    #[test]
    fn test_counting_radix_sort_guide() {
        let s = SortingDecisionTree::counting_radix_sort_guide();
        assert!(!s.is_empty());
        assert!(s.contains("CountingSort") || s.contains("RadixSort"));
        assert!(s.contains("O(n + k)"));
    }

    #[test]
    fn test_insertion_sort_guide() {
        let s = SortingDecisionTree::insertion_sort_guide();
        assert!(!s.is_empty());
        assert!(s.contains("InsertionSort"));
        assert!(s.contains("O(n²)"));
    }

    #[test]
    fn test_rust_sort_decision() {
        let s = SortingDecisionTree::rust_sort_decision();
        assert!(!s.is_empty());
        assert!(s.contains("sort_unstable"));
        assert!(s.contains("sort"));
        assert!(s.contains("Timsort"));
    }

    // ---------------- SearchingDecisionTree ----------------

    #[test]
    fn test_linear_vs_binary_vs_interpolation() {
        let s = SearchingDecisionTree::linear_vs_binary_vs_interpolation();
        assert!(!s.is_empty());
        assert!(s.contains("二分搜索") || s.contains("Binary"));
        assert!(s.contains("线性搜索") || s.contains("Linear"));
        assert!(s.contains("插值搜索") || s.contains("Interpolation"));
    }

    #[test]
    fn test_hash_vs_tree_lookup() {
        let s = SearchingDecisionTree::hash_vs_tree_lookup();
        assert!(!s.is_empty());
        assert!(s.contains("HashMap"));
        assert!(s.contains("BTreeMap"));
    }

    #[test]
    fn test_preprocess_vs_linear_scan() {
        let s = SearchingDecisionTree::preprocess_vs_linear_scan();
        assert!(!s.is_empty());
        assert!(s.contains("排序") || s.contains("预处理"));
        assert!(s.contains("线性扫描") || s.contains("线性扫描"));
    }

    #[test]
    fn test_string_matching_guide() {
        let s = SearchingDecisionTree::string_matching_guide();
        assert!(!s.is_empty());
        assert!(s.contains("KMP") || s.contains("Boyer-Moore") || s.contains("Rabin-Karp"));
    }

    // ---------------- GraphAlgorithmDecisionTree ----------------

    #[test]
    fn test_bfs_vs_dfs() {
        let s = GraphAlgorithmDecisionTree::bfs_vs_dfs();
        assert!(!s.is_empty());
        assert!(s.contains("BFS"));
        assert!(s.contains("DFS"));
        assert!(s.contains("VecDeque"));
    }

    #[test]
    fn test_shortest_path_decision() {
        let s = GraphAlgorithmDecisionTree::shortest_path_decision();
        assert!(!s.is_empty());
        assert!(s.contains("Dijkstra"));
        assert!(s.contains("Bellman-Ford"));
        assert!(s.contains("Floyd-Warshall"));
    }

    #[test]
    fn test_mst_decision() {
        let s = GraphAlgorithmDecisionTree::mst_decision();
        assert!(!s.is_empty());
        assert!(s.contains("Prim") || s.contains("Kruskal"));
        assert!(s.contains("UnionFind") || s.contains("并查集"));
    }

    #[test]
    fn test_topological_sort_decision() {
        let s = GraphAlgorithmDecisionTree::topological_sort_decision();
        assert!(!s.is_empty());
        assert!(s.contains("Kahn") || s.contains("拓扑"));
    }

    // ---------------- DynamicProgrammingDecisionTree ----------------

    #[test]
    fn test_when_dp_applies() {
        let s = DynamicProgrammingDecisionTree::when_dp_applies();
        assert!(!s.is_empty());
        assert!(s.contains("最优子结构"));
        assert!(s.contains("重叠子问题"));
    }

    #[test]
    fn test_top_down_vs_bottom_up() {
        let s = DynamicProgrammingDecisionTree::top_down_vs_bottom_up();
        assert!(!s.is_empty());
        assert!(s.contains("Top-Down") || s.contains("记忆化"));
        assert!(s.contains("Bottom-Up") || s.contains("填表"));
    }

    #[test]
    fn test_space_optimization() {
        let s = DynamicProgrammingDecisionTree::space_optimization();
        assert!(!s.is_empty());
        assert!(s.contains("滚动数组") || s.contains("空间优化"));
    }

    #[test]
    fn test_greedy_vs_dp() {
        let s = DynamicProgrammingDecisionTree::greedy_vs_dp();
        assert!(!s.is_empty());
        assert!(s.contains("贪心") || s.contains("Greedy"));
        assert!(s.contains("动态规划") || s.contains("DP"));
    }

    // ---------------- ConcurrencyAlgorithmDecisionTree ----------------

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_sequential_vs_parallel() {
        let s = ConcurrencyAlgorithmDecisionTree::sequential_vs_parallel();
        assert!(!s.is_empty());
        assert!(s.contains("Amdahl") || s.contains("并行"));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_data_vs_task_parallelism() {
        let s = ConcurrencyAlgorithmDecisionTree::data_vs_task_parallelism();
        assert!(!s.is_empty());
        assert!(s.contains("数据并行") || s.contains("Data Parallelism"));
        assert!(s.contains("任务并行") || s.contains("Task Parallelism"));
    }

    #[test]
    fn test_lock_vs_lock_free() {
        let s = ConcurrencyAlgorithmDecisionTree::lock_vs_lock_free();
        assert!(!s.is_empty());
        assert!(s.contains("Mutex") || s.contains("Lock"));
        assert!(s.contains("Atomic") || s.contains("无锁"));
    }

    #[test]
    fn test_simd_applicability() {
        let s = ConcurrencyAlgorithmDecisionTree::simd_applicability();
        assert!(!s.is_empty());
        assert!(s.contains("SIMD"));
        assert!(s.contains("SoA") || s.contains("向量化"));
    }

    // ---------------- AlgorithmSkeletons ----------------

    #[test]
    fn test_binary_search_skeleton() {
        let arr = vec![1, 3, 5, 7, 9, 11];
        assert_eq!(AlgorithmSkeletons::binary_search(&arr, 7), Some(3));
        assert_eq!(AlgorithmSkeletons::binary_search(&arr, 4), None);
    }

    #[test]
    fn test_quick_sort_skeleton() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        AlgorithmSkeletons::quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }

    #[test]
    fn test_bfs_skeleton() {
        let edges = vec![(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)];
        let order = AlgorithmSkeletons::bfs_traversal(5, &edges, 0);
        assert_eq!(order[0], 0);
        assert!(order.contains(&4));
    }
}
