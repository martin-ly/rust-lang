# 集合类型

> **标准库中的数据结构**
> **预计时间**: 4 小时
**权威来源**: [Rust Standard Library - Collections](https://doc.rust-lang.org/std/collections/)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 选择合适的集合类型
- [ ] 高效使用 Vec 和 HashMap
- [ ] 理解各集合的性能特征
- [ ] 掌握迭代器与集合的配合使用

## 📋 先决条件

- 理解泛型基础
- 了解所有权和借用

## 🧠 核心概念

### 1. 集合概览

| 集合 | 特点 | 使用场景 |
|------|------|----------|
| `Vec<T>` | 动态数组 | 顺序访问，变长列表 |
| `VecDeque<T>` | 双端队列 | 两端插入删除 |
| `LinkedList<T>` | 双向链表 | 频繁中间插入删除 |
| `HashMap<K,V>` | 哈希表 | 键值查找 |
| `BTreeMap<K,V>` | 有序树 | 有序遍历 |
| `HashSet<T>` | 哈希集合 | 去重，成员检查 |
| `BinaryHeap<T>` | 二叉堆 | 优先级队列 |

### 2. Vec - 动态数组

```rust
// 创建
let mut v = Vec::new();
let v2 = vec![1, 2, 3];  // 宏创建

// 添加元素
v.push(1);
v.push(2);

// 访问
let first = &v[0];       // 索引访问（可能 panic）
let first = v.get(0);    // 安全访问（返回 Option）

// 迭代
for x in &v {
    println!("{}", x);
}

// 容量管理
v.capacity();  // 当前容量
v.reserve(10); // 预分配
v.shrink_to_fit(); // 释放多余容量
```

#### 性能特征

| 操作 | 时间复杂度 | 说明 |
|------|-----------|------|
| push | 均摊 O(1) | 偶尔需要扩容 |
| pop | O(1) | 尾部移除 |
| insert/remove | O(n) | 需要移动元素 |
| index | O(1) | 随机访问 |

### 3. HashMap - 哈希表

```rust
use std::collections::HashMap;

// 创建
let mut scores = HashMap::new();

// 插入
scores.insert("Alice", 95);
scores.insert("Bob", 87);

// 访问
let alice_score = scores.get("Alice");  // Some(&95)

// 安全获取或默认值
let charlie_score = scores.get("Charlie").copied().unwrap_or(0);

// 更新
scores.entry("Alice").and_modify(|e| *e += 5);  // Alice 现在 100

// 不存在则插入
scores.entry("Charlie").or_insert(70);

// 迭代
for (name, score) in &scores {
    println!("{}: {}", name, score);
}
```

#### 自定义键类型

```rust
use std::collections::HashMap;
use std::hash::Hash;

#[derive(Eq, PartialEq, Hash)]
struct Point {
    x: i32,
    y: i32,
}

let mut map = HashMap::new();
map.insert(Point { x: 0, y: 0 }, "origin");
```

### 4. HashSet - 集合

```rust
use std::collections::HashSet;

let mut set = HashSet::new();
set.insert(1);
set.insert(2);
set.insert(2);  // 重复，被忽略

// 检查成员
if set.contains(&1) {
    println!("Contains 1");
}

// 集合操作
let a: HashSet<i32> = [1, 2, 3].iter().cloned().collect();
let b: HashSet<i32> = [2, 3, 4].iter().cloned().collect();

let intersection: HashSet<_> = a.intersection(&b).collect();
let union: HashSet<_> = a.union(&b).collect();
```

### 5. VecDeque - 双端队列

```rust
use std::collections::VecDeque;

let mut deque = VecDeque::new();

// 两端操作都高效 O(1)
deque.push_back(1);
deque.push_back(2);
deque.push_front(0);

// 弹出
let front = deque.pop_front();  // Some(0)
let back = deque.pop_back();    // Some(2)
```

### 6. BinaryHeap - 优先队列

```rust
use std::collections::BinaryHeap;

let mut heap = BinaryHeap::new();
heap.push(3);
heap.push(1);
heap.push(5);

// 弹出最大值
while let Some(max) = heap.pop() {
    println!("{}", max);  // 5, 3, 1
}

// 自定义优先级
#[derive(Eq, PartialEq)]
struct Task {
    priority: u32,
    name: String,
}

impl Ord for Task {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.priority.cmp(&other.priority).reverse()  // 最小堆
    }
}

impl PartialOrd for Task {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
```

## 💻 综合示例

### 词频统计

```rust
use std::collections::HashMap;

fn word_frequency(text: &str) -> HashMap<String, u32> {
    let mut freq = HashMap::new();

    for word in text.split_whitespace() {
        let word = word.to_lowercase()
            .trim_matches(|c: char| !c.is_alphabetic())
            .to_string();

        if !word.is_empty() {
            *freq.entry(word).or_insert(0) += 1;
        }
    }

    freq
}

fn main() {
    let text = "hello world hello rust hello";
    let freq = word_frequency(text);

    // 按频率排序
    let mut pairs: Vec<_> = freq.into_iter().collect();
    pairs.sort_by(|a, b| b.1.cmp(&a.1));

    for (word, count) in pairs {
        println!("{}: {}", word, count);
    }
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 修复 |
|------|------|------|
| HashMap 键未实现 Hash | 类型约束 | #[derive(Hash)] |
| Vec 扩容频繁 | 初始容量不足 | with_capacity |
| 迭代时修改集合 | 借用规则 | 先收集再修改 |

## 🎮 练习

### 练习 1: LRU 缓存

使用 HashMap 和 VecDeque 实现一个简单的 LRU 缓存。

### 练习 2: 图遍历

使用 HashMap 表示图，实现 BFS 遍历。

<details>
<summary>参考答案</summary>

```rust
use std::collections::{HashMap, HashSet, VecDeque};

fn bfs(graph: &HashMap<String, Vec<String>>, start: &str) -> Vec<String> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    let mut result = Vec::new();

    queue.push_back(start.to_string());
    visited.insert(start.to_string());

    while let Some(node) = queue.pop_front() {
        result.push(node.clone());

        if let Some(neighbors) = graph.get(&node) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    visited.insert(neighbor.clone());
                    queue.push_back(neighbor.clone());
                }
            }
        }
    }

    result
}
```

</details>

## ✅ 自我检测

1. Vec 和 LinkedList 的主要区别是什么？
2. HashMap 的 entry API 有什么优势？
3. 什么时候应该使用 BTreeMap 而不是 HashMap？

## 📖 延伸阅读

- [std::collections](https://doc.rust-lang.org/std/collections/)
- [Algorithm Complexity](https://doc.rust-lang.org/std/collections/index.html#complexity)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
