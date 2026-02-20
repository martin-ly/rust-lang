# 📦 Rust 集合与迭代器速查卡

> **快速参考** | [完整文档](../../../crates/c03_control_fn/docs/tier_03_references/02_迭代器参考.md) | [代码示例](../../../crates/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-01-27
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录

- [📦 Rust 集合与迭代器速查卡](#-rust-集合与迭代器速查卡)
  - [📋 目录](#-目录)
  - [📊 Vec（动态数组）](#-vec动态数组)
    - [创建](#创建)
    - [添加元素](#添加元素)
    - [访问元素](#访问元素)
    - [修改元素](#修改元素)
    - [删除元素](#删除元素)
    - [查询](#查询)
    - [切片操作](#切片操作)
  - [🗺️ HashMap（哈希映射）](#️-hashmap哈希映射)
    - [创建](#创建-1)
    - [插入和更新](#插入和更新)
    - [访问](#访问)
    - [删除](#删除)
    - [查询](#查询-1)
    - [迭代](#迭代)
  - [🔢 HashSet（哈希集合）](#-hashset哈希集合)
    - [创建](#创建-2)
    - [添加和删除](#添加和删除)
    - [查询](#查询-2)
    - [集合操作](#集合操作)
  - [📚 其他集合](#-其他集合)
    - [VecDeque（双端队列）](#vecdeque双端队列)
    - [切片 as\_array（Rust 1.93）](#切片-as_arrayrust-193)
    - [BTreeMap（有序映射）](#btreemap有序映射)
    - [BinaryHeap（优先队列）](#binaryheap优先队列)
  - [🔄 迭代器基础](#-迭代器基础)
    - [三种迭代方式](#三种迭代方式)
    - [手动迭代](#手动迭代)
  - [🔧 迭代器适配器](#-迭代器适配器)
    - [转换适配器](#转换适配器)
    - [选择适配器](#选择适配器)
    - [组合适配器](#组合适配器)
    - [其他适配器](#其他适配器)
  - [🍽️ 迭代器消费者](#️-迭代器消费者)
    - [收集](#收集)
    - [查找](#查找)
    - [聚合](#聚合)
    - [折叠](#折叠)
    - [其他消费者](#其他消费者)
  - [🎯 常用模式](#-常用模式)
    - [转换和过滤](#转换和过滤)
    - [链式操作](#链式操作)
    - [分组](#分组)
    - [去重](#去重)
    - [窗口操作](#窗口操作)
  - [💡 代码示例](#-代码示例)
    - [示例 1: 自定义迭代器](#示例-1-自定义迭代器)
    - [示例 2: 实现 IntoIterator](#示例-2-实现-intoiterator)
    - [示例 3: 迭代器适配器链](#示例-3-迭代器适配器链)
    - [示例 4: 使用 Entry API 高效更新 HashMap](#示例-4-使用-entry-api-高效更新-hashmap)
    - [示例 5: LRU Cache 实现](#示例-5-lru-cache-实现)
  - [🎯 使用场景](#-使用场景)
    - [场景: 数据处理管道](#场景-数据处理管道)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 迭代时修改集合](#反例-1-迭代时修改集合)
    - [反例 2: 索引越界](#反例-2-索引越界)
    - [反例 3: 在迭代时修改集合（安全版本）](#反例-3-在迭代时修改集合安全版本)
    - [反例 4: 错误使用 drain](#反例-4-错误使用-drain)
    - [反例 5: HashMap 遍历顺序依赖](#反例-5-hashmap-遍历顺序依赖)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与类型系统](#形式化理论与类型系统)
    - [相关速查卡](#相关速查卡)

---

## 📊 Vec（动态数组）

### 创建

```rust
// 空 Vec
let mut vec: Vec<i32> = Vec::new();
let mut vec = vec![];

// 带初始值
let vec = vec![1, 2, 3];
let vec = vec![0; 10]; // 10个0

// 预分配容量
let mut vec = Vec::with_capacity(10);
```

### 添加元素

```rust
let mut vec = vec![1, 2, 3];

// push - 末尾添加
vec.push(4);

// insert - 指定位置插入
vec.insert(1, 10);

// extend - 扩展
vec.extend([5, 6, 7]);
vec.extend_from_slice(&[8, 9]);
```

### 访问元素

```rust
let vec = vec![1, 2, 3, 4, 5];

// 索引访问（可能 panic）
let first = vec[0];

// get - 安全访问
let first = vec.get(0); // Option<&i32>
let first = vec.get(0).unwrap();

// first/last
let first = vec.first(); // Option<&i32>
let last = vec.last();   // Option<&i32>
```

### 修改元素

```rust
let mut vec = vec![1, 2, 3];

// 通过索引修改
vec[0] = 10;

// get_mut
if let Some(x) = vec.get_mut(0) {
    *x = 10;
}
```

### 删除元素

```rust
let mut vec = vec![1, 2, 3, 4, 5];

// pop - 移除最后一个
let last = vec.pop(); // Option<i32>

// remove - 移除指定位置
let item = vec.remove(1);

// swap_remove - 快速移除（不保持顺序）
let item = vec.swap_remove(0);

// clear - 清空
vec.clear();
```

### 查询

```rust
let vec = vec![1, 2, 3, 4, 5];

// len
let length = vec.len();

// is_empty
let empty = vec.is_empty();

// contains
let has = vec.contains(&3);

// capacity
let cap = vec.capacity();
```

### 切片操作

```rust
let vec = vec![1, 2, 3, 4, 5];

// 获取切片
let slice: &[i32] = &vec[1..3];
let slice = vec.as_slice();

// 分割
let (left, right) = vec.split_at(2);
```

---

## 🗺️ HashMap（哈希映射）

### 创建

```rust
use std::collections::HashMap;

// 空 HashMap
let mut map: HashMap<String, i32> = HashMap::new();

// 从迭代器创建
let map: HashMap<_, _> = vec![("a", 1), ("b", 2)]
    .into_iter()
    .collect();
```

### 插入和更新

```rust
let mut map = HashMap::new();

// insert - 插入或更新
map.insert("key".to_string(), 42);
map.insert("key".to_string(), 100); // 更新

// entry API
map.entry("key".to_string())
    .or_insert(0); // 不存在时插入

map.entry("key".to_string())
    .and_modify(|v| *v += 1) // 存在时修改
    .or_insert(1);            // 不存在时插入
```

### 访问

```rust
let mut map = HashMap::new();
map.insert("key".to_string(), 42);

// get - 返回 Option
let value = map.get("key"); // Option<&i32>

// get_mut - 可变引用
if let Some(v) = map.get_mut("key") {
    *v = 100;
}

// 直接索引（可能 panic）
let value = map["key"];
```

### 删除

```rust
let mut map = HashMap::new();
map.insert("key".to_string(), 42);

// remove - 删除并返回值
let value = map.remove("key"); // Option<i32>

// remove_entry - 删除并返回键值对
let entry = map.remove_entry("key"); // Option<(K, V)>

// clear - 清空
map.clear();
```

### 查询

```rust
let map: HashMap<_, _> = vec![("a", 1), ("b", 2)]
    .into_iter()
    .collect();

// contains_key
let has = map.contains_key("a");

// len
let length = map.len();

// is_empty
let empty = map.is_empty();
```

### 迭代

```rust
let map: HashMap<_, _> = vec![("a", 1), ("b", 2)]
    .into_iter()
    .collect();

// 迭代键值对
for (key, value) in &map {
    println!("{}: {}", key, value);
}

// 只迭代键
for key in map.keys() {
    println!("{}", key);
}

// 只迭代值
for value in map.values() {
    println!("{}", value);
}

// 可变迭代值
for value in map.values_mut() {
    *value += 1;
}
```

---

## 🔢 HashSet（哈希集合）

### 创建

```rust
use std::collections::HashSet;

// 空 HashSet
let mut set: HashSet<i32> = HashSet::new();

// 从迭代器创建
let set: HashSet<_> = vec![1, 2, 3].into_iter().collect();
```

### 添加和删除

```rust
let mut set = HashSet::new();

// insert - 添加元素
set.insert(1);
set.insert(2);

// remove - 删除元素
set.remove(&1);

// clear - 清空
set.clear();
```

### 查询

```rust
let set: HashSet<_> = vec![1, 2, 3].into_iter().collect();

// contains
let has = set.contains(&2);

// len
let length = set.len();

// is_empty
let empty = set.is_empty();
```

### 集合操作

```rust
let set1: HashSet<_> = vec![1, 2, 3].into_iter().collect();
let set2: HashSet<_> = vec![3, 4, 5].into_iter().collect();

// 并集
let union: HashSet<_> = set1.union(&set2).collect();

// 交集
let intersection: HashSet<_> = set1.intersection(&set2).collect();

// 差集
let difference: HashSet<_> = set1.difference(&set2).collect();

// 对称差集
let symmetric_diff: HashSet<_> = set1.symmetric_difference(&set2).collect();
```

---

## 📚 其他集合

### VecDeque（双端队列）

```rust
use std::collections::VecDeque;

let mut deque = VecDeque::new();

// 两端操作
deque.push_front(1);
deque.push_back(2);
let front = deque.pop_front();
let back = deque.pop_back();

// Rust 1.93: 条件弹出
let mut d = VecDeque::from([1, 2, 3, 4, 5]);
if let Some(v) = d.pop_front_if(|x| *x < 3) {
    // v 为满足条件的第一个元素
}
if let Some(v) = d.pop_back_if(|x| *x > 4) {
    // v 为满足条件的最后一个元素
}
```

### 切片 as_array（Rust 1.93）

```rust
let slice = &[1, 2, 3, 4];
let array: Option<&[i32; 4]> = slice.as_array();
```

### BTreeMap（有序映射）

```rust
use std::collections::BTreeMap;

let mut map = BTreeMap::new();
map.insert("b", 2);
map.insert("a", 1);
map.insert("c", 3);

// 自动排序
for (k, v) in &map {
    println!("{}: {}", k, v); // a: 1, b: 2, c: 3
}
```

**Rust 1.93 注意**：`BTreeMap::append` 行为变更——若源与目标有相同 key，**不再覆盖**目标中的值，保留目标原有条目。需覆盖时请使用 `insert` 或 `entry` API。

### BinaryHeap（优先队列）

```rust
use std::collections::BinaryHeap;

let mut heap = BinaryHeap::new();
heap.push(3);
heap.push(1);
heap.push(5);

// 最大堆
while let Some(max) = heap.pop() {
    println!("{}", max); // 5, 3, 1
}
```

---

## 🔄 迭代器基础

### 三种迭代方式

```rust
let vec = vec![1, 2, 3];

// iter - 不可变引用
for item in vec.iter() {
    println!("{}", item); // item: &i32
}

// iter_mut - 可变引用
let mut vec = vec![1, 2, 3];
for item in vec.iter_mut() {
    *item += 1; // item: &mut i32
}

// into_iter - 获取所有权
for item in vec.into_iter() {
    println!("{}", item); // item: i32
}
// vec 不再可用
```

### 手动迭代

```rust
let mut iter = vec![1, 2, 3].into_iter();

// next - 获取下一个元素
while let Some(item) = iter.next() {
    println!("{}", item);
}
```

---

## 🔧 迭代器适配器

### 转换适配器

```rust
let vec = vec![1, 2, 3, 4, 5];

// map - 转换元素
let doubled: Vec<_> = vec.iter().map(|x| x * 2).collect();

// filter - 过滤元素
let evens: Vec<_> = vec.iter().filter(|&&x| x % 2 == 0).collect();

// filter_map - 组合 filter 和 map
let result: Vec<_> = vec.iter()
    .filter_map(|&x| if x % 2 == 0 { Some(x * 2) } else { None })
    .collect();

// flat_map - 展平嵌套
let nested = vec![vec![1, 2], vec![3, 4]];
let flat: Vec<_> = nested.into_iter().flat_map(|v| v).collect();

// flatten - 展平一层
let flat: Vec<_> = nested.into_iter().flatten().collect();
```

### 选择适配器

```rust
let vec = vec![1, 2, 3, 4, 5];

// take - 取前 n 个
let first_three: Vec<_> = vec.iter().take(3).collect();

// skip - 跳过前 n 个
let rest: Vec<_> = vec.iter().skip(2).collect();

// take_while - 取满足条件的前缀
let result: Vec<_> = vec.iter().take_while(|&&x| x < 4).collect();

// skip_while - 跳过满足条件的前缀
let result: Vec<_> = vec.iter().skip_while(|&&x| x < 3).collect();

// step_by - 按步长迭代
let result: Vec<_> = vec.iter().step_by(2).collect();
```

### 组合适配器

```rust
let vec1 = vec![1, 2, 3];
let vec2 = vec![4, 5, 6];

// chain - 连接迭代器
let chained: Vec<_> = vec1.iter().chain(vec2.iter()).collect();

// zip - 组合两个迭代器
let zipped: Vec<_> = vec1.iter().zip(vec2.iter()).collect();

// enumerate - 添加索引
let enumerated: Vec<_> = vec1.iter().enumerate().collect();
// [(0, &1), (1, &2), (2, &3)]
```

### 其他适配器

```rust
let vec = vec![1, 2, 3];

// rev - 反转
let reversed: Vec<_> = vec.iter().rev().collect();

// cycle - 无限循环
let cycled: Vec<_> = vec.iter().cycle().take(10).collect();

// inspect - 观察元素（调试用）
let result: Vec<_> = vec.iter()
    .inspect(|x| println!("{}", x))
    .map(|x| x * 2)
    .collect();
```

---

## 🍽️ 迭代器消费者

### 收集

```rust
let vec = vec![1, 2, 3, 4, 5];

// collect - 收集到集合
let doubled: Vec<_> = vec.iter().map(|x| x * 2).collect();
let set: HashSet<_> = vec.iter().collect();
let map: HashMap<_, _> = vec.iter().enumerate().collect();

// partition - 分组
let (even, odd): (Vec<_>, Vec<_>) = vec.iter()
    .partition(|&&x| x % 2 == 0);
```

### 查找

```rust
let vec = vec![1, 2, 3, 4, 5];

// find - 查找第一个满足条件的
let found = vec.iter().find(|&&x| x > 3); // Option<&i32>

// position - 查找位置
let pos = vec.iter().position(|&x| x == 3); // Option<usize>

// any - 是否存在满足条件的
let has = vec.iter().any(|&x| x > 10); // bool

// all - 是否全部满足条件
let all = vec.iter().all(|&x| x > 0); // bool
```

### 聚合

```rust
let vec = vec![1, 2, 3, 4, 5];

// count - 计数
let count = vec.iter().count(); // usize

// sum - 求和
let sum: i32 = vec.iter().sum();

// product - 求积
let product: i32 = vec.iter().product();

// max/min - 最大值/最小值
let max = vec.iter().max(); // Option<&i32>
let min = vec.iter().min(); // Option<&i32>

// max_by/min_by - 自定义比较
let max = vec.iter().max_by(|a, b| a.cmp(b));
```

### 折叠

```rust
let vec = vec![1, 2, 3, 4, 5];

// fold - 折叠
let sum = vec.iter().fold(0, |acc, x| acc + x);

// reduce - 使用第一个元素作为初始值
let sum = vec.iter().reduce(|acc, x| acc + x); // Option<i32>

// try_fold - 可能失败的折叠
let result: Result<i32, _> = vec.iter()
    .try_fold(0, |acc, x| Ok(acc + x));
```

### 其他消费者

```rust
let vec = vec![1, 2, 3, 4, 5];

// for_each - 对每个元素执行操作
vec.iter().for_each(|x| println!("{}", x));

// nth - 获取第 n 个元素
let third = vec.iter().nth(2); // Option<&i32>

// last - 最后一个元素
let last = vec.iter().last(); // Option<&i32>

// collect - 收集到字符串
let joined: String = vec.iter().map(|x| x.to_string()).collect();
```

---

## 🎯 常用模式

### 转换和过滤

```rust
let vec = vec![1, 2, 3, 4, 5];

// 转换并过滤
let result: Vec<_> = vec.iter()
    .map(|x| x * 2)
    .filter(|&x| x > 5)
    .collect();
```

### 链式操作

```rust
let vec = vec![1, 2, 3, 4, 5];

// 复杂链式操作
let result: Vec<_> = vec.iter()
    .filter(|&&x| x % 2 == 0)
    .map(|x| x * x)
    .enumerate()
    .map(|(i, x)| (i, x))
    .collect();
```

### 分组

```rust
use std::collections::HashMap;

let vec = vec![1, 2, 3, 4, 5];

// 按奇偶分组
let grouped: HashMap<_, Vec<_>> = vec.iter()
    .map(|&x| (x % 2, x))
    .fold(HashMap::new(), |mut acc, (key, val)| {
        acc.entry(key).or_insert_with(Vec::new).push(val);
        acc
    });
```

### 去重

```rust
use std::collections::HashSet;

let vec = vec![1, 2, 2, 3, 3, 3];

// 使用 HashSet 去重
let unique: Vec<_> = vec.iter()
    .collect::<HashSet<_>>()
    .into_iter()
    .collect();

// 保持顺序去重
let mut seen = HashSet::new();
let unique: Vec<_> = vec.iter()
    .filter(|&x| seen.insert(*x))
    .collect();
```

### 窗口操作

```rust
let vec = vec![1, 2, 3, 4, 5];

// 滑动窗口（需要 itertools）
// use itertools::Itertools;
// let windows: Vec<_> = vec.iter().tuple_windows().collect();

// 原生滑动窗口实现
fn sliding_windows<T: Clone>(slice: &[T], size: usize) -> Vec<Vec<T>> {
    slice.windows(size).map(|w| w.to_vec()).collect()
}

let windows = sliding_windows(&vec, 3);
// [[1, 2, 3], [2, 3, 4], [3, 4, 5]]
```

---

## 💡 代码示例

### 示例 1: 自定义迭代器

```rust
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Fibonacci {
    fn new() -> Self {
        Self { curr: 0, next: 1 }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.curr;
        self.curr = self.next;
        self.next = current + self.next;
        Some(current)
    }
}

// 使用
let fib = Fibonacci::new();
let first_10: Vec<u64> = fib.take(10).collect();
// [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

### 示例 2: 实现 IntoIterator

```rust
struct BookCollection {
    books: Vec<String>,
}

impl IntoIterator for BookCollection {
    type Item = String;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.books.into_iter()
    }
}

impl<'a> IntoIterator for &'a BookCollection {
    type Item = &'a String;
    type IntoIter = std::slice::Iter<'a, String>;

    fn into_iter(self) -> Self::IntoIter {
        self.books.iter()
    }
}

// 使用
let collection = BookCollection {
    books: vec!["Rust Book".to_string(), "Programming".to_string()],
};

for book in &collection {
    println!("{}", book);
}
```

### 示例 3: 迭代器适配器链

```rust
let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

// 复杂数据处理管道
let result: Vec<i32> = data
    .iter()
    .filter(|&&x| x % 2 == 0)      // 筛选偶数
    .map(|&x| x * x)                // 平方
    .filter(|&x| x > 10)            // 筛选大于10的
    .take(3)                        // 取前3个
    .collect();

assert_eq!(result, vec![16, 36, 64]);
```

### 示例 4: 使用 Entry API 高效更新 HashMap

```rust
use std::collections::HashMap;

fn word_frequency(text: &str) -> HashMap<String, usize> {
    let mut freq = HashMap::new();

    for word in text.split_whitespace() {
        let word = word.to_lowercase();
        // Entry API 避免两次哈希计算
        *freq.entry(word).or_insert(0) += 1;
    }

    freq
}

// 使用
let text = "the quick brown fox jumps over the lazy dog";
let freq = word_frequency(text);
assert_eq!(freq.get("the"), Some(&2));
```

### 示例 5: LRU Cache 实现

```rust
use std::collections::VecDeque;
use std::collections::HashMap;

struct LRUCache<K, V> {
    capacity: usize,
    map: HashMap<K, V>,
    order: VecDeque<K>,
}

impl<K: Clone + Eq + std::hash::Hash, V> LRUCache<K, V> {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            order: VecDeque::with_capacity(capacity),
        }
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        if self.map.contains_key(key) {
            // 更新访问顺序
            self.order.retain(|k| k != key);
            self.order.push_back(key.clone());
            self.map.get(key)
        } else {
            None
        }
    }

    fn put(&mut self, key: K, value: V) {
        if self.map.contains_key(&key) {
            self.order.retain(|k| k != &key);
        } else if self.map.len() >= self.capacity {
            // 淘汰最久未使用的
            if let Some(lru_key) = self.order.pop_front() {
                self.map.remove(&lru_key);
            }
        }

        self.order.push_back(key.clone());
        self.map.insert(key, value);
    }
}

// 使用
let mut cache = LRUCache::new(2);
cache.put(1, "a");
cache.put(2, "b");
cache.put(3, "c");  // 淘汰 1
assert_eq!(cache.get(&1), None);
assert_eq!(cache.get(&2), Some(&"b"));
```

---

## 🎯 使用场景

### 场景: 数据处理管道

在实际项目中，迭代器常用于构建高效的数据处理管道。以下是一个日志分析管道的示例：

```rust
use std::collections::HashMap;

struct LogEntry {
    timestamp: u64,
    level: String,
    message: String,
}

fn analyze_logs(logs: Vec<LogEntry>) -> HashMap<String, usize> {
    logs.into_iter()
        .filter(|log| log.level == "ERROR" || log.level == "WARN")
        .map(|log| {
            // 提取错误类型
            log.message.split(':').next().unwrap_or("Unknown").to_string()
        })
        .fold(HashMap::new(), |mut acc, error_type| {
            *acc.entry(error_type).or_insert(0) += 1;
            acc
        })
}

// 更复杂的管道：时间窗口聚合
fn time_window_aggregation(
    logs: Vec<LogEntry>,
    window_secs: u64,
) -> Vec<(u64, usize)> {
    let mut result = vec![];
    let mut current_window = 0u64;
    let mut count = 0usize;

    for log in logs {
        let window = log.timestamp / window_secs;
        if window != current_window {
            if count > 0 {
                result.push((current_window, count));
            }
            current_window = window;
            count = 0;
        }
        count += 1;
    }

    if count > 0 {
        result.push((current_window, count));
    }

    result
}
```

---

## 🚫 反例速查

### 反例 1: 迭代时修改集合

**错误示例**:

```rust
let mut v = vec![1, 2, 3];
for x in &v {
    v.push(*x);  // ❌ 编译错误：借用了 v 时不能修改
}
```

**原因**: 迭代器持有集合的借用，同时修改会违反借用规则。

**修正**:

```rust
let v = vec![1, 2, 3];
let extra: Vec<_> = v.iter().cloned().collect();
// 或先收集再修改
```

---

### 反例 2: 索引越界

**错误示例**:

```rust
let v = vec![1, 2, 3];
let x = v[10];  // ❌ panic: index out of bounds
```

**原因**: 索引越界会 panic。

**修正**:

```rust
let x = v.get(10);  // ✅ 返回 Option
```

---

### 反例 3: 在迭代时修改集合（安全版本）

**错误示例**:

```rust
let mut v = vec![1, 2, 3];
for i in 0..v.len() {
    if v[i] % 2 == 0 {
        v.remove(i);  // ❌ 索引错位，可能 panic
    }
}
```

**原因**: 删除元素后，后续元素的索引会变化，可能导致越界或跳过元素。

**修正**: 使用 `retain`：

```rust
let mut v = vec![1, 2, 3, 4, 5];
v.retain(|&x| x % 2 != 0);  // ✅ 保留奇数
// v = [1, 3, 5]
```

---

### 反例 4: 错误使用 drain

**错误示例**:

```rust
let mut v = vec![1, 2, 3, 4, 5];
let drained: Vec<_> = v.drain(2..).collect();
// 以为 v 是 [1, 2]，但 drain 返回的迭代器必须被消耗
```

**原因**: `drain` 返回的迭代器必须被完全消耗，否则未移除的元素可能处于未定义状态。

**修正**:

```rust
let mut v = vec![1, 2, 3, 4, 5];
{
    let drained: Vec<_> = v.drain(2..).collect();
    // 处理 drained
} // drain 迭代器被 drop，v 变为 [1, 2]
```

---

### 反例 5: HashMap 遍历顺序依赖

**错误示例**:

```rust
let map: HashMap<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
let keys: Vec<_> = map.keys().collect();
// 假设 keys 总是 [1, 2]，但实际上顺序不确定
```

**原因**: `HashMap` 的遍历顺序是不确定的，依赖于哈希函数和插入顺序。

**修正**: 如果需要有序，使用 `BTreeMap`：

```rust
use std::collections::BTreeMap;
let map: BTreeMap<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
// 遍历时保证按键排序
```

---

## 📚 相关文档

- [迭代器参考](../../../crates/c03_control_fn/docs/tier_03_references/02_迭代器参考.md)
- [算法与数据结构文档](../../../crates/c08_algorithms/README.md)

## 🧩 相关示例代码

以下示例与集合/迭代器相关，位于 `crates/c08_algorithms/examples/`，可直接运行（例如：`cargo run -p c08_algorithms --example data_structures_demo`）。

- [数据结构与集合用法](../../../crates/c08_algorithms/examples/data_structures_demo.rs)
- [排序、搜索与图算法](../../../crates/c08_algorithms/examples/sorting_algorithms_demo.rs)、[searching_algorithms_demo.rs](../../../crates/c08_algorithms/examples/searching_algorithms_demo.rs)、[graph_algorithms_demo.rs](../../../crates/c08_algorithms/examples/graph_algorithms_demo.rs)
- [动态规划与贪心](../../../crates/c08_algorithms/examples/dynamic_programming_demo.rs)、[greedy_algorithms_demo.rs](../../../crates/c08_algorithms/examples/greedy_algorithms_demo.rs)

---

## 📚 相关资源

### 官方文档

- [Rust 集合文档](https://doc.rust-lang.org/std/collections/)
- [Iterator trait 文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
- [Rust Reference - Collections](https://doc.rust-lang.org/reference/items/collections.html)

### 项目内部文档

- [完整迭代器参考](../../../crates/c03_control_fn/docs/tier_03_references/02_迭代器参考.md)
- [集合研究笔记](../../research_notes/)

### 形式化理论与类型系统

- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 集合类型与类型理论
- [构造能力理论](../../research_notes/type_theory/construction_capability.md) — 迭代器的表达能力
- [泛型编程形式化](../../research_notes/type_theory/trait_system_formalization.md) — Iterator trait 形式化
- [所有权模型](../../research_notes/formal_methods/ownership_model.md) — 集合所有权转移形式化
- [变型理论](../../research_notes/type_theory/variance_theory.md) — 集合协变/逆变

### 相关速查卡

- [控制流与函数速查卡](./control_flow_functions_cheatsheet.md) - 循环与迭代器
- [类型系统速查卡](./type_system.md) - 集合类型
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与集合
- [字符串与格式化速查卡](./strings_formatting_cheatsheet.md) - 字符串集合

---

**最后更新**: 2026-01-27
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.0 更新完成**

🎯 **掌握集合与迭代器，高效处理数据！**
