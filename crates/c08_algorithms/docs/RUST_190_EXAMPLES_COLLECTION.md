# 💻 Rust 1.90 算法与数据结构 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码总量**: ~850行可运行代码

---

## 📋 目录

- [💻 Rust 1.90 算法与数据结构 - 实战示例集](#-rust-190-算法与数据结构---实战示例集)
  - [📋 目录](#-目录)
  - [📊 数据结构实现](#-数据结构实现)
    - [示例1: 自定义栈与队列](#示例1-自定义栈与队列)
    - [示例2: LRU缓存 (Rust 1.90特性)](#示例2-lru缓存-rust-190特性)
    - [示例3: Trie前缀树](#示例3-trie前缀树)
  - [🔍 经典算法](#-经典算法)
    - [示例4: 排序算法集合](#示例4-排序算法集合)
    - [示例5: 二分搜索变体](#示例5-二分搜索变体)
    - [示例6: 图算法 (DFS/BFS/Dijkstra)](#示例6-图算法-dfsbfsdijkstra)
  - [⚡ 并发算法 (Rayon)](#-并发算法-rayon)
    - [示例7: 并行排序与搜索](#示例7-并行排序与搜索)
    - [示例8: 并发Map-Reduce](#示例8-并发map-reduce)
  - [🏗️ 综合项目](#️-综合项目)
    - [项目1: 表达式求值器](#项目1-表达式求值器)
    - [项目2: 任务调度系统](#项目2-任务调度系统)

---

## 📊 数据结构实现

### 示例1: 自定义栈与队列

```rust
/// 基于Vec的栈实现
#[derive(Debug)]
struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Self { items: Vec::new() }
    }
    
    fn push(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }
    
    fn peek(&self) -> Option<&T> {
        self.items.last()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    
    fn len(&self) -> usize {
        self.items.len()
    }
}

/// 基于VecDeque的队列实现
use std::collections::VecDeque;

#[derive(Debug)]
struct Queue<T> {
    items: VecDeque<T>,
}

impl<T> Queue<T> {
    fn new() -> Self {
        Self { items: VecDeque::new() }
    }
    
    fn enqueue(&mut self, item: T) {
        self.items.push_back(item);
    }
    
    fn dequeue(&mut self) -> Option<T> {
        self.items.pop_front()
    }
    
    fn peek(&self) -> Option<&T> {
        self.items.front()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    
    fn len(&self) -> usize {
        self.items.len()
    }
}

/// 应用: 括号匹配
fn is_balanced_parentheses(s: &str) -> bool {
    let mut stack = Stack::new();
    
    for ch in s.chars() {
        match ch {
            '(' | '[' | '{' => stack.push(ch),
            ')' | ']' | '}' => {
                match (stack.pop(), ch) {
                    (Some('('), ')') | 
                    (Some('['), ']') | 
                    (Some('{'), '}') => continue,
                    _ => return false,
                }
            }
            _ => {}
        }
    }
    
    stack.is_empty()
}

fn main() {
    // 栈测试
    let mut stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    println!("Stack: {:?}", stack);
    println!("Pop: {:?}", stack.pop());
    
    // 队列测试
    let mut queue = Queue::new();
    queue.enqueue("first");
    queue.enqueue("second");
    queue.enqueue("third");
    println!("\nQueue: {:?}", queue);
    println!("Dequeue: {:?}", queue.dequeue());
    
    // 括号匹配测试
    let test_cases = vec![
        "()",
        "()[]{}",
        "(]",
        "([)]",
        "{[]}",
    ];
    
    println!("\n=== Parentheses Matching ===");
    for case in test_cases {
        println!("{:?} -> {}", case, is_balanced_parentheses(case));
    }
}
```

---

### 示例2: LRU缓存 (Rust 1.90特性)

```rust
use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

/// 双向链表节点
struct Node<K, V> {
    key: K,
    value: V,
    prev: Option<Rc<RefCell<Node<K, V>>>>,
    next: Option<Rc<RefCell<Node<K, V>>>>,
}

/// LRU缓存实现
struct LRUCache<K, V> 
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    capacity: usize,
    map: HashMap<K, Rc<RefCell<Node<K, V>>>>,
    head: Option<Rc<RefCell<Node<K, V>>>>,
    tail: Option<Rc<RefCell<Node<K, V>>>>,
}

impl<K, V> LRUCache<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::new(),
            head: None,
            tail: None,
        }
    }
    
    fn get(&mut self, key: &K) -> Option<V> {
        if let Some(node) = self.map.get(key) {
            let value = node.borrow().value.clone();
            // 移到头部
            self.move_to_front(Rc::clone(node));
            Some(value)
        } else {
            None
        }
    }
    
    fn put(&mut self, key: K, value: V) {
        if let Some(node) = self.map.get(&key) {
            // 更新值
            node.borrow_mut().value = value;
            self.move_to_front(Rc::clone(node));
        } else {
            // 新节点
            let node = Rc::new(RefCell::new(Node {
                key: key.clone(),
                value,
                prev: None,
                next: None,
            }));
            
            self.add_to_front(Rc::clone(&node));
            self.map.insert(key, node);
            
            // 检查容量
            if self.map.len() > self.capacity {
                if let Some(tail) = self.tail.take() {
                    let key = tail.borrow().key.clone();
                    self.remove_node(Rc::clone(&tail));
                    self.map.remove(&key);
                }
            }
        }
    }
    
    fn move_to_front(&mut self, node: Rc<RefCell<Node<K, V>>>) {
        self.remove_node(Rc::clone(&node));
        self.add_to_front(node);
    }
    
    fn add_to_front(&mut self, node: Rc<RefCell<Node<K, V>>>) {
        if let Some(head) = self.head.take() {
            node.borrow_mut().next = Some(Rc::clone(&head));
            head.borrow_mut().prev = Some(Rc::clone(&node));
            self.head = Some(node);
        } else {
            // 第一个节点
            self.head = Some(Rc::clone(&node));
            self.tail = Some(node);
        }
    }
    
    fn remove_node(&mut self, node: Rc<RefCell<Node<K, V>>>) {
        let prev = node.borrow().prev.clone();
        let next = node.borrow().next.clone();
        
        match (prev, next) {
            (Some(p), Some(n)) => {
                p.borrow_mut().next = Some(Rc::clone(&n));
                n.borrow_mut().prev = Some(p);
            }
            (None, Some(n)) => {
                n.borrow_mut().prev = None;
                self.head = Some(n);
            }
            (Some(p), None) => {
                p.borrow_mut().next = None;
                self.tail = Some(p);
            }
            (None, None) => {
                self.head = None;
                self.tail = None;
            }
        }
        
        node.borrow_mut().prev = None;
        node.borrow_mut().next = None;
    }
}

fn main() {
    let mut cache = LRUCache::new(2);
    
    cache.put(1, "one");
    cache.put(2, "two");
    println!("Get 1: {:?}", cache.get(&1)); // Some("one")
    
    cache.put(3, "three"); // 驱逐key 2
    println!("Get 2: {:?}", cache.get(&2)); // None
    println!("Get 3: {:?}", cache.get(&3)); // Some("three")
}
```

---

### 示例3: Trie前缀树

```rust
use std::collections::HashMap;

/// Trie节点
#[derive(Default)]
struct TrieNode {
    children: HashMap<char, TrieNode>,
    is_end: bool,
}

/// Trie树
#[derive(Default)]
struct Trie {
    root: TrieNode,
}

impl Trie {
    fn new() -> Self {
        Self::default()
    }
    
    /// 插入单词
    fn insert(&mut self, word: &str) {
        let mut node = &mut self.root;
        for ch in word.chars() {
            node = node.children.entry(ch).or_default();
        }
        node.is_end = true;
    }
    
    /// 搜索单词
    fn search(&self, word: &str) -> bool {
        self.find_node(word)
            .map(|node| node.is_end)
            .unwrap_or(false)
    }
    
    /// 前缀匹配
    fn starts_with(&self, prefix: &str) -> bool {
        self.find_node(prefix).is_some()
    }
    
    /// 查找节点
    fn find_node(&self, prefix: &str) -> Option<&TrieNode> {
        let mut node = &self.root;
        for ch in prefix.chars() {
            node = node.children.get(&ch)?;
        }
        Some(node)
    }
    
    /// 自动补全
    fn autocomplete(&self, prefix: &str) -> Vec<String> {
        let mut results = Vec::new();
        if let Some(node) = self.find_node(prefix) {
            self.collect_words(node, prefix.to_string(), &mut results);
        }
        results
    }
    
    fn collect_words(&self, node: &TrieNode, current: String, results: &mut Vec<String>) {
        if node.is_end {
            results.push(current.clone());
        }
        
        for (&ch, child) in &node.children {
            let mut new_word = current.clone();
            new_word.push(ch);
            self.collect_words(child, new_word, results);
        }
    }
}

fn main() {
    let mut trie = Trie::new();
    
    // 插入单词
    let words = vec!["apple", "app", "application", "apply", "banana"];
    for word in words {
        trie.insert(word);
    }
    
    // 搜索
    println!("Search 'app': {}", trie.search("app"));
    println!("Search 'appl': {}", trie.search("appl"));
    
    // 前缀匹配
    println!("Starts with 'app': {}", trie.starts_with("app"));
    
    // 自动补全
    println!("Autocomplete 'app': {:?}", trie.autocomplete("app"));
}
```

---

## 🔍 经典算法

### 示例4: 排序算法集合

```rust
/// 快速排序
fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quick_sort(&mut arr[..pivot_index]);
    quick_sort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len / 2;
    arr.swap(pivot_index, len - 1);
    
    let mut i = 0;
    for j in 0..len - 1 {
        if arr[j] < arr[len - 1] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, len - 1);
    i
}

/// 归并排序
fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);
    
    let mut temp = arr.to_vec();
    merge(&arr[..mid], &arr[mid..], &mut temp);
    arr.copy_from_slice(&temp);
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T], result: &mut [T]) {
    let (mut i, mut j, mut k) = (0, 0, 0);
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result[k] = left[i].clone();
            i += 1;
        } else {
            result[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }
    
    result[k..k + left.len() - i].clone_from_slice(&left[i..]);
    result[k + left.len() - i..].clone_from_slice(&right[j..]);
}

/// 堆排序
fn heap_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    
    // 构建最大堆
    for i in (0..len / 2).rev() {
        heapify(arr, len, i);
    }
    
    // 排序
    for i in (1..len).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

fn heapify<T: Ord>(arr: &mut [T], n: usize, i: usize) {
    let mut largest = i;
    let left = 2 * i + 1;
    let right = 2 * i + 2;
    
    if left < n && arr[left] > arr[largest] {
        largest = left;
    }
    
    if right < n && arr[right] > arr[largest] {
        largest = right;
    }
    
    if largest != i {
        arr.swap(i, largest);
        heapify(arr, n, largest);
    }
}

fn main() {
    let mut data1 = vec![64, 34, 25, 12, 22, 11, 90];
    quick_sort(&mut data1);
    println!("QuickSort: {:?}", data1);
    
    let mut data2 = vec![64, 34, 25, 12, 22, 11, 90];
    merge_sort(&mut data2);
    println!("MergeSort: {:?}", data2);
    
    let mut data3 = vec![64, 34, 25, 12, 22, 11, 90];
    heap_sort(&mut data3);
    println!("HeapSort: {:?}", data3);
}
```

---

### 示例5: 二分搜索变体

```rust
/// 标准二分搜索
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

/// 查找第一个等于target的位置
fn binary_search_first<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();
    let mut result = None;
    
    while left < right {
        let mid = left + (right - left) / 2;
        
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => {
                result = Some(mid);
                right = mid; // 继续向左搜索
            }
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    
    result
}

/// 查找最后一个等于target的位置
fn binary_search_last<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();
    let mut result = None;
    
    while left < right {
        let mid = left + (right - left) / 2;
        
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => {
                result = Some(mid);
                left = mid + 1; // 继续向右搜索
            }
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    
    result
}

fn main() {
    let arr = vec![1, 2, 2, 2, 3, 4, 5];
    
    println!("Binary search for 2: {:?}", binary_search(&arr, &2));
    println!("First 2: {:?}", binary_search_first(&arr, &2));
    println!("Last 2: {:?}", binary_search_last(&arr, &2));
}
```

---

### 示例6: 图算法 (DFS/BFS/Dijkstra)

```rust
use std::collections::{HashMap, HashSet, VecDeque, BinaryHeap};
use std::cmp::Ordering;

type Graph = HashMap<usize, Vec<usize>>;
type WeightedGraph = HashMap<usize, Vec<(usize, usize)>>;

/// DFS递归实现
fn dfs_recursive(graph: &Graph, start: usize, visited: &mut HashSet<usize>) {
    visited.insert(start);
    println!("Visit: {}", start);
    
    if let Some(neighbors) = graph.get(&start) {
        for &neighbor in neighbors {
            if !visited.contains(&neighbor) {
                dfs_recursive(graph, neighbor, visited);
            }
        }
    }
}

/// BFS实现
fn bfs(graph: &Graph, start: usize) {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    
    queue.push_back(start);
    visited.insert(start);
    
    while let Some(node) = queue.pop_front() {
        println!("Visit: {}", node);
        
        if let Some(neighbors) = graph.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    queue.push_back(neighbor);
                }
            }
        }
    }
}

/// Dijkstra最短路径
#[derive(Eq, PartialEq)]
struct State {
    cost: usize,
    node: usize,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost) // 最小堆
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn dijkstra(graph: &WeightedGraph, start: usize, end: usize) -> Option<usize> {
    let mut dist = HashMap::new();
    let mut heap = BinaryHeap::new();
    
    dist.insert(start, 0);
    heap.push(State { cost: 0, node: start });
    
    while let Some(State { cost, node }) = heap.pop() {
        if node == end {
            return Some(cost);
        }
        
        if cost > *dist.get(&node).unwrap_or(&usize::MAX) {
            continue;
        }
        
        if let Some(neighbors) = graph.get(&node) {
            for &(next_node, weight) in neighbors {
                let next_cost = cost + weight;
                
                if next_cost < *dist.get(&next_node).unwrap_or(&usize::MAX) {
                    dist.insert(next_node, next_cost);
                    heap.push(State { cost: next_cost, node: next_node });
                }
            }
        }
    }
    
    None
}

fn main() {
    // 无权图
    let mut graph = Graph::new();
    graph.insert(0, vec![1, 2]);
    graph.insert(1, vec![0, 3]);
    graph.insert(2, vec![0, 3]);
    graph.insert(3, vec![1, 2]);
    
    println!("=== DFS ===");
    let mut visited = HashSet::new();
    dfs_recursive(&graph, 0, &mut visited);
    
    println!("\n=== BFS ===");
    bfs(&graph, 0);
    
    // 加权图
    let mut weighted_graph = WeightedGraph::new();
    weighted_graph.insert(0, vec![(1, 4), (2, 1)]);
    weighted_graph.insert(1, vec![(3, 1)]);
    weighted_graph.insert(2, vec![(1, 2), (3, 5)]);
    weighted_graph.insert(3, vec![]);
    
    println!("\n=== Dijkstra ===");
    if let Some(dist) = dijkstra(&weighted_graph, 0, 3) {
        println!("Shortest path from 0 to 3: {}", dist);
    }
}
```

---

## ⚡ 并发算法 (Rayon)

### 示例7: 并行排序与搜索

```rust
use rayon::prelude::*;

/// 并行快速排序
fn parallel_quick_sort<T: Ord + Send>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    let (left, right) = arr.split_at_mut(pivot_index);
    
    rayon::join(
        || parallel_quick_sort(left),
        || parallel_quick_sort(&mut right[1..])
    );
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len / 2;
    arr.swap(pivot_index, len - 1);
    
    let mut i = 0;
    for j in 0..len - 1 {
        if arr[j] < arr[len - 1] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, len - 1);
    i
}

/// 并行搜索
fn parallel_search<T: PartialEq + Sync>(arr: &[T], target: &T) -> Option<usize> {
    arr.par_iter()
        .position_any(|x| x == target)
}

fn main() {
    let mut data: Vec<i32> = (0..1000000).rev().collect();
    
    // 并行排序
    parallel_quick_sort(&mut data);
    println!("Sorted first 10: {:?}", &data[..10]);
    
    // 并行搜索
    if let Some(index) = parallel_search(&data, &500000) {
        println!("Found 500000 at index: {}", index);
    }
}
```

---

### 示例8: 并发Map-Reduce

```rust
use rayon::prelude::*;

/// 并行Map-Reduce: 词频统计
fn word_count(text: &str) -> std::collections::HashMap<String, usize> {
    text.par_split_whitespace()
        .map(|word| (word.to_lowercase(), 1))
        .fold(
            || std::collections::HashMap::new(),
            |mut map, (word, count)| {
                *map.entry(word).or_insert(0) += count;
                map
            }
        )
        .reduce(
            || std::collections::HashMap::new(),
            |mut map1, map2| {
                for (word, count) in map2 {
                    *map1.entry(word).or_insert(0) += count;
                }
                map1
            }
        )
}

fn main() {
    let text = "the quick brown fox jumps over the lazy dog the fox";
    let counts = word_count(text);
    
    println!("Word counts:");
    for (word, count) in counts {
        println!("{}: {}", word, count);
    }
}
```

---

## 🏗️ 综合项目

### 项目1: 表达式求值器

```rust
use std::collections::HashMap;

#[derive(Debug)]
enum Token {
    Number(f64),
    Operator(char),
    LeftParen,
    RightParen,
}

/// 词法分析
fn tokenize(expr: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut num_buffer = String::new();
    
    for ch in expr.chars() {
        match ch {
            '0'..='9' | '.' => num_buffer.push(ch),
            '+' | '-' | '*' | '/' => {
                if !num_buffer.is_empty() {
                    tokens.push(Token::Number(num_buffer.parse().unwrap()));
                    num_buffer.clear();
                }
                tokens.push(Token::Operator(ch));
            }
            '(' => {
                tokens.push(Token::LeftParen);
            }
            ')' => {
                if !num_buffer.is_empty() {
                    tokens.push(Token::Number(num_buffer.parse().unwrap()));
                    num_buffer.clear();
                }
                tokens.push(Token::RightParen);
            }
            ' ' => {
                if !num_buffer.is_empty() {
                    tokens.push(Token::Number(num_buffer.parse().unwrap()));
                    num_buffer.clear();
                }
            }
            _ => {}
        }
    }
    
    if !num_buffer.is_empty() {
        tokens.push(Token::Number(num_buffer.parse().unwrap()));
    }
    
    tokens
}

/// 求值
fn evaluate(expr: &str) -> Result<f64, String> {
    let tokens = tokenize(expr);
    let mut operands = Vec::new();
    let mut operators = Vec::new();
    
    let precedence = |op: char| -> i32 {
        match op {
            '+' | '-' => 1,
            '*' | '/' => 2,
            _ => 0,
        }
    };
    
    let apply_op = |op: char, b: f64, a: f64| -> f64 {
        match op {
            '+' => a + b,
            '-' => a - b,
            '*' => a * b,
            '/' => a / b,
            _ => 0.0,
        }
    };
    
    for token in tokens {
        match token {
            Token::Number(n) => operands.push(n),
            Token::Operator(op) => {
                while let Some(&top_op) = operators.last() {
                    if top_op == '(' || precedence(top_op) < precedence(op) {
                        break;
                    }
                    let op = operators.pop().unwrap();
                    let b = operands.pop().unwrap();
                    let a = operands.pop().unwrap();
                    operands.push(apply_op(op, b, a));
                }
                operators.push(op);
            }
            Token::LeftParen => operators.push('('),
            Token::RightParen => {
                while let Some(op) = operators.pop() {
                    if op == '(' {
                        break;
                    }
                    let b = operands.pop().unwrap();
                    let a = operands.pop().unwrap();
                    operands.push(apply_op(op, b, a));
                }
            }
        }
    }
    
    while let Some(op) = operators.pop() {
        let b = operands.pop().unwrap();
        let a = operands.pop().unwrap();
        operands.push(apply_op(op, b, a));
    }
    
    operands.pop().ok_or("Invalid expression".to_string())
}

fn main() {
    let expressions = vec![
        "3 + 4 * 2",
        "(3 + 4) * 2",
        "10 / 2 + 3",
        "1 + 2 * 3 - 4 / 2",
    ];
    
    for expr in expressions {
        match evaluate(expr) {
            Ok(result) => println!("{} = {}", expr, result),
            Err(e) => println!("Error evaluating {}: {}", expr, e),
        }
    }
}
```

---

### 项目2: 任务调度系统

```rust
use std::collections::BinaryHeap;
use std::cmp::Ordering;

#[derive(Eq, PartialEq, Clone, Debug)]
struct Task {
    id: usize,
    priority: usize,
    name: String,
}

impl Ord for Task {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority)
    }
}

impl PartialOrd for Task {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 任务调度器
struct TaskScheduler {
    queue: BinaryHeap<Task>,
}

impl TaskScheduler {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
    
    fn add_task(&mut self, task: Task) {
        self.queue.push(task);
    }
    
    fn get_next_task(&mut self) -> Option<Task> {
        self.queue.pop()
    }
    
    fn peek_next(&self) -> Option<&Task> {
        self.queue.peek()
    }
    
    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }
}

fn main() {
    let mut scheduler = TaskScheduler::new();
    
    // 添加任务
    scheduler.add_task(Task { id: 1, priority: 2, name: "Task A".to_string() });
    scheduler.add_task(Task { id: 2, priority: 5, name: "Task B".to_string() });
    scheduler.add_task(Task { id: 3, priority: 1, name: "Task C".to_string() });
    scheduler.add_task(Task { id: 4, priority: 3, name: "Task D".to_string() });
    
    // 执行任务
    println!("Executing tasks by priority:");
    while let Some(task) = scheduler.get_next_task() {
        println!("Executing: {} (priority: {})", task.name, task.priority);
    }
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码总量**: ~850行  
**维护者**: Rust Learning Community

---

💻 **掌握算法与数据结构，提升编程核心竞争力！** 🚀✨
