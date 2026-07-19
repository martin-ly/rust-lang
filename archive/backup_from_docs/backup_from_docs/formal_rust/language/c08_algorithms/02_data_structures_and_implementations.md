# 数据结构体体体与实现


## 📊 目录

- [概述](#概述)
- [线性数据结构体体体](#线性数据结构体体体)
  - [动态数组（Vec）](#动态数组vec)
  - [双端队列（VecDeque）](#双端队列vecdeque)
  - [栈与队列](#栈与队列)
- [树形数据结构体体体](#树形数据结构体体体)
  - [二叉树](#二叉树)
  - [平衡二叉搜索树（AVL/红黑树）](#平衡二叉搜索树avl红黑树)
- [图数据结构体体体](#图数据结构体体体)
  - [邻接表](#邻接表)
  - [邻接矩阵](#邻接矩阵)
- [哈希表与映射](#哈希表与映射)
  - [HashMap](#hashmap)
  - [HashSet](#hashset)
- [总结](#总结)
  - [关键要点](#关键要点)
  - [下一步](#下一步)


## 概述

数据结构体体体是算法高效运行的基础。Rust 通过类型系统和所有权模型，为数据结构体体体的实现提供了安全、高效的支持。本章系统梳理线性数据结构体体体、树形结构体体体、图结构体体体以及哈希表与映射的 Rust 实现与应用。

## 线性数据结构体体体

### 动态数组（Vec）

```rust
fn vec_example() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    println!("{:?}", v);
}
```

### 双端队列（VecDeque）

```rust
use std::collections::VecDeque;

fn vecdeque_example() {
    let mut dq = VecDeque::new();
    dq.push_back(1);
    dq.push_front(0);
    dq.push_back(2);
    println!("{:?}", dq);
}
```

### 栈与队列

```rust
// 栈
fn stack_example() {
    let mut stack = Vec::new();
    stack.push(1);
    stack.push(2);
    println!("栈顶: {:?}", stack.pop());
}

// 队列
use std::collections::VecDeque;
fn queue_example() {
    let mut queue = VecDeque::new();
    queue.push_back(1);
    queue.push_back(2);
    println!("队首: {:?}", queue.pop_front());
}
```

## 树形数据结构体体体

### 二叉树

```rust
#[derive(Debug)]
struct TreeNode<T> {
    val: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

impl<T> TreeNode<T> {
    fn new(val: T) -> Self {
        TreeNode { val, left: None, right: None }
    }
}

fn binary_tree_example() {
    let mut root = TreeNode::new(1);
    root.left = Some(Box::new(TreeNode::new(2)));
    root.right = Some(Box::new(TreeNode::new(3)));
    println!("{:?}", root);
}
```

### 平衡二叉搜索树（AVL/红黑树）

> Rust 标准库提供了 BTreeMap/BTreeSet，底层为平衡树结构体体体。

```rust
use std::collections::BTreeMap;

fn btreemap_example() {
    let mut map = BTreeMap::new();
    map.insert(3, "c");
    map.insert(1, "a");
    map.insert(2, "b");
    for (k, v) in &map {
        println!("{} => {}", k, v);
    }
}
```

## 图数据结构体体体

### 邻接表

```rust
use std::collections::HashMap;

struct Graph {
    adj: HashMap<u32, Vec<u32>>,
}

impl Graph {
    fn new() -> Self {
        Graph { adj: HashMap::new() }
    }
    fn add_edge(&mut self, u: u32, v: u32) {
        self.adj.entry(u).or_default().push(v);
    }
}

fn graph_example() {
    let mut g = Graph::new();
    g.add_edge(1, 2);
    g.add_edge(1, 3);
    g.add_edge(2, 3);
    println!("{:?}", g.adj);
}
```

### 邻接矩阵

```rust
fn adjacency_matrix_example() {
    let n = 3;
    let mut matrix = vec![vec![0; n]; n];
    matrix[0][1] = 1;
    matrix[1][2] = 1;
    println!("{:?}", matrix);
}
```

## 哈希表与映射

### HashMap

```rust
use std::collections::HashMap;

fn hashmap_example() {
    let mut map = HashMap::new();
    map.insert("a", 1);
    map.insert("b", 2);
    println!("{:?}", map);
}
```

### HashSet

```rust
use std::collections::HashSet;

fn hashset_example() {
    let mut set = HashSet::new();
    set.insert(1);
    set.insert(2);
    println!("{:?}", set);
}
```

## 总结

Rust 的数据结构体体体实现兼顾了性能与安全。通过标准库和自定义实现，开发者可以高效地管理和操作各种数据结构体体体。

### 关键要点

1. **线性结构体体体** - Vec、VecDeque、栈、队列
2. **树结构体体体** - 二叉树、BTreeMap
3. **图结构体体体** - 邻接表、邻接矩阵
4. **哈希结构体体体** - HashMap、HashSet

### 下一步

在下一章中，我们将探讨高级算法技术，包括动态规划、贪心算法、回溯算法和分治算法。

"

---
