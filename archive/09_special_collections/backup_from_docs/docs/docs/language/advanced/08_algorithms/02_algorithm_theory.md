
# Rust算法全景：形式化分析与实现

## 目录

- [Rust算法全景：形式化分析与实现](#rust算法全景形式化分析与实现)
  - [目录](#目录)
  - [1. 引言：算法与Rust](#1-引言算法与rust)
  - [2. 基础数据结构算法](#2-基础数据结构算法)
    - [2.1 线性结构](#21-线性结构)
      - [2.1.1 动态数组](#211-动态数组)
      - [2.1.2 链表](#212-链表)
      - [2.1.3 栈与队列](#213-栈与队列)
    - [2.2 树结构](#22-树结构)
      - [2.2.1 二叉树](#221-二叉树)
      - [2.2.2 二叉搜索树](#222-二叉搜索树)
      - [2.2.3 平衡树](#223-平衡树)
      - [2.2.4 红黑树](#224-红黑树)
    - [2.3 图结构](#23-图结构)
      - [2.3.1 图的表示](#231-图的表示)
      - [2.3.2 图的遍历](#232-图的遍历)
    - [2.4 散列结构](#24-散列结构)
      - [2.4.1 散列函数](#241-散列函数)
      - [2.4.2 冲突解决](#242-冲突解决)
  - [3. 排序算法](#3-排序算法)
    - [3.1 比较排序](#31-比较排序)
      - [3.1.1 快速排序](#311-快速排序)
      - [3.1.2 归并排序](#312-归并排序)
      - [3.1.3 堆排序](#313-堆排序)
    - [3.2 非比较排序](#32-非比较排序)
      - [3.2.1 计数排序](#321-计数排序)
      - [3.2.2 基数排序](#322-基数排序)
      - [3.2.3 桶排序](#323-桶排序)
    - [3.3 外部排序](#33-外部排序)
    - [3.4 排序算法复杂度与稳定性](#34-排序算法复杂度与稳定性)
  - [4. 搜索与查找算法](#4-搜索与查找算法)
    - [4.1 基础搜索算法](#41-基础搜索算法)
      - [4.1.1 线性搜索](#411-线性搜索)
      - [4.1.2 二分搜索](#412-二分搜索)
      - [4.1.3 插值搜索](#413-插值搜索)
    - [4.2 高级搜索策略](#42-高级搜索策略)
      - [4.2.1 启发式搜索](#421-启发式搜索)
      - [4.2.2 跳跃搜索](#422-跳跃搜索)
    - [4.3 字符串搜索算法](#43-字符串搜索算法)
      - [4.3.1 朴素字符串搜索](#431-朴素字符串搜索)
      - [4.3.2 KMP算法](#432-kmp算法)
      - [4.3.3 Boyer-Moore算法](#433-boyer-moore算法)
  - [5. 图论算法](#5-图论算法)
    - [5.1 遍历算法](#51-遍历算法)
      - [5.1.1 拓扑排序](#511-拓扑排序)
    - [5.2 最短路径算法](#52-最短路径算法)
      - [5.2.1 Dijkstra算法](#521-dijkstra算法)
      - [5.2.2 Bellman-Ford算法](#522-bellman-ford算法)
      - [5.2.3 Floyd-Warshall算法](#523-floyd-warshall算法)
    - [5.3 最小生成树](#53-最小生成树)
      - [5.3.1 Prim算法](#531-prim算法)
      - [5.3.2 Kruskal算法](#532-kruskal算法)
    - [5.4 网络流算法](#54-网络流算法)
      - [5.4.1 Ford-Fulkerson算法](#541-ford-fulkerson算法)
      - [5.4.2 Edmonds-Karp算法](#542-edmonds-karp算法)
    - [5.5 二分图算法](#55-二分图算法)
      - [5.5.1 二分图检测](#551-二分图检测)
      - [5.5.2 最大二分匹配](#552-最大二分匹配)
  - [6. 数值算法](#6-数值算法)
    - [6.1 基本数值算法](#61-基本数值算法)
      - [6.1.1 最大公约数与最小公倍数](#611-最大公约数与最小公倍数)
      - [6.1.2 素数测试与生成](#612-素数测试与生成)
      - [6.1.3 快速幂](#613-快速幂)
    - [6.2 数值计算](#62-数值计算)
      - [6.2.1 牛顿法求根](#621-牛顿法求根)
      - [6.2.2 数值积分](#622-数值积分)
    - [6.3 矩阵运算](#63-矩阵运算)
      - [6.3.1 矩阵乘法](#631-矩阵乘法)
      - [6.3.2 高斯消元](#632-高斯消元)
  - [7. 密码学算法](#7-密码学算法)
    - [7.1 散列算法](#71-散列算法)
      - [7.1.1 SHA-256](#711-sha-256)
      - [7.1.2 HMAC](#712-hmac)
    - [7.2 对称加密](#72-对称加密)
      - [7.2.1 AES](#721-aes)
    - [7.3 非对称加密](#73-非对称加密)
      - [7.3.1 RSA](#731-rsa)
  - [8. 并行与并发算法](#8-并行与并发算法)
    - [8.1 并行基础算法](#81-并行基础算法)
      - [8.1.1 并行求和](#811-并行求和)
      - [8.1.2 并行排序](#812-并行排序)
    - [8.2 并发数据结构](#82-并发数据结构)
      - [8.2.1 无锁栈](#821-无锁栈)
      - [8.2.2 读写锁](#822-读写锁)
    - [8.3 工作窃取算法](#83-工作窃取算法)
  - [9. 高级算法范式](#9-高级算法范式)
    - [9.1 贪心算法](#91-贪心算法)
    - [9.2 动态规划](#92-动态规划)
    - [9.3 分治算法](#93-分治算法)
    - [9.4 回溯算法](#94-回溯算法)
    - [9.5 随机化算法](#95-随机化算法)
  - [10. 机器学习算法](#10-机器学习算法)
    - [10.1 监督学习](#101-监督学习)
      - [10.1.1 线性回归](#1011-线性回归)
      - [10.1.2 决策树](#1012-决策树)
    - [10.2 无监督学习](#102-无监督学习)
      - [10.2.1 K均值聚类](#1021-k均值聚类)
      - [10.2.2 主成分分析(PCA)](#1022-主成分分析pca)
  - [11. 总结与思维导图](#11-总结与思维导图)
  - [11. 总结与未来发展](#11-总结与未来发展)
    - [11.1 Rust算法实现的优势](#111-rust算法实现的优势)
    - [11.2 算法研究与实践的未来趋势](#112-算法研究与实践的未来趋势)
      - [11.2.1 异构计算算法](#1121-异构计算算法)
      - [11.2.2 量子算法与量子抗性算法](#1122-量子算法与量子抗性算法)
      - [11.2.3 自适应与在线算法](#1123-自适应与在线算法)
    - [11.3 形式化验证与正确性证明](#113-形式化验证与正确性证明)
    - [11.4 结语](#114-结语)
  - [完整思维导图](#完整思维导图)

## 1. 引言：算法与Rust

算法是计算机科学的核心，而Rust作为一种强调安全性、性能和并发的系统编程语言，提供了实现高效算法的理想环境。
Rust的所有权系统、零成本抽象和类型系统使得复杂算法实现既安全又高效。

**定义 1.1 (算法)** 算法是解决特定问题的明确定义的计算过程，具有有限性、确定性、可行性和输入输出特性。

**定理 1.1 (正确性)** 算法A对于问题P是正确的，当且仅当对任意合法输入x，A(x)在有限步骤内终止并产生满足P规范的输出。

本文将从形式化角度系统地探讨各类算法的原理和Rust实现，展示Rust语言特性如何影响算法设计与实现。

## 2. 基础数据结构算法

### 2.1 线性结构

**定义 2.1.1 (线性结构)** 线性结构是元素之间存在一对一线性关系的数据结构，包括数组、链表、栈、队列等。

#### 2.1.1 动态数组

**定理 2.1.1 (动态数组摊销复杂度)** 具有倍增扩容策略的动态数组，其插入操作的摊销时间复杂度为O(1)。

**证明:** 假设初始容量为1，每次扩容为原来的2倍。经过n次插入操作后，总共的元素搬移次数为1+2+4+...+2^k，其中k=⌊log₂n⌋。
此数列和为2^(k+1)-1<2n，因此n次操作的摊销代价为O(1)。

Rust实现:

```rust
pub struct DynamicArray<T> {
    data: Vec<T>,
}

impl<T> DynamicArray<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }
    
    pub fn push(&mut self, item: T) {
        self.data.push(item); // Vec已实现动态扩容
    }
    
    pub fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }
    
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
    
    pub fn len(&self) -> usize {
        self.data.len()
    }
}
```

#### 2.1.2 链表

**定义 2.1.2 (链表)** 链表是由一系列节点组成的数据结构，每个节点包含数据和指向下一节点的引用。

**定理 2.1.2 (单向链表操作复杂度)** 单向链表的头部插入和删除操作的时间复杂度为O(1)，而查找和尾部操作的时间复杂度为O(n)。

Rust中的单链表实现挑战了所有权模型，经典实现：

```rust
pub struct List<T> {
    head: Option<Box<Node<T>>>,
}

struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        Self { head: None }
    }
    
    pub fn push_front(&mut self, value: T) {
        let new_node = Box::new(Node {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
    
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.value
        })
    }
}
```

#### 2.1.3 栈与队列

**定义 2.1.3 (栈)** 栈是一种后进先出(LIFO)的线性数据结构，只允许在同一端(栈顶)进行插入和删除操作。

**定义 2.1.4 (队列)** 队列是一种先进先出(FIFO)的线性数据结构，在一端(队尾)插入，另一端(队首)删除。

**定理 2.1.3 (栈操作复杂度)** 栈的压栈(push)和出栈(pop)操作时间复杂度均为O(1)。

**定理 2.1.4 (队列操作复杂度)** 基于循环数组实现的队列，其入队(enqueue)和出队(dequeue)操作的时间复杂度均为O(1)。

Rust实现:

```rust
// 栈实现
pub struct Stack<T> {
    elements: Vec<T>,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Self { elements: Vec::new() }
    }
    
    pub fn push(&mut self, value: T) {
        self.elements.push(value);
    }
    
    pub fn pop(&mut self) -> Option<T> {
        self.elements.pop()
    }
    
    pub fn peek(&self) -> Option<&T> {
        self.elements.last()
    }
    
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }
}

// 循环队列实现
pub struct CircularQueue<T> {
    elements: Vec<Option<T>>,
    capacity: usize,
    head: usize,
    tail: usize,
    size: usize,
}

impl<T> CircularQueue<T> {
    pub fn new(capacity: usize) -> Self {
        let mut elements = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            elements.push(None);
        }
        
        Self {
            elements,
            capacity,
            head: 0,
            tail: 0,
            size: 0,
        }
    }
    
    pub fn enqueue(&mut self, value: T) -> Result<(), &'static str> {
        if self.size == self.capacity {
            return Err("Queue is full");
        }
        
        self.elements[self.tail] = Some(value);
        self.tail = (self.tail + 1) % self.capacity;
        self.size += 1;
        Ok(())
    }
    
    pub fn dequeue(&mut self) -> Option<T> {
        if self.size == 0 {
            return None;
        }
        
        let value = self.elements[self.head].take();
        self.head = (self.head + 1) % self.capacity;
        self.size -= 1;
        value
    }
}
```

### 2.2 树结构

**定义 2.2.1 (树)** 树是一种非线性层次结构，由节点和连接节点的边组成，没有环路。

#### 2.2.1 二叉树

**定义 2.2.2 (二叉树)** 二叉树是每个节点最多有两个子节点的树结构。

**定理 2.2.1 (二叉树节点关系)** n个节点的二叉树共有n-1条边。

**定理 2.2.2 (二叉树高度与节点数)** 高度为h的二叉树，节点数最少为h，最多为2^h-1。

Rust实现:

```rust
pub struct BinaryTree<T> {
    root: Option<Box<Node<T>>>,
}

struct Node<T> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T> BinaryTree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    pub fn height(&self) -> usize {
        Self::height_recursive(&self.root)
    }
    
    fn height_recursive(node: &Option<Box<Node<T>>>) -> usize {
        match node {
            None => 0,
            Some(n) => {
                let left_height = Self::height_recursive(&n.left);
                let right_height = Self::height_recursive(&n.right);
                1 + std::cmp::max(left_height, right_height)
            }
        }
    }
}
```

#### 2.2.2 二叉搜索树

**定义 2.2.3 (二叉搜索树)** 二叉搜索树是一种特殊的二叉树，对于任何节点，其左子树上所有节点的值都小于该节点的值，右子树上所有节点的值都大于该节点的值。

**定理 2.2.3 (BST搜索复杂度)** 在高度为h的二叉搜索树中，搜索、插入和删除操作的时间复杂度均为O(h)。

**定理 2.2.4 (BST中序遍历)** 二叉搜索树的中序遍历产生元素的有序序列。

Rust实现:

```rust
pub struct BinarySearchTree<T: Ord> {
    root: Option<Box<Node<T>>>,
}

struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T: Ord> BinarySearchTree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    pub fn insert(&mut self, value: T) {
        Self::insert_recursive(&mut self.root, value);
    }
    
    fn insert_recursive(node: &mut Option<Box<Node<T>>>, value: T) {
        match node {
            None => {
                *node = Some(Box::new(Node {
                    value,
                    left: None,
                    right: None,
                }));
            }
            Some(n) => {
                if value < n.value {
                    Self::insert_recursive(&mut n.left, value);
                } else if value > n.value {
                    Self::insert_recursive(&mut n.right, value);
                }
                // 如果相等，不做任何操作（不插入重复值）
            }
        }
    }
    
    pub fn search(&self, value: &T) -> bool {
        Self::search_recursive(&self.root, value)
    }
    
    fn search_recursive(node: &Option<Box<Node<T>>>, value: &T) -> bool {
        match node {
            None => false,
            Some(n) => {
                if value < &n.value {
                    Self::search_recursive(&n.left, value)
                } else if value > &n.value {
                    Self::search_recursive(&n.right, value)
                } else {
                    true
                }
            }
        }
    }
    
    pub fn in_order_traversal(&self, visit: &mut impl FnMut(&T)) {
        Self::in_order_recursive(&self.root, visit);
    }
    
    fn in_order_recursive(node: &Option<Box<Node<T>>>, visit: &mut impl FnMut(&T)) {
        if let Some(n) = node {
            Self::in_order_recursive(&n.left, visit);
            visit(&n.value);
            Self::in_order_recursive(&n.right, visit);
        }
    }
}
```

#### 2.2.3 平衡树

**定义 2.2.4 (平衡二叉树)** 平衡二叉树是一种特殊的二叉搜索树，对于任何节点，其左右子树的高度差不超过1。

**定理 2.2.5 (AVL树高度)** 含有n个节点的AVL树的高度为O(log n)。

**定理 2.2.6 (AVL旋转)** 在AVL树中，插入或删除节点后，至多需要O(log n)次旋转操作来恢复平衡。

Rust实现AVL树核心部分:

```rust
pub struct AVLTree<T: Ord> {
    root: Option<Box<Node<T>>>,
}

struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
    height: usize,
}

impl<T: Ord> AVLTree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    fn height(node: &Option<Box<Node<T>>>) -> usize {
        match node {
            None => 0,
            Some(n) => n.height,
        }
    }
    
    fn balance_factor(node: &Node<T>) -> isize {
        Self::height(&node.left) as isize - Self::height(&node.right) as isize
    }
    
    fn update_height(node: &mut Node<T>) {
        node.height = 1 + std::cmp::max(
            Self::height(&node.left),
            Self::height(&node.right)
        );
    }
    
    // 右旋转
    fn rotate_right(mut node: Box<Node<T>>) -> Box<Node<T>> {
        let mut left_child = node.left.take().unwrap();
        node.left = left_child.right.take();
        Self::update_height(&mut node);
        
        left_child.right = Some(node);
        Self::update_height(&mut left_child);
        
        left_child
    }
    
    // 左旋转
    fn rotate_left(mut node: Box<Node<T>>) -> Box<Node<T>> {
        let mut right_child = node.right.take().unwrap();
        node.right = right_child.left.take();
        Self::update_height(&mut node);
        
        right_child.left = Some(node);
        Self::update_height(&mut right_child);
        
        right_child
    }
    
    // 平衡节点
    fn balance(mut node: Box<Node<T>>) -> Box<Node<T>> {
        Self::update_height(&mut node);
        let balance = Self::balance_factor(&node);
        
        if balance > 1 {
            // 左子树过高
            if let Some(left) = &node.left {
                if Self::balance_factor(left) < 0 {
                    // LR情况，先左旋左子树
                    let left_child = node.left.take().unwrap();
                    node.left = Some(Self::rotate_left(left_child));
                }
            }
            // LL情况，右旋
            return Self::rotate_right(node);
        } else if balance < -1 {
            // 右子树过高
            if let Some(right) = &node.right {
                if Self::balance_factor(right) > 0 {
                    // RL情况，先右旋右子树
                    let right_child = node.right.take().unwrap();
                    node.right = Some(Self::rotate_right(right_child));
                }
            }
            // RR情况，左旋
            return Self::rotate_left(node);
        }
        
        node
    }
    
    pub fn insert(&mut self, value: T) {
        self.root = Self::insert_recursive(self.root.take(), value);
    }
    
    fn insert_recursive(node: Option<Box<Node<T>>>, value: T) -> Option<Box<Node<T>>> {
        match node {
            None => Some(Box::new(Node {
                value,
                left: None,
                right: None,
                height: 1,
            })),
            Some(mut n) => {
                if value < n.value {
                    n.left = Self::insert_recursive(n.left, value);
                } else if value > n.value {
                    n.right = Self::insert_recursive(n.right, value);
                } else {
                    return Some(n); // 已存在，不做改变
                }
                
                Some(Self::balance(n))
            }
        }
    }
}
```

#### 2.2.4 红黑树

**定义 2.2.5 (红黑树)** 红黑树是一种自平衡二叉搜索树，每个节点都有一个额外的颜色属性（红色或黑色），并满足以下性质：

1. 每个节点是红色或黑色
2. 根节点是黑色
3. 所有叶子节点（NULL节点）是黑色
4. 红色节点的两个子节点都是黑色
5. 从任一节点到其每个叶子节点的路径上包含相同数量的黑色节点

**定理 2.2.7 (红黑树高度)** 含有n个节点的红黑树高度不超过2log₂(n+1)。

**推论 2.2.1** 红黑树的基本操作（搜索、插入、删除）时间复杂度为O(log n)。

Rust中红黑树的实现较复杂，这里展示部分关键结构：

```rust
pub struct RedBlackTree<T: Ord> {
    root: Option<Box<Node<T>>>,
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum Color {
    Red,
    Black,
}

struct Node<T: Ord> {
    value: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
    color: Color,
}

impl<T: Ord> RedBlackTree<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    // 复杂的实现，包括旋转、重新着色等操作...
}
```

### 2.3 图结构

**定义 2.3.1 (图)** 图G是一个二元组G=(V,E)，其中V是顶点集合，E是边集合。若E中的边是有方向的，则G为有向图，否则为无向图。

#### 2.3.1 图的表示

**定义 2.3.2 (邻接矩阵)** 邻接矩阵是一个V×V的矩阵A，其中`A[i][j]=1`表示存在从顶点i到j的边，否则`A[i][j]=0`。

**定义 2.3.3 (邻接表)** 邻接表由|V|个链表组成，第i个链表包含与顶点i相邻的所有顶点。

**定理 2.3.1 (空间复杂度对比)** 邻接矩阵的空间复杂度为O(V²)，而邻接表的空间复杂度为O(V+E)。

Rust实现:

```rust
// 邻接矩阵表示
pub struct GraphMatrix {
    adj_matrix: Vec<Vec<bool>>,
    vertex_count: usize,
}

impl GraphMatrix {
    pub fn new(vertex_count: usize) -> Self {
        let adj_matrix = vec![vec![false; vertex_count]; vertex_count];
        Self { adj_matrix, vertex_count }
    }
    
    pub fn add_edge(&mut self, from: usize, to: usize) {
        if from < self.vertex_count && to < self.vertex_count {
            self.adj_matrix[from][to] = true;
        }
    }
    
    pub fn has_edge(&self, from: usize, to: usize) -> bool {
        from < self.vertex_count && to < self.vertex_count && self.adj_matrix[from][to]
    }
}

// 邻接表表示
pub struct GraphList {
    adj_lists: Vec<Vec<usize>>,
}

impl GraphList {
    pub fn new(vertex_count: usize) -> Self {
        let adj_lists = vec![Vec::new(); vertex_count];
        Self { adj_lists }
    }
    
    pub fn add_edge(&mut self, from: usize, to: usize) {
        if from < self.adj_lists.len() && to < self.adj_lists.len() {
            self.adj_lists[from].push(to);
        }
    }
    
    pub fn neighbors(&self, vertex: usize) -> &[usize] {
        if vertex < self.adj_lists.len() {
            &self.adj_lists[vertex]
        } else {
            &[]
        }
    }
}
```

#### 2.3.2 图的遍历

**定义 2.3.4 (图遍历)** 图遍历是系统地访问图中所有顶点的过程，常见方法包括深度优先搜索(DFS)和广度优先搜索(BFS)。

**定理 2.3.2 (DFS/BFS复杂度)** 使用邻接表表示的图，DFS和BFS的时间复杂度均为O(V+E)；使用邻接矩阵表示时，复杂度为O(V²)。

Rust实现:

```rust
impl GraphList {
    // 深度优先搜索
    pub fn dfs(&self, start: usize, visit: &mut impl FnMut(usize)) {
        let mut visited = vec![false; self.adj_lists.len()];
        self.dfs_recursive(start, &mut visited, visit);
    }
    
    fn dfs_recursive(&self, vertex: usize, visited: &mut [bool], visit: &mut impl FnMut(usize)) {
        if vertex >= visited.len() || visited[vertex] {
            return;
        }
        
        visited[vertex] = true;
        visit(vertex);
        
        for &neighbor in &self.adj_lists[vertex] {
            self.dfs_recursive(neighbor, visited, visit);
        }
    }
    
    // 广度优先搜索
    pub fn bfs(&self, start: usize, visit: &mut impl FnMut(usize)) {
        let mut visited = vec![false; self.adj_lists.len()];
        let mut queue = std::collections::VecDeque::new();
        
        visited[start] = true;
        queue.push_back(start);
        
        while let Some(vertex) = queue.pop_front() {
            visit(vertex);
            
            for &neighbor in &self.adj_lists[vertex] {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }
    }
}
```

### 2.4 散列结构

**定义 2.4.1 (散列表)** 散列表是一种数据结构，它使用散列函数将键映射到值，提供快速的查找和插入操作。

**定理 2.4.1 (理想散列表性能)** 在理想情况下（无冲突），散列表的查找、插入和删除操作的平均时间复杂度为O(1)。

**定理 2.4.2 (负载因子与性能)** 当散列表的负载因子α（元素数量/桶数量）增加时，性能下降。许多实现在α超过某个阈值（如0.7）时会触发重新散列。

#### 2.4.1 散列函数

**定义 2.4.2 (散列函数)** 散列函数h:K→[0,m-1]将键空间K映射到m个整数（桶索引），理想的散列函数应具有均匀分布性。

#### 2.4.2 冲突解决

**定义 2.4.3 (散列冲突)** 当两个不同的键被散列函数映射到同一个桶时，发生散列冲突。

**定义 2.4.4 (链式法)** 链式法通过在每个桶中维护一个链表来解决冲突，冲突的键存储在同一桶的链表中。

**定义 2.4.5 (开放寻址法)** 开放寻址法在发生冲突时尝试其他桶位置，包括线性探测、二次探测和双重散列等策略。

Rust实现简单的散列表:

```rust
pub struct HashMap<K, V> {
    buckets: Vec<Vec<(K, V)>>,
    capacity: usize,
    size: usize,
}

impl<K: Eq + std::hash::Hash, V> HashMap<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            buckets: vec![Vec::new(); capacity],
            capacity,
            size: 0,
        }
    }
    
    fn hash(&self, key: &K) -> usize {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize % self.capacity
    }
    
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let bucket_index = self.hash(&key);
        let bucket = &mut self.buckets[bucket_index];
        
        // 查找key是否已存在
        for i in 0..bucket.len() {
            if bucket[i].0 == key {
                return Some(std::mem::replace(&mut bucket[i].1, value));
            }
        }
        
        // 不存在，插入新键值对
        bucket.push((key, value));
        self.size += 1;
        
        // 检查是否需要扩容
        if self.size > self.capacity * 3 / 4 {
            // 扩容逻辑...
        }
        
        None
    }
    
    pub fn get(&self, key: &K) -> Option<&V> {
        let bucket_index = self.hash(key);
        self.buckets[bucket_index]
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v)
    }
    
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let bucket_index = self.hash(key);
        let bucket = &mut self.buckets[bucket_index];
        
        let pos = bucket.iter().position(|(k, _)| k == key)?;
        self.size -= 1;
        Some(bucket.swap_remove(pos).1)
    }
}
```

## 3. 排序算法

### 3.1 比较排序

**定义 3.1.1 (比较排序)** 比较排序是通过比较元素之间的相对大小来确定排序顺序的算法。

**定理 3.1.1 (比较排序下界)** 任何基于比较的排序算法，最坏情况下的时间复杂度至少为Ω(n log n)。

**证明:** 使用决策树模型。n个不同元素的排列有n!种可能，决策树的高度至少为log₂(n!)≈n log₂n，故比较次数的下界为Ω(n log n)。

#### 3.1.1 快速排序

**定义 3.1.2 (快速排序)** 快速排序是一种分治算法，选择一个元素作为"基准"，将小于基准的元素放在前面，大于基准的元素放在后面，然后递归地对子数组排序。

**定理 3.1.2 (快速排序平均复杂度)** 快速排序的平均时间复杂度为O(n log n)，最坏情况为O(n²)。

Rust实现:

```rust
pub fn quicksort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quicksort(&mut arr[0..pivot_index]);
    quicksort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord + Clone>(arr: &mut [T]) -> usize {
    let pivot_index = arr.len() - 1;
    let pivot = arr[pivot_index].clone();
    
    let mut i = 0;
    for j in 0..pivot_index {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot_index);
    i
}
```

#### 3.1.2 归并排序

**定义 3.1.3 (归并排序)** 归并排序是一种分治算法，将数组分成两个子数组，递归地对子数组排序，然后合并两个已排序的子数组。

**定理 3.1.3 (归并排序复杂度)** 归并排序的时间复杂度为O(n log n)，空间复杂度为O(n)。

Rust实现:

```rust
pub fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    merge_sort(&mut arr[0..mid]);
    merge_sort(&mut arr[mid..]);
    
    let left = arr[0..mid].to_vec();
    let right = arr[mid..].to_vec();
    
    merge(arr, &left, &right);
}

fn merge<T: Ord + Clone>(arr: &mut [T], left: &[T], right: &[T]) {
    let mut i = 0;  // 左数组索引
    let mut j = 0;  // 右数组索引
    let mut k = 0;  // 合并数组索引
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i].clone();
            i += 1;
        } else {
            arr[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }
    
    // 复制剩余的元素
    while i < left.len() {
        arr[k] = left[i].clone();
        i += 1;
        k += 1;
    }
    
    while j < right.len() {
        arr[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}
```

#### 3.1.3 堆排序

**定义 3.1.4 (堆)** 堆是一种特殊的完全二叉树，最大堆满足每个节点的值都大于或等于其子节点的值，最小堆满足每个节点的值都小于或等于其子节点的值。

**定义 3.1.5 (堆排序)** 堆排序是利用堆的性质进行排序的算法，先构建最大堆，然后反复将堆顶元素（最大值）与末尾元素交换，并重新调整堆。

**定理 3.1.4 (堆排序复杂度)** 堆排序的时间复杂度为O(n log n)，空间复杂度为O(1)。

Rust实现:

```rust
pub fn heap_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    // 

```rust
pub fn heap_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    // 构建最大堆
    let len = arr.len();
    for i in (0..len/2).rev() {
        heapify(arr, len, i);
    }
    
    // 逐个将堆顶元素（最大值）放到末尾
    for i in (1..len).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

fn heapify<T: Ord>(arr: &mut [T], heap_size: usize, root: usize) {
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;
    
    // 比较左子节点
    if left < heap_size && arr[left] > arr[largest] {
        largest = left;
    }
    
    // 比较右子节点
    if right < heap_size && arr[right] > arr[largest] {
        largest = right;
    }
    
    // 如果最大值不是根节点，交换并继续堆化
    if largest != root {
        arr.swap(root, largest);
        heapify(arr, heap_size, largest);
    }
}
```

### 3.2 非比较排序

**定义 3.2.1 (非比较排序)** 非比较排序不依赖元素之间的比较，而是利用元素本身的特性进行排序，可以突破比较排序的Ω(n log n)下界。

#### 3.2.1 计数排序

**定义 3.2.2 (计数排序)** 计数排序是一种基于元素值的分布进行排序的算法，适用于已知范围内的整数。

**定理 3.2.1 (计数排序复杂度)** 若排序n个元素，取值范围为k，则计数排序的时间和空间复杂度均为O(n+k)。

Rust实现:

```rust
pub fn counting_sort(arr: &mut [usize], max_val: usize) {
    if arr.len() <= 1 {
        return;
    }
    
    // 创建计数数组
    let mut counts = vec![0; max_val + 1];
    
    // 统计每个元素出现的次数
    for &val in arr.iter() {
        counts[val] += 1;
    }
    
    // 累加计数，确定每个元素的结束位置
    for i in 1..counts.len() {
        counts[i] += counts[i - 1];
    }
    
    // 创建辅助数组，根据计数数组重建排序结果
    let mut output = vec![0; arr.len()];
    for &val in arr.iter().rev() {
        counts[val] -= 1;
        output[counts[val]] = val;
    }
    
    // 将排序结果复制回原数组
    arr.copy_from_slice(&output);
}
```

#### 3.2.2 基数排序

**定义 3.2.3 (基数排序)** 基数排序是一种多关键字排序算法，将元素按位分组，从最低有效位（或最高有效位）开始，依次对每一位进行排序。

**定理 3.2.2 (基数排序复杂度)** 对于n个d位数，每位数字范围为k，基数排序的时间复杂度为O(d(n+k))。

Rust实现:

```rust
pub fn radix_sort(arr: &mut [u32]) {
    if arr.len() <= 1 {
        return;
    }
    
    // 找出最大值，确定位数
    let max_val = *arr.iter().max().unwrap_or(&0);
    
    // 对每一位进行计数排序
    let mut exp = 1;
    while max_val / exp > 0 {
        counting_sort_by_digit(arr, exp);
        exp *= 10;
    }
}

fn counting_sort_by_digit(arr: &mut [u32], exp: u32) {
    let mut output = vec![0; arr.len()];
    let mut counts = vec![0; 10];
    
    // 统计当前位上每个数字出现的次数
    for &val in arr.iter() {
        let digit = (val / exp) % 10;
        counts[digit as usize] += 1;
    }
    
    // 累加计数
    for i in 1..10 {
        counts[i] += counts[i - 1];
    }
    
    // 构建输出数组
    for &val in arr.iter().rev() {
        let digit = (val / exp) % 10;
        counts[digit as usize] -= 1;
        output[counts[digit as usize]] = val;
    }
    
    // 复制回原数组
    arr.copy_from_slice(&output);
}
```

#### 3.2.3 桶排序

**定义 3.2.4 (桶排序)** 桶排序是将元素分布到有限数量的桶中，每个桶单独排序，然后依次合并所有桶的元素。

**定理 3.2.3 (桶排序复杂度)** 当输入均匀分布时，桶排序的平均时间复杂度为O(n+k)，其中k是桶的数量。

Rust实现:

```rust
pub fn bucket_sort(arr: &mut [f64]) {
    if arr.len() <= 1 {
        return;
    }
    
    let n = arr.len();
    let mut buckets: Vec<Vec<f64>> = vec![Vec::new(); n];
    
    // 将元素分配到桶中
    for &val in arr.iter() {
        let bucket_index = (val * n as f64).floor() as usize;
        let bucket_index = bucket_index.min(n - 1); // 防止索引越界
        buckets[bucket_index].push(val);
    }
    
    // 对每个桶内部排序
    for bucket in buckets.iter_mut() {
        bucket.sort_by(|a, b| a.partial_cmp(b).unwrap());
    }
    
    // 合并桶
    let mut index = 0;
    for bucket in buckets.iter() {
        for &val in bucket.iter() {
            arr[index] = val;
            index += 1;
        }
    }
}
```

### 3.3 外部排序

**定义 3.3.1 (外部排序)** 外部排序是处理大数据集、不能全部加载到内存中的排序算法，通常基于归并排序策略。

**定理 3.3.1 (外部归并排序)** 对于n个元素，m个可用内存块，外部归并排序的I/O复杂度为O((n/m)log(n/m))。

Rust实现（概念性）:

```rust
// 外部排序通常涉及文件I/O，这里给出概念性框架
pub fn external_merge_sort(input_file: &str, output_file: &str, buffer_size: usize) {
    // 1. 分割阶段：读取输入文件，分割成多个排序好的小文件
    let temp_files = split_and_sort(input_file, buffer_size);
    
    // 2. 合并阶段：合并这些排序好的小文件
    merge_files(&temp_files, output_file, buffer_size);
    
    // 3. 清理临时文件
    for file in temp_files {
        std::fs::remove_file(file).expect("Failed to remove temporary file");
    }
}

fn split_and_sort(input_file: &str, buffer_size: usize) -> Vec<String> {
    // 读取输入文件，按buffer_size分割并排序，写入临时文件
    // 返回临时文件名列表
    unimplemented!()
}

fn merge_files(temp_files: &[String], output_file: &str, buffer_size: usize) {
    // 使用多路合并算法合并已排序的临时文件
    unimplemented!()
}
```

### 3.4 排序算法复杂度与稳定性

**定义 3.4.1 (稳定排序)** 稳定排序算法保证排序前后，相等元素的相对顺序不变。

**定理 3.4.1 (稳定性与应用)** 稳定性在多关键字排序中尤为重要，可通过多次稳定排序实现。

排序算法复杂度与稳定性总结：

| 算法 | 最佳时间 | 平均时间 | 最坏时间 | 空间复杂度 | 稳定性 |
|------|----------|----------|----------|------------|--------|
| 快速排序 | O(n log n) | O(n log n) | O(n²) | O(log n) | 不稳定 |
| 归并排序 | O(n log n) | O(n log n) | O(n log n) | O(n) | 稳定 |
| 堆排序 | O(n log n) | O(n log n) | O(n log n) | O(1) | 不稳定 |
| 插入排序 | O(n) | O(n²) | O(n²) | O(1) | 稳定 |
| 冒泡排序 | O(n) | O(n²) | O(n²) | O(1) | 稳定 |
| 计数排序 | O(n+k) | O(n+k) | O(n+k) | O(n+k) | 稳定 |
| 基数排序 | O(d(n+k)) | O(d(n+k)) | O(d(n+k)) | O(n+k) | 稳定 |
| 桶排序 | O(n+k) | O(n+k) | O(n²) | O(n*k) | 稳定 |

## 4. 搜索与查找算法

### 4.1 基础搜索算法

**定义 4.1.1 (搜索)** 搜索是在集合中查找特定元素的过程。

#### 4.1.1 线性搜索

**定义 4.1.2 (线性搜索)** 线性搜索是顺序检查集合中每个元素的简单搜索算法。

**定理 4.1.1 (线性搜索复杂度)** 线性搜索的时间复杂度为O(n)。

Rust实现:

```rust
pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (index, item) in arr.iter().enumerate() {
        if item == target {
            return Some(index);
        }
    }
    None
}
```

#### 4.1.2 二分搜索

**定义 4.1.3 (二分搜索)** 二分搜索是在已排序数组中查找元素的高效算法，每次比较中将搜索范围缩小一半。

**定理 4.1.2 (二分搜索复杂度)** 二分搜索的时间复杂度为O(log n)。

Rust实现:

```rust
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mut low = 0;
    let mut high = arr.len() - 1;
    
    while low <= high {
        let mid = low + (high - low) / 2;
        
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => low = mid + 1,
            std::cmp::Ordering::Greater => {
                if mid == 0 {
                    break;
                }
                high = mid - 1;
            }
        }
    }
    
    None
}
```

#### 4.1.3 插值搜索

**定义 4.1.4 (插值搜索)** 插值搜索是二分搜索的改进版，使用元素的值分布信息来估计目标位置。

**定理 4.1.3 (插值搜索复杂度)** 当元素均匀分布时，插值搜索的平均时间复杂度为O(log log n)；最坏情况为O(n)。

Rust实现:

```rust
pub fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    
    let mut low = 0;
    let mut high = arr.len() - 1;
    
    while low <= high && target >= arr[low] && target <= arr[high] {
        // 避免除以零
        if arr[high] == arr[low] {
            if arr[low] == target {
                return Some(low);
            }
            return None;
        }
        
        // 根据目标值估计位置
        let pos = low + (((target - arr[low]) as usize) * (high - low))
                       / ((arr[high] - arr[low]) as usize);
        
        if pos >= arr.len() {
            break;
        }
        
        if arr[pos] == target {
            return Some(pos);
        } else if arr[pos] < target {
            low = pos + 1;
        } else {
            high = pos - 1;
        }
    }
    
    None
}
```

### 4.2 高级搜索策略

#### 4.2.1 启发式搜索

**定义 4.2.1 (启发式搜索)** 启发式搜索利用问题特定信息来指导搜索过程，减少搜索空间。

**定义 4.2.2 (A*算法)** A*算法是一种启发式搜索算法，使用估价函数f(n) = g(n) + h(n)，其中g(n)是从起点到节点n的实际代价，h(n)是从节点n到目标的估计代价。

**定理 4.2.1 (A*完备性)** 若启发函数h(n)不高估实际代价，则A*算法是完备的，即总能找到最优解（如果存在）。

Rust实现A*算法框架:

```rust
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;

// 节点结构，用于优先队列
#[derive(Eq, PartialEq)]
struct Node {
    position: (i32, i32),
    cost: i32,      // g(n)
    heuristic: i32, // h(n)
}

// 优先队列所需的比较实现
impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        // 注意：这里使用reverse以使BinaryHeap成为最小堆
        (other.cost + other.heuristic).cmp(&(self.cost + self.heuristic))
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn a_star(
    start: (i32, i32),
    goal: (i32, i32),
    h: impl Fn((i32, i32)) -> i32,
    neighbors: impl Fn((i32, i32)) -> Vec<((i32, i32), i32)>,
) -> Option<Vec<(i32, i32)>> {
    let mut open_set = BinaryHeap::new();
    let mut came_from = HashMap::new();
    let mut g_score = HashMap::new();
    
    // 初始化起点
    g_score.insert(start, 0);
    open_set.push(Node {
        position: start,
        cost: 0,
        heuristic: h(start),
    });
    
    while let Some(current) = open_set.pop() {
        let current_pos = current.position;
        
        // 到达目标
        if current_pos == goal {
            // 重建路径
            let mut path = vec![current_pos];
            let mut pos = current_pos;
            while let Some(&prev) = came_from.get(&pos) {
                path.push(prev);
                pos = prev;
            }
            path.reverse();
            return Some(path);
        }
        
        // 探索邻居
        for (neighbor, move_cost) in neighbors(current_pos) {
            let tentative_g = g_score[&current_pos] + move_cost;
            
            if !g_score.contains_key(&neighbor) || tentative_g < g_score[&neighbor] {
                // 这是更好的路径
                came_from.insert(neighbor, current_pos);
                g_score.insert(neighbor, tentative_g);
                open_set.push(Node {
                    position: neighbor,
                    cost: tentative_g,
                    heuristic: h(neighbor),
                });
            }
        }
    }
    
    // 无法找到路径
    None
}
```

#### 4.2.2 跳跃搜索

**定义 4.2.3 (跳跃搜索)** 跳跃搜索是在有序数组中以固定步长"跳跃"，找到合适范围后进行线性搜索的算法。

**定理 4.2.2 (跳跃搜索最优步长)** 对于长度为n的数组，跳跃搜索的最优步长为√n，此时时间复杂度为O(√n)。

Rust实现:

```rust
pub fn jump_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let n = arr.len();
    if n == 0 {
        return None;
    }
    
    // 计算跳跃步长
    let step = (n as f64).sqrt() as usize;
    
    // 跳跃寻找区间
    let mut prev = 0;
    let mut step_idx = step;
    
    while step_idx < n && &arr[step_idx - 1] < target {
        prev = step_idx;
        step_idx += step;
        if prev >= n {
            return None;
        }
    }
    
    // 线性搜索确定的区间
    while prev < n && &arr[prev] < target {
        prev += 1;
    }
    
    // 检查是否找到
    if prev < n && &arr[prev] == target {
        Some(prev)
    } else {
        None
    }
}
```

### 4.3 字符串搜索算法

**定义 4.3.1 (字符串搜索)** 字符串搜索是在文本中查找模式字符串出现位置的过程。

#### 4.3.1 朴素字符串搜索

**定义 4.3.2 (朴素字符串搜索)** 朴素字符串搜索是通过逐一比较文本中每个可能位置与模式字符串的算法。

**定理 4.3.1 (朴素搜索复杂度)** 朴素字符串搜索的时间复杂度为O(n×m)，其中n是文本长度，m是模式长度。

Rust实现:

```rust
pub fn naive_string_search(text: &str, pattern: &str) -> Vec<usize> {
    let text_chars: Vec<char> = text.chars().collect();
    let pattern_chars: Vec<char> = pattern.chars().collect();
    
    let mut matches = Vec::new();
    
    if pattern_chars.is_empty() || pattern_chars.len() > text_chars.len() {
        return matches;
    }
    
    let text_len = text_chars.len();
    let pattern_len = pattern_chars.len();
    
    for i in 0..=text_len - pattern_len {
        let mut j = 0;
        while j < pattern_len && text_chars[i + j] == pattern_chars[j] {
            j += 1;
        }
        
        if j == pattern_len {
            matches.push(i);
        }
    }
    
    matches
}
```

#### 4.3.2 KMP算法

**定义 4.3.3 (KMP算法)** Knuth-Morris-Pratt算法通过预处理模式字符串，构建"部分匹配表"，避免不必要的比较。

**定理 4.3.2 (KMP复杂度)** KMP算法的时间复杂度为O(n+m)，其中n是文本长度，m是模式长度。

Rust实现:

```rust
pub fn kmp_search(text: &str, pattern: &str) -> Vec<usize> {
    let text_chars: Vec<char> = text.chars().collect();
    let pattern_chars: Vec<char> = pattern.chars().collect();
    
    let mut matches = Vec::new();
    
    if pattern_chars.is_empty() || pattern_chars.len() > text_chars.len() {
        return matches;
    }
    
    // 构建部分匹配表
    let lps = compute_lps(&pattern_chars);
    
    let text_len = text_chars.len();
    let pattern_len = pattern_chars.len();
    
    let mut i = 0; // 文本索引
    let mut j = 0; // 模式索引
    
    while i < text_len {
        if pattern_chars[j] == text_chars[i] {
            i += 1;
            j += 1;
        }
        
        if j == pattern_len {
            // 找到匹配
            matches.push(i - j);
            j = lps[j - 1];
        } else if i < text_len && pattern_chars[j] != text_chars[i] {
            if j != 0 {
                j = lps[j - 1];
            } else {
                i += 1;
            }
        }
    }
    
    matches
}

// 计算Longest Prefix which is also Suffix (LPS)数组
fn compute_lps(pattern: &[char]) -> Vec<usize> {
    let len = pattern.len();
    let mut lps = vec![0; len];
    
    let mut len_prev = 0; // 前一个LPS值
    let mut i = 1;
    
    while i < len {
        if pattern[i] == pattern[len_prev] {
            len_prev += 1;
            lps[i] = len_prev;
            i += 1;
        } else {
            if len_prev != 0 {
                len_prev = lps[len_prev - 1];
            } else {
                lps[i] = 0;
                i += 1;
            }
        }
    }
    
    lps
}
```

#### 4.3.3 Boyer-Moore算法

**定义 4.3.4 (Boyer-Moore算法)** Boyer-Moore算法是一种高效的字符串搜索算法，使用"坏字符"和"好后缀"两种启发式规则来加速搜索。

**定理 4.3.3 (Boyer-Moore复杂度)** Boyer-Moore算法的平均时间复杂度为O(n/m)，最坏情况为O(n×m)。

Rust实现（简化版，只使用坏字符规则）:

```rust
pub fn boyer_moore_search(text: &str, pattern: &str) -> Vec<usize> {
    let text_chars: Vec<char> = text.chars().collect();
    let pattern_chars: Vec<char> = pattern.chars().collect();
    
    let mut matches = Vec::new();
    
    if pattern_chars.is_empty() || pattern_chars.len() > text_chars.len() {
        return matches;
    }
    
    let text_len = text_chars.len();
    let pattern_len = pattern_chars.len();
    
    // 构建坏字符表
    let mut bad_char = vec![pattern_len; 256]; // 假设ASCII字符集
    
    for i in 0..pattern_len - 1 {
        bad_char[pattern_chars[i] as usize] = pattern_len - 1 - i;
    }
    
    let mut i = pattern_len - 1;
    
    while i < text_len {
        let mut j = pattern_len - 1;
        let mut k = i;
        
        // 从右向左比较
        while j >= 0 && text_chars[k] == pattern_chars[j] {
            if j == 0 {
                matches.push(k);
                break;
            }
            j -= 1;
            k -= 1;
        }
        
        // 移动模式串
        let shift = if j >= 0 {
            let bc = bad_char[text_chars[k] as usize];
            if bc > pattern_len - j {
                bc
            } else {
                pattern_len - j
            }
        } else {
            1
        };
        
        i += shift;
    }
    
    matches
}
```

## 5. 图论算法

### 5.1 遍历算法

图的遍历算法已在2.3.2节中介绍。这里补充另一个重要的遍历算法：拓扑排序。

#### 5.1.1 拓扑排序

**定义 5.1.1 (拓扑排序)** 拓扑排序是有向无环图(DAG)的顶点排序，使得对于每条有向边(u, v)，顶点u在排序中都在v之前。

**定理 5.1.1 (拓扑排序存在性)** 拓扑排序存在当且仅当图是有向无环图。

**定理 5.1.2 (拓扑排序唯一性)** 若图中所有顶点间都存在路径，则拓扑排序唯一；否则可能有多个有效的拓扑排序。

Rust实现:

```rust
pub fn topological_sort(graph: &GraphList) -> Option<Vec<usize>> {
    let n = graph.adj_lists.len();
    let mut in_degree = vec![0; n];
    
    // 计算每个顶点的入度
    for adj_list in &graph.adj_lists {
        for &v in adj_list {
            in_degree[v] += 1;
        }
    }
    
    // 将所有入度为0的顶点放入队列
    let mut queue = std::collections::VecDeque::new();
    for (v, &degree) in in_degree.iter().enumerate() {
        if degree == 0 {
            queue.push_back(v);
        }
    }
    
    let mut result = Vec::with_capacity(n);
    
    // 不断删除入度为0的顶点
    while let Some(u) = queue.pop_front() {
        result.push(u);
        
        // 更新相邻顶点的入度
        for &v in graph.neighbors(u) {
            in_degree[v] -= 1;
            if in_degree[v] == 0 {
                queue.push_back(v);
            }
        }
    }
    
    // 如果结果中的顶点数小于图的顶点数，则存在环
    if result.len() == n {
        Some(result)
    } else {
        None
    }
}
```

### 5.2 最短路径算法

**定义 5.2.1 (最短路径)** 最短路径是图中两个顶点之间权重和最小的路径。

#### 5.2.1 Dijkstra算法

**定义 5.2.2 (Dijkstra算法)** Dijkstra算法是求解单源最短路径问题的贪心算法，适用于所有边权重都为非负的图。

**定理 5.2.1 (Dijkstra正确性)** 当所有边权重非负时，Dijkstra算法能正确找到单源最短路径。

Rust实现:

```rust
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Reverse;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct State {
    cost: Reverse<usize>,
    vertex: usize,
}

pub fn dijkstra(graph: &[Vec<(usize, usize)>], start: usize) -> Vec<Option<usize>> {
    let n = graph.len();
    let mut dist = vec![None; n]; // 距离初始化为无穷大
    dist[start] = Some(0);
    
    let mut pq = BinaryHeap::new();
    pq.push(State { cost: Reverse(0), vertex: start });
    
    while let Some(State { cost: Reverse(cost), vertex }) = pq.pop() {
        // 已找到更短的路径
        if let Some(d) = dist[vertex] {
            if cost > d {
                continue;
            }
        }
        
        // 遍历相邻顶点
        for &(next, weight) in &graph[vertex] {
            let next_cost = cost + weight;
            
            if dist[next].map_or(true, |d| next_cost < d) {
                dist[next] = Some(next_cost);
                pq.push(State { cost: Reverse(next_cost), vertex: next });
            }
        }
    }
    
    dist
}
```

#### 5.2.2 Bellman-Ford算法

**定义 5.2.3 (Bellman-Ford算法)** Bellman-Ford算法是求解单源最短路径问题的动态规划算法，适用于包含负权边的图，并能检测负权环。

**定理 5.2.2 (Bellman-Ford复杂度)** Bellman-Ford算法的时间复杂度为O(V×E)，其中V是顶点数，E是边数。

Rust实现:

```rust
pub fn bellman_ford(graph: &[Vec<(usize, isize)>], start: usize) -> Option<Vec<Option<isize>>> {
    let n = graph.len();
    let mut dist = vec![None; n];
    dist[start] = Some(0);
    
    // 最多需要n-1次迭代
    for _ in 0..n-1 {
        let mut updated = false;
        
        // 遍历所有边
        for u in 0..n {
            if let Some(d_u) = dist[u] {
                for &(v, weight) in &graph[u] {
                    let new_dist = d_u + weight;
                    if dist[v].map_or(true, |d_v| new_dist < d_v) {
                        dist[v] = Some(new_dist);
                        updated = true;
                    }
                }
            }
        }
        
        // 如果没有更新，提前终止
        if !updated {
            break;
        }
    }
    
    // 检测负权环
    for u in 0..n {
        if let Some(d_u) = dist[u] {
            for &(v, weight) in &graph[u] {
                if let Some(d_v) = dist[v] {
                    if d_u + weight < d_v {
                        // 存在负权环
                        return None;
                    }
                }
            }
        }
    }
    
    Some(dist)
}
```

#### 5.2.3 Floyd-Warshall算法

**定义 5.2.4 (Floyd-Warshall算法)** Floyd-Warshall算法是求解所有顶点对之间最短路径的动态规划算法。

**定理 5.2.3 (Floyd-Warshall复杂度)** Floyd-Warshall算法的时间复杂度为O(V³)，其中V是顶点数。

Rust实现:

```rust
pub fn floyd_warshall(graph: &[Vec<Option<isize>>]) -> Vec<Vec<Option<isize>>> {
    let n = graph.len();
    let mut dist = graph.to_vec();
    
    // 初始化对角线
    for i in 0..n {
        dist[i][i] = Some(0);
    }
    
    // 动态规划
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if let (Some(d_ik), Some(d_kj)) = (dist[i][k], dist[k][j]) {
                    let new_dist = d_ik + d_kj;
                    if dist[i][j].map_or(true, |d_ij| new_dist < d_ij) {
                        dist[i][j] = Some(new_dist);
                    }
                }
            }
        }
    }
    
    dist
}
```

### 5.3 最小生成树

**定义 5.3.1 (最小生成树)** 最小生成树是带权无向图的一个子图，包含所有顶点且权重和最小的树。

#### 5.3.1 Prim算法

**定义 5.3.2 (Prim算法)** Prim算法是一种贪心算法，通过每次选择与当前树相连的最小权重边来构建最小生成树。

**定理 5.3.1 (Prim正确性)** Prim算法能正确找到最小生成树。

Rust实现:

```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

pub fn prim(graph: &[Vec<(usize, usize)>]) -> Option<Vec<(usize, usize)>> {
    if graph.is_empty() {
        return None;
    }
    
    let n = graph.len();
    let mut in_mst = vec![false; n];
    let mut mst_edges = Vec::new();
    let mut pq = BinaryHeap::new();
    
    // 从顶点0开始
    in_mst[0] = true;
    
    // 添加所有与顶点0相邻的边
    for &(v, weight) in &graph[0] {
        pq.push(Reverse((weight, 0, v)));
    }
    
    // 选择n-1条边
    while let Some(Reverse((weight, u, v))) = pq.pop() {
        if in_mst[v] {
            continue;
        }
        
        // 将v加入MST
        in_mst[v] = true;
        mst_edges.push((u, v));
        
        // 添加所有与v相邻的边
        for &(next, edge_weight) in &graph[v] {
            if !in_mst[next] {
                pq.push(Reverse((edge_weight, v, next)));
            }
        }
    }
    
    // 检查是否所有顶点都在MST中
    if mst_edges.len() == n - 1 {
        Some(mst_edges)
    } else {
        None // 图不连通
    }
}
```

#### 5.3.2 Kruskal算法

**定义 5.3.3 (Kruskal算法)** Kruskal算法是一种贪心算法，按权重递增顺序处理边，若不形成环则加入最小生成树。

**定理 5

**定理 5.3.2 (Kruskal正确性)** Kruskal算法能正确找到最小生成树。

Rust实现:

```rust
// 并查集实现
struct DisjointSet {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl DisjointSet {
    fn new(size: usize) -> Self {
        let mut parent = Vec::with_capacity(size);
        for i in 0..size {
            parent.push(i);
        }
        DisjointSet {
            parent,
            rank: vec![0; size],
        }
    }
    
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    fn union(&mut self, x: usize, y: usize) {
        let root_x = self.find(x);
        let root_y = self.find(y);
        
        if root_x == root_y {
            return;
        }
        
        if self.rank[root_x] < self.rank[root_y] {
            self.parent[root_x] = root_y;
        } else {
            self.parent[root_y] = root_x;
            if self.rank[root_x] == self.rank[root_y] {
                self.rank[root_x] += 1;
            }
        }
    }
}

pub fn kruskal(n: usize, edges: &[(usize, usize, usize)]) -> Vec<(usize, usize, usize)> {
    // 边：(u, v, weight)
    let mut sorted_edges = edges.to_vec();
    sorted_edges.sort_by_key(|e| e.2);
    
    let mut disjoint_set = DisjointSet::new(n);
    let mut mst = Vec::new();
    
    for &(u, v, weight) in &sorted_edges {
        if disjoint_set.find(u) != disjoint_set.find(v) {
            disjoint_set.union(u, v);
            mst.push((u, v, weight));
        }
    }
    
    mst
}
```

### 5.4 网络流算法

**定义 5.4.1 (网络流)** 网络流是指在有向图中，从源点到汇点的流量分配，满足容量限制和流量守恒。

#### 5.4.1 Ford-Fulkerson算法

**定义 5.4.2 (Ford-Fulkerson算法)** Ford-Fulkerson算法是一种通过迭代寻找增广路径来计算最大流的方法。

**定理 5.4.1 (最大流最小割定理)** 在一个网络中，最大流的值等于最小割的容量。

Rust实现:

```rust
pub fn ford_fulkerson(graph: &[Vec<(usize, i32)>], source: usize, sink: usize) -> i32 {
    let n = graph.len();
    
    // 构建残余网络
    let mut residual_graph = vec![vec![(0, 0); 0]; n];
    
    // 初始化残余网络
    for (u, edges) in graph.iter().enumerate() {
        for &(v, capacity) in edges {
            // 正向边
            residual_graph[u].push((v, capacity));
            // 反向边（初始容量为0）
            residual_graph[v].push((u, 0));
        }
    }
    
    // 为每条边存储在残余网络中的索引
    let mut edge_indices = vec![vec![0; n]; n];
    for u in 0..n {
        for (i, &(v, _)) in residual_graph[u].iter().enumerate() {
            edge_indices[u][v] = i;
        }
    }
    
    let mut max_flow = 0;
    
    // 寻找增广路径
    loop {
        let mut visited = vec![false; n];
        let mut path = vec![0; n];
        
        // 使用BFS寻找增广路径
        if !bfs(&residual_graph, source, sink, &mut visited, &mut path) {
            break;
        }
        
        // 找到路径上的最小残余容量
        let mut path_flow = i32::MAX;
        let mut current = sink;
        
        while current != source {
            let prev = path[current];
            let edge_idx = edge_indices[prev][current];
            path_flow = path_flow.min(residual_graph[prev][edge_idx].1);
            current = prev;
        }
        
        // 更新残余容量
        current = sink;
        while current != source {
            let prev = path[current];
            let forward_idx = edge_indices[prev][current];
            let backward_idx = edge_indices[current][prev];
            
            residual_graph[prev][forward_idx].1 -= path_flow;
            residual_graph[current][backward_idx].1 += path_flow;
            
            current = prev;
        }
        
        max_flow += path_flow;
    }
    
    max_flow
}

fn bfs(
    graph: &[Vec<(usize, i32)>],
    source: usize,
    sink: usize,
    visited: &mut [bool],
    path: &mut [usize],
) -> bool {
    let mut queue = std::collections::VecDeque::new();
    visited[source] = true;
    queue.push_back(source);
    
    while let Some(u) = queue.pop_front() {
        for (i, &(v, capacity)) in graph[u].iter().enumerate() {
            if !visited[v] && capacity > 0 {
                visited[v] = true;
                path[v] = u;
                queue.push_back(v);
                
                if v == sink {
                    return true;
                }
            }
        }
    }
    
    false
}
```

#### 5.4.2 Edmonds-Karp算法

**定义 5.4.3 (Edmonds-Karp算法)** Edmonds-Karp算法是Ford-Fulkerson算法的一种实现，使用BFS寻找最短增广路径。

**定理 5.4.2 (Edmonds-Karp复杂度)** Edmonds-Karp算法的时间复杂度为O(V×E²)，其中V是顶点数，E是边数。

Edmonds-Karp算法实现与Ford-Fulkerson类似，只是固定使用BFS寻找增广路径。

### 5.5 二分图算法

**定义 5.5.1 (二分图)** 二分图是一种可以将顶点分为两个不相交集合的图，使得每条边的两个端点分别属于不同集合。

#### 5.5.1 二分图检测

**定理 5.5.1 (二分图特性)** 一个图是二分图当且仅当它不包含奇数长度的环。

Rust实现:

```rust
pub fn is_bipartite(graph: &[Vec<usize>]) -> bool {
    let n = graph.len();
    let mut colors = vec![None; n];
    
    for start in 0..n {
        if colors[start].is_none() {
            // 对每个未染色的连通分量进行BFS着色
            if !bfs_color(graph, start, &mut colors) {
                return false;
            }
        }
    }
    
    true
}

fn bfs_color(graph: &[Vec<usize>], start: usize, colors: &mut [Option<bool>]) -> bool {
    let mut queue = std::collections::VecDeque::new();
    colors[start] = Some(true);
    queue.push_back(start);
    
    while let Some(u) = queue.pop_front() {
        for &v in &graph[u] {
            if colors[v].is_none() {
                // 给相邻顶点染相反的颜色
                colors[v] = Some(!colors[u].unwrap());
                queue.push_back(v);
            } else if colors[v] == colors[u] {
                // 相邻顶点颜色相同，不是二分图
                return false;
            }
        }
    }
    
    true
}
```

#### 5.5.2 最大二分匹配

**定义 5.5.2 (二分匹配)** 二分匹配是二分图中的一组边，其中任意两条边不共享端点。

**定义 5.5.3 (最大二分匹配)** 最大二分匹配是指匹配边数最多的二分匹配。

**定理 5.5.2 (König定理)** 在二分图中，最大匹配的大小等于最小顶点覆盖的大小。

Rust实现（使用匈牙利算法）:

```rust
pub fn maximum_bipartite_matching(graph: &[Vec<usize>], left_size: usize) -> Vec<Option<usize>> {
    let mut matching = vec![None; graph.len()];
    let mut visited = vec![false; left_size];
    
    // 尝试为每个左侧顶点找到匹配
    for u in 0..left_size {
        visited.fill(false);
        if dfs(graph, u, &mut matching, &mut visited) {
            // 增广路径找到
        }
    }
    
    matching
}

fn dfs(
    graph: &[Vec<usize>],
    u: usize,
    matching: &mut [Option<usize>],
    visited: &mut [bool],
) -> bool {
    visited[u] = true;
    
    // 尝试匹配右侧顶点
    for &v in &graph[u] {
        // 如果v未匹配，或者v的匹配可以找到增广路径
        if matching[v].is_none() || 
           (!visited[matching[v].unwrap()] && dfs(graph, matching[v].unwrap(), matching, visited)) {
            matching[v] = Some(u);
            return true;
        }
    }
    
    false
}
```

## 6. 数值算法

### 6.1 基本数值算法

#### 6.1.1 最大公约数与最小公倍数

**定义 6.1.1 (最大公约数)** 两个整数的最大公约数(GCD)是能够同时整除两个数的最大正整数。

**定义 6.1.2 (最小公倍数)** 两个整数的最小公倍数(LCM)是能够被两个数整除的最小正整数。

**定理 6.1.1 (欧几里得算法)** 对于正整数a和b，gcd(a,b) = gcd(b, a mod b)，当b=0时，gcd(a,0) = a。

Rust实现:

```rust
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

pub fn lcm(a: u64, b: u64) -> u64 {
    a / gcd(a, b) * b
}
```

#### 6.1.2 素数测试与生成

**定义 6.1.3 (素数)** 素数是指大于1的自然数，除了1和它本身外没有其他因数。

**定理 6.1.2 (埃拉托斯特尼筛法)** 埃拉托斯特尼筛法是一种高效生成小于n的所有素数的算法。

Rust实现:

```rust
pub fn sieve_of_eratosthenes(n: usize) -> Vec<usize> {
    let mut is_prime = vec![true; n + 1];
    is_prime[0] = false;
    is_prime[1] = false;
    
    let mut p = 2;
    while p * p <= n {
        if is_prime[p] {
            let mut i = p * p;
            while i <= n {
                is_prime[i] = false;
                i += p;
            }
        }
        p += 1;
    }
    
    let mut primes = Vec::new();
    for i in 2..=n {
        if is_prime[i] {
            primes.push(i);
        }
    }
    
    primes
}
```

#### 6.1.3 快速幂

**定义 6.1.4 (快速幂)** 快速幂是一种高效计算a^n的算法，基于二进制分解指数。

**定理 6.1.3 (快速幂复杂度)** 快速幂算法的时间复杂度为O(log n)。

Rust实现:

```rust
pub fn pow_mod(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1;
    base %= modulus;
    
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exp >>= 1;
    }
    
    result
}
```

### 6.2 数值计算

#### 6.2.1 牛顿法求根

**定义 6.2.1 (牛顿法)** 牛顿法是一种迭代求解方程f(x)=0的方法，使用切线逼近。

**定理 6.2.1 (牛顿法收敛性)** 若f(x)在根附近满足一定条件，且初值足够接近，则牛顿法具有二次收敛性。

Rust实现:

```rust
pub fn newton_sqrt(n: f64, epsilon: f64) -> f64 {
    if n < 0.0 {
        panic!("Cannot compute square root of negative number");
    }
    
    if n == 0.0 {
        return 0.0;
    }
    
    let mut x = n; // 初始猜测值
    
    loop {
        let next_x = 0.5 * (x + n / x);
        
        if (next_x - x).abs() < epsilon {
            return next_x;
        }
        
        x = next_x;
    }
}
```

#### 6.2.2 数值积分

**定义 6.2.2 (数值积分)** 数值积分是近似计算定积分值的方法，常用方法包括矩形法、梯形法和辛普森法。

**定理 6.2.2 (梯形法误差)** 梯形法的误差为O(h²)，其中h是子区间宽度。

Rust实现(梯形法):

```rust
pub fn trapezoidal_integration<F>(f: F, a: f64, b: f64, n: usize) -> f64
where
    F: Fn(f64) -> f64,
{
    let h = (b - a) / (n as f64);
    let mut sum = 0.5 * (f(a) + f(b));
    
    for i in 1..n {
        let x = a + (i as f64) * h;
        sum += f(x);
    }
    
    sum * h
}
```

### 6.3 矩阵运算

#### 6.3.1 矩阵乘法

**定义 6.3.1 (矩阵乘法)** 若A是m×n矩阵，B是n×p矩阵，则C=A×B是m×p矩阵，其中C[i,j] = ∑(k=0 to n-1) A[i,k]×B[k,j]。

Rust实现:

```rust
pub fn matrix_multiply(a: &[Vec<f64>], b: &[Vec<f64>]) -> Option<Vec<Vec<f64>>> {
    if a.is_empty() || b.is_empty() || a[0].len() != b.len() {
        return None; // 不兼容的矩阵尺寸
    }
    
    let m = a.len();
    let n = a[0].len();
    let p = b[0].len();
    
    let mut result = vec![vec![0.0; p]; m];
    
    for i in 0..m {
        for j in 0..p {
            for k in 0..n {
                result[i][j] += a[i][k] * b[k][j];
            }
        }
    }
    
    Some(result)
}
```

#### 6.3.2 高斯消元

**定义 6.3.2 (高斯消元)** 高斯消元是一种求解线性方程组的算法，通过行运算将系数矩阵转化为上三角或对角形式。

**定理 6.3.1 (高斯消元复杂度)** 高斯消元法的时间复杂度为O(n³)，其中n是未知数的个数。

Rust实现:

```rust
pub fn gaussian_elimination(a: &mut [Vec<f64>], b: &mut [f64]) -> Option<Vec<f64>> {
    let n = a.len();
    if n == 0 || a[0].len() != n || b.len() != n {
        return None; // 不兼容的矩阵与向量尺寸
    }
    
    // 前向消元
    for i in 0..n {
        // 找到主元
        let mut max_row = i;
        for j in i+1..n {
            if a[j][i].abs() > a[max_row][i].abs() {
                max_row = j;
            }
        }
        
        // 如果主元太小，方程组可能无解或有无穷多解
        if a[max_row][i].abs() < 1e-10 {
            return None;
        }
        
        // 交换行
        if max_row != i {
            a[i].swap_with_slice(&mut a[max_row]);
            b.swap(i, max_row);
        }
        
        // 消元
        for j in i+1..n {
            let factor = a[j][i] / a[i][i];
            b[j] -= factor * b[i];
            
            for k in i..n {
                a[j][k] -= factor * a[i][k];
            }
        }
    }
    
    // 回代
    let mut x = vec![0.0; n];
    for i in (0..n).rev() {
        let mut sum = b[i];
        for j in i+1..n {
            sum -= a[i][j] * x[j];
        }
        x[i] = sum / a[i][i];
    }
    
    Some(x)
}
```

## 7. 密码学算法

### 7.1 散列算法

#### 7.1.1 SHA-256

**定义 7.1.1 (SHA-256)** SHA-256是SHA-2家族中的一种密码散列函数，生成256位（32字节）的散列值。

Rust实现（使用外部库）:

```rust
use sha2::{Sha256, Digest};

pub fn sha256_hash(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    
    let mut output = [0u8; 32];
    output.copy_from_slice(&result);
    output
}
```

#### 7.1.2 HMAC

**定义 7.1.2 (HMAC)** HMAC是一种基于哈希函数的消息认证码，用于验证消息的完整性和真实性。

Rust实现（使用外部库）:

```rust
use hmac::{Hmac, Mac, NewMac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

pub fn hmac_sha256(key: &[u8], message: &[u8]) -> Vec<u8> {
    let mut mac = HmacSha256::new_varkey(key)
        .expect("HMAC can take key of any size");
    mac.update(message);
    let result = mac.finalize();
    result.into_bytes().to_vec()
}
```

### 7.2 对称加密

#### 7.2.1 AES

**定义 7.2.1 (AES)** AES是一种对称加密算法，以块为单位进行加密，支持128、192和256位密钥。

Rust实现（使用外部库，AES-GCM模式）:

```rust
use aes_gcm::{
    aead::{Aead, KeyInit, OsRng},
    Aes256Gcm, Nonce
};
use rand::RngCore;

pub fn aes_gcm_encrypt(key: &[u8; 32], plaintext: &[u8]) -> Result<(Vec<u8>, [u8; 12]), Box<dyn std::error::Error>> {
    let cipher = Aes256Gcm::new_from_slice(key)?;
    
    // 生成随机nonce
    let mut nonce_bytes = [0u8; 12];
    OsRng.fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);
    
    // 加密
    let ciphertext = cipher.encrypt(nonce, plaintext.as_ref())?;
    
    Ok((ciphertext, nonce_bytes))
}

pub fn aes_gcm_decrypt(key: &[u8; 32], ciphertext: &[u8], nonce_bytes: &[u8; 12]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let cipher = Aes256Gcm::new_from_slice(key)?;
    let nonce = Nonce::from_slice(nonce_bytes);
    
    // 解密
    let plaintext = cipher.decrypt(nonce, ciphertext.as_ref())?;
    
    Ok(plaintext)
}
```

### 7.3 非对称加密

#### 7.3.1 RSA

**定义 7.3.1 (RSA)** RSA是一种非对称加密算法，基于大质数分解的困难性。

**定理 7.3.1 (RSA原理)** RSA的安全性基于大整数因数分解的计算复杂度，已知模数n=p×q难以分解出质数p和q。

Rust实现（使用外部库）:

```rust
use rsa::{
    PublicKey, RsaPrivateKey, RsaPublicKey, PaddingScheme,
    pkcs8::{EncodePublicKey, EncodePrivateKey}
};
use rand::rngs::OsRng;

pub fn generate_rsa_keypair(bits: usize) -> Result<(RsaPublicKey, RsaPrivateKey), Box<dyn std::error::Error>> {
    let mut rng = OsRng;
    let private_key = RsaPrivateKey::new(&mut rng, bits)?;
    let public_key = RsaPublicKey::from(&private_key);
    
    Ok((public_key, private_key))
}

pub fn rsa_encrypt(public_key: &RsaPublicKey, data: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut rng = OsRng;
    let padding = PaddingScheme::new_oaep_sha256();
    let encrypted_data = public_key.encrypt(&mut rng, padding, data)?;
    
    Ok(encrypted_data)
}

pub fn rsa_decrypt(private_key: &RsaPrivateKey, encrypted_data: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let padding = PaddingScheme::new_oaep_sha256();
    let decrypted_data = private_key.decrypt(padding, encrypted_data)?;
    
    Ok(decrypted_data)
}
```

## 8. 并行与并发算法

### 8.1 并行基础算法

#### 8.1.1 并行求和

**定义 8.1.1 (并行求和)** 并行求和是利用多线程或多处理器同时处理数据子集，然后合并结果的计算方法。

Rust实现:

```rust
use rayon::prelude::*;

pub fn parallel_sum(data: &[i32]) -> i32 {
    data.par_iter().sum()
}

pub fn parallel_map_reduce<T, F, G>(data: &[T], map_fn: F, reduce_fn: G) -> T
where
    T: Send + Sync + Clone,
    F: Fn(&T) -> T + Send + Sync,
    G: Fn(T, T) -> T + Send + Sync,
{
    data.par_iter()
        .map(map_fn)
        .reduce_with(|a, b| reduce_fn(a, b))
        .unwrap_or_else(|| panic!("Empty data"))
}
```

#### 8.1.2 并行排序

**定义 8.1.2 (并行排序)** 并行排序是利用多个处理单元同时进行排序操作的算法。

Rust实现（使用rayon库）:

```rust
use rayon::prelude::*;

pub fn parallel_sort<T: Ord + Send>(data: &mut [T]) {
    data.par_sort();
}

pub fn parallel_sort_by<T, F>(data: &mut [T], compare: F)
where
    T: Send,
    F: Fn(&T, &T) -> std::cmp::Ordering + Send + Sync,
{
    data.par_sort_by(compare);
}
```

### 8.2 并发数据结构

#### 8.2.1 无锁栈

**定义 8.2.1 (无锁栈)** 无锁栈是一种不使用互斥锁而通过原子操作实现线程安全的栈数据结构。

Rust实现:

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        LockFreeStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }
    
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));
        
        loop {
            let current_head = self.head.load(Ordering::Relaxed);
            unsafe {
                (*new_node).next = current_head;
            }
            
            // CAS操作确保原子性
            if self.head.compare_exchange(
                current_head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed
            ).is_ok() {
                break;
            }
        }
    }
    
    pub fn pop(&self) -> Option<T> {
        loop {
            let current_head = self.head.load(Ordering::Acquire);
            if current_head.is_null() {
                return None;
            }
            
            let next;
            unsafe {
                next = (*current_head).next;
            }
            
            // CAS操作确保原子性
            if self.head.compare_exchange(
                current_head,
                next,
                Ordering::Release,
                Ordering::Relaxed
            ).is_ok() {
                unsafe {
                    let data = Box::from_raw(current_head).data;
                    return Some(data);
                }
            }
        }
    }
}

impl<T> Drop for LockFreeStack<T> {
    fn drop(&mut self) {
        let mut current = self.head.load(Ordering::Relaxed);
        while !current.is_null() {
            unsafe {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
    }
}
```

#### 8.2.2 读写锁

**定义 8.2.2 (读写锁)** 读写锁是一种同步机制，允许多个线程同时读取共享资源，但写入时需要独占访问。

Rust实现（使用标准库）:

```rust
use std::sync::{Arc, RwLock};

pub struct SharedData<T> {
    data: Arc<RwLock<T>>,
}

impl<T: Clone> SharedData<T> {
    pub fn new(initial: T) -> Self {
        SharedData {
            data: Arc::new(RwLock::new(initial)),
        }
    }
    
    pub fn read(&self) -> Result<T, String> {
        match self.data.read() {
            Ok(guard) => Ok(guard.clone()),
            Err(_) => Err("读取锁被中毒".to_string()),
        }
    }
    
    pub fn write(&self, new_value: T) -> Result<(), String> {
        match self.data.write() {
            Ok(mut guard) => {
                *guard = new_value;
                Ok(())
            },
            Err(_) => Err("写入锁被中毒".to_string()),
        }
    }
    
    // 创建一个克隆，可用于在其他线程中使用
    pub fn clone(&self) -> Self {
        SharedData {
            data: Arc::clone(&self.data),
        }
    }
}
```

### 8.3 工作窃取算法

**定义 8.3.1 (工作窃取)** 工作窃取是一种用于负载均衡的并行计算技术，空闲线程可以"窃取"其他线程队列中的任务。

**定理 8.3.1 (工作窃取的效率)** 在理想条件下，工作窃取可以实现接近线性的加速比。

Rust实现（概念性框架）:

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;

pub struct WorkStealingPool {
    queues: Vec<Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>>,
    threads: Vec<thread::JoinHandle<()>>,
}

impl WorkStealingPool {
    pub fn new(num_threads: usize) -> Self {
        let mut queues = Vec::with_capacity(num_threads);
        for _ in 0..num_threads {
            queues.push(Arc::new(Mutex::new(VecDeque::new())));
        }
        
        let mut threads = Vec::with_capacity(num_threads);
        let queues_arc = Arc::new(queues.clone());
        
        for id in 0..num_threads {
            let thread_queues = Arc::clone(&queues_arc);
            let thread = thread::spawn(move || {
                let mut rng = rand::thread_rng();
                
                loop {
                    // 尝试从自己的队列获取任务
                    let task = {
                        let mut queue = thread_queues[id].lock().unwrap();
                        queue.pop_front()
                    };
                    
                    match task {
                        Some(task) => {
                            task(); // 执行任务
                        },
                        None => {
                            // 尝试窃取其他队列的任务
                            let victim_id = (id + 1) % num_threads; // 简化：总是尝试窃取下一个队列
                            let stolen = {
                                let mut victim_queue = thread_queues[victim_id].lock().unwrap();
                                victim_queue.pop_back() // 从尾部窃取
                            };
                            
                            if let Some(task) = stolen {
                                task(); // 执行窃取的任务
                            } else {
                                thread::yield_now(); // 无任务可窃取，让出CPU
                            }
                        }
                    }
                }
            });
            
            threads.push(thread);
        }
        
        WorkStealingPool {
            queues,
            threads,
        }
    }
    
    pub fn submit<F>(&self, task: F, worker_hint: usize)
    where
        F: FnOnce() + Send + 'static,
    {
        let queue_id = worker_hint % self.queues.len();
        let mut queue = self.queues[queue_id].lock().unwrap();
        queue.push_back(Box::new(task));
    }
}
```

## 9. 高级算法范式

### 9.1 贪心算法

**定义 9.1.1 (贪心算法)** 贪心算法是一种在每一步选择中都采取当前状态下最优选择的算法策略。

**定理 9.1.1 (贪心算法的适用条件)** 贪心算法在具有最优子结构和贪心选择性质的问题上能得到全局最优解。

Rust实现（活动选择问题）:

```rust
pub fn activity_selection(start: &[usize], finish: &[usize]) -> Vec<usize> {
    if start.len() != finish.len() || start.is_empty() {
        return Vec::new();
    }
    
    // 按结束时间排序活动
    let mut activities: Vec<(usize, usize, usize)> = start.iter()
        .zip(finish.iter())
        .enumerate()
        .map(|(i, (&s, &f))| (i, s, f))
        .collect();
    
    activities.sort_by_key(|&(_, _, f)| f);
    
    let mut selected = vec![activities[0].0];
    let mut last_finish = activities[0].2;
    
    for &(idx, start, finish) in activities.iter().skip(1) {
        if start >= last_finish {
            selected.push(idx);
            last_finish = finish;
        }
    }
    
    selected
}
```

### 9.2 动态规划

**定义 9.2.1 (动态规划)** 动态规划是一种通过将复杂问题分解为子问题并存储子问题结果以避免重复计算的算法策略。

**定理 9.2.1 (动态规划的适用条件)** 动态规划适用于具有重叠子问题和最优子结构性质的问题。

Rust实现（0-1背包问题）:

```rust
pub fn knapsack(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    if n == 0 || n != values.len() {
        return 0;
    }
    
    // 创建DP表
    let mut dp = vec![vec![0; capacity + 1]; n + 1];
    
    for i in 1..=n {
        for w in 0..=capacity {
            if weights[i-1] <= w {
                // 可以选择当前物品
                dp[i][w] = dp[i-1][w].max(dp[i-1][w - weights[i-1]] + values[i-1]);
            } else {
                // 无法选

```rust
                // 无法选择当前物品
                dp[i][w] = dp[i-1][w];
            }
        }
    }
    
    dp[n][capacity]
}
```

### 9.3 分治算法

**定义 9.3.1 (分治算法)** 分治算法是一种将问题分解为子问题，独立解决子问题后合并结果的算法策略。

**定理 9.3.1 (分治复杂度)** 若问题规模为n，被分成a个规模为n/b的子问题，每次分解和合并的复杂度为O(n^d)，则总时间复杂度为O(n^d)（若a<b^d）、O(n^d·log n)（若a=b^d）或O(n^(logb a))（若a>b^d）。

Rust实现（最近点对问题）:

```rust
use std::cmp::Ordering;

#[derive(Clone, Copy, Debug)]
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    fn distance(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        (dx * dx + dy * dy).sqrt()
    }
}

pub fn closest_pair(points: &[Point]) -> Option<(Point, Point, f64)> {
    if points.len() < 2 {
        return None;
    }
    
    // 按x坐标排序点
    let mut sorted_x = points.to_vec();
    sorted_x.sort_by(|a, b| a.x.partial_cmp(&b.x).unwrap_or(Ordering::Equal));
    
    // 调用分治算法
    closest_pair_recursive(&sorted_x)
}

fn closest_pair_recursive(points_sorted_x: &[Point]) -> Option<(Point, Point, f64)> {
    let n = points_sorted_x.len();
    
    // 基本情况
    if n <= 3 {
        return brute_force(points_sorted_x);
    }
    
    // 分割点集
    let mid = n / 2;
    let mid_point = points_sorted_x[mid];
    
    // 递归求解左右子问题
    let left_result = closest_pair_recursive(&points_sorted_x[..mid]);
    let right_result = closest_pair_recursive(&points_sorted_x[mid..]);
    
    // 合并阶段
    let (mut best_pair, mut min_dist) = match (left_result, right_result) {
        (Some((p1, p2, d1)), Some((p3, p4, d2))) => {
            if d1 <= d2 {
                ((p1, p2), d1)
            } else {
                ((p3, p4), d2)
            }
        },
        (Some((p1, p2, d)), None) => ((p1, p2), d),
        (None, Some((p1, p2, d))) => ((p1, p2), d),
        _ => return None,
    };
    
    // 检查跨越中线的点对
    let mut strip = Vec::new();
    for point in points_sorted_x {
        if (point.x - mid_point.x).abs() < min_dist {
            strip.push(*point);
        }
    }
    
    // 按y坐标排序
    strip.sort_by(|a, b| a.y.partial_cmp(&b.y).unwrap_or(Ordering::Equal));
    
    // 检查条带内的点对
    for i in 0..strip.len() {
        for j in i+1..strip.len() {
            if strip[j].y - strip[i].y >= min_dist {
                break; // 可提前终止
            }
            
            let dist = strip[i].distance(&strip[j]);
            if dist < min_dist {
                min_dist = dist;
                best_pair = (strip[i], strip[j]);
            }
        }
    }
    
    Some((best_pair.0, best_pair.1, min_dist))
}

fn brute_force(points: &[Point]) -> Option<(Point, Point, f64)> {
    if points.len() < 2 {
        return None;
    }
    
    let mut min_dist = f64::INFINITY;
    let mut closest_pair = (points[0], points[1]);
    
    for i in 0..points.len() {
        for j in i+1..points.len() {
            let dist = points[i].distance(&points[j]);
            if dist < min_dist {
                min_dist = dist;
                closest_pair = (points[i], points[j]);
            }
        }
    }
    
    Some((closest_pair.0, closest_pair.1, min_dist))
}
```

### 9.4 回溯算法

**定义 9.4.1 (回溯算法)** 回溯算法是一种通过试探并在不满足条件时回退的搜索算法，用于解决约束满足问题。

**定理 9.4.1 (回溯时间复杂度)** 回溯算法的最坏时间复杂度通常为O(b^d)，其中b是分支因子，d是树的深度。

Rust实现（N皇后问题）:

```rust
pub fn solve_n_queens(n: usize) -> Vec<Vec<String>> {
    let mut result = Vec::new();
    let mut board = vec![vec!['.'; n]; n];
    
    backtrack(&mut result, &mut board, 0, n);
    
    result
}

fn backtrack(result: &mut Vec<Vec<String>>, board: &mut Vec<Vec<char>>, row: usize, n: usize) {
    if row == n {
        // 找到一个有效解
        let solution = board.iter()
            .map(|row| row.iter().collect::<String>())
            .collect();
        result.push(solution);
        return;
    }
    
    for col in 0..n {
        if is_valid(board, row, col, n) {
            // 尝试在当前位置放置皇后
            board[row][col] = 'Q';
            
            // 递归处理下一行
            backtrack(result, board, row + 1, n);
            
            // 回溯，撤销选择
            board[row][col] = '.';
        }
    }
}

fn is_valid(board: &[Vec<char>], row: usize, col: usize, n: usize) -> bool {
    // 检查列冲突
    for i in 0..row {
        if board[i][col] == 'Q' {
            return false;
        }
    }
    
    // 检查左上对角线
    let mut i = row as isize - 1;
    let mut j = col as isize - 1;
    while i >= 0 && j >= 0 {
        if board[i as usize][j as usize] == 'Q' {
            return false;
        }
        i -= 1;
        j -= 1;
    }
    
    // 检查右上对角线
    let mut i = row as isize - 1;
    let mut j = col as isize + 1;
    while i >= 0 && j < n as isize {
        if board[i as usize][j as usize] == 'Q' {
            return false;
        }
        i -= 1;
        j += 1;
    }
    
    true
}
```

### 9.5 随机化算法

**定义 9.5.1 (随机化算法)** 随机化算法使用随机数来决定算法的执行路径，有时能提供更高效或更简单的解决方案。

**定理 9.5.1 (随机化算法特点)** 随机化算法通常以概率保证正确性，或者以高概率提供近似解。

Rust实现（快速选择算法，寻找第k小元素）:

```rust
use rand::Rng;

pub fn randomized_quick_select<T: Ord + Copy>(arr: &mut [T], k: usize) -> Option<T> {
    if k == 0 || k > arr.len() {
        return None;
    }
    
    quick_select(arr, 0, arr.len() - 1, k - 1)
}

fn quick_select<T: Ord + Copy>(arr: &mut [T], left: usize, right: usize, k: usize) -> Option<T> {
    if left == right {
        return Some(arr[left]);
    }
    
    // 随机选择枢轴
    let pivot_idx = partition(arr, left, right);
    
    match k.cmp(&pivot_idx) {
        std::cmp::Ordering::Equal => Some(arr[k]),
        std::cmp::Ordering::Less => quick_select(arr, left, pivot_idx - 1, k),
        std::cmp::Ordering::Greater => quick_select(arr, pivot_idx + 1, right, k),
    }
}

fn partition<T: Ord + Copy>(arr: &mut [T], left: usize, right: usize) -> usize {
    // 随机选择枢轴
    let mut rng = rand::thread_rng();
    let pivot_idx = rng.gen_range(left..=right);
    arr.swap(pivot_idx, right);
    
    let pivot = arr[right];
    let mut i = left;
    
    for j in left..right {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, right);
    i
}
```

## 10. 机器学习算法

### 10.1 监督学习

#### 10.1.1 线性回归

**定义 10.1.1 (线性回归)** 线性回归是一种通过拟合特征的线性组合来预测连续目标变量的监督学习算法。

**定理 10.1.1 (线性回归最小二乘解)** 对于给定的特征矩阵X和目标向量y，线性回归参数的最小二乘解为β = (X'X)^(-1)X'y，其中X'表示X的转置。

Rust实现（梯度下降法求解线性回归）:

```rust
pub struct LinearRegression {
    weights: Vec<f64>,
    bias: f64,
}

impl LinearRegression {
    pub fn new() -> Self {
        LinearRegression {
            weights: Vec::new(),
            bias: 0.0,
        }
    }
    
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64], learning_rate: f64, epochs: usize) -> Result<(), String> {
        if x.is_empty() || y.is_empty() || x.len() != y.len() {
            return Err("数据不能为空且x与y的数量必须相同".to_string());
        }
        
        let n_samples = x.len();
        let n_features = x[0].len();
        
        // 初始化权重和偏置
        self.weights = vec![0.0; n_features];
        self.bias = 0.0;
        
        // 梯度下降优化
        for _ in 0..epochs {
            // 预测
            let predictions: Vec<f64> = x.iter()
                .map(|xi| self.predict_sample(xi))
                .collect();
            
            // 计算梯度
            let mut dw = vec![0.0; n_features];
            let mut db = 0.0;
            
            for i in 0..n_samples {
                let error = predictions[i] - y[i];
                
                // 权重梯度
                for j in 0..n_features {
                    dw[j] += error * x[i][j];
                }
                
                // 偏置梯度
                db += error;
            }
            
            // 更新参数
            for j in 0..n_features {
                self.weights[j] -= learning_rate * dw[j] / (n_samples as f64);
            }
            self.bias -= learning_rate * db / (n_samples as f64);
        }
        
        Ok(())
    }
    
    fn predict_sample(&self, x: &[f64]) -> f64 {
        let mut prediction = self.bias;
        for i in 0..self.weights.len() {
            prediction += self.weights[i] * x[i];
        }
        prediction
    }
    
    pub fn predict(&self, x: &[Vec<f64>]) -> Result<Vec<f64>, String> {
        if x.is_empty() || x[0].len() != self.weights.len() {
            return Err("输入特征数量与模型不匹配".to_string());
        }
        
        let predictions = x.iter()
            .map(|xi| self.predict_sample(xi))
            .collect();
        
        Ok(predictions)
    }
}
```

#### 10.1.2 决策树

**定义 10.1.2 (决策树)** 决策树是一种树状模型，通过一系列条件判断对数据进行分类或回归。

**定理 10.1.2 (信息增益)** 信息增益衡量特征分割前后信息熵的减少量，越高表示分割质量越好，公式为IG(S,A) = H(S) - ∑(|Sv|/|S|) H(Sv)，其中S是数据集，A是特征，H是信息熵。

Rust实现（简化版ID3决策树分类器）:

```rust
use std::collections::HashMap;

enum NodeType {
    Leaf { class: usize },
    Internal { feature: usize, threshold: f64, left: Box<DecisionNode>, right: Box<DecisionNode> },
}

struct DecisionNode {
    node_type: NodeType,
}

pub struct DecisionTreeClassifier {
    root: Option<DecisionNode>,
    max_depth: usize,
}

impl DecisionTreeClassifier {
    pub fn new(max_depth: usize) -> Self {
        DecisionTreeClassifier {
            root: None,
            max_depth,
        }
    }
    
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[usize]) -> Result<(), String> {
        if x.is_empty() || y.is_empty() || x.len() != y.len() {
            return Err("数据不能为空且x与y的数量必须相同".to_string());
        }
        
        self.root = Some(self.build_tree(x, y, 0));
        Ok(())
    }
    
    fn build_tree(&self, x: &[Vec<f64>], y: &[usize], depth: usize) -> DecisionNode {
        // 检查是否所有样本属于同一类别
        let mut class_count = HashMap::new();
        for &class in y {
            *class_count.entry(class).or_insert(0) += 1;
        }
        
        // 如果只有一个类别或达到最大深度，创建叶节点
        if class_count.len() == 1 || depth >= self.max_depth {
            let majority_class = class_count
                .into_iter()
                .max_by_key(|&(_, count)| count)
                .map(|(class, _)| class)
                .unwrap_or(0);
            
            return DecisionNode {
                node_type: NodeType::Leaf { class: majority_class },
            };
        }
        
        // 寻找最佳特征和阈值
        let (best_feature, best_threshold) = self.find_best_split(x, y);
        
        // 根据最佳特征和阈值分割数据
        let mut left_indices = Vec::new();
        let mut right_indices = Vec::new();
        
        for i in 0..x.len() {
            if x[i][best_feature] <= best_threshold {
                left_indices.push(i);
            } else {
                right_indices.push(i);
            }
        }
        
        // 如果无法有效分割，创建叶节点
        if left_indices.is_empty() || right_indices.is_empty() {
            let majority_class = class_count
                .into_iter()
                .max_by_key(|&(_, count)| count)
                .map(|(class, _)| class)
                .unwrap_or(0);
            
            return DecisionNode {
                node_type: NodeType::Leaf { class: majority_class },
            };
        }
        
        // 创建子树
        let left_x: Vec<Vec<f64>> = left_indices.iter().map(|&i| x[i].clone()).collect();
        let left_y: Vec<usize> = left_indices.iter().map(|&i| y[i]).collect();
        
        let right_x: Vec<Vec<f64>> = right_indices.iter().map(|&i| x[i].clone()).collect();
        let right_y: Vec<usize> = right_indices.iter().map(|&i| y[i]).collect();
        
        // 递归构建左右子树
        let left_subtree = self.build_tree(&left_x, &left_y, depth + 1);
        let right_subtree = self.build_tree(&right_x, &right_y, depth + 1);
        
        DecisionNode {
            node_type: NodeType::Internal {
                feature: best_feature,
                threshold: best_threshold,
                left: Box::new(left_subtree),
                right: Box::new(right_subtree),
            },
        }
    }
    
    fn find_best_split(&self, x: &[Vec<f64>], y: &[usize]) -> (usize, f64) {
        let n_features = x[0].len();
        let mut best_gini = f64::INFINITY;
        let mut best_feature = 0;
        let mut best_threshold = 0.0;
        
        for feature in 0..n_features {
            // 获取特征的所有唯一值
            let mut values: Vec<f64> = x.iter().map(|sample| sample[feature]).collect();
            values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            values.dedup();
            
            // 对每个可能的阈值计算基尼不纯度
            for i in 0..values.len() - 1 {
                let threshold = (values[i] + values[i + 1]) / 2.0;
                
                // 分割数据
                let mut left_y = Vec::new();
                let mut right_y = Vec::new();
                
                for (sample, &class) in x.iter().zip(y.iter()) {
                    if sample[feature] <= threshold {
                        left_y.push(class);
                    } else {
                        right_y.push(class);
                    }
                }
                
                // 计算加权基尼不纯度
                let n = y.len() as f64;
                let gini = (left_y.len() as f64 / n) * self.gini_impurity(&left_y) + 
                           (right_y.len() as f64 / n) * self.gini_impurity(&right_y);
                
                if gini < best_gini {
                    best_gini = gini;
                    best_feature = feature;
                    best_threshold = threshold;
                }
            }
        }
        
        (best_feature, best_threshold)
    }
    
    fn gini_impurity(&self, y: &[usize]) -> f64 {
        if y.is_empty() {
            return 0.0;
        }
        
        let mut class_count = HashMap::new();
        for &class in y {
            *class_count.entry(class).or_insert(0) += 1;
        }
        
        let n = y.len() as f64;
        let mut gini = 1.0;
        
        for &count in class_count.values() {
            let p = count as f64 / n;
            gini -= p * p;
        }
        
        gini
    }
    
    pub fn predict(&self, x: &[Vec<f64>]) -> Result<Vec<usize>, String> {
        match &self.root {
            Some(root) => {
                let predictions = x.iter()
                    .map(|sample| self.predict_sample(sample, root))
                    .collect();
                Ok(predictions)
            },
            None => Err("模型未训练".to_string()),
        }
    }
    
    fn predict_sample(&self, x: &[f64], node: &DecisionNode) -> usize {
        match &node.node_type {
            NodeType::Leaf { class } => *class,
            NodeType::Internal { feature, threshold, left, right } => {
                if x[*feature] <= *threshold {
                    self.predict_sample(x, left)
                } else {
                    self.predict_sample(x, right)
                }
            }
        }
    }
}
```

### 10.2 无监督学习

#### 10.2.1 K均值聚类

**定义 10.2.1 (K均值聚类)** K均值聚类是一种将数据分为K个簇的无监督学习算法，每个数据点被分配到距离最近的簇中心。

**定理 10.2.1 (K均值收敛性)** K均值算法总是收敛到一个局部最优解，但不保证全局最优。

Rust实现:

```rust
pub struct KMeans {
    k: usize,
    centroids: Vec<Vec<f64>>,
    max_iterations: usize,
}

impl KMeans {
    pub fn new(k: usize, max_iterations: usize) -> Self {
        KMeans {
            k,
            centroids: Vec::new(),
            max_iterations,
        }
    }
    
    pub fn fit(&mut self, x: &[Vec<f64>]) -> Result<(), String> {
        if x.is_empty() || self.k > x.len() {
            return Err("数据太少或k值太大".to_string());
        }
        
        let n_samples = x.len();
        let n_features = x[0].len();
        
        // 随机初始化中心点（简单起见，直接从样本中选择）
        let mut rng = rand::thread_rng();
        let mut indices: Vec<usize> = (0..n_samples).collect();
        indices.shuffle(&mut rng);
        
        self.centroids = indices[0..self.k]
            .iter()
            .map(|&idx| x[idx].clone())
            .collect();
        
        // K均值迭代
        for _ in 0..self.max_iterations {
            // 分配样本到最近的中心点
            let mut clusters: Vec<Vec<usize>> = vec![Vec::new(); self.k];
            
            for i in 0..n_samples {
                let cluster_idx = self.predict_sample(&x[i]);
                clusters[cluster_idx].push(i);
            }
            
            // 保存旧中心点，用于检查收敛
            let old_centroids = self.centroids.clone();
            
            // 更新中心点
            for (i, cluster) in clusters.iter().enumerate() {
                if cluster.is_empty() {
                    continue;
                }
                
                let mut new_centroid = vec![0.0; n_features];
                
                for &idx in cluster {
                    for j in 0..n_features {
                        new_centroid[j] += x[idx][j];
                    }
                }
                
                for j in 0..n_features {
                    new_centroid[j] /= cluster.len() as f64;
                }
                
                self.centroids[i] = new_centroid;
            }
            
            // 检查收敛
            if self.is_converged(&old_centroids) {
                break;
            }
        }
        
        Ok(())
    }
    
    fn is_converged(&self, old_centroids: &[Vec<f64>]) -> bool {
        for (old, current) in old_centroids.iter().zip(self.centroids.iter()) {
            for (old_val, current_val) in old.iter().zip(current.iter()) {
                if (old_val - current_val).abs() > 1e-6 {
                    return false;
                }
            }
        }
        true
    }
    
    pub fn predict(&self, x: &[Vec<f64>]) -> Result<Vec<usize>, String> {
        if self.centroids.is_empty() {
            return Err("模型未训练".to_string());
        }
        
        let predictions = x.iter()
            .map(|sample| self.predict_sample(sample))
            .collect();
        
        Ok(predictions)
    }
    
    fn predict_sample(&self, x: &[f64]) -> usize {
        let mut min_dist = f64::INFINITY;
        let mut cluster_idx = 0;
        
        for (i, centroid) in self.centroids.iter().enumerate() {
            let dist = self.euclidean_distance(x, centroid);
            if dist < min_dist {
                min_dist = dist;
                cluster_idx = i;
            }
        }
        
        cluster_idx
    }
    
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}
```

#### 10.2.2 主成分分析(PCA)

**定义 10.2.2 (主成分分析)** 主成分分析是一种降维技术，通过线性变换将数据投影到方差最大的方向。

**定理 10.2.2 (PCA最优性)** PCA产生的低维表示在最小化重构误差的意义上是最优的线性投影。

Rust实现:

```rust
pub struct PCA {
    n_components: usize,
    components: Vec<Vec<f64>>,
    mean: Vec<f64>,
}

impl PCA {
    pub fn new(n_components: usize) -> Self {
        PCA {
            n_components,
            components: Vec::new(),
            mean: Vec::new(),
        }
    }
    
    pub fn fit_transform(&mut self, x: &[Vec<f64>]) -> Result<Vec<Vec<f64>>, String> {
        if x.is_empty() {
            return Err("数据集不能为空".to_string());
        }
        
        let n_samples = x.len();
        let n_features = x[0].len();
        
        if self.n_components > n_features {
            return Err("主成分数不能大于特征数".to_string());
        }
        
        // 计算均值
        self.mean = vec![0.0; n_features];
        for sample in x {
            for j in 0..n_features {
                self.mean[j] += sample[j];
            }
        }
        for j in 0..n_features {
            self.mean[j] /= n_samples as f64;
        }
        
        // 中心化数据
        let mut centered_x = vec![vec![0.0; n_features]; n_samples];
        for i in 0..n_samples {
            for j in 0..n_features {
                centered_x[i][j] = x[i][j] - self.mean[j];
            }
        }
        
        // 计算协方差矩阵
        let mut cov_matrix = vec![vec![0.0; n_features]; n_features];
        for i in 0..n_features {
            for j in 0..n_features {
                let mut cov = 0.0;
                for k in 0..n_samples {
                    cov += centered_x[k][i] * centered_x[k][j];
                }
                cov_matrix[i][j] = cov / (n_samples as f64 - 1.0);
            }
        }
        
        // 这里简化处理：在真实应用中，应使用特征值分解
        // 这里假设我们已经通过某种方法获得了特征向量
        // 在实际实现中，应使用数值计算库如ndarray或rust-matio
        
        // 假设已获得主成分（特征向量）
        self.components = vec![vec![0.0; n_features]; self.n_components];
        
        // 此处代码应执行特征值分解并选择最大特征值对应的特征向量
        // 由于这需要线性代数库支持，这里只是概念性的
        
        // 应用变换，投影到主成分上
        let mut transformed = vec![vec![0.0; self.n_components]; n_samples];
        for i in 0..n_samples {
            for j in 0..self.n_components {
                for k in 0..n_features {
                    transformed[i][j] += centered_x[i][k] * self.components[j][k];
                }
            }
        }
        
        Ok(transformed)
    }
    
    pub fn transform(&self, x: &[Vec<f64>]) -> Result<Vec<Vec<f64>>, String> {
        if self.components.is_empty() {
            return Err("模型未训练".to_string());
        }
        
        let n_samples = x.len();
        let n_features = x[0].len();
        
        if n_features != self.mean.len() {
            return Err("特征数量与训练时不匹配".to_string());
        }
        
        // 中心化数据
        let mut centered_x = vec![vec![0.0; n_features]; n_samples];
        for i in 0..n_samples {
            for j in 0..n_features {
                centered_x[i][j] = x[i][j] - self.mean[j];
            }
        }
        
        // 投影到主成分上
        let mut transformed = vec![vec![0.0; self.n_components]; n_samples];
        for i in 0..n_samples {
            for j in 0..self.n_components {
                for k in 0..n_features {
                    transformed[i][j] += centered_x[i][k] * self.components[j][k];
                }
            }
        }
        
        Ok(transformed)
    }
}
```

## 11. 总结与思维导图

以上我们详细介绍了Rust算法实现的多个方面，从基础数据结构到高级算法范式，从经典算法到现代机器学习方法。Rust语言的安全性、性能和表达能力使其成为算法实现的理想选择。

下面是本文内容的思维导图:

```text
Rust算法全景：形式化分析与实现
│
├── 1. 引言
│   ├── 算法定义与重要性
│   ├── Rust语言特点
│   └── 形式化方法价值
│
├── 2. 基础数据结构算法
│   ├── 2.1 线性结构
│   │   ├── 动态数组、链表
│   │   └── 栈、队列
│   ├── 2.2 树结构
│   │   ├── 二叉树、二叉搜索树
│   │   └── 平衡树(AVL、红黑树)
│   ├── 2.3 图结构
│   │   ├── 邻接矩阵、邻接表
│   │   └── 图遍历(DFS、BFS)
│   └── 2.4 哈希表
│
├── 3. 排序算法
│   ├── 3.1 比较排序
│   │   ├── 快速排序、归并排序
│   │   ├── 堆排序
│   │   └── 插入排序、冒泡排序
│   ├── 3.2 非比较排序
│   │   ├── 计数排序、基数排序
│   │   └── 桶排序
│   ├── 3.3 外部排序
│   └── 3.4 排序算法复杂度与稳定性
│
├── 4. 搜索与查找算法
│   ├── 4.1 基础搜索算法
│   │   ├── 线性搜索、二分搜索
│   │   └── 插值搜索
│   ├── 4.2 高级搜索策略
│   │   ├── 启发式搜索(A*)
│   │   └── 跳跃搜索
│   └── 4.3 字符串搜索算法
│       ├── 朴素搜索、KMP算法
│       └── Boyer-Moore算法
│
├── 5. 图论算法
│   ├── 5.1 遍历算法
│   │   └── 拓扑排序
│   ├── 5.2 最短路径算法
│   │   ├── Dijkstra算法
│   │   ├── Bellman-Ford算法
│   │   └── Floyd-Warshall算法
│   ├── 5.3 最小生成树
│   │   ├── Prim算法
│   │   └── Kruskal算法
│   ├── 5.4 网络流算法
│   │   ├── Ford-Fulkerson算法
│   │   └── Edmonds-Karp算法
│   └── 5.5 二分图算法
│       ├── 二分图检测
│       └── 最大二分匹配
│
├── 6. 数值算法
│   ├── 6.1 基本数值算法
│   │   ├── GCD和LCM
│   │   ├── 素数生成和测试
│   │   └── 快速幂
│   ├── 6.2 数值计算
│   │   ├── 牛顿法求根
│   │   └── 数值积分
│   └── 6.3 矩阵运算
│       ├── 矩阵乘法
│       └── 高斯消元
│
├── 7. 密码学算法
│   ├── 7.1 散列算法
│   │   ├── SHA-256
│   │   └── HMAC
│   ├── 7.2 对称加密
│   │   └── AES
│   └── 7.3 非对称加密
│       └── RSA
│
├── 8. 并行与并发算法
│   ├── 8.1 并行基础算法
│   │   ├── 并行求和
│   │   └── 并行排序
│   ├── 8.2 并发数据结构
│   │   ├── 无锁栈
│   │   └── 读写锁
│   └── 8.3 工作窃取算法
│
├── 9. 高级算法范式
│   ├── 9.1 贪心算法
│   ├── 9.2 动态规划
│   ├── 9.3 分治算法
│   ├── 9.4 回溯算法
│   └── 9.5 随机化算法
│
└── 10. 机器学习算法
    ├── 10.1 监督学习
    │   ├── 线性回归
    │   └── 决策树
    └── 10.2 无监督学习
        ├── K均值聚类
        └── 主成分分析(PCA)
```

## 11. 总结与未来发展

通过本文的系统性探讨，我们详细阐述了Rust实现各类算法的形式化方法和具体实现。Rust语言结合了高级语言的抽象能力和底层语言的性能控制，为算法实现提供了独特优势。

### 11.1 Rust算法实现的优势

**定理 11.1.1 (Rust内存安全定理)** Rust的所有权系统在编译时保证了算法实现中不会出现悬垂引用、数据竞争和内存泄漏，同时不引入运行时开销。

**定理 11.1.2 (零成本抽象)** Rust的泛型、特质和生命周期机制使算法可以高度抽象而不牺牲性能，编译器优化消除了抽象带来的开销。

Rust在算法实现中展现出以下几个核心优势：

1. 内存安全与并发安全
2. 高性能与可预测的资源使用
3. 表达能力强的类型系统
4. 无垃圾回收的确定性资源管理
5. 与C语言的无缝互操作性

### 11.2 算法研究与实践的未来趋势

随着计算环境和应用需求的不断变化，未来算法研究与实践将呈现以下趋势：

#### 11.2.1 异构计算算法

**定义 11.2.1 (异构计算)** 异构计算指在包含多种类型处理单元(CPU、GPU、TPU等)的系统中进行计算，每种处理单元执行最适合其架构的任务。

```rust
// 一个简单的异构计算框架示例
pub trait ComputeKernel<T> {
    fn execute(&self, data: &[T]) -> Vec<T>;
    fn target_device(&self) -> DeviceType;
}

pub enum DeviceType {
    CPU,
    GPU,
    FPGA,
    TPU,
}

pub struct HeterogeneousCompute<T> {
    kernels: Vec<Box<dyn ComputeKernel<T>>>,
}

impl<T: Clone + Send + Sync + 'static> HeterogeneousCompute<T> {
    pub fn new() -> Self {
        HeterogeneousCompute { kernels: Vec::new() }
    }
    
    pub fn add_kernel(&mut self, kernel: Box<dyn ComputeKernel<T>>) {
        self.kernels.push(kernel);
    }
    
    pub fn execute(&self, data: &[T], preferred_device: Option<DeviceType>) -> Vec<T> {
        // 选择最适合的内核
        let kernel = match preferred_device {
            Some(device) => self.kernels.iter()
                .find(|k| k.target_device() == device)
                .unwrap_or_else(|| {
                    &self.kernels[0] // 默认使用第一个
                }),
            None => &self.kernels[0]
        };
        
        kernel.execute(data)
    }
}
```

#### 11.2.2 量子算法与量子抗性算法

**定义 11.2.2 (量子算法)** 量子算法是专为量子计算机设计的算法，利用量子叠加和纠缠等原理解决问题。

**定义 11.2.3 (量子抗性算法)** 量子抗性算法是能够抵抗量子计算攻击的密码学算法。

```rust
// 量子抗性加密算法示例框架
pub trait QuantumResistantCrypto {
    fn generate_keypair(&self) -> (Vec<u8>, Vec<u8>);
    fn encrypt(&self, public_key: &[u8], message: &[u8]) -> Vec<u8>;
    fn decrypt(&self, private_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, CryptoError>;
}

pub enum CryptoError {
    InvalidKey,
    DecryptionFailure,
    AuthenticationFailure,
}

// 格基密码学实现示例（概念性）
pub struct LatticeBasedEncryption {
    dimension: usize,
    modulus: u64,
}

impl QuantumResistantCrypto for LatticeBasedEncryption {
    fn generate_keypair(&self) -> (Vec<u8>, Vec<u8>) {
        // 生成格基密钥对的算法
        unimplemented!()
    }
    
    fn encrypt(&self, public_key: &[u8], message: &[u8]) -> Vec<u8> {
        // 基于格的加密算法
        unimplemented!()
    }
    
    fn decrypt(&self, private_key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, CryptoError> {
        // 基于格的解密算法
        unimplemented!()
    }
}
```

#### 11.2.3 自适应与在线算法

**定义 11.2.4 (自适应算法)** 自适应算法能够根据输入特性或运行环境动态调整其行为和参数。

**定义 11.2.5 (在线算法)** 在线算法在不知道完整输入序列的情况下处理数据，每次决策仅基于当前和过去的输入。

```rust
// 自适应排序算法示例
pub struct AdaptiveSorter<T: Ord> {
    threshold: usize,
    data_characteristics: DataCharacteristics,
}

enum DataCharacteristics {
    NearSorted,
    Random,
    Reversed,
    ManyDuplicates,
}

impl<T: Ord + Clone> AdaptiveSorter<T> {
    pub fn new() -> Self {
        AdaptiveSorter {
            threshold: 1000,
            data_characteristics: DataCharacteristics::Random,
        }
    }
    
    pub fn sort(&mut self, data: &mut [T]) {
        // 分析数据特性
        self.analyze_data(data);
        
        // 根据数据特性和大小选择最优算法
        match self.data_characteristics {
            DataCharacteristics::NearSorted => {
                if data.len() < self.threshold {
                    insertion_sort(data);
                } else {
                    tim_sort(data);
                }
            },
            DataCharacteristics::Reversed => {
                data.reverse();
                if !is_sorted(data) {
                    quicksort(data);
                }
            },
            DataCharacteristics::ManyDuplicates => {
                three_way_quicksort(data);
            },
            DataCharacteristics::Random => {
                if data.len() < self.threshold {
                    quicksort(data);
                } else {
                    parallel_sort(data);
                }
            }
        }
    }
    
    fn analyze_data(&mut self, data: &[T]) {
        // 分析数据特性以确定最优策略
        unimplemented!()
    }
}

// 各种排序算法的实现（这里省略）
fn insertion_sort<T: Ord>(_data: &mut [T]) { unimplemented!() }
fn tim_sort<T: Ord + Clone>(_data: &mut [T]) { unimplemented!() }
fn quicksort<T: Ord>(_data: &mut [T]) { unimplemented!() }
fn three_way_quicksort<T: Ord>(_data: &mut [T]) { unimplemented!() }
fn parallel_sort<T: Ord + Send>(_data: &mut [T]) { unimplemented!() }
fn is_sorted<T: Ord>(data: &[T]) -> bool {
    data.windows(2).all(|w| w[0] <= w[1])
}
```

### 11.3 形式化验证与正确性证明

随着算法复杂性的增加和应用场景的关键性提升，形式化验证将成为确保算法正确性的重要手段。

**定义 11.3.1 (形式化验证)** 形式化验证是使用数学方法严格证明算法满足其规范的过程。

```rust
// 使用契约编程进行形式化规范示例
#[pre(n >= 0)]
#[post(ret >= 0)]
#[ensures(ret * ret <= n && (ret + 1) * (ret + 1) > n)]
fn integer_sqrt(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    
    let mut x = n;
    let mut y = (x + 1) / 2;
    
    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }
    
    x
}

// 注意：上述代码中的属性宏是概念性的，Rust目前需要特定库支持契约编程
```

### 11.4 结语

本文系统地探讨了Rust中算法的形式化分析与实现，从基础数据结构到复杂的机器学习算法。Rust语言的安全特性、表达能力和性能使其成为现代算法研究与应用的理想选择。

随着计算领域的发展，算法设计与实现将继续面临新的挑战，如异构计算、量子计算、大规模分布式系统等。Rust语言的模型有潜力应对这些挑战，为未来的算法研究与工程实践提供坚实基础。

探索和实现高效、正确、安全的算法是计算机科学永恒的主题。通过融合形式化方法和工程实践，我们可以构建更可靠、更强大的算法系统，推动技术进步与科学发展。

## 完整思维导图

```text
Rust算法全景：形式化分析与实现
│
├── 1. 引言
│   ├── 算法定义与重要性
│   ├── Rust语言特点
│   └── 形式化方法价值
│
├── 2. 基础数据结构算法
│   ├── 2.1 线性结构
│   │   ├── 动态数组、链表
│   │   └── 栈、队列
│   ├── 2.2 树结构
│   │   ├── 二叉树、二叉搜索树
│   │   └── 平衡树(AVL、红黑树)
│   ├── 2.3 图结构
│   │   ├── 邻接矩阵、邻接表
│   │   └── 图遍历(DFS、BFS)
│   └── 2.4 哈希表
│
├── 3. 排序算法
│   ├── 3.1 比较排序
│   │   ├── 快速排序、归并排序
│   │   ├── 堆排序
│   │   └── 插入排序、冒泡排序
│   ├── 3.2 非比较排序
│   │   ├── 计数排序、基数排序
│   │   └── 桶排序
│   ├── 3.3 外部排序
│   └── 3.4 排序算法复杂度与稳定性
│
├── 4. 搜索与查找算法
│   ├── 4.1 基础搜索算法
│   │   ├── 线性搜索、二分搜索
│   │   └── 插值搜索
│   ├── 4.2 高级搜索策略
│   │   ├── 启发式搜索(A*)
│   │   └── 跳跃搜索
│   └── 4.3 字符串搜索算法
│       ├── 朴素搜索、KMP算法
│       └── Boyer-Moore算法
│
├── 5. 图论算法
│   ├── 5.1 遍历算法
│   │   └── 拓扑排序
│   ├── 5.2 最短路径算法
│   │   ├── Dijkstra算法
│   │   ├── Bellman-Ford算法
│   │   └── Floyd-Warshall算法
│   ├── 5.3 最小生成树
│   │   ├── Prim算法
│   │   └── Kruskal算法
│   ├── 5.4 网络流算法
│   │   ├── Ford-Fulkerson算法
│   │   └── Edmonds-Karp算法
│   └── 5.5 二分图算法
│       ├── 二分图检测
│       └── 最大二分匹配
│
├── 6. 数值算法
│   ├── 6.1 基本数值算法
│   │   ├── GCD和LCM
│   │   ├── 素数生成和测试
│   │   └── 快速幂
│   ├── 6.2 数值计算
│   │   ├── 牛顿法求根
│   │   └── 数值积分
│   └── 6.3 矩阵运算
│       ├── 矩阵乘法
│       └── 高斯消元
│
├── 7. 密码学算法
│   ├── 7.1 散列算法
│   │   ├── SHA-256
│   │   └── HMAC
│   ├── 7.2 对称加密
│   │   └── AES
│   └── 7.3 非对称加密
│       └── RSA
│
├── 8. 并行与并发算法
│   ├── 8.1 并行基础算法
│   │   ├── 并行求和
│   │   └── 并行排序
│   ├── 8.2 并发数据结构
│   │   ├── 无锁栈
│   │   └── 读写锁
│   └── 8.3 工作窃取算法
│
├── 9. 高级算法范式
│   ├── 9.1 贪心算法
│   ├── 9.2 动态规划
│   ├── 9.3 分治算法
│   ├── 9.4 回溯算法
│   └── 9.5 随机化算法
│
├── 10. 机器学习算法
│   ├── 10.1 监督学习
│   │   ├── 线性回归
│   │   └── 决策树
│   └── 10.2 无监督学习
│       ├── K均值聚类
│       └── 主成分分析(PCA)
│
└── 11. 总结与未来发展
    ├── 11.1 Rust算法实现的优势
    ├── 11.2 算法研究与实践的未来趋势
    │   ├── 异构计算算法
    │   ├── 量子算法与量子抗性算法
    │   └── 自适应与在线算法
    ├── 11.3 形式化验证与正确性证明
    └── 11.4 结语
```
