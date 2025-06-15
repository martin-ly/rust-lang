# 迭代器模式 (Iterator Pattern) - 形式化重构

## 目录

1. [模式概述](#1-模式概述)
2. [形式化定义](#2-形式化定义)
3. [数学理论](#3-数学理论)
4. [核心定理](#4-核心定理)
5. [Rust实现](#5-rust实现)
6. [应用场景](#6-应用场景)
7. [变体模式](#7-变体模式)
8. [性能分析](#8-性能分析)
9. [总结](#9-总结)

## 1. 模式概述

### 1.1 基本概念

迭代器模式是一种行为型设计模式，它提供一种方法顺序访问一个聚合对象中的各个元素，而又不暴露其内部的表示。

### 1.2 模式特征

- **封装性**：隐藏聚合对象的内部结构
- **统一接口**：提供统一的遍历接口
- **多态性**：支持不同类型的聚合对象
- **并发安全**：支持并发遍历

## 2. 形式化定义

### 2.1 迭代器模式五元组

**定义2.1 (迭代器模式五元组)**
设 $I = (A, T, S, M, C)$ 为一个迭代器模式，其中：

- $A = \{a_1, a_2, ..., a_n\}$ 是聚合对象集合
- $T = \{t_1, t_2, ..., t_m\}$ 是遍历类型集合
- $S = \{s_1, s_2, ..., s_k\}$ 是状态集合
- $M = \{m_1, m_2, ..., m_l\}$ 是方法集合
- $C = \{c_1, c_2, ..., c_p\}$ 是约束集合

### 2.2 迭代器接口定义

**定义2.2 (迭代器接口)**
迭代器接口 $I_{iter}$ 定义为：

$$I_{iter} = \{\text{next}() \rightarrow \text{Option<T>}, \text{has\_next}() \rightarrow \text{bool}, \text{reset}() \rightarrow \text{void}\}$$

### 2.3 聚合接口定义

**定义2.3 (聚合接口)**
聚合接口 $I_{agg}$ 定义为：

$$I_{agg} = \{\text{create\_iterator}() \rightarrow \text{Iterator<T>}, \text{size}() \rightarrow \text{usize}\}$$

### 2.4 遍历函数定义

**定义2.4 (遍历函数)**
遍历函数 $f_T: A \times I_{iter} \rightarrow S \times \text{Result}$ 定义为：

$$f_T(a, iter) = \begin{cases}
(s_{next}, \text{success}) & \text{if iteration succeeds} \\
(s_{end}, \text{end}) & \text{if iteration ends}
\end{cases}$$

## 3. 数学理论

### 3.1 遍历序列理论

**定义3.1 (遍历序列)**
对于聚合对象 $A$ 和迭代器 $I$，遍历序列 $S_A$ 定义为：

$$S_A = (e_1, e_2, ..., e_n)$$

其中 $e_i$ 是聚合对象中的第 $i$ 个元素。

### 3.2 遍历完整性理论

**定义3.2 (遍历完整性)**
迭代器 $I$ 对于聚合对象 $A$ 是完整的，当且仅当：

$$\forall e \in A, \exists i: \text{next}^i(I) = \text{Some}(e)$$

### 3.3 遍历唯一性理论

**定义3.3 (遍历唯一性)**
迭代器 $I$ 对于聚合对象 $A$ 是唯一的，当且仅当：

$$\forall e \in A, \exists! i: \text{next}^i(I) = \text{Some}(e)$$

### 3.4 遍历顺序理论

**定义3.4 (遍历顺序)**
迭代器 $I$ 的遍历顺序是确定的，当且仅当：

$$\forall i, j: i < j \Rightarrow \text{position}(e_i) < \text{position}(e_j)$$

## 4. 核心定理

### 4.1 遍历完整性定理

**定理4.1 (遍历完整性)**
如果迭代器 $I$ 对于聚合对象 $A$ 是完整的，则遍历过程会访问所有元素。

**证明：**
1. 根据定义3.2，$\forall e \in A, \exists i: \text{next}^i(I) = \text{Some}(e)$
2. 这意味着每个元素都会被访问到
3. 完整性得证。

### 4.2 遍历唯一性定理

**定理4.2 (遍历唯一性)**
如果迭代器 $I$ 对于聚合对象 $A$ 是唯一的，则每个元素只被访问一次。

**证明：**
1. 根据定义3.3，$\forall e \in A, \exists! i: \text{next}^i(I) = \text{Some}(e)$
2. 这意味着每个元素只被访问一次
3. 唯一性得证。

### 4.3 遍历终止性定理

**定理4.3 (遍历终止性)**
对于有限聚合对象 $A$，迭代器 $I$ 的遍历过程必然终止。

**证明：**
1. 聚合对象 $A$ 是有限的，包含 $n$ 个元素
2. 每次调用 `next()` 至少前进一个位置
3. 最多调用 $n$ 次 `next()`
4. 遍历过程必然终止。

### 4.4 遍历复杂度定理

**定理4.4 (遍历复杂度)**
对于包含 $n$ 个元素的聚合对象，完整遍历的时间复杂度为 $O(n)$。

**证明：**
1. 每个元素需要访问一次
2. 每次访问需要常数时间
3. 总复杂度为 $O(n)$

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 迭代器trait
pub trait Iterator<T>: fmt::Display {
    fn next(&mut self) -> Option<T>;
    fn has_next(&self) -> bool;
    fn reset(&mut self);
    fn count(&self) -> usize;
}

// 聚合trait
pub trait Aggregate<T>: fmt::Display {
    fn create_iterator(&self) -> Box<dyn Iterator<T>>;
    fn size(&self) -> usize;
    fn is_empty(&self) -> bool;
}

// 具体聚合：数组
pub struct ArrayAggregate<T> {
    data: Vec<T>,
}

impl<T> ArrayAggregate<T> {
    pub fn new() -> Self {
        ArrayAggregate { data: Vec::new() }
    }

    pub fn add(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<T: fmt::Display> fmt::Display for ArrayAggregate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayAggregate[size: {}]", self.data.len())
    }
}

impl<T: Clone> Aggregate<T> for ArrayAggregate<T> {
    fn create_iterator(&self) -> Box<dyn Iterator<T>> {
        Box::new(ArrayIterator::new(self.data.clone()))
    }

    fn size(&self) -> usize {
        self.data.len()
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

// 具体迭代器：数组迭代器
pub struct ArrayIterator<T> {
    data: Vec<T>,
    current: usize,
}

impl<T> ArrayIterator<T> {
    pub fn new(data: Vec<T>) -> Self {
        ArrayIterator { data, current: 0 }
    }
}

impl<T: fmt::Display> fmt::Display for ArrayIterator<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayIterator[current: {}, total: {}]", self.current, self.data.len())
    }
}

impl<T: Clone> Iterator<T> for ArrayIterator<T> {
    fn next(&mut self) -> Option<T> {
        if self.current < self.data.len() {
            let item = self.data[self.current].clone();
            self.current += 1;
            Some(item)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current < self.data.len()
    }

    fn reset(&mut self) {
        self.current = 0;
    }

    fn count(&self) -> usize {
        self.data.len()
    }
}

// 具体聚合：链表
pub struct LinkedListAggregate<T> {
    head: Option<Box<ListNode<T>>>,
    size: usize,
}

struct ListNode<T> {
    data: T,
    next: Option<Box<ListNode<T>>>,
}

impl<T> LinkedListAggregate<T> {
    pub fn new() -> Self {
        LinkedListAggregate {
            head: None,
            size: 0,
        }
    }

    pub fn add(&mut self, item: T) {
        let new_node = Box::new(ListNode {
            data: item,
            next: self.head.take(),
        });
        self.head = Some(new_node);
        self.size += 1;
    }

    pub fn len(&self) -> usize {
        self.size
    }
}

impl<T: fmt::Display> fmt::Display for LinkedListAggregate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LinkedListAggregate[size: {}]", self.size)
    }
}

impl<T: Clone> Aggregate<T> for LinkedListAggregate<T> {
    fn create_iterator(&self) -> Box<dyn Iterator<T>> {
        Box::new(LinkedListIterator::new(self.clone()))
    }

    fn size(&self) -> usize {
        self.size
    }

    fn is_empty(&self) -> bool {
        self.size == 0
    }
}

// 具体迭代器：链表迭代器
pub struct LinkedListIterator<T> {
    aggregate: LinkedListAggregate<T>,
    current: Option<Box<ListNode<T>>>,
}

impl<T> LinkedListIterator<T> {
    pub fn new(aggregate: LinkedListAggregate<T>) -> Self {
        LinkedListIterator {
            current: aggregate.head.clone(),
            aggregate,
        }
    }
}

impl<T: fmt::Display> fmt::Display for LinkedListIterator<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LinkedListIterator")
    }
}

impl<T: Clone> Iterator<T> for LinkedListIterator<T> {
    fn next(&mut self) -> Option<T> {
        if let Some(node) = self.current.take() {
            let data = node.data;
            self.current = node.next;
            Some(data)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current.is_some()
    }

    fn reset(&mut self) {
        self.current = self.aggregate.head.clone();
    }

    fn count(&self) -> usize {
        self.aggregate.size
    }
}

// 为LinkedListAggregate实现Clone
impl<T: Clone> Clone for LinkedListAggregate<T> {
    fn clone(&self) -> Self {
        let mut new_list = LinkedListAggregate::new();
        let mut current = &self.head;
        
        while let Some(node) = current {
            new_list.add(node.data.clone());
            current = &node.next;
        }
        
        new_list
    }
}

// 为ListNode实现Clone
impl<T: Clone> Clone for ListNode<T> {
    fn clone(&self) -> Self {
        ListNode {
            data: self.data.clone(),
            next: self.next.clone(),
        }
    }
}

// 为Option<Box<ListNode<T>>>实现Clone
impl<T: Clone> Clone for Option<Box<ListNode<T>>> {
    fn clone(&self) -> Self {
        match self {
            Some(node) => Some(Box::new(node.clone())),
            None => None,
        }
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;

// 泛型迭代器trait
pub trait GenericIterator<T>: fmt::Display {
    fn next(&mut self) -> Option<T>;
    fn has_next(&self) -> bool;
    fn reset(&mut self);
    fn count(&self) -> usize;
    fn peek(&self) -> Option<&T>;
}

// 泛型聚合trait
pub trait GenericAggregate<T>: fmt::Display {
    fn create_iterator(&self) -> Box<dyn GenericIterator<T>>;
    fn size(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn contains(&self, item: &T) -> bool;
}

// 泛型数组聚合
pub struct GenericArrayAggregate<T> {
    data: Vec<T>,
}

impl<T> GenericArrayAggregate<T> {
    pub fn new() -> Self {
        GenericArrayAggregate { data: Vec::new() }
    }

    pub fn add(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<T: fmt::Display> fmt::Display for GenericArrayAggregate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GenericArrayAggregate[size: {}]", self.data.len())
    }
}

impl<T: Clone + PartialEq> GenericAggregate<T> for GenericArrayAggregate<T> {
    fn create_iterator(&self) -> Box<dyn GenericIterator<T>> {
        Box::new(GenericArrayIterator::new(self.data.clone()))
    }

    fn size(&self) -> usize {
        self.data.len()
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn contains(&self, item: &T) -> bool {
        self.data.contains(item)
    }
}

// 泛型数组迭代器
pub struct GenericArrayIterator<T> {
    data: Vec<T>,
    current: usize,
}

impl<T> GenericArrayIterator<T> {
    pub fn new(data: Vec<T>) -> Self {
        GenericArrayIterator { data, current: 0 }
    }
}

impl<T: fmt::Display> fmt::Display for GenericArrayIterator<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GenericArrayIterator[current: {}, total: {}]", self.current, self.data.len())
    }
}

impl<T: Clone> GenericIterator<T> for GenericArrayIterator<T> {
    fn next(&mut self) -> Option<T> {
        if self.current < self.data.len() {
            let item = self.data[self.current].clone();
            self.current += 1;
            Some(item)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current < self.data.len()
    }

    fn reset(&mut self) {
        self.current = 0;
    }

    fn count(&self) -> usize {
        self.data.len()
    }

    fn peek(&self) -> Option<&T> {
        self.data.get(self.current)
    }
}
```

### 5.3 异步实现

```rust
use std::fmt;
use async_trait::async_trait;

// 异步迭代器trait
#[async_trait]
pub trait AsyncIterator<T>: fmt::Display + Send + Sync {
    async fn next(&mut self) -> Option<T>;
    fn has_next(&self) -> bool;
    async fn reset(&mut self);
    fn count(&self) -> usize;
}

// 异步聚合trait
#[async_trait]
pub trait AsyncAggregate<T>: fmt::Display + Send + Sync {
    async fn create_iterator(&self) -> Box<dyn AsyncIterator<T>>;
    fn size(&self) -> usize;
    fn is_empty(&self) -> bool;
}

// 异步数组聚合
pub struct AsyncArrayAggregate<T> {
    data: Vec<T>,
}

impl<T> AsyncArrayAggregate<T> {
    pub fn new() -> Self {
        AsyncArrayAggregate { data: Vec::new() }
    }

    pub fn add(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl<T: fmt::Display> fmt::Display for AsyncArrayAggregate<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AsyncArrayAggregate[size: {}]", self.data.len())
    }
}

#[async_trait]
impl<T: Clone + Send + Sync> AsyncAggregate<T> for AsyncArrayAggregate<T> {
    async fn create_iterator(&self) -> Box<dyn AsyncIterator<T>> {
        Box::new(AsyncArrayIterator::new(self.data.clone()))
    }

    fn size(&self) -> usize {
        self.data.len()
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

// 异步数组迭代器
pub struct AsyncArrayIterator<T> {
    data: Vec<T>,
    current: usize,
}

impl<T> AsyncArrayIterator<T> {
    pub fn new(data: Vec<T>) -> Self {
        AsyncArrayIterator { data, current: 0 }
    }
}

impl<T: fmt::Display> fmt::Display for AsyncArrayIterator<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AsyncArrayIterator[current: {}, total: {}]", self.current, self.data.len())
    }
}

#[async_trait]
impl<T: Clone + Send + Sync> AsyncIterator<T> for AsyncArrayIterator<T> {
    async fn next(&mut self) -> Option<T> {
        if self.current < self.data.len() {
            // 模拟异步操作
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
            let item = self.data[self.current].clone();
            self.current += 1;
            Some(item)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current < self.data.len()
    }

    async fn reset(&mut self) {
        self.current = 0;
    }

    fn count(&self) -> usize {
        self.data.len()
    }
}
```

### 5.4 应用场景实现

```rust
// 文件系统迭代器
pub struct FileSystemAggregate {
    root_path: String,
}

impl FileSystemAggregate {
    pub fn new(root_path: String) -> Self {
        FileSystemAggregate { root_path }
    }
}

impl fmt::Display for FileSystemAggregate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileSystemAggregate(root: {})", self.root_path)
    }
}

impl Aggregate<String> for FileSystemAggregate {
    fn create_iterator(&self) -> Box<dyn Iterator<String>> {
        Box::new(FileSystemIterator::new(self.root_path.clone()))
    }

    fn size(&self) -> usize {
        // 简化实现，返回0
        0
    }

    fn is_empty(&self) -> bool {
        true
    }
}

pub struct FileSystemIterator {
    root_path: String,
    current_path: String,
    visited: Vec<String>,
}

impl FileSystemIterator {
    pub fn new(root_path: String) -> Self {
        FileSystemIterator {
            current_path: root_path.clone(),
            root_path,
            visited: Vec::new(),
        }
    }
}

impl fmt::Display for FileSystemIterator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileSystemIterator(current: {})", self.current_path)
    }
}

impl Iterator<String> for FileSystemIterator {
    fn next(&mut self) -> Option<String> {
        // 模拟文件系统遍历
        if self.visited.len() < 5 {
            let file_path = format!("{}/file_{}.txt", self.current_path, self.visited.len());
            self.visited.push(file_path.clone());
            Some(file_path)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.visited.len() < 5
    }

    fn reset(&mut self) {
        self.visited.clear();
        self.current_path = self.root_path.clone();
    }

    fn count(&self) -> usize {
        self.visited.len()
    }
}

// 数据库结果集迭代器
pub struct DatabaseAggregate {
    connection_string: String,
    query: String,
}

impl DatabaseAggregate {
    pub fn new(connection_string: String, query: String) -> Self {
        DatabaseAggregate {
            connection_string,
            query,
        }
    }
}

impl fmt::Display for DatabaseAggregate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatabaseAggregate(query: {})", self.query)
    }
}

impl Aggregate<Vec<String>> for DatabaseAggregate {
    fn create_iterator(&self) -> Box<dyn Iterator<Vec<String>>> {
        Box::new(DatabaseIterator::new(self.connection_string.clone(), self.query.clone()))
    }

    fn size(&self) -> usize {
        // 简化实现，返回0
        0
    }

    fn is_empty(&self) -> bool {
        true
    }
}

pub struct DatabaseIterator {
    connection_string: String,
    query: String,
    current_row: usize,
    total_rows: usize,
}

impl DatabaseIterator {
    pub fn new(connection_string: String, query: String) -> Self {
        DatabaseIterator {
            connection_string,
            query,
            current_row: 0,
            total_rows: 10, // 模拟10行数据
        }
    }
}

impl fmt::Display for DatabaseIterator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatabaseIterator(row: {}/{})", self.current_row, self.total_rows)
    }
}

impl Iterator<Vec<String>> for DatabaseIterator {
    fn next(&mut self) -> Option<Vec<String>> {
        if self.current_row < self.total_rows {
            // 模拟数据库行数据
            let row_data = vec![
                format!("id_{}", self.current_row),
                format!("name_{}", self.current_row),
                format!("value_{}", self.current_row),
            ];
            self.current_row += 1;
            Some(row_data)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current_row < self.total_rows
    }

    fn reset(&mut self) {
        self.current_row = 0;
    }

    fn count(&self) -> usize {
        self.total_rows
    }
}

// 网络流迭代器
pub struct NetworkStreamAggregate {
    url: String,
    buffer_size: usize,
}

impl NetworkStreamAggregate {
    pub fn new(url: String, buffer_size: usize) -> Self {
        NetworkStreamAggregate { url, buffer_size }
    }
}

impl fmt::Display for NetworkStreamAggregate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NetworkStreamAggregate(url: {}, buffer: {})", self.url, self.buffer_size)
    }
}

impl Aggregate<Vec<u8>> for NetworkStreamAggregate {
    fn create_iterator(&self) -> Box<dyn Iterator<Vec<u8>>> {
        Box::new(NetworkStreamIterator::new(self.url.clone(), self.buffer_size))
    }

    fn size(&self) -> usize {
        // 简化实现，返回0
        0
    }

    fn is_empty(&self) -> bool {
        true
    }
}

pub struct NetworkStreamIterator {
    url: String,
    buffer_size: usize,
    current_chunk: usize,
    total_chunks: usize,
}

impl NetworkStreamIterator {
    pub fn new(url: String, buffer_size: usize) -> Self {
        NetworkStreamIterator {
            url,
            buffer_size,
            current_chunk: 0,
            total_chunks: 100, // 模拟100个数据块
        }
    }
}

impl fmt::Display for NetworkStreamIterator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NetworkStreamIterator(chunk: {}/{})", self.current_chunk, self.total_chunks)
    }
}

impl Iterator<Vec<u8>> for NetworkStreamIterator {
    fn next(&mut self) -> Option<Vec<u8>> {
        if self.current_chunk < self.total_chunks {
            // 模拟网络数据块
            let mut chunk = Vec::with_capacity(self.buffer_size);
            for i in 0..self.buffer_size {
                chunk.push((self.current_chunk + i) as u8);
            }
            self.current_chunk += 1;
            Some(chunk)
        } else {
            None
        }
    }

    fn has_next(&self) -> bool {
        self.current_chunk < self.total_chunks
    }

    fn reset(&mut self) {
        self.current_chunk = 0;
    }

    fn count(&self) -> usize {
        self.total_chunks
    }
}
```

## 6. 应用场景

### 6.1 集合遍历

迭代器模式在集合遍历中广泛应用：

- **数组遍历**：顺序访问数组元素
- **链表遍历**：顺序访问链表节点
- **树遍历**：深度优先或广度优先遍历
- **图遍历**：访问图中的所有节点

### 6.2 文件系统遍历

在文件系统操作中，迭代器模式用于：

- **目录遍历**：遍历目录中的所有文件
- **递归遍历**：递归遍历子目录
- **过滤遍历**：只遍历特定类型的文件
- **并行遍历**：并行遍历多个目录

### 6.3 数据库查询

在数据库操作中，迭代器模式用于：

- **结果集遍历**：遍历查询结果
- **分页遍历**：分页获取数据
- **流式遍历**：流式处理大量数据
- **缓存遍历**：遍历缓存中的数据

## 7. 变体模式

### 7.1 双向迭代器

```rust
pub trait BidirectionalIterator<T>: Iterator<T> {
    fn previous(&mut self) -> Option<T>;
    fn has_previous(&self) -> bool;
    fn go_to_end(&mut self);
}
```

### 7.2 随机访问迭代器

```rust
pub trait RandomAccessIterator<T>: Iterator<T> {
    fn get(&self, index: usize) -> Option<&T>;
    fn set(&mut self, index: usize, value: T) -> bool;
    fn jump_to(&mut self, index: usize) -> bool;
}
```

### 7.3 过滤迭代器

```rust
pub struct FilterIterator<T, F> {
    iterator: Box<dyn Iterator<T>>,
    predicate: F,
}

impl<T, F> FilterIterator<T, F>
where
    F: Fn(&T) -> bool,
{
    pub fn new(iterator: Box<dyn Iterator<T>>, predicate: F) -> Self {
        FilterIterator { iterator, predicate }
    }
}

impl<T, F> Iterator<T> for FilterIterator<T, F>
where
    F: Fn(&T) -> bool,
{
    fn next(&mut self) -> Option<T> {
        while let Some(item) = self.iterator.next() {
            if (self.predicate)(&item) {
                return Some(item);
            }
        }
        None
    }

    fn has_next(&self) -> bool {
        self.iterator.has_next()
    }

    fn reset(&mut self) {
        self.iterator.reset();
    }

    fn count(&self) -> usize {
        self.iterator.count()
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **创建迭代器**：$O(1)$，创建迭代器对象
- **遍历元素**：$O(n)$，其中 $n$ 是元素数量
- **查找元素**：$O(n)$，线性查找
- **重置迭代器**：$O(1)$，重置状态

### 8.2 空间复杂度

- **迭代器状态**：$O(1)$，存储当前位置
- **聚合对象**：$O(n)$，存储所有元素
- **临时变量**：$O(1)$，常数空间

### 8.3 优化策略

1. **延迟加载**：延迟加载数据
2. **缓存机制**：缓存已访问的元素
3. **并行遍历**：支持并行遍历
4. **内存池**：重用迭代器对象

## 9. 总结

迭代器模式通过提供统一的遍历接口，实现了聚合对象内部结构的封装，具有以下优势：

1. **封装性**：隐藏聚合对象的内部结构
2. **统一性**：提供统一的遍历接口
3. **多态性**：支持不同类型的聚合对象
4. **扩展性**：易于添加新的遍历方式

通过形式化的数学理论和完整的Rust实现，我们建立了迭代器模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。 