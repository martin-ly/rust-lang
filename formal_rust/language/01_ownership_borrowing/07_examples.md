# 07 所有权与借用系统实际应用示例

## 目录

- [07 所有权与借用系统实际应用示例](#07-所有权与借用系统实际应用示例)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 示例特点](#11-示例特点)
    - [1.2 示例分类](#12-示例分类)
  - [2. 基础示例](#2-基础示例)
    - [2.1 基本所有权示例](#21-基本所有权示例)
    - [2.2 基本借用示例](#22-基本借用示例)
  - [3. 数据结构示例](#3-数据结构示例)
    - [3.1 链表示例](#31-链表示例)
    - [3.2 树结构示例](#32-树结构示例)
    - [3.3 图结构示例](#33-图结构示例)
  - [4. 函数示例](#4-函数示例)
    - [4.1 函数参数示例](#41-函数参数示例)
    - [4.2 函数返回值示例](#42-函数返回值示例)
    - [4.3 闭包示例](#43-闭包示例)
  - [5. 并发示例](#5-并发示例)
    - [5.1 线程示例](#51-线程示例)
    - [5.2 共享状态示例](#52-共享状态示例)
  - [6. 智能指针示例](#6-智能指针示例)
    - [6.1 Box示例](#61-box示例)
    - [6.2 Rc示例](#62-rc示例)
    - [6.3 Arc示例](#63-arc示例)
  - [7. 生命周期示例](#7-生命周期示例)
    - [7.1 基本生命周期示例](#71-基本生命周期示例)
    - [7.2 生命周期省略示例](#72-生命周期省略示例)
    - [7.3 复杂生命周期示例](#73-复杂生命周期示例)
  - [8. 高级示例](#8-高级示例)
    - [8.1 迭代器示例](#81-迭代器示例)
    - [8.2 错误处理示例](#82-错误处理示例)
    - [8.3 泛型示例](#83-泛型示例)
  - [9. 参考文献](#9-参考文献)
    - [9.1 技术文档](#91-技术文档)
    - [9.2 在线资源](#92-在线资源)
    - [9.3 实践指南](#93-实践指南)

## 1. 概述

本文档提供了Rust所有权与借用系统的完整实际应用示例，涵盖了从基础概念到高级应用的各个方面。
这些示例展示了如何在实际编程中正确使用所有权、借用和生命周期系统。

### 1.1 示例特点

- **实用性**：所有示例都是实际可运行的代码
- **教育性**：每个示例都包含详细的解释和说明
- **渐进性**：从简单到复杂，逐步深入
- **完整性**：覆盖所有权系统的所有重要概念

### 1.2 示例分类

- **基础示例**：基本的所有权和借用概念
- **数据结构示例**：在数据结构中的应用
- **函数示例**：函数中的所有权和借用
- **并发示例**：并发编程中的应用
- **智能指针示例**：智能指针的使用
- **生命周期示例**：生命周期标注和推断
- **高级示例**：复杂场景的应用

## 2. 基础示例

### 2.1 基本所有权示例

**示例 2.1.1**：基本所有权转移

```rust
fn main() {
    // 创建一个String
    let s1 = String::from("hello");
    println!("s1: {}", s1);
    
    // 所有权转移
    let s2 = s1;  // s1的所有权转移到s2
    println!("s2: {}", s2);
    
    // 这里不能使用s1，因为所有权已经转移
    // println!("s1: {}", s1);  // 编译错误！
}
```

**解释**：

- `String` 是拥有所有权的类型
- 当 `s1` 赋值给 `s2` 时，所有权发生转移
- 转移后，`s1` 不再有效，不能使用

**示例 2.1.2**：Copy trait示例

```rust
fn main() {
    // i32实现了Copy trait
    let x = 5;
    let y = x;  // x被复制给y，而不是转移
    println!("x: {}, y: {}", x, y);  // 都可以使用
    
    // 元组也可以Copy（如果所有元素都实现了Copy）
    let tuple1 = (1, 2, 3);
    let tuple2 = tuple1;  // 复制
    println!("tuple1: {:?}, tuple2: {:?}", tuple1, tuple2);
}
```

**解释**：

- 实现了 `Copy` trait 的类型在赋值时会被复制
- 复制后，原值仍然可以使用
- 基本类型（如 `i32`、`bool`、`char`）都实现了 `Copy`

### 2.2 基本借用示例

**示例 2.2.1**：不可变借用

```rust
fn main() {
    let s1 = String::from("hello");
    
    // 不可变借用
    let len = calculate_length(&s1);
    println!("The length of '{}' is {}.", s1, len);
    
    // s1仍然可以使用
    println!("s1: {}", s1);
}

fn calculate_length(s: &String) -> usize {
    s.len()
}
```

**解释**：

- `&s1` 创建了对 `s1` 的不可变引用
- 函数 `calculate_length` 借用 `s1` 但不获取所有权
- 函数调用后，`s1` 仍然可以使用

**示例 2.2.2**：可变借用

```rust
fn main() {
    let mut s = String::from("hello");
    
    // 可变借用
    change(&mut s);
    println!("s: {}", s);
}

fn change(some_string: &mut String) {
    some_string.push_str(", world");
}
```

**解释**：

- `&mut s` 创建了对 `s` 的可变引用
- 函数 `change` 可以修改借用的字符串
- 可变借用允许修改被借用的值

**示例 2.2.3**：借用规则示例

```rust
fn main() {
    let mut s = String::from("hello");
    
    // 多个不可变借用
    let r1 = &s;
    let r2 = &s;
    println!("r1: {}, r2: {}", r1, r2);
    
    // 可变借用（在不可变借用之后）
    let r3 = &mut s;
    r3.push_str(", world");
    println!("r3: {}", r3);
    
    // 注意：r1和r2在这里已经不能使用了
    // println!("r1: {}, r2: {}", r1, r2);  // 编译错误！
}
```

**解释**：

- 可以有多个不可变借用同时存在
- 可变借用是排他的，不能与其他借用同时存在
- 借用检查器确保借用规则得到遵守

## 3. 数据结构示例

### 3.1 链表示例

**示例 3.1.1**：简单链表

```rust
struct Node {
    data: i32,
    next: Option<Box<Node>>,
}

impl Node {
    fn new(data: i32) -> Self {
        Node {
            data,
            next: None,
        }
    }
    
    fn append(&mut self, data: i32) {
        match &mut self.next {
            None => {
                self.next = Some(Box::new(Node::new(data)));
            }
            Some(next) => {
                next.append(data);
            }
        }
    }
    
    fn print(&self) {
        print!("{} -> ", self.data);
        if let Some(next) = &self.next {
            next.print();
        } else {
            println!("None");
        }
    }
}

fn main() {
    let mut list = Node::new(1);
    list.append(2);
    list.append(3);
    list.print();
}
```

**解释**：

- 使用 `Box<Node>` 表示链表节点
- `Box` 提供了堆分配和自动内存管理
- 链表的所有权关系清晰，每个节点拥有下一个节点

**示例 3.1.2**：带引用的链表

```rust
struct Node<'a> {
    data: i32,
    next: Option<&'a Node<'a>>,
}

impl<'a> Node<'a> {
    fn new(data: i32) -> Self {
        Node {
            data,
            next: None,
        }
    }
    
    fn set_next(&mut self, next: &'a Node<'a>) {
        self.next = Some(next);
    }
    
    fn print(&self) {
        print!("{} -> ", self.data);
        if let Some(next) = self.next {
            next.print();
        } else {
            println!("None");
        }
    }
}

fn main() {
    let mut node1 = Node::new(1);
    let mut node2 = Node::new(2);
    let node3 = Node::new(3);
    
    node2.set_next(&node3);
    node1.set_next(&node2);
    
    node1.print();
}
```

**解释**：

- 使用生命周期参数 `'a` 管理引用的生命周期
- 引用链表避免了堆分配，但需要管理生命周期
- 生命周期确保引用不会超出被引用对象的生命周期

### 3.2 树结构示例

**示例 3.2.1**：二叉树

```rust
struct TreeNode {
    data: i32,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl TreeNode {
    fn new(data: i32) -> Self {
        TreeNode {
            data,
            left: None,
            right: None,
        }
    }
    
    fn insert(&mut self, data: i32) {
        if data < self.data {
            match &mut self.left {
                None => {
                    self.left = Some(Box::new(TreeNode::new(data)));
                }
                Some(left) => {
                    left.insert(data);
                }
            }
        } else {
            match &mut self.right {
                None => {
                    self.right = Some(Box::new(TreeNode::new(data)));
                }
                Some(right) => {
                    right.insert(data);
                }
            }
        }
    }
    
    fn inorder_traversal(&self) {
        if let Some(left) = &self.left {
            left.inorder_traversal();
        }
        print!("{} ", self.data);
        if let Some(right) = &self.right {
            right.inorder_traversal();
        }
    }
}

fn main() {
    let mut tree = TreeNode::new(5);
    tree.insert(3);
    tree.insert(7);
    tree.insert(1);
    tree.insert(9);
    
    print!("Inorder traversal: ");
    tree.inorder_traversal();
    println!();
}
```

**解释**：

- 二叉树使用 `Option<Box<TreeNode>>` 表示子节点
- 每个节点拥有其子节点的所有权
- 树的结构清晰，内存管理自动

### 3.3 图结构示例

**示例 3.3.1**：邻接表图

```rust
use std::collections::HashMap;

struct Graph {
    nodes: HashMap<i32, Vec<i32>>,
}

impl Graph {
    fn new() -> Self {
        Graph {
            nodes: HashMap::new(),
        }
    }
    
    fn add_node(&mut self, node: i32) {
        self.nodes.entry(node).or_insert_with(Vec::new);
    }
    
    fn add_edge(&mut self, from: i32, to: i32) {
        if let Some(neighbors) = self.nodes.get_mut(&from) {
            neighbors.push(to);
        }
    }
    
    fn get_neighbors(&self, node: i32) -> Option<&Vec<i32>> {
        self.nodes.get(&node)
    }
    
    fn print(&self) {
        for (node, neighbors) in &self.nodes {
            println!("Node {}: {:?}", node, neighbors);
        }
    }
}

fn main() {
    let mut graph = Graph::new();
    
    // 添加节点
    for i in 0..5 {
        graph.add_node(i);
    }
    
    // 添加边
    graph.add_edge(0, 1);
    graph.add_edge(0, 2);
    graph.add_edge(1, 3);
    graph.add_edge(2, 3);
    graph.add_edge(3, 4);
    
    graph.print();
}
```

**解释**：

- 使用 `HashMap` 存储图的邻接表
- 每个节点拥有其邻居列表的所有权
- 图结构清晰，易于理解和维护

## 4. 函数示例

### 4.1 函数参数示例

**示例 4.1.1**：所有权转移参数

```rust
fn main() {
    let s = String::from("hello");
    takes_ownership(s);
    // s在这里已经无效，不能使用
    // println!("s: {}", s);  // 编译错误！
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string离开作用域并被释放
```

**解释**：

- 函数 `takes_ownership` 获取参数的所有权
- 调用后，原变量不再有效
- 函数结束时，参数被自动释放

**示例 4.1.2**：借用参数

```rust
fn main() {
    let s = String::from("hello");
    makes_copy(s);
    println!("s: {}", s);  // 仍然可以使用
}

fn makes_copy(some_string: &String) {
    println!("{}", some_string);
} // some_string离开作用域，但不会释放，因为它没有所有权
```

**解释**：

- 函数 `makes_copy` 借用参数，不获取所有权
- 调用后，原变量仍然有效
- 借用避免了不必要的内存分配和释放

**示例 4.1.3**：可变借用参数

```rust
fn main() {
    let mut s = String::from("hello");
    change(&mut s);
    println!("s: {}", s);
}

fn change(some_string: &mut String) {
    some_string.push_str(", world");
}
```

**解释**：

- 函数 `change` 获取可变借用
- 可以修改被借用的值
- 调用后，原变量仍然有效，但值被修改

### 4.2 函数返回值示例

**示例 4.2.1**：返回所有权

```rust
fn main() {
    let s1 = gives_ownership();
    let s2 = String::from("hello");
    let s3 = takes_and_gives_back(s2);
    
    println!("s1: {}", s1);
    println!("s3: {}", s3);
}

fn gives_ownership() -> String {
    let some_string = String::from("yours");
    some_string  // 返回所有权
}

fn takes_and_gives_back(a_string: String) -> String {
    a_string  // 返回所有权
}
```

**解释**：

- 函数可以返回值的所有权
- 返回后，调用者获得所有权
- 所有权转移是显式的，易于跟踪

**示例 4.2.2**：返回引用

```rust
fn main() {
    let s1 = String::from("hello");
    let result = first_word(&s1);
    println!("First word: {}", result);
    println!("s1: {}", s1);  // 仍然可以使用
}

fn first_word(s: &String) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}
```

**解释**：

- 函数返回对输入字符串的引用
- 返回的引用与输入参数有相同的生命周期
- 避免了不必要的内存分配

### 4.3 闭包示例

**示例 4.3.1**：基本闭包

```rust
fn main() {
    let x = 5;
    
    let add_x = |y| x + y;  // 闭包捕获x
    
    println!("add_x(3): {}", add_x(3));
    println!("add_x(7): {}", add_x(7));
}
```

**解释**：

- 闭包可以捕获其环境中的变量
- 捕获的变量在闭包的生命周期内有效
- 闭包的所有权规则与普通函数相同

**示例 4.3.2**：移动闭包

```rust
fn main() {
    let s = String::from("hello");
    
    let print_s = move || {
        println!("s: {}", s);
    };
    
    print_s();
    // s在这里已经无效，因为所有权被移动到闭包中
    // println!("s: {}", s);  // 编译错误！
}
```

**解释**：

- `move` 关键字强制闭包获取捕获变量的所有权
- 移动后，原变量不再有效
- 移动闭包常用于线程间传递数据

## 5. 并发示例

### 5.1 线程示例

**示例 5.1.1**：基本线程

```rust
use std::thread;
use std::time::Duration;

fn main() {
    let handle = thread::spawn(|| {
        for i in 1..10 {
            println!("hi number {} from the spawned thread!", i);
            thread::sleep(Duration::from_millis(1));
        }
    });
    
    for i in 1..5 {
        println!("hi number {} from the main thread!", i);
        thread::sleep(Duration::from_millis(1));
    }
    
    handle.join().unwrap();
}
```

**解释**：

- `thread::spawn` 创建新线程
- 线程函数通过移动闭包传递
- `join` 等待线程完成

**示例 5.1.2**：线程间数据传递

```rust
use std::thread;

fn main() {
    let v = vec![1, 2, 3, 4, 5];
    
    let handle = thread::spawn(move || {
        println!("Here's a vector: {:?}", v);
    });
    
    handle.join().unwrap();
}
```

**解释**：

- 使用 `move` 闭包将数据移动到线程中
- 移动后，主线程不能访问数据
- 这确保了线程安全

### 5.2 共享状态示例

**示例 5.2.1**：Mutex共享

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", *counter.lock().unwrap());
}
```

**解释**：

- `Arc` 提供线程间的共享所有权
- `Mutex` 提供互斥访问
- 组合使用确保线程安全

**示例 5.2.2**：通道通信

```rust
use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        let val = String::from("hi");
        tx.send(val).unwrap();
        // val在这里已经无效，因为所有权被发送
    });
    
    let received = rx.recv().unwrap();
    println!("Got: {}", received);
}
```

**解释**：

- 通道提供线程间的消息传递
- 发送数据时转移所有权
- 避免了共享状态的问题

## 6. 智能指针示例

### 6.1 Box示例

**示例 6.1.1**：基本Box使用

```rust
fn main() {
    let b = Box::new(5);
    println!("b = {}", b);
    
    // Box在作用域结束时自动释放
}
```

**解释**：

- `Box` 将数据存储在堆上
- 自动管理内存分配和释放
- 适用于递归数据结构

**示例 6.1.2**：递归数据结构

```rust
enum List {
    Cons(i32, Box<List>),
    Nil,
}

use List::{Cons, Nil};

fn main() {
    let list = Cons(1,
        Box::new(Cons(2,
            Box::new(Cons(3,
                Box::new(Nil))))));
    
    print_list(&list);
}

fn print_list(list: &List) {
    match list {
        Cons(head, tail) => {
            println!("{}", head);
            print_list(tail);
        }
        Nil => {
            println!("End of list");
        }
    }
}
```

**解释**：

- `Box` 允许递归数据结构
- 每个 `Cons` 节点拥有下一个节点的所有权
- 自动内存管理确保正确释放

### 6.2 Rc示例

**示例 6.2.1**：基本Rc使用

```rust
use std::rc::Rc;

fn main() {
    let a = Rc::new(5);
    let b = Rc::clone(&a);
    let c = Rc::clone(&a);
    
    println!("a = {}", a);
    println!("b = {}", b);
    println!("c = {}", c);
    println!("Reference count: {}", Rc::strong_count(&a));
}
```

**解释**：

- `Rc` 允许多个所有者共享数据
- 使用引用计数管理内存
- 当引用计数归零时自动释放

**示例 6.2.2**：共享数据结构

```rust
use std::rc::Rc;

struct Node {
    data: i32,
    next: Option<Rc<Node>>,
}

impl Node {
    fn new(data: i32) -> Self {
        Node {
            data,
            next: None,
        }
    }
    
    fn set_next(&mut self, next: Rc<Node>) {
        self.next = Some(next);
    }
    
    fn print(&self) {
        print!("{} -> ", self.data);
        if let Some(next) = &self.next {
            next.print();
        } else {
            println!("None");
        }
    }
}

fn main() {
    let mut node1 = Node::new(1);
    let mut node2 = Node::new(2);
    let node3 = Rc::new(Node::new(3));
    
    // 多个节点可以共享同一个后续节点
    node1.set_next(Rc::clone(&node3));
    node2.set_next(Rc::clone(&node3));
    
    node1.print();
    node2.print();
}
```

**解释**：

- `Rc` 允许多个节点共享同一个子节点
- 避免了重复的内存分配
- 引用计数确保正确的内存管理

### 6.3 Arc示例

**示例 6.3.1**：线程间共享

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];
    
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

**解释**：

- `Arc` 提供线程间的共享所有权
- 原子引用计数确保线程安全
- 多个线程可以安全地访问共享数据

## 7. 生命周期示例

### 7.1 基本生命周期示例

**示例 7.1.1**：函数生命周期

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    let result = longest(&string1, string2);
    println!("The longest string is {}", result);
}
```

**解释**：

- 生命周期参数 `'a` 表示输入和输出引用的生命周期
- 编译器确保返回的引用不会超出输入引用的生命周期
- 生命周期标注帮助编译器进行借用检查

**示例 7.1.2**：结构体生命周期

```rust
struct ImportantExcerpt<'a> {
    part: &'a str,
}

fn main() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().unwrap();
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Excerpt: {}", i.part);
}
```

**解释**：

- 结构体包含引用时需要生命周期参数
- 生命周期参数确保结构体不会超出其引用字段的生命周期
- 这防止了悬垂引用

### 7.2 生命周期省略示例

**示例 7.2.1**：生命周期省略

```rust
// 省略前
fn first_word<'a>(s: &'a str) -> &'a str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}

// 省略后（编译器自动推断）
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}

fn main() {
    let s = String::from("hello world");
    let word = first_word(&s);
    println!("First word: {}", word);
}
```

**解释**：

- 编译器可以自动推断某些生命周期
- 省略规则基于常见的编程模式
- 省略后的代码更简洁，但语义相同

### 7.3 复杂生命周期示例

**示例 7.3.1**：多个生命周期参数

```rust
fn longest_with_an_announcement<'a, 'b>(
    x: &'a str,
    y: &'a str,
    ann: &'b str,
) -> &'a str {
    println!("Announcement! {}", ann);
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    let announcement = "I'm about to find the longest string!";
    
    let result = longest_with_an_announcement(&string1, string2, announcement);
    println!("The longest string is {}", result);
}
```

**解释**：

- 多个生命周期参数处理不同的生命周期需求
- `'a` 用于输入字符串和返回值
- `'b` 用于公告字符串，独立于其他生命周期

## 8. 高级示例

### 8.1 迭代器示例

**示例 8.1.1**：自定义迭代器

```rust
struct Counter {
    count: u32,
    max: u32,
}

impl Counter {
    fn new(max: u32) -> Counter {
        Counter {
            count: 0,
            max,
        }
    }
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.max {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

fn main() {
    let mut counter = Counter::new(5);
    
    for num in counter {
        println!("{}", num);
    }
}
```

**解释**：

- 迭代器模式利用了所有权和借用系统
- `next` 方法借用 `self` 并返回 `Option`
- 迭代器可以安全地遍历数据结构

### 8.2 错误处理示例

**示例 8.2.1**：Result类型使用

```rust
use std::fs::File;
use std::io::{self, Read};

fn read_username_from_file() -> Result<String, io::Error> {
    let mut f = File::open("hello.txt")?;
    let mut s = String::new();
    f.read_to_string(&mut s)?;
    Ok(s)
}

fn main() {
    match read_username_from_file() {
        Ok(username) => println!("Username: {}", username),
        Err(e) => println!("Error: {}", e),
    }
}
```

**解释**：

- `Result` 类型强制处理错误情况
- `?` 操作符简化错误传播
- 所有权系统确保资源的正确管理

### 8.3 泛型示例

**示例 8.3.1**：泛型函数

```rust
fn largest<T: PartialOrd + Copy>(list: &[T]) -> T {
    let mut largest = list[0];
    
    for &item in list.iter() {
        if item > largest {
            largest = item;
        }
    }
    
    largest
}

fn main() {
    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    println!("The largest number is {}", result);
    
    let char_list = vec!['y', 'm', 'a', 'q'];
    let result = largest(&char_list);
    println!("The largest char is {}", result);
}
```

**解释**：

- 泛型函数可以处理多种类型
- trait约束确保类型具有必要的功能
- 借用系统确保函数调用的安全性

## 9. 参考文献

### 9.1 技术文档

1. **Rust Book** (2024). "The Rust Programming Language - Understanding Ownership"
2. **Rust Reference** (2024). "The Rust Reference - Memory Safety"
3. **Rust By Example** (2024). "Rust By Example - Ownership and Borrowing"

### 9.2 在线资源

1. **Rust Playground** (2024). "Rust Playground - Online Rust Compiler"
2. **Rustlings** (2024). "Rustlings - Ownership and Borrowing Exercises"
3. **Rust Documentation** (2024). "Rust Documentation - Memory Safety"

### 9.3 实践指南

1. **Rust Best Practices** (2024). "Rust Best Practices - Memory Management"
2. **Rust Performance Guide** (2024). "Rust Performance Guide - Zero Cost Abstractions"
3. **Rust Security Guide** (2024). "Rust Security Guide - Memory Safety"

---

**文档版本**: 1.0.0  
**最后更新**: 2025-01-27  
**维护者**: Rust语言形式化理论项目组  
**状态**: 完成
