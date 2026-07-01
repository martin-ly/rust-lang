# 🔧 C04: Generic Programming - 实战项目集

> **创建日期**: 2025-10-25
> **文档版本**: v1.0
> **适用模块**: C04 泛型编程
> **目标**: 通过实战项目掌握泛型、Trait Bounds 和类型系统

---

## 📋 本文档目录

- [🔧 C04: Generic Programming - 实战项目集](#-c04-generic-programming---实战项目集)
  - [📋 本文档目录](#-本文档目录)
  - [📋 项目概览](#-项目概览)
  - [项目1: 泛型容器](#项目1-泛型容器)
    - [📖 项目说明](#-项目说明)
    - [学习目标](#学习目标)
    - [核心代码](#核心代码)
    - [测试输出](#测试输出)
  - [项目2: 泛型算法库](#项目2-泛型算法库)
    - [📖 项目说明2](#-项目说明2)
    - [学习目标2](#学习目标2)
    - [核心代码2](#核心代码2)
  - [项目3: 类型级编程](#项目3-类型级编程)
    - [📖 项目说明3](#-项目说明3)
    - [学习目标3](#学习目标3)
    - [核心代码3](#核心代码3)
  - [📝 总结](#-总结)
    - [关键概念](#关键概念)

## 📋 项目概览

| #   | 项目名称  | 难度   | 预计时间 | 核心概念                 |
| :--- | :--- | :--- | :--- | :--- |
| 1   | [泛型容器](#项目1-泛型容器)     | ⭐     | 1-2小时  | 泛型结构体、方法         |
| 2   | [泛型算法库](#项目2-泛型算法库) | ⭐⭐   | 2-3小时  | Trait Bounds、where 子句 |
| 3   | [类型级编程](#项目3-类型级编程) | ⭐⭐⭐ | 3-4小时  | 零大小类型、PhantomData  |

---

## 项目1: 泛型容器

### 📖 项目说明

**难度**: ⭐
**预计时间**: 1-2小时

### 学习目标

- 实现泛型结构体
- 定义泛型方法
- 使用 Trait Bounds
- 实现常用容器方法

### 核心代码

```rust
use std::fmt::Display;

/// 泛型栈
struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Stack { items: Vec::new() }
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

    fn len(&self) -> usize {
        self.items.len()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// 为实现了 Display 的类型添加额外方法
impl<T: Display> Stack<T> {
    fn print_all(&self) {
        println!("Stack contents:");
        for (i, item) in self.items.iter().enumerate() {
            println!("  [{}]: {}", i, item);
        }
    }
}

/// 泛型队列
struct Queue<T> {
    items: Vec<T>,
}

impl<T> Queue<T> {
    fn new() -> Self {
        Queue { items: Vec::new() }
    }

    fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    fn dequeue(&mut self) -> Option<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    fn peek(&self) -> Option<&T> {
        self.items.first()
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

/// 泛型配对
struct Pair<T, U> {
    first: T,
    second: U,
}

impl<T, U> Pair<T, U> {
    fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }

    fn split(self) -> (T, U) {
        (self.first, self.second)
    }
}

impl<T: Display, U: Display> Pair<T, U> {
    fn show(&self) {
        println!("Pair: ({}, {})", self.first, self.second);
    }
}

fn main() {
    println!("===== 泛型容器测试 =====\n");

    // 测试1: 泛型栈
    {
        println!("测试1: 泛型栈\n");

        let mut stack = Stack::new();
        stack.push(1);
        stack.push(2);
        stack.push(3);

        println!("栈大小: {}", stack.len());
        stack.print_all();

        println!("\n弹出元素:");
        while let Some(item) = stack.pop() {
            println!("  {}", item);
        }
        println!();
    }

    // 测试2: 字符串栈
    {
        println!("测试2: 字符串栈\n");

        let mut stack = Stack::new();
        stack.push("Hello".to_string());
        stack.push("Rust".to_string());

        stack.print_all();
        println!();
    }

    // 测试3: 泛型队列
    {
        println!("测试3: 泛型队列\n");

        let mut queue = Queue::new();
        queue.enqueue("First");
        queue.enqueue("Second");
        queue.enqueue("Third");

        println!("队列大小: {}", queue.len());

        println!("出队:");
        while let Some(item) = queue.dequeue() {
            println!("  {}", item);
        }
        println!();
    }

    // 测试4: 泛型配对
    {
        println!("测试4: 泛型配对\n");

        let pair1 = Pair::new(10, "ten");
        pair1.show();

        let pair2 = Pair::new("key", 42);
        pair2.show();

        let (k, v) = pair2.split();
        println!("分离: {} = {}\n", k, v);
    }
}
```

### 测试输出

```text
===== 泛型容器测试 =====

测试1: 泛型栈

栈大小: 3
Stack contents:
  [0]: 1
  [1]: 2
  [2]: 3

弹出元素:
  3
  2
  1

测试2: 字符串栈

Stack contents:
  [0]: Hello
  [1]: Rust

测试3: 泛型队列

队列大小: 3
出队:
  First
  Second
  Third
```

---

## 项目2: 泛型算法库

### 📖 项目说明2

**难度**: ⭐⭐
**预计时间**: 2-3小时

### 学习目标2

- 使用复杂的 Trait Bounds
- 实现泛型算法
- 使用 where 子句
- 关联类型应用

### 核心代码2

```rust
use std::cmp::PartialOrd;
use std::fmt::Debug;

/// 查找最大值（泛型）
fn find_max<T: PartialOrd + Copy>(slice: &[T]) -> Option<T> {
    if slice.is_empty() {
        return None;
    }

    let mut max = slice[0];
    for &item in slice.iter().skip(1) {
        if item > max {
            max = item;
        }
    }
    Some(max)
}

/// 排序算法（冒泡排序）
fn bubble_sort<T: PartialOrd>(slice: &mut [T]) {
    let len = slice.len();
    for i in 0..len {
        for j in 0..len - 1 - i {
            if slice[j] > slice[j + 1] {
                slice.swap(j, j + 1);
            }
        }
    }
}

/// 二分查找
fn binary_search<T: PartialOrd>(slice: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = slice.len();

    while left < right {
        let mid = (left + right) / 2;

        if slice[mid] < *target {
            left = mid + 1;
        } else if slice[mid] > *target {
            right = mid;
        } else {
            return Some(mid);
        }
    }

    None
}

/// 映射和过滤
fn map_and_filter<T, U, F, P>(slice: &[T], map: F, predicate: P) -> Vec<U>
where
    T: Clone,
    F: Fn(&T) -> U,
    P: Fn(&U) -> bool,
{
    slice.iter()
        .map(map)
        .filter(predicate)
        .collect()
}

/// 统计信息
struct Stats<T> {
    min: T,
    max: T,
    count: usize,
}

fn calculate_stats<T>(slice: &[T]) -> Option<Stats<T>>
where
    T: PartialOrd + Copy + Debug,
{
    if slice.is_empty() {
        return None;
    }

    let mut min = slice[0];
    let mut max = slice[0];

    for &item in slice.iter() {
        if item < min {
            min = item;
        }
        if item > max {
            max = item;
        }
    }

    Some(Stats {
        min,
        max,
        count: slice.len(),
    })
}

fn main() {
    println!("===== 泛型算法库测试 =====\n");

    // 测试1: 查找最大值
    {
        println!("测试1: 查找最大值\n");

        let numbers = vec![3, 7, 2, 9, 1];
        if let Some(max) = find_max(&numbers) {
            println!("最大值: {}", max);
        }

        let floats = vec![3.14, 2.71, 1.41, 9.81];
        if let Some(max) = find_max(&floats) {
            println!("最大浮点数: {}\n", max);
        }
    }

    // 测试2: 排序
    {
        println!("测试2: 冒泡排序\n");

        let mut numbers = vec![5, 2, 8, 1, 9];
        println!("原始: {:?}", numbers);

        bubble_sort(&mut numbers);
        println!("排序后: {:?}\n", numbers);
    }

    // 测试3: 二分查找
    {
        println!("测试3: 二分查找\n");

        let numbers = vec![1, 3, 5, 7, 9, 11];

        match binary_search(&numbers, &7) {
            Some(idx) => println!("找到 7 在索引: {}", idx),
            None => println!("未找到"),
        }

        match binary_search(&numbers, &4) {
            Some(idx) => println!("找到 4 在索引: {}", idx),
            None => println!("未找到 4\n"),
        }
    }

    // 测试4: 映射和过滤
    {
        println!("测试4: 映射和过滤\n");

        let numbers = vec![1, 2, 3, 4, 5];

        let doubled_evens = map_and_filter(
            &numbers,
            |&n| n * 2,
            |&n| n % 2 == 0,
        );

        println!("原始: {:?}", numbers);
        println!("加倍的偶数: {:?}\n", doubled_evens);
    }

    // 测试5: 统计
    {
        println!("测试5: 统计信息\n");

        let numbers = vec![3, 7, 2, 9, 1, 5];

        if let Some(stats) = calculate_stats(&numbers) {
            println!("数据: {:?}", numbers);
            println!("最小值: {:?}", stats.min);
            println!("最大值: {:?}", stats.max);
            println!("数量: {}", stats.count);
        }
    }
}
```

---

## 项目3: 类型级编程

### 📖 项目说明3

**难度**: ⭐⭐⭐
**预计时间**: 3-4小时

### 学习目标3

- 使用零大小类型（ZST）
- 理解 PhantomData
- 实现类型状态模式
- 编译期类型检查

### 核心代码3

```rust
use std::marker::PhantomData;

/// 状态标记
struct Open;
struct Closed;

/// 文件句柄（类型状态模式）
struct File<State> {
    name: String,
    _state: PhantomData<State>,
}

impl File<Closed> {
    fn new(name: String) -> Self {
        File {
            name,
            _state: PhantomData,
        }
    }

    fn open(self) -> File<Open> {
        println!("📂 打开文件: {}", self.name);
        File {
            name: self.name,
            _state: PhantomData,
        }
    }
}

impl File<Open> {
    fn write(&self, data: &str) {
        println!("✍️  写入: {}", data);
    }

    fn read(&self) -> String {
        println!("📖 读取文件");
        "file contents".to_string()
    }

    fn close(self) -> File<Closed> {
        println!("🔒 关闭文件: {}", self.name);
        File {
            name: self.name,
            _state: PhantomData,
        }
    }
}

fn main() {
    println!("===== 类型级编程测试 =====\n");

    let file = File::new("data.txt".to_string());

    // file.write("test");  // ❌ 编译错误：关闭的文件不能写入

    let file = file.open();
    file.write("Hello, Rust!");
    let _ = file.read();

    let file = file.close();

    // file.write("test");  // ❌ 编译错误：关闭的文件不能写入

    // 可以重新打开
    let file = file.open();
    file.write("More data");
}
```

---

## 📝 总结

### 关键概念

| 概念         | 项目1  | 项目2  | 项目3  |
| :--- | :--- | :--- | :--- || 泛型结构体   | ✅✅✅ | ✅     | ✅✅   |
| 泛型函数     | ✅✅   | ✅✅✅ | ✅     |
| Trait Bounds | ✅✅   | ✅✅✅ | ✅✅   |
| where 子句   | ❌     | ✅✅✅ | ✅     |
| PhantomData  | ❌     | ❌     | ✅✅✅ |
| 类型状态     | ❌     | ❌     | ✅✅✅ |

---

**文档版本**: v1.0
**创建日期**: 2025-10-25

**🎯 掌握泛型编程，写出灵活且类型安全的代码！🦀**-

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
