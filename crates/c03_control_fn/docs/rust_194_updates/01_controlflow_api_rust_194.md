# Rust 1.94: ControlFlow API 与生成器深度解析

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10

---

## 目录

- [Rust 1.94: ControlFlow API 与生成器深度解析](#rust-194-controlflow-api-与生成器深度解析)
  - [目录](#目录)
  - [ControlFlow API 完善](#controlflow-api-完善)
    - [1.1 基础 API](#11-基础-api)
    - [1.2 try\_for\_each 模式](#12-try_for_each-模式)
    - [1.3 嵌套 ControlFlow](#13-嵌套-controlflow)
  - [生成器 (gen 关键字)](#生成器-gen-关键字)
    - [2.1 基础生成器](#21-基础生成器)
    - [2.2 异步生成器](#22-异步生成器)
    - [2.3 生成器与所有权](#23-生成器与所有权)
  - [迭代器模式增强](#迭代器模式增强)
    - [3.1 自定义迭代器适配器](#31-自定义迭代器适配器)
    - [3.2 惰性求值链](#32-惰性求值链)
  - [实战应用](#实战应用)
    - [4.1 高性能事件处理器](#41-高性能事件处理器)
    - [4.2 分页数据加载](#42-分页数据加载)
    - [4.3 递归生成器](#43-递归生成器)
  - [性能优化](#性能优化)
    - [5.1 ControlFlow vs Result](#51-controlflow-vs-result)
  - [相关文档](#相关文档)

---

## ControlFlow API 完善

### 1.1 基础 API

Rust 1.94 完善了 `std::ops::ControlFlow`，提供了完整的控制流管理能力：

```rust
use std::ops::ControlFlow;

/// ControlFlow<B, C> 表示两种状态：
/// - Continue(C): 继续执行
/// - Break(B): 提前终止

fn basic_control_flow() {
    // 创建 ControlFlow 实例
    let continue_result: ControlFlow<i32, ()> = ControlFlow::Continue(());
    let break_result: ControlFlow<i32, ()> = ControlFlow::Break(42);

    // 检查状态
    assert!(continue_result.is_continue());
    assert!(break_result.is_break());

    // 获取值（Rust 1.94 完善）
    if let Some(value) = break_result.break_value() {
        println!("Break value: {}", value); // 42
    }

    // continue_value() 获取 Continue 值
    let continue_with_data: ControlFlow<i32, String> =
        ControlFlow::Continue("success".to_string());

    if let Some(value) = continue_with_data.continue_value() {
        println!("Continue value: {}", value);
    }
}
```

### 1.2 try_for_each 模式

```rust
use std::ops::ControlFlow;

/// 使用 ControlFlow 实现提前返回的遍历
fn find_first_negative(numbers: &[i32]) -> Option<i32> {
    numbers.iter().try_for_each(|&n| {
        if n < 0 {
            ControlFlow::Break(n)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

/// 查找满足条件的第一个元素
fn find_first<T>(items: &[T], predicate: impl Fn(&T) -> bool) -> Option<&T> {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

/// 验证所有元素满足条件
fn all<T>(items: &[T], predicate: impl Fn(&T) -> bool) -> bool {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }).is_continue()
}
```

### 1.3 嵌套 ControlFlow

```rust
use std::ops::ControlFlow;

/// 嵌套遍历中的控制流
fn nested_search(matrix: &[Vec<i32>], target: i32) -> Option<(usize, usize)> {
    matrix.iter().enumerate().try_for_each(|(row_idx, row)| {
        row.iter().enumerate().try_for_each(|(col_idx, &value)| {
            if value == target {
                ControlFlow::Break((row_idx, col_idx))
            } else {
                ControlFlow::Continue(())
            }
        })
    }).break_value()
}

/// 复杂条件的提前返回
fn process_items(items: &[Result<i32, String>]) -> ControlFlow<String, Vec<i32>> {
    let mut results = Vec::new();

    for item in items {
        match item {
            Ok(value) if *value < 0 => {
                return ControlFlow::Break(
                    format!("Negative value found: {}", value)
                );
            }
            Ok(value) => results.push(*value),
            Err(e) => {
                return ControlFlow::Break(
                    format!("Error processing item: {}", e)
                );
            }
        }
    }

    ControlFlow::Continue(results)
}
```

---

## 生成器 (gen 关键字)

### 2.1 基础生成器

```rust
#![feature(gen_blocks)]

/// 生成器：惰性求值的序列生成
fn fibonacci() -> impl Iterator<Item = u64> {
    gen {
        let (mut a, mut b) = (0, 1);
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}

/// 有限生成器
fn range_generator(start: i32, end: i32) -> impl Iterator<Item = i32> {
    gen {
        let mut current = start;
        while current < end {
            yield current;
            current += 1;
        }
    }
}

/// 带条件的生成器
fn even_numbers(max: i32) -> impl Iterator<Item = i32> {
    gen {
        for i in 0..max {
            if i % 2 == 0 {
                yield i;
            }
        }
    }
}
```

### 2.2 异步生成器

```rust
#![feature(async_gen_blocks)]
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

/// 异步生成器
async fn async_data_stream() -> impl Iterator<Item = i32> {
    gen {
        for i in 0..10 {
            // 模拟异步操作
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            yield i * i;
        }
    }
}

/// 带错误处理的异步生成器
async fn fallible_stream() -> impl Iterator<Item = Result<String, std::io::Error>> {
    gen {
        for i in 0..5 {
            if i == 3 {
                yield Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "Simulated error"
                ));
            } else {
                yield Ok(format!("Item {}", i));
            }
        }
    }
}
```

### 2.3 生成器与所有权

```rust
#![feature(gen_blocks)]

/// 生成器中的所有权转移
fn into_generator<T>(data: Vec<T>) -> impl Iterator<Item = T> {
    gen {
        // data 的所有权转移到生成器中
        for item in data {
            yield item;
        }
        // data 在这里被释放
    }
}

/// 借用生成器
fn borrow_generator<T>(data: &[T]) -> impl Iterator<Item = &T> + use<'_> {
    gen {
        for item in data {
            yield item;
        }
    }
}

/// 复杂的所有权模式
fn filtered_generator<T, F>(
    data: Vec<T>,
    filter: F
) -> impl Iterator<Item = T> + use<T, F>
where
    F: Fn(&T) -> bool,
{
    gen {
        for item in data {
            if filter(&item) {
                yield item;
            }
        }
    }
}
```

---

## 迭代器模式增强

### 3.1 自定义迭代器适配器

```rust
use std::ops::ControlFlow;

/// 使用 ControlFlow 的自定义适配器
trait ControlFlowIterator: Iterator + Sized {
    /// 找到第一个满足条件的元素，或者执行回调
    fn find_or_else<F, G>(
        self,
        predicate: F,
        else_fn: G
    ) -> Option<Self::Item>
    where
        F: FnMut(&Self::Item) -> bool,
        G: FnOnce(),
    {
        let result = self.try_for_each(|item| {
            if predicate(&item) {
                ControlFlow::Break(item)
            } else {
                ControlFlow::Continue(())
            }
        });

        match result {
            ControlFlow::Break(item) => Some(item),
            ControlFlow::Continue(()) => {
                else_fn();
                None
            }
        }
    }

    /// 批量处理，支持提前终止
    fn process_batch<F, B>(
        self,
        mut processor: F,
    ) -> ControlFlow<B, Vec<Self::Item>>
    where
        F: FnMut(&Self::Item) -> ControlFlow<B, ()>,
    {
        let mut unprocessed = Vec::new();

        for item in self {
            match processor(&item) {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(reason) => {
                    unprocessed.push(item);
                    return ControlFlow::Break(reason);
                }
            }
        }

        ControlFlow::Continue(unprocessed)
    }
}

impl<I: Iterator> ControlFlowIterator for I {}
```

### 3.2 惰性求值链

```rust
/// 惰性求值的处理管道
struct LazyPipeline<T, I: Iterator<Item = T>> {
    iterator: I,
}

impl<T, I: Iterator<Item = T>> LazyPipeline<T, I> {
    fn new(iterator: I) -> Self {
        Self { iterator }
    }

    /// 过滤并转换
    fn filter_map<U, F>(
        self,
        mut f: F
    ) -> LazyPipeline<U, impl Iterator<Item = U>>
    where
        F: FnMut(T) -> Option<U>,
    {
        LazyPipeline {
            iterator: self.iterator.filter_map(move |item| f(item)),
        }
    }

    /// 提前终止的条件处理
    fn take_while_ok<U, E>(
        self
    ) -> impl Iterator<Item = U>
    where
        T: Into<Result<U, E>>,
    {
        let mut stopped = false;
        self.iterator.take_while(move |item| {
            if stopped {
                return false;
            }
            match item.into() {
                Ok(_) => true,
                Err(_) => {
                    stopped = true;
                    false
                }
            }
        }).filter_map(|item| item.into().ok())
    }

    fn collect<B: FromIterator<T>>(self) -> B {
        self.iterator.collect()
    }
}
```

---

## 实战应用

### 4.1 高性能事件处理器

```rust
use std::ops::ControlFlow;

/// 事件处理结果
enum EventResult {
    Handled,
    Ignored,
    Error(String),
}

/// 使用 ControlFlow 的事件处理器
struct EventProcessor;

impl EventProcessor {
    fn process_events(
        &self,
        events: Vec<Event>
    ) -> ControlFlow<String, Vec<EventResult>> {
        let mut results = Vec::with_capacity(events.len());

        for event in events {
            match self.handle_event(event) {
                ControlFlow::Continue(result) => results.push(result),
                ControlFlow::Break(error) => {
                    return ControlFlow::Break(error);
                }
            }
        }

        ControlFlow::Continue(results)
    }

    fn handle_event(&self, event: Event) -> ControlFlow<String, EventResult> {
        match event.kind {
            EventKind::Critical => {
                // 关键错误，立即终止
                ControlFlow::Break(
                    format!("Critical error: {:?}", event.data)
                )
            }
            EventKind::Warning => {
                // 记录警告但继续
                eprintln!("Warning: {:?}", event.data);
                ControlFlow::Continue(EventResult::Handled)
            }
            EventKind::Info => {
                ControlFlow::Continue(EventResult::Ignored)
            }
        }
    }
}

#[derive(Debug)]
struct Event {
    kind: EventKind,
    data: Vec<u8>,
}

#[derive(Debug)]
enum EventKind {
    Critical,
    Warning,
    Info,
}
```

### 4.2 分页数据加载

```rust
#![feature(gen_blocks)]

/// 异步分页数据加载器
struct PaginatedLoader<T> {
    page_size: usize,
    fetch_page: Box<dyn Fn(usize) -> Vec<T>>,
}

impl<T> PaginatedLoader<T> {
    fn new<F>(page_size: usize, fetch_page: F) -> Self
    where
        F: Fn(usize) -> Vec<T> + 'static,
    {
        Self {
            page_size,
            fetch_page: Box::new(fetch_page),
        }
    }

    /// 生成器模式：惰性加载所有页面
    fn load_all(&self) -> impl Iterator<Item = T> + use<T> {
        let page_size = self.page_size;
        let fetch = &self.fetch_page;

        gen {
            let mut page = 0;
            loop {
                let items = fetch(page);
                if items.is_empty() {
                    break;
                }
                for item in items {
                    yield item;
                }
                page += 1;
            }
        }
    }

    /// 带提前终止的分页加载
    fn load_until<F>(
        &self,
        condition: F
    ) -> impl Iterator<Item = T> + use<T, F>
    where
        F: Fn(&T) -> bool,
    {
        let page_size = self.page_size;
        let fetch = &self.fetch_page;

        gen {
            let mut page = 0;
            'outer: loop {
                let items = fetch(page);
                if items.is_empty() {
                    break;
                }
                for item in items {
                    if condition(&item) {
                        break 'outer;
                    }
                    yield item;
                }
                page += 1;
            }
        }
    }
}

// 使用示例
fn main() {
    let loader = PaginatedLoader::new(10, |page| {
        // 模拟数据库查询
        (0..10).map(|i| format!("Page {}, Item {}", page, i)).collect()
    });

    // 加载前 25 个元素
    let items: Vec<String> = loader.load_all().take(25).collect();
    assert_eq!(items.len(), 25);
}
```

### 4.3 递归生成器

```rust
#![feature(gen_blocks)]

/// 树结构的递归生成器
tree_node! {
    TreeNode<T> {
        value: T,
        children: Vec<TreeNode<T>>,
    }
}

// 简化版树节点定义
struct TreeNode<T> {
    value: T,
    children: Vec<TreeNode<T>>,
}

impl<T> TreeNode<T> {
    fn new(value: T) -> Self {
        Self {
            value,
            children: vec![],
        }
    }

    fn add_child(&mut self, child: TreeNode<T>) {
        self.children.push(child);
    }

    /// 深度优先遍历生成器
    fn dfs_iter(&self) -> impl Iterator<Item = &T> {
        gen {
            yield &self.value;
            for child in &self.children {
                for value in child.dfs_iter() {
                    yield value;
                }
            }
        }
    }

    /// 广度优先遍历生成器
    fn bfs_iter(&self) -> impl Iterator<Item = &T> {
        let mut queue = vec![self];

        gen {
            while let Some(node) = queue.remove(0) {
                yield &node.value;
                for child in &node.children {
                    queue.push(child);
                }
            }
        }
    }
}
```

---

## 性能优化

### 5.1 ControlFlow vs Result

```rust
use std::ops::ControlFlow;

/// ControlFlow 在迭代器中的性能优势
///
/// ControlFlow 专门设计用于迭代器控制流，
/// 相比 Result，它避免了错误类型构造的开销

fn benchmark_comparison() {
    let data: Vec<i32> = (0..1_000_000).collect();

    // 使用 Result 的提前返回
    let result_way = || -> Result<(), String> {
        for item in &data {
            if *item == 500_000 {
                return Err("Found".to_string());
            }
        }
        Ok(())
    };

    // 使用 ControlFlow 的提前返回
    let control_flow_way = || -> ControlFlow<String, ()> {
        for item in &data {
            if *item == 500_000 {
                return ControlFlow::Break("Found".to_string());
            }
        }
        ControlFlow::Continue(())
    };

    // ControlFlow 版本通常更快，因为它避免了 String 分配
}
```

---

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [C03 控制流主索引](../00_MASTER_INDEX.md)
- [生成器 RFC](https://rust-lang.github.io/rfcs/2996-generator-capture-mutable.html)
- [ControlFlow 文档](https://doc.rust-lang.org/std/ops/enum.ControlFlow.html)
