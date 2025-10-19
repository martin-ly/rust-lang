# 智能指针系统 - Smart Pointers System

**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 完整版  

## 📋 目录

- [智能指针系统 - Smart Pointers System](#智能指针系统---smart-pointers-system)
  - [📋 目录](#-目录)
  - [1. Box - 堆分配](#1-box---堆分配)
  - [2. Rc - 引用计数](#2-rc---引用计数)
  - [3. Arc - 原子引用计数](#3-arc---原子引用计数)
  - [4. RefCell - 内部可变性](#4-refcell---内部可变性)
  - [5. Cow - 写时复制](#5-cow---写时复制)
  - [6. 自定义智能指针](#6-自定义智能指针)
  - [📚 总结](#-总结)

## 1. Box - 堆分配

`Box<T>` 是最简单的智能指针，用于在堆上分配数据。

```rust
// Box 基础使用
fn box_basics() {
    let b = Box::new(5);
    println!("b = {}", b);
} // b 离开作用域，堆上的数据被自动释放

// Box 用于递归类型
enum List {
    Cons(i32, Box<List>),
    Nil,
}

use List::{Cons, Nil};

fn create_list() -> List {
    Cons(1, Box::new(
        Cons(2, Box::new(
            Cons(3, Box::new(Nil))
        ))
    ))
}

// Box 用于大型数据
struct LargeData {
    data: [u8; 10000],
}

fn box_large_data() {
    // 在堆上分配，避免栈溢出
    let large = Box::new(LargeData {
        data: [0; 10000],
    });
    
    println!("Size: {}", std::mem::size_of_val(&large)); // 只是一个指针的大小
}

// Box 实现 trait 对象
trait Animal {
    fn make_sound(&self);
}

struct Dog;
struct Cat;

impl Animal for Dog {
    fn make_sound(&self) {
        println!("Woof!");
    }
}

impl Animal for Cat {
    fn make_sound(&self) {
        println!("Meow!");
    }
}

fn box_trait_object() {
    let animals: Vec<Box<dyn Animal>> = vec![
        Box::new(Dog),
        Box::new(Cat),
    ];
    
    for animal in animals {
        animal.make_sound();
    }
}
```

## 2. Rc - 引用计数

`Rc<T>` 允许多个所有者共享数据（单线程）。

```rust
use std::rc::Rc;

// Rc 基础使用
fn rc_basics() {
    let data = Rc::new(vec![1, 2, 3]);
    
    let data1 = Rc::clone(&data);
    let data2 = Rc::clone(&data);
    
    println!("Count: {}", Rc::strong_count(&data)); // 3
    println!("Data1: {:?}", data1);
    println!("Data2: {:?}", data2);
}

// Rc 用于共享数据结构
struct Node {
    value: i32,
    next: Option<Rc<Node>>,
}

fn create_shared_list() {
    let tail = Rc::new(Node {
        value: 3,
        next: None,
    });
    
    let middle = Rc::new(Node {
        value: 2,
        next: Some(Rc::clone(&tail)),
    });
    
    let head1 = Node {
        value: 1,
        next: Some(Rc::clone(&middle)),
    };
    
    let head2 = Node {
        value: 10,
        next: Some(Rc::clone(&middle)),
    };
    
    // head1 和 head2 共享 middle 和 tail
}

// Rc 与 RefCell 结合实现共享可变性
use std::cell::RefCell;

type SharedNode = Rc<RefCell<Node>>;

struct MutableNode {
    value: i32,
    next: Option<SharedNode>,
}

fn rc_refcell_example() {
    let node1 = Rc::new(RefCell::new(MutableNode {
        value: 1,
        next: None,
    }));
    
    let node2 = Rc::new(RefCell::new(MutableNode {
        value: 2,
        next: Some(Rc::clone(&node1)),
    }));
    
    // 可以修改共享的节点
    node1.borrow_mut().value = 10;
    
    println!("Node1 value: {}", node1.borrow().value); // 10
}

// Rc 的循环引用问题
use std::rc::Weak;

struct TreeNode {
    value: i32,
    parent: RefCell<Weak<TreeNode>>,
    children: RefCell<Vec<Rc<TreeNode>>>,
}

impl TreeNode {
    fn new(value: i32) -> Rc<Self> {
        Rc::new(Self {
            value,
            parent: RefCell::new(Weak::new()),
            children: RefCell::new(Vec::new()),
        })
    }
    
    fn add_child(parent: &Rc<Self>, child: Rc<Self>) {
        *child.parent.borrow_mut() = Rc::downgrade(parent);
        parent.children.borrow_mut().push(child);
    }
}
```

## 3. Arc - 原子引用计数

`Arc<T>` 是线程安全的引用计数指针。

```rust
use std::sync::Arc;
use std::thread;

// Arc 基础使用
fn arc_basics() {
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, data_clone);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// Arc 与 Mutex 实现共享可变状态
use std::sync::Mutex;

fn arc_mutex_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter_clone.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", *counter.lock().unwrap());
}

// Arc 与 RwLock 优化读写性能
use std::sync::RwLock;

fn arc_rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 创建多个读线程
    for i in 0..5 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let read_guard = data_clone.read().unwrap();
            println!("Read thread {}: {:?}", i, *read_guard);
        });
        handles.push(handle);
    }
    
    // 创建一个写线程
    let data_clone = Arc::clone(&data);
    let write_handle = thread::spawn(move || {
        let mut write_guard = data_clone.write().unwrap();
        write_guard.push(4);
    });
    handles.push(write_handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// Arc 用于并发数据结构
use std::sync::atomic::{AtomicUsize, Ordering};

struct ConcurrentCounter {
    count: AtomicUsize,
}

impl ConcurrentCounter {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            count: AtomicUsize::new(0),
        })
    }
    
    fn increment(&self) {
        self.count.fetch_add(1, Ordering::SeqCst);
    }
    
    fn get(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}

fn concurrent_counter_example() {
    let counter = ConcurrentCounter::new();
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                counter_clone.increment();
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final count: {}", counter.get()); // 1000
}
```

## 4. RefCell - 内部可变性

`RefCell<T>` 在运行时检查借用规则。

```rust
use std::cell::RefCell;

// RefCell 基础使用
fn refcell_basics() {
    let data = RefCell::new(vec![1, 2, 3]);
    
    // 不可变借用
    {
        let borrow1 = data.borrow();
        let borrow2 = data.borrow();
        println!("{:?}", *borrow1);
        println!("{:?}", *borrow2);
    }
    
    // 可变借用
    {
        let mut borrow_mut = data.borrow_mut();
        borrow_mut.push(4);
    }
    
    println!("{:?}", data.borrow());
}

// RefCell 用于内部可变性模式
struct Cache {
    value: RefCell<Option<String>>,
}

impl Cache {
    fn new() -> Self {
        Self {
            value: RefCell::new(None),
        }
    }
    
    // 即使 &self，也可以修改内部状态
    fn get_or_compute(&self, compute: impl FnOnce() -> String) -> String {
        if let Some(cached) = self.value.borrow().as_ref() {
            return cached.clone();
        }
        
        let computed = compute();
        *self.value.borrow_mut() = Some(computed.clone());
        computed
    }
}

// RefCell 用于递归数据结构
struct TreeNode2 {
    value: i32,
    left: RefCell<Option<Box<TreeNode2>>>,
    right: RefCell<Option<Box<TreeNode2>>>,
}

impl TreeNode2 {
    fn new(value: i32) -> Self {
        Self {
            value,
            left: RefCell::new(None),
            right: RefCell::new(None),
        }
    }
    
    fn set_left(&self, node: TreeNode2) {
        *self.left.borrow_mut() = Some(Box::new(node));
    }
    
    fn set_right(&self, node: TreeNode2) {
        *self.right.borrow_mut() = Some(Box::new(node));
    }
}

// RefCell 的运行时检查
fn refcell_runtime_check() {
    let data = RefCell::new(5);
    
    let borrow1 = data.borrow();
    // let borrow_mut = data.borrow_mut(); // 会 panic！
    
    drop(borrow1); // 释放不可变借用
    let borrow_mut = data.borrow_mut(); // 现在可以
}
```

## 5. Cow - 写时复制

`Cow<T>` 提供写时复制功能。

```rust
use std::borrow::Cow;

// Cow 基础使用
fn cow_basics() {
    let s = "Hello";
    
    // 借用模式
    let cow_borrowed: Cow<str> = Cow::Borrowed(s);
    println!("{}", cow_borrowed);
    
    // 拥有模式
    let cow_owned: Cow<str> = Cow::Owned(String::from("World"));
    println!("{}", cow_owned);
}

// Cow 用于条件克隆
fn process_string(input: &str) -> Cow<str> {
    if input.contains("bad") {
        // 需要修改，创建拥有的版本
        Cow::Owned(input.replace("bad", "good"))
    } else {
        // 不需要修改，借用原始字符串
        Cow::Borrowed(input)
    }
}

// Cow 用于配置
#[derive(Debug, Clone)]
struct Config<'a> {
    name: Cow<'a, str>,
    value: Cow<'a, str>,
}

impl<'a> Config<'a> {
    fn new(name: &'a str, value: &'a str) -> Self {
        Self {
            name: Cow::Borrowed(name),
            value: Cow::Borrowed(value),
        }
    }
    
    fn with_name(mut self, name: String) -> Self {
        self.name = Cow::Owned(name);
        self
    }
    
    fn to_owned(self) -> Config<'static> {
        Config {
            name: Cow::Owned(self.name.into_owned()),
            value: Cow::Owned(self.value.into_owned()),
        }
    }
}

// Cow 用于优化性能
fn optimize_with_cow(data: &[i32]) -> Cow<[i32]> {
    if data.iter().all(|&x| x >= 0) {
        // 所有元素都是正数，不需要修改
        Cow::Borrowed(data)
    } else {
        // 需要修改，创建拥有的版本
        let mut owned = data.to_vec();
        for x in &mut owned {
            *x = x.abs();
        }
        Cow::Owned(owned)
    }
}
```

## 6. 自定义智能指针

创建自定义智能指针。

```rust
use std::ops::{Deref, DerefMut};

// 基础智能指针
struct MyBox<T> {
    value: T,
}

impl<T> MyBox<T> {
    fn new(value: T) -> Self {
        Self { value }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

// 带析构的智能指针
struct CustomSmartPointer {
    data: String,
}

impl Drop for CustomSmartPointer {
    fn drop(&mut self) {
        println!("Dropping CustomSmartPointer with data: {}", self.data);
    }
}

// 计数智能指针
use std::cell::Cell;

struct CountedPointer<T> {
    value: T,
    count: Cell<usize>,
}

impl<T> CountedPointer<T> {
    fn new(value: T) -> Self {
        Self {
            value,
            count: Cell::new(0),
        }
    }
    
    fn access(&self) -> &T {
        self.count.set(self.count.get() + 1);
        &self.value
    }
    
    fn access_count(&self) -> usize {
        self.count.get()
    }
}

// 带验证的智能指针
struct ValidatedPointer<T> {
    value: T,
    validator: Box<dyn Fn(&T) -> bool>,
}

impl<T> ValidatedPointer<T> {
    fn new(value: T, validator: impl Fn(&T) -> bool + 'static) -> Result<Self, &'static str> {
        if validator(&value) {
            Ok(Self {
                value,
                validator: Box::new(validator),
            })
        } else {
            Err("Initial value failed validation")
        }
    }
    
    fn set(&mut self, new_value: T) -> Result<(), &'static str> {
        if (self.validator)(&new_value) {
            self.value = new_value;
            Ok(())
        } else {
            Err("New value failed validation")
        }
    }
    
    fn get(&self) -> &T {
        &self.value
    }
}

// 使用示例
fn custom_pointer_examples() {
    // MyBox 示例
    let b = MyBox::new(String::from("Hello"));
    println!("{}", *b); // 解引用
    
    // CustomSmartPointer 示例
    {
        let _p = CustomSmartPointer {
            data: String::from("my stuff"),
        };
        // 自动调用 drop
    }
    
    // CountedPointer 示例
    let counter = CountedPointer::new(42);
    println!("{}", counter.access());
    println!("{}", counter.access());
    println!("Access count: {}", counter.access_count()); // 2
    
    // ValidatedPointer 示例
    let mut validated = ValidatedPointer::new(10, |x| *x > 0).unwrap();
    println!("Value: {}", validated.get());
    
    if let Err(e) = validated.set(-5) {
        println!("Error: {}", e);
    }
}
```

## 📚 总结

智能指针是 Rust 中管理内存和所有权的强大工具：

1. **Box**：堆分配，单一所有权
2. **Rc/Arc**：引用计数，多个所有权
3. **RefCell**：内部可变性，运行时借用检查
4. **Cow**：写时复制，优化性能
5. **自定义智能指针**：实现特定需求

通过合理使用智能指针，开发者可以：

- 灵活管理内存
- 实现复杂的数据结构
- 优化性能
- 确保内存安全

---

**相关文档**：

- [所有权基础](../02_core/01_ownership_fundamentals.md)
- [高级借用模式](./02_advanced_borrowing.md)
- [内存安全保证](../04_safety/01_memory_safety.md)

**最后更新**: 2025年1月27日  
**维护状态**: 活跃维护中  
**质量等级**: 完整版
