# 🎯 Rust 智能指针速查卡 {#-rust-智能指针速查卡}

> **快速参考** | [完整文档](../../../crates/c01_ownership_borrow_scope/docs/README.md) | [代码示例](../../../crates/c01_ownership_borrow_scope/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [🎯 Rust 智能指针速查卡 {#-rust-智能指针速查卡}](#-rust-智能指针速查卡--rust-智能指针速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🎯 智能指针概览 {#-智能指针概览}](#-智能指针概览--智能指针概览)
  - [📦 `Box<T>` - 堆分配 {#-box---堆分配}](#-boxt---堆分配--box---堆分配)
    - [基本用法](#基本用法)
    - [使用场景 {#-使用场景}](#使用场景--使用场景)
    - [API](#api)
  - [🔗 `Rc<T>` - 引用计数（单线程） {#-rc---引用计数单线程}](#-rct---引用计数单线程--rc---引用计数单线程)
    - [基本用法 {#基本用法-1}](#基本用法-基本用法-1)
    - [使用场景 {#使用场景-1}](#使用场景-使用场景-1)
    - [API {#api-1}](#api-api-1)
  - [🔗 `Arc<T>` - 原子引用计数（多线程） {#-arc---原子引用计数多线程}](#-arct---原子引用计数多线程--arc---原子引用计数多线程)
    - [基本用法 {#基本用法-2}](#基本用法-基本用法-2)
    - [使用场景 {#使用场景-2}](#使用场景-使用场景-2)
    - [API {#api-2}](#api-api-2)
  - [🔓 `RefCell<T>` - 内部可变性（单线程） {#-refcell---内部可变性单线程}](#-refcellt---内部可变性单线程--refcell---内部可变性单线程)
    - [基本用法 {#基本用法-3}](#基本用法-基本用法-3)
    - [使用场景 {#使用场景-3}](#使用场景-使用场景-3)
    - [API {#api-3}](#api-api-3)
    - [运行时借用检查](#运行时借用检查)
  - [🔒 `Mutex<T>` - 互斥锁（多线程） {#-mutex---互斥锁多线程}](#-mutext---互斥锁多线程--mutex---互斥锁多线程)
    - [基本用法 {#基本用法-4}](#基本用法-基本用法-4)
    - [使用场景 {#使用场景-4}](#使用场景-使用场景-4)
    - [API {#api-4}](#api-api-4)
  - [🔓 `RwLock<T>` - 读写锁（多线程） {#-rwlock---读写锁多线程}](#-rwlockt---读写锁多线程--rwlock---读写锁多线程)
    - [基本用法 {#基本用法-5}](#基本用法-基本用法-5)
    - [使用场景 {#使用场景-5}](#使用场景-使用场景-5)
    - [API {#api-5}](#api-api-5)
  - [🔗 `Weak<T>` - 弱引用 {#-weak---弱引用}](#-weakt---弱引用--weak---弱引用)
    - [基本用法 {#基本用法-6}](#基本用法-基本用法-6)
    - [使用场景 {#使用场景-6}](#使用场景-使用场景-6)
    - [API {#api-6}](#api-api-6)
  - [🔄 组合模式 {#-组合模式}](#-组合模式--组合模式)
    - [`Rc<RefCell<T>>` - 单线程内部可变性](#rcrefcellt---单线程内部可变性)
    - [`Arc<Mutex<T>>` - 多线程共享可变数据](#arcmutext---多线程共享可变数据)
    - [`Arc<RwLock<T>>` - 多线程读写锁](#arcrwlockt---多线程读写锁)
    - [`Rc<RefCell<Vec<T>>>` - 共享可变向量](#rcrefcellvect---共享可变向量)
  - [💡 代码示例 {#-代码示例}](#-代码示例--代码示例)
    - [示例 1: 实现链表](#示例-1-实现链表)
    - [示例 2: 带父指针的树结构（避免循环引用）](#示例-2-带父指针的树结构避免循环引用)
    - [示例 3: 自定义智能指针](#示例-3-自定义智能指针)
    - [示例 4: OnceCell 和 LazyLock（Rust 1.80+）](#示例-4-oncecell-和-lazylockrust-180)
    - [示例 5: 使用 Pin 的自引用结构](#示例-5-使用-pin-的自引用结构)
  - [🎯 使用场景](#-使用场景)
    - [场景: 图结构实现](#场景-图结构实现)
  - [🎯 选择指南 {#-选择指南}](#-选择指南--选择指南)
    - [决策树](#决策树)
    - [性能对比](#性能对比)
    - [常见组合](#常见组合)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: Rc 用于多线程](#反例-1-rc-用于多线程)
    - [反例 2: RefCell 在已借出时再次借用](#反例-2-refcell-在已借出时再次借用)
    - [反例 3: 循环引用导致内存泄漏](#反例-3-循环引用导致内存泄漏)
    - [反例 4: 错误地使用 Mutex 守卫](#反例-4-错误地使用-mutex-守卫)
    - [反例 5: Pin 误用导致未定义行为](#反例-5-pin-误用导致未定义行为)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与类型系统](#形式化理论与类型系统)
    - [相关速查卡](#相关速查卡)

---

## 🎯 智能指针概览 {#-智能指针概览}

```text
智能指针类型选择树：

需要堆分配？
├─ 是 → Box<T>
└─ 否 → 需要多重所有权？
    ├─ 是 → 单线程？
    │  ├─ 是 → Rc<T>
    │  └─ 否 → Arc<T>
    └─ 否 → 需要内部可变性？
        ├─ 是 → 单线程？
        │  ├─ 是 → RefCell<T>
        │  └─ 否 → Mutex<T> 或 RwLock<T>
        └─ 否 → 使用普通引用 &T 或 &mut T
```

---

## 📦 `Box<T>` - 堆分配 {#-box---堆分配}

### 基本用法

```rust
// 创建
let b = Box::new(5);
let b: Box<i32> = Box::new(5);

// 解引用
let value = *b;
println!("{}", *b);

// 自动解引用
fn print_value(b: Box<i32>) {
    println!("{}", b); // 自动解引用
}
```

### 使用场景 {#-使用场景}

```rust
// 1. 递归类型
enum List {
    Cons(i32, Box<List>),
    Nil,
}

// 2. 大型数据（避免栈溢出）
let large_array = Box::new([0u8; 1_000_000]);

// 3. Trait 对象
trait Draw {
    fn draw(&self);
}
let shapes: Vec<Box<dyn Draw>> = vec![];

// 4. 转移所有权但保持小尺寸
fn take_ownership(b: Box<i32>) {
    // Box 在栈上只有指针大小
}
```

### API

```rust
// 创建
let b = Box::new(value);
let b = Box::from(value);

// 解引用
let value = *b;
let value = b.as_ref(); // &T
let value = b.as_mut(); // &mut T

// 消耗 Box 获取值
let value = *b; // 或 Box::into_inner(b)
```

---

## 🔗 `Rc<T>` - 引用计数（单线程） {#-rc---引用计数单线程}

### 基本用法 {#基本用法-1}

```rust
use std::rc::Rc;

// 创建
let a = Rc::new(5);
let b = Rc::clone(&a); // 引用计数 +1
let c = a.clone();     // 也可以

// 使用
println!("{}", *a);
println!("{}", *b);

// 引用计数
println!("count: {}", Rc::strong_count(&a));
```

### 使用场景 {#使用场景-1}

```rust
// 多重所有权（单线程）
struct Node {
    value: i32,
    children: Vec<Rc<Node>>,
}

let node = Rc::new(Node {
    value: 1,
    children: vec![],
});

let child1 = Rc::clone(&node);
let child2 = Rc::clone(&node);
```

### API {#api-1}

```rust
use std::rc::Rc;

// 创建
let rc = Rc::new(value);

// 克隆（增加引用计数）
let rc2 = Rc::clone(&rc);
let rc3 = rc.clone();

// 引用计数
let strong_count = Rc::strong_count(&rc);
let weak_count = Rc::weak_count(&rc);

// 尝试获取可变引用（仅当引用计数为1时）
if let Some(data) = Rc::get_mut(&mut rc) {
    *data += 1;
}

// 解引用
let value = *rc;
```

---

## 🔗 `Arc<T>` - 原子引用计数（多线程） {#-arc---原子引用计数多线程}

### 基本用法 {#基本用法-2}

```rust
use std::sync::Arc;
use std::thread;

let data = Arc::new(5);
let data1 = Arc::clone(&data);
let data2 = Arc::clone(&data);

let handle1 = thread::spawn(move || {
    println!("Thread 1: {}", *data1);
});

let handle2 = thread::spawn(move || {
    println!("Thread 2: {}", *data2);
});

handle1.join().unwrap();
handle2.join().unwrap();
```

### 使用场景 {#使用场景-2}

```rust
// 多线程共享数据（只读）
use std::sync::Arc;
use std::thread;

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
```

### API {#api-2}

```rust
use std::sync::Arc;

// API 与 Rc 相同，但线程安全
let arc = Arc::new(value);
let arc2 = Arc::clone(&arc);
let count = Arc::strong_count(&arc);
```

---

## 🔓 `RefCell<T>` - 内部可变性（单线程） {#-refcell---内部可变性单线程}

### 基本用法 {#基本用法-3}

```rust
use std::cell::RefCell;

let data = RefCell::new(5);

// 不可变借用
let r = data.borrow();
println!("{}", *r);
drop(r); // 显式释放

// 可变借用
let mut r = data.borrow_mut();
*r += 1;
```

### 使用场景 {#使用场景-3}

```rust
// 在不可变引用中修改数据
struct Counter {
    count: RefCell<i32>,
}

impl Counter {
    fn increment(&self) {
        *self.count.borrow_mut() += 1;
    }

    fn get(&self) -> i32 {
        *self.count.borrow()
    }
}
```

### API {#api-3}

```rust
use std::cell::RefCell;

let cell = RefCell::new(value);

// 不可变借用
let r = cell.borrow();        // Ref<T>
let r = cell.try_borrow();    // Result<Ref<T>, BorrowError>

// 可变借用
let mut r = cell.borrow_mut();      // RefMut<T>
let r = cell.try_borrow_mut();      // Result<RefMut<T>, BorrowMutError>

// 获取内部值（消耗 RefCell）
let value = cell.into_inner();
```

### 运行时借用检查

```rust
let cell = RefCell::new(5);

let r1 = cell.borrow();      // OK
let r2 = cell.borrow();      // OK（多个不可变借用）
// let r3 = cell.borrow_mut(); // ❌ panic! 运行时错误

drop(r1);
drop(r2);

let r3 = cell.borrow_mut();  // OK
```

---

## 🔒 `Mutex<T>` - 互斥锁（多线程） {#-mutex---互斥锁多线程}

### 基本用法 {#基本用法-4}

```rust
use std::sync::{Arc, Mutex};
use std::thread;

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
```

### 使用场景 {#使用场景-4}

```rust
// 多线程共享可变数据
use std::sync::{Arc, Mutex};
use std::thread;

struct SharedData {
    data: Arc<Mutex<Vec<i32>>>,
}

impl SharedData {
    fn add(&self, value: i32) {
        let mut vec = self.data.lock().unwrap();
        vec.push(value);
    }
}
```

### API {#api-4}

```rust
use std::sync::Mutex;

let mutex = Mutex::new(value);

// 获取锁
let guard = mutex.lock().unwrap();      // MutexGuard<T>
let guard = mutex.try_lock();           // Result<MutexGuard<T>, TryLockError>

// 使用
let value = *guard;
*guard = new_value;

// 锁自动释放（guard 被 drop）
```

---

## 🔓 `RwLock<T>` - 读写锁（多线程） {#-rwlock---读写锁多线程}

### 基本用法 {#基本用法-5}

```rust
use std::sync::{Arc, RwLock};
use std::thread;

let data = Arc::new(RwLock::new(0));

// 多个读取者
let handles: Vec<_> = (0..5).map(|i| {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        let r = data.read().unwrap();
        println!("Reader {}: {}", i, *r);
    })
}).collect();

// 写入者
let writer = {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        let mut w = data.write().unwrap();
        *w += 1;
    })
};

for handle in handles {
    handle.join().unwrap();
}
writer.join().unwrap();
```

### 使用场景 {#使用场景-5}

```rust
// 读多写少的场景
use std::sync::{Arc, RwLock};

struct Cache {
    data: Arc<RwLock<HashMap<String, String>>>,
}

impl Cache {
    fn get(&self, key: &str) -> Option<String> {
        let map = self.data.read().unwrap();
        map.get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        let mut map = self.data.write().unwrap();
        map.insert(key, value);
    }
}
```

### API {#api-5}

```rust
use std::sync::RwLock;

let rwlock = RwLock::new(value);

// 读取锁（多个读取者可以同时持有）
let r = rwlock.read().unwrap();      // RwLockReadGuard<T>
let r = rwlock.try_read();           // Result<RwLockReadGuard<T>, TryLockError>

// 写入锁（独占）
let mut w = rwlock.write().unwrap(); // RwLockWriteGuard<T>
let w = rwlock.try_write();          // Result<RwLockWriteGuard<T>, TryLockError>
```

---

## 🔗 `Weak<T>` - 弱引用 {#-weak---弱引用}

### 基本用法 {#基本用法-6}

```rust
use std::rc::{Rc, Weak};

let strong = Rc::new(5);

// 创建弱引用
let weak: Weak<i32> = Rc::downgrade(&strong);

// 升级为强引用
if let Some(strong) = weak.upgrade() {
    println!("Value: {}", *strong);
} else {
    println!("Value has been dropped");
}

// 丢弃强引用
drop(strong);

// 弱引用无法升级
assert!(weak.upgrade().is_none());
```

### 使用场景 {#使用场景-6}

```rust
// 避免循环引用
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    parent: RefCell<Weak<Node>>,
    children: RefCell<Vec<Rc<Node>>>,
}

let leaf = Rc::new(Node {
    value: 3,
    parent: RefCell::new(Weak::new()),
    children: RefCell::new(vec![]),
});

let branch = Rc::new(Node {
    value: 5,
    parent: RefCell::new(Weak::new()),
    children: RefCell::new(vec![Rc::clone(&leaf)]),
});

*leaf.parent.borrow_mut() = Rc::downgrade(&branch);
```

### API {#api-6}

```rust
use std::rc::{Rc, Weak};

// 创建弱引用
let weak = Rc::downgrade(&rc);

// 升级为强引用
let strong = weak.upgrade(); // Option<Rc<T>>

// 引用计数
let strong_count = weak.strong_count();
let weak_count = weak.weak_count();
```

---

## 🔄 组合模式 {#-组合模式}

### `Rc<RefCell<T>>` - 单线程内部可变性

```rust
use std::rc::Rc;
use std::cell::RefCell;

let data = Rc::new(RefCell::new(5));

let data1 = Rc::clone(&data);
let data2 = Rc::clone(&data);

// 多个所有者可以修改
*data1.borrow_mut() += 1;
*data2.borrow_mut() += 2;

println!("{}", *data.borrow()); // 8
```

### `Arc<Mutex<T>>` - 多线程共享可变数据

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let data = Arc::new(Mutex::new(0));

let handles: Vec<_> = (0..10).map(|_| {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        let mut num = data.lock().unwrap();
        *num += 1;
    })
}).collect();

for handle in handles {
    handle.join().unwrap();
}
```

### `Arc<RwLock<T>>` - 多线程读写锁

```rust
use std::sync::{Arc, RwLock};
use std::thread;

let data = Arc::new(RwLock::new(0));

// 多个读取者
for _ in 0..5 {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        let r = data.read().unwrap();
        println!("{}", *r);
    });
}

// 写入者
let data = Arc::clone(&data);
thread::spawn(move || {
    let mut w = data.write().unwrap();
    *w += 1;
});
```

### `Rc<RefCell<Vec<T>>>` - 共享可变向量

```rust
use std::rc::Rc;
use std::cell::RefCell;

let vec = Rc::new(RefCell::new(vec![1, 2, 3]));

let vec1 = Rc::clone(&vec);
let vec2 = Rc::clone(&vec);

vec1.borrow_mut().push(4);
vec2.borrow_mut().push(5);

println!("{:?}", vec.borrow()); // [1, 2, 3, 4, 5]
```

---

## 💡 代码示例 {#-代码示例}

### 示例 1: 实现链表

```rust
use std::rc::Rc;
use std::cell::RefCell;

struct Node<T> {
    value: T,
    next: Option<Rc<RefCell<Node<T>>>>,
}

struct LinkedList<T> {
    head: Option<Rc<RefCell<Node<T>>>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self {
        Self { head: None }
    }

    fn push_front(&mut self, value: T) {
        let new_node = Rc::new(RefCell::new(Node {
            value,
            next: self.head.clone(),
        }));
        self.head = Some(new_node);
    }

    fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|old_head| {
            if let Some(next) = old_head.borrow_mut().next.take() {
                self.head = Some(next);
            }
            // 这里简化处理，实际中需要 Rc::try_unwrap
            Rc::try_unwrap(old_head).ok().unwrap().into_inner().value
        })
    }
}

// 使用
let mut list = LinkedList::new();
list.push_front(1);
list.push_front(2);
list.push_front(3);
assert_eq!(list.pop_front(), Some(3));
```

### 示例 2: 带父指针的树结构（避免循环引用）

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

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
            children: RefCell::new(vec![]),
        })
    }

    fn add_child(parent: &Rc<Self>, child: &Rc<Self>) {
        parent.children.borrow_mut().push(Rc::clone(child));
        *child.parent.borrow_mut() = Rc::downgrade(parent);
    }

    fn get_parent(&self) -> Option<Rc<Self>> {
        self.parent.borrow().upgrade()
    }
}

// 使用
let root = TreeNode::new(1);
let child = TreeNode::new(2);
TreeNode::add_child(&root, &child);

if let Some(parent) = child.get_parent() {
    println!("Parent value: {}", parent.value); // 1
}

// 当 root 被 drop 后，child 的 parent 自动变为 None
```

### 示例 3: 自定义智能指针

```rust
use std::ops::{Deref, Drop};

struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("MyBox is being dropped!");
    }
}

// 使用
fn hello(name: &str) {
    println!("Hello, {}!", name);
}

let m = MyBox::new(String::from("Rust"));
hello(&m);  // 自动解引用 &MyBox<String> -> &String -> &str
```

### 示例 4: OnceCell 和 LazyLock（Rust 1.80+）

```rust
use std::sync::LazyLock;

// 延迟初始化全局数据
static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    println!("Initializing CONFIG...");
    Config {
        db_url: "postgres://localhost".to_string(),
        max_connections: 10,
    }
});

struct Config {
    db_url: String,
    max_connections: usize,
}

fn main() {
    println!("Before accessing CONFIG");
    println!("DB URL: {}", CONFIG.db_url);  // 此时才初始化
    println!("Max connections: {}", CONFIG.max_connections);
}
```

### 示例 5: 使用 Pin 的自引用结构

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    // 指向 data 的指针
    ptr_to_data: *const String,
    _pin: PhantomPinned,  // 禁止移动
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data;
        unsafe {
            let mut_ref: Pin<&mut Self> = Pin::as_mut(&mut boxed);
            Pin::get_unchecked_mut(mut_ref).ptr_to_data = ptr;
        }

        boxed
    }

    fn get_data(&self) -> &str {
        &self.data
    }
}

// 使用
let data = SelfReferential::new("Hello".to_string());
println!("{}", data.get_data());
```

---

## 🎯 使用场景

### 场景: 图结构实现

在实际项目中，智能指针常用于实现复杂的数据结构。以下是一个有向图的实现：

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;
use std::collections::HashMap;

type NodeId = usize;

struct GraphNode<T> {
    id: NodeId,
    value: T,
    edges: RefCell<Vec<Weak<GraphNode<T>>>>,
}

struct Graph<T> {
    nodes: RefCell<HashMap<NodeId, Rc<GraphNode<T>>>>,
    next_id: RefCell<NodeId>,
}

impl<T> Graph<T> {
    fn new() -> Self {
        Self {
            nodes: RefCell::new(HashMap::new()),
            next_id: RefCell::new(0),
        }
    }

    fn add_node(&self, value: T) -> NodeId {
        let id = *self.next_id.borrow();
        *self.next_id.borrow_mut() += 1;

        let node = Rc::new(GraphNode {
            id,
            value,
            edges: RefCell::new(vec![]),
        });

        self.nodes.borrow_mut().insert(id, node);
        id
    }

    fn add_edge(&self, from: NodeId, to: NodeId) {
        if let (Some(from_node), Some(to_node)) =
            (self.nodes.borrow().get(&from).cloned(),
             self.nodes.borrow().get(&to).cloned()) {
            from_node.edges.borrow_mut().push(Rc::downgrade(&to_node));
        }
    }

    fn get_neighbors(&self, node_id: NodeId) -> Vec<NodeId> {
        self.nodes.borrow()
            .get(&node_id)
            .map(|node| {
                node.edges.borrow()
                    .iter()
                    .filter_map(|weak| weak.upgrade().map(|n| n.id))
                    .collect()
            })
            .unwrap_or_default()
    }
}
```

---

## 🎯 选择指南 {#-选择指南}

### 决策树

```text
需要堆分配？
├─ 是 → Box<T>
└─ 否 → 需要多重所有权？
    ├─ 是 → 单线程？
    │  ├─ 是 → Rc<T>
    │  └─ 否 → Arc<T>
    └─ 否 → 需要内部可变性？
        ├─ 是 → 单线程？
        │  ├─ 是 → RefCell<T>
        │  └─ 否 → 读多写少？
        │      ├─ 是 → RwLock<T>
        │      └─ 否 → Mutex<T>
        └─ 否 → 使用普通引用
```

### 性能对比

| 类型         | 开销         | 线程安全 | 可变性     |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `Rc<T>`      | 引用计数     | ❌       | 编译时检查 |
| `Arc<T>`     | 原子引用计数 | ✅       | 编译时检查 |
| `RefCell<T>` | 运行时检查   | ❌       | 运行时检查 |
| `Mutex<T>`   | 锁开销       | ✅       | 运行时检查 |
| `RwLock<T>`  | 锁开销       | ✅       | 运行时检查 |

### 常见组合

| 场景               | 推荐组合                  |
| :--- | :--- | :--- | :--- | :--- |
| 多线程共享可变     | `Arc<Mutex<T>>`           |
| 多线程读多写少     | `Arc<RwLock<T>>`          |
| 树结构（避免循环） | `Rc<Node>` + `Weak<Node>` |

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: Rc 用于多线程

**错误示例**:

```rust
let rc = Rc::new(1);
thread::spawn(|| {
    println!("{}", rc);  // ❌ Rc 不是 Send
});
```

**原因**: `Rc` 非线程安全，多线程用 `Arc`。

**修正**:

```rust
let arc = Arc::new(1);
thread::spawn(move || println!("{}", arc));
```

---

### 反例 2: RefCell 在已借出时再次借用

**错误示例**:

```rust
let r = RefCell::new(1);
let g1 = r.borrow_mut();
let g2 = r.borrow();  // ❌ panic: 已借出可变借用
```

**原因**: 运行时借用检查，同一时刻只能有一个可变借用或多个不可变借用。

**修正**:

```rust
let g1 = r.borrow_mut();
drop(g1);  // 先释放
let g2 = r.borrow();
```

---

### 反例 3: 循环引用导致内存泄漏

**错误示例**:

```rust
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    value: i32,
    next: RefCell<Option<Rc<Node>>>,  // ❌ 强引用循环
}

let a = Rc::new(Node { value: 1, next: RefCell::new(None) });
let b = Rc::new(Node { value: 2, next: RefCell::new(None) });

*a.next.borrow_mut() = Some(Rc::clone(&b));
*b.next.borrow_mut() = Some(Rc::clone(&a));
// a 和 b 形成循环引用，永远不会被释放
```

**原因**: `Rc` 使用强引用，循环引用会导致引用计数永不为零。

**修正**: 使用 `Weak` 打破循环：

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    parent: RefCell<Option<Weak<Node>>>,  // ✅ 弱引用
    children: RefCell<Vec<Rc<Node>>>,
}
```

---

### 反例 4: 错误地使用 Mutex 守卫

**错误示例**:

```rust
use std::sync::{Arc, Mutex};

let data = Arc::new(Mutex::new(vec![1, 2, 3]));

let lock = data.lock().unwrap();
let first = &lock[0];  // 持有对锁内数据的引用
// lock 守卫在此之后被 drop，但 first 引用仍然"有效"
// 实际上这是未定义行为（编译器通常会阻止）
```

**原因**: MutexGuard 被释放后，锁内数据的引用会变为悬空指针。

**修正**:

```rust
let first = {
    let lock = data.lock().unwrap();
    lock[0]  // 复制值，而不是返回引用
}; // lock 在此处释放
```

---

### 反例 5: Pin 误用导致未定义行为

**错误示例**:

```rust
use std::pin::Pin;

struct Unmovable {
    data: String,
    self_ptr: *const String,
}

impl Unmovable {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Unmovable {
            data,
            self_ptr: std::ptr::null(),
        });
        // ❌ 不安全：直接修改 pin 后的数据
        boxed.self_ptr = &boxed.data;
        boxed
    }
}
```

**原因**: 直接修改 `Pin<Box<T>>` 可能破坏自引用不变量。

**修正**: 使用 `Pin::get_unchecked_mut` 在 unsafe 块中修改：

```rust
impl Unmovable {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Unmovable {
            data,
            self_ptr: std::ptr::null(),
        });

        let ptr = &boxed.data;
        unsafe {
            Pin::get_unchecked_mut(boxed.as_mut()).self_ptr = ptr;
        }
        boxed
    }
}
```

---

## 📚 相关文档 {#-相关文档}

- [所有权与智能指针文档](../../../crates/c01_ownership_borrow_scope/docs/README.md)
- [智能指针 API 参考](../../../crates/c01_ownership_borrow_scope/docs/tier_03_references/05_智能指针API参考.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例位于 `crates/c01_ownership_borrow_scope/examples/`，可直接运行（例如：`cargo run -p c01_ownership_borrow_scope --example advanced_ownership_examples`）。

- [高级所有权与智能指针](../../../crates/c01_ownership_borrow_scope/examples/advanced_ownership_examples.rs)、[advanced_ownership_patterns.rs](../../../crates/c01_ownership_borrow_scope/examples/advanced_ownership_patterns.rs)
- [综合所有权示例](../../../crates/c01_ownership_borrow_scope/examples/comprehensive_ownership_examples.rs)、[moving00.rs](../../../crates/c01_ownership_borrow_scope/examples/moving00.rs)～[moving06.rs](../../../crates/c01_ownership_borrow_scope/examples/moving06.rs)
- [Rust 1.91/1.92 特性演示](../../../crates/c01_ownership_borrow_scope/examples/rust_191_features_demo.rs)、[rust_192_features_demo.rs](../../../crates/c01_ownership_borrow_scope/examples/rust_192_features_demo.rs)

---

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 智能指针文档](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Rust Reference - Smart Pointers](https://doc.rust-lang.org/reference/types/pointer.html)

### 项目内部文档

- [完整智能指针文档](../../../crates/c01_ownership_borrow_scope/docs/tier_03_references/05_智能指针API参考.md)
- [智能指针示例](../../../crates/c01_ownership_borrow_scope/examples/)
- [所有权系统研究](../../research_notes/formal_methods/ownership_model.md)

### 形式化理论与类型系统

- [所有权模型形式化](../../research_notes/formal_methods/ownership_model.md) — 所有权系统形式化基础
- [生命周期形式化](../../research_notes/formal_methods/lifetime_formalization.md) — 智能指针生命周期
- [Pin 形式化](../../research_notes/formal_methods/pin_self_referential.md) — 自引用结构形式化
- [Send/Sync 形式化](../../research_notes/formal_methods/send_sync_formalization.md) — 线程安全 trait 形式化
- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 智能指针类型理论

### 相关速查卡

- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与智能指针
- [类型系统速查卡](./type_system.md) - 指针类型
- [线程与并发速查卡](./threads_concurrency_cheatsheet.md) - Arc 在多线程中的应用
- [异步编程速查卡](./async_patterns.md) - Arc 在异步中的应用

---

**最后更新**: 2026-01-27
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.0 更新完成**

🎯 **掌握智能指针，灵活管理内存！**
