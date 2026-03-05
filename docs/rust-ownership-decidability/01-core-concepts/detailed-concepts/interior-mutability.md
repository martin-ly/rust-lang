# 内部可变性模式

> **目标**: 全面掌握 Rust 内部可变性模式，包括 `Cell<T>`、`RefCell<T>`、`Mutex<T>`、`RwLock<T>` 的工作原理和使用场景。

---

## 目录

- [内部可变性模式](#内部可变性模式)
  - [目录](#目录)
  - [1. 形式化定义](#1-形式化定义)
    - [1.1 内部可变性的形式化模型](#11-内部可变性的形式化模型)
    - [1.2 内部可变性的安全保证](#12-内部可变性的安全保证)
    - [1.3 内部可变性类型谱系](#13-内部可变性类型谱系)
  - [2. Cell 详解](#2-cell-详解)
    - [2.1 Cell 的形式化定义](#21-cell-的形式化定义)
    - [2.2 Cell 的核心操作](#22-cell-的核心操作)
    - [2.3 Cell 与 Copy 类型](#23-cell-与-copy-类型)
    - [2.4 Cell 的内存模型](#24-cell-的内存模型)
    - [2.5 Cell 的线程不安全性](#25-cell-的线程不安全性)
    - [2.6 Cell 的实际应用场景](#26-cell-的实际应用场景)
      - [场景 1: 延迟初始化](#场景-1-延迟初始化)
      - [场景 2: 计数器](#场景-2-计数器)
      - [场景 3: 图结构中的标记](#场景-3-图结构中的标记)
  - [3. RefCell 深入](#3-refcell-深入)
    - [3.1 RefCell 的形式化定义](#31-refcell-的形式化定义)
    - [3.2 RefCell 的运行时借用规则](#32-refcell-的运行时借用规则)
    - [3.3 运行时借用检查](#33-运行时借用检查)
    - [3.4 RefCell 的 panic 与 try\_ 方法](#34-refcell-的-panic-与-try_-方法)
    - [3.5 RefCell 与 Rc 的组合](#35-refcell-与-rc-的组合)
    - [3.6 RefCell 的常见陷阱](#36-refcell-的常见陷阱)
      - [陷阱 1: 运行时 panic](#陷阱-1-运行时-panic)
      - [陷阱 2: 引用泄露](#陷阱-2-引用泄露)
    - [3.7 RefCell 与 Observable 模式](#37-refcell-与-observable-模式)
  - [4. 线程安全内部可变性](#4-线程安全内部可变性)
    - [4.1 Mutex 详解](#41-mutex-详解)
    - [4.2 Mutex 的 poison 机制](#42-mutex-的-poison-机制)
    - [4.3 RwLock 详解](#43-rwlock-详解)
    - [4.4 Atomic 类型](#44-atomic-类型)
    - [4.5 线程安全类型的组合](#45-线程安全类型的组合)
  - [5. 常见陷阱与解决方案](#5-常见陷阱与解决方案)
    - [陷阱 1: RefCell 运行时 panic](#陷阱-1-refcell-运行时-panic)
    - [陷阱 2: Mutex 死锁](#陷阱-2-mutex-死锁)
    - [陷阱 3: 持有锁过长时间](#陷阱-3-持有锁过长时间)
    - [陷阱 4: 在 async 中使用 Mutex](#陷阱-4-在-async-中使用-mutex)
    - [陷阱 5: 循环引用导致内存泄漏](#陷阱-5-循环引用导致内存泄漏)
  - [6. 与其他语言对比](#6-与其他语言对比)
    - [6.1 C++: mutable 和 const\_cast](#61-c-mutable-和-const_cast)
    - [6.2 Java: final 与对象状态](#62-java-final-与对象状态)
    - [6.3 Swift: 值类型与引用类型](#63-swift-值类型与引用类型)
    - [6.4 Go: 通道与互斥](#64-go-通道与互斥)
  - [7. 性能影响分析](#7-性能影响分析)
    - [7.1 运行时开销对比](#71-运行时开销对比)
    - [7.2 基准测试](#72-基准测试)
    - [7.3 缓存影响](#73-缓存影响)
    - [7.4 内存布局](#74-内存布局)
  - [8. 高级模式](#8-高级模式)
    - [8.1 自定义内部可变性类型](#81-自定义内部可变性类型)
    - [8.2 读写锁的升级/降级](#82-读写锁的升级降级)
    - [8.3 无锁数据结构基础](#83-无锁数据结构基础)
    - [8.4 作用域线程模式](#84-作用域线程模式)
  - [总结](#总结)

---

## 1. 形式化定义

### 1.1 内部可变性的形式化模型

**定义 1.1** (内部可变性): 内部可变性是指在拥有不可变引用 (`&T`) 的情况下修改 `T` 内部状态的能力。

**形式化表示**:

```
let x: T
let r: &T = &x
// 内部可变性允许通过 r 修改 x 的内部状态
```

**定义 1.2** (不变量分类):

- **外部可变性**: 通过 `&mut T` 修改
- **内部可变性**: 通过 `&T` 修改（需要特殊类型）

### 1.2 内部可变性的安全保证

内部可变性类型必须维持 Rust 的核心安全不变量：

```
类型 T 实现内部可变性当且仅当：
1. T 的 API 维护别名 XOR 可变规则
2. 运行时检查防止违反借用规则
3. 单线程或多线程安全通过类型系统保证
```

### 1.3 内部可变性类型谱系

```
                    内部可变性类型
                          │
            ┌─────────────┼─────────────┐
            ▼             ▼             ▼
      单线程           单线程           多线程
     (Move)        (RefCount)      (Sync)
            │             │             │
            ▼             ▼             ▼
       Cell<T>      RefCell<T>    Mutex<T>
                        │        RwLock<T>
                        ▼        Atomic*
                   UnsafeCell<T>
                   (底层原语)
```

---

## 2. Cell<T> 详解

### 2.1 Cell 的形式化定义

**定义 2.1** (`Cell<T>`): `Cell<T>` 是一种提供内部可变性的容器，通过值的**移动**实现修改，适用于实现 `Copy` 的类型。

```rust
pub struct Cell<T: ?Sized> {
    value: UnsafeCell<T>,
}
```

### 2.2 Cell 的核心操作

```rust
use std::cell::Cell;

fn main() {
    let cell = Cell::new(5);

    // 获取值（对于 Copy 类型）
    let val = cell.get();
    println!("Initial: {}", val);  // 5

    // 设置新值
    cell.set(10);
    println!("After set: {}", cell.get());  // 10

    // 替换并返回旧值
    let old = cell.replace(20);
    println!("Old: {}, New: {}", old, cell.get());  // 10, 20
}
```

### 2.3 Cell 与 Copy 类型

`Cell<T>` 要求 `T: Copy` 才能使用 `get()`：

```rust
use std::cell::Cell;

// ✅ 对于 Copy 类型
let int_cell: Cell<i32> = Cell::new(42);
let val: i32 = int_cell.get();  // 复制值

// ❌ 对于非 Copy 类型
let string_cell: Cell<String> = Cell::new(String::from("hello"));
// let s: String = string_cell.get();  // 编译错误：String 不是 Copy
```

### 2.4 Cell 的内存模型

```rust
// Cell<i32> 的内存布局
// 栈上：
// ┌─────────────────┐
// │ value: i32      │  4 bytes
// └─────────────────┘

// Cell<String> 的内存布局
// 栈上：
// ┌─────────────────┬─────────────────┬─────────────────┐
// │ ptr: *mut u8    │ len: usize      │ cap: usize      │  24 bytes
// └────────┬────────┴─────────────────┴─────────────────┘
//          │
//          ▼
// 堆上："hello"
```

### 2.5 Cell 的线程不安全性

`Cell<T>` 故意不实现 `Sync`，防止多线程同时访问：

```rust
use std::cell::Cell;
use std::sync::Arc;
use std::thread;

// ❌ 编译错误：Cell 不能在线程间共享
let cell = Arc::new(Cell::new(0));
let cell_clone = Arc::clone(&cell);

thread::spawn(move || {
    cell_clone.set(1);  // 错误：Cell 不是 Sync
});
```

### 2.6 Cell 的实际应用场景

#### 场景 1: 延迟初始化

```rust
use std::cell::Cell;

struct LazyValue<T> {
    computed: Cell<bool>,
    value: Cell<Option<T>>,
    compute_fn: fn() -> T,
}

impl<T: Copy> LazyValue<T> {
    fn new(f: fn() -> T) -> Self {
        LazyValue {
            computed: Cell::new(false),
            value: Cell::new(None),
            compute_fn: f,
        }
    }

    fn get(&self) -> T {
        if !self.computed.get() {
            self.value.set(Some((self.compute_fn)()));
            self.computed.set(true);
        }
        self.value.get().unwrap()
    }
}
```

#### 场景 2: 计数器

```rust
use std::cell::Cell;

struct Stats {
    read_count: Cell<u64>,
    write_count: Cell<u64>,
}

impl Stats {
    fn record_read(&self) {
        self.read_count.set(self.read_count.get() + 1);
    }

    fn record_write(&self) {
        self.write_count.set(self.write_count.get() + 1);
    }

    fn report(&self) -> (u64, u64) {
        (self.read_count.get(), self.write_count.get())
    }
}
```

#### 场景 3: 图结构中的标记

```rust
use std::cell::Cell;
use std::rc::Rc;

struct Node {
    value: i32,
    visited: Cell<bool>,
    neighbors: Vec<Rc<Node>>,
}

fn dfs(node: &Rc<Node>) {
    if node.visited.get() {
        return;
    }
    node.visited.set(true);
    println!("Visit: {}", node.value);

    for neighbor in &node.neighbors {
        dfs(neighbor);
    }
}
```

---

## 3. RefCell<T> 深入

### 3.1 RefCell 的形式化定义

**定义 3.1** (`RefCell<T>`): `RefCell<T>` 提供运行时借用检查的内部可变性，允许在单线程环境中获取可变或不可变引用。

```rust
pub struct RefCell<T: ?Sized> {
    borrow: Cell<BorrowFlag>,
    value: UnsafeCell<T>,
}

type BorrowFlag = isize;
const UNUSED: BorrowFlag = 0;
```

### 3.2 RefCell 的运行时借用规则

```rust
use std::cell::RefCell;

fn main() {
    let cell = RefCell::new(vec![1, 2, 3]);

    // 获取不可变借用
    {
        let v = cell.borrow();
        println!("{:?}", *v);  // [1, 2, 3]
    }  // 借用在这里结束

    // 获取可变借用
    {
        let mut v = cell.borrow_mut();
        v.push(4);
    }

    println!("{:?}", cell.borrow());  // [1, 2, 3, 4]
}
```

### 3.3 运行时借用检查

```rust
use std::cell::RefCell;

fn main() {
    let cell = RefCell::new(5);

    let _borrow1 = cell.borrow();
    let _borrow2 = cell.borrow();

    // ❌ 运行时 panic：已经存在不可变借用
    // let _borrow_mut = cell.borrow_mut();

    println!("{}", _borrow1);
}
```

**借用计数原理**:

```
borrow = 0:    无人借用（可以获取可变或不可变）
borrow > 0:    有 n 个不可变借用（只能再获取不可变）
borrow = -1:   有一个可变借用（不能再获取任何借用）
```

### 3.4 RefCell 的 panic 与 try_ 方法

```rust
use std::cell::RefCell;

fn safe_access(cell: &RefCell<Vec<i32>>) {
    // 尝试获取借用，失败时返回 Err 而非 panic
    match cell.try_borrow() {
        Ok(v) => println!("Got: {:?}", v),
        Err(_) => println!("Already mutably borrowed"),
    }

    match cell.try_borrow_mut() {
        Ok(mut v) => {
            v.push(42);
            println!("Modified");
        }
        Err(_) => println!("Already borrowed"),
    }
}
```

### 3.5 RefCell 与 Rc 的组合

```rust
use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    // 多个所有者 + 内部可变性
    let shared_vec: Rc<RefCell<Vec<i32>>> = Rc::new(RefCell::new(vec![1, 2, 3]));

    let shared1 = Rc::clone(&shared_vec);
    let shared2 = Rc::clone(&shared_vec);

    // 通过 shared1 修改
    shared1.borrow_mut().push(4);

    // 通过 shared2 读取
    println!("{:?}", shared2.borrow());  // [1, 2, 3, 4]
}
```

### 3.6 RefCell 的常见陷阱

#### 陷阱 1: 运行时 panic

```rust
use std::cell::RefCell;

fn panic_example(cell: &RefCell<i32>) {
    let mut ref1 = cell.borrow_mut();
    let ref2 = cell.borrow();  // ❌ panic!
    println!("{}", ref2);
}
```

#### 陷阱 2: 引用泄露

```rust
use std::cell::RefCell;

fn leak_example() {
    let cell = RefCell::new(5);

    // 获取 Ref，但不立即使用
    let leaked = cell.borrow();

    // ... 很多代码 ...

    // 在此期间，cell 一直被借用
    // cell.borrow_mut();  // 会 panic

    println!("{}", leaked);  // 在这里才使用
}
```

**解决方案**: 缩小借用范围

```rust
fn fixed_example() {
    let cell = RefCell::new(5);

    {
        let value = cell.borrow();
        println!("{}", value);
    }  // 借用在这里结束

    // 现在可以获取可变借用
    *cell.borrow_mut() = 10;
}
```

### 3.7 RefCell 与 Observable 模式

```rust
use std::cell::RefCell;
use std::rc::Rc;

type Callback<T> = Box<dyn Fn(&T)>;

struct Observable<T> {
    value: RefCell<T>,
    observers: RefCell<Vec<Callback<T>>>,
}

impl<T: Clone> Observable<T> {
    fn new(value: T) -> Self {
        Observable {
            value: RefCell::new(value),
            observers: RefCell::new(Vec::new()),
        }
    }

    fn subscribe<F>(&self, callback: F)
    where
        F: Fn(&T) + 'static,
    {
        self.observers.borrow_mut().push(Box::new(callback));
    }

    fn set(&self, value: T) {
        *self.value.borrow_mut() = value.clone();
        for observer in self.observers.borrow().iter() {
            observer(&value);
        }
    }

    fn get(&self) -> T {
        self.value.borrow().clone()
    }
}
```

---

## 4. 线程安全内部可变性

### 4.1 Mutex<T> 详解

**定义 4.1** (`Mutex<T>`): `Mutex<T>` 提供互斥访问，确保任意时刻只有一个线程可以访问数据。

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

    println!("Result: {}", *counter.lock().unwrap());  // 10
}
```

### 4.2 Mutex 的 poison 机制

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let mutex_clone = Arc::clone(&mutex);

    let handle = thread::spawn(move || {
        let _guard = mutex_clone.lock().unwrap();
        panic!("Thread panicked while holding lock!");
    });

    let _ = handle.join();

    // 锁被 "poisoned"，其他线程可以检测到这个状态
    match mutex.lock() {
        Ok(guard) => println!("Value: {}", *guard),
        Err(poisoned) => {
            println!("Lock was poisoned!");
            let guard = poisoned.into_inner();
            println!("Recovered value: {}", *guard);
        }
    }
}
```

### 4.3 RwLock<T> 详解

**定义 4.2** (`RwLock<T>`): `RwLock<T>` 提供多读单写的访问模式，适用于读多写少的场景。

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn main() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读线程
    let mut handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Reader {}: {:?}", i, *read_guard);
        }));
    }

    // 一个写线程
    let data_write = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut write_guard = data_write.write().unwrap();
        write_guard.push(4);
        println!("Writer: modified data");
    }));

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 4.4 Atomic 类型

对于简单类型，可以使用无锁的原子操作：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

fn main() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            // 不同的一致性级别
            counter.fetch_add(1, Ordering::SeqCst);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", counter.load(Ordering::SeqCst));
}
```

**内存序选择**:

| Ordering | 说明 | 使用场景 |
|----------|------|----------|
| `Relaxed` | 无顺序约束 | 简单的计数器 |
| `Acquire` | 加载时获取 | 锁的释放 |
| `Release` | 存储时释放 | 锁的获取 |
| `AcqRel` | 两者都有 | CAS 操作 |
| `SeqCst` | 顺序一致 | 默认安全选择 |

### 4.5 线程安全类型的组合

```rust
use std::sync::{Arc, RwLock};
use std::cell::RefCell;

// ❌ 错误：RefCell 不是 Sync，不能在多线程间共享
// let data: Arc<RefCell<Vec<i32>>> = ...;

// ✅ 正确：使用 Mutex 或 RwLock
let data: Arc<RwLock<Vec<i32>>> = Arc::new(RwLock::new(vec![]));

// ✅ 如果需要 RefCell 的功能，在单线程内使用
let data: Arc<RwLock<RefCell<Vec<i32>>>> =
    Arc::new(RwLock::new(RefCell::new(vec![])));
// 注意：这种组合很少需要
```

---

## 5. 常见陷阱与解决方案

### 陷阱 1: RefCell 运行时 panic

```rust
use std::cell::RefCell;

fn recursive_call(cell: &RefCell<i32>) {
    let mut borrow = cell.borrow_mut();
    if *borrow < 10 {
        *borrow += 1;
        // ❌ panic：已经持有 borrow_mut，又尝试获取
        recursive_call(cell);
    }
}
```

**解决方案**:

```rust
fn recursive_call_fixed(cell: &RefCell<i32>) {
    let should_recurse = {
        let mut borrow = cell.borrow_mut();
        if *borrow < 10 {
            *borrow += 1;
            true
        } else {
            false
        }
    };  // borrow 在这里结束

    if should_recurse {
        recursive_call_fixed(cell);
    }
}
```

### 陷阱 2: Mutex 死锁

```rust
use std::sync::{Mutex, Arc};

fn deadlock_example() {
    let m1 = Arc::new(Mutex::new(0));
    let m2 = Arc::new(Mutex::new(0));

    let m1_clone = Arc::clone(&m1);
    let m2_clone = Arc::clone(&m2);

    std::thread::spawn(move || {
        let _guard1 = m1_clone.lock().unwrap();
        let _guard2 = m2_clone.lock().unwrap();  // 可能死锁
    });

    let _guard2 = m2.lock().unwrap();
    let _guard1 = m1.lock().unwrap();  // 可能死锁
}
```

**解决方案**: 统一加锁顺序

```rust
fn safe_locking() {
    let m1 = Arc::new(Mutex::new(0));
    let m2 = Arc::new(Mutex::new(0));

    // 总是先锁 m1，再锁 m2
    let _guard1 = m1.lock().unwrap();
    let _guard2 = m2.lock().unwrap();
}
```

### 陷阱 3: 持有锁过长时间

```rust
use std::sync::Mutex;
use std::thread;
use std::time::Duration;

fn slow_with_lock() {
    let data = Mutex::new(vec![1, 2, 3]);

    let guard = data.lock().unwrap();
    // ❌ 持有锁的同时进行耗时操作
    thread::sleep(Duration::from_secs(10));
    drop(guard);
}
```

**解决方案**: 缩小锁的作用域

```rust
fn fast_with_lock() {
    let data = Mutex::new(vec![1, 2, 3]);

    {
        let guard = data.lock().unwrap();
        // 快速操作
        let _ = guard.len();
    }  // 锁在这里释放

    // 耗时操作在锁外进行
    thread::sleep(Duration::from_secs(10));
}
```

### 陷阱 4: 在 async 中使用 Mutex

```rust
// ❌ 错误：标准库 Mutex 在 async 中可能导致线程阻塞
async fn bad_async() {
    let mutex = std::sync::Mutex::new(0);
    let _guard = mutex.lock().unwrap();
    some_async_fn().await;  // 可能阻塞整个线程！
}

// ✅ 正确：使用 tokio::sync::Mutex
async fn good_async() {
    let mutex = tokio::sync::Mutex::new(0);
    let _guard = mutex.lock().await;
    some_async_fn().await;  // 可以正确让出
}
```

### 陷阱 5: 循环引用导致内存泄漏

```rust
use std::cell::RefCell;
use std::rc::Rc;

struct Node {
    next: Option<Rc<RefCell<Node>>>,
    prev: Option<Rc<RefCell<Node>>>,
}

fn memory_leak() {
    let node1 = Rc::new(RefCell::new(Node { next: None, prev: None }));
    let node2 = Rc::new(RefCell::new(Node { next: None, prev: None }));

    node1.borrow_mut().next = Some(Rc::clone(&node2));
    node2.borrow_mut().prev = Some(Rc::clone(&node1));

    // 循环引用！内存泄漏
}
```

**解决方案**: 使用 Weak 引用

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};

struct SafeNode {
    next: Option<Rc<RefCell<SafeNode>>>,
    prev: Option<Weak<RefCell<SafeNode>>>,  // Weak 不增加引用计数
}

fn no_memory_leak() {
    let node1 = Rc::new(RefCell::new(SafeNode { next: None, prev: None }));
    let node2 = Rc::new(RefCell::new(SafeNode { next: None, prev: None }));

    node1.borrow_mut().next = Some(Rc::clone(&node2));
    node2.borrow_mut().prev = Some(Rc::downgrade(&node1));

    // 可以正确释放
}
```

---

## 6. 与其他语言对比

### 6.1 C++: mutable 和 const_cast

**C++ 版本**:

```cpp
class Logger {
    mutable int log_count = 0;  // 可以在 const 方法中修改
public:
    void log(const std::string& msg) const {
        ++log_count;  // 允许，因为是 mutable
        std::cout << msg << std::endl;
    }
};

// const_cast（危险！）
void dangerous(const int* ptr) {
    int* mutable_ptr = const_cast<int*>(ptr);
    *mutable_ptr = 42;  // 未定义行为如果原值真的是 const
}
```

**对比分析**:

| 特性 | Rust | C++ |
|------|------|-----|
| 内部可变性 | Cell/RefCell/Mutex | mutable/const_cast |
| 安全检查 | 编译期 + 运行期 | 无（程序员责任）|
| 线程安全 | 类型系统区分 | 无区分 |
| 性能开销 | 零成本或最小 | 相同 |

### 6.2 Java: final 与对象状态

**Java 版本**:

```java
public class Counter {
    private int count = 0;  // 即使引用是 final，状态也可变

    public synchronized void increment() {  // 需要显式同步
        count++;
    }

    public synchronized int get() {
        return count;
    }
}

// 使用
final Counter counter = new Counter();  // 引用不可变
counter.increment();  // 但对象状态可变
```

**对比分析**:

| 特性 | Rust | Java |
|------|------|------|
| 不可变性 | &T 保证递归不可变 | final 只保证引用 |
| 线程同步 | Mutex/RwLock 类型化 | synchronized 方法/块 |
| 编译期检查 | 完整借用检查 | 无 |
| 运行时检查 | RefCell panic | 运行时异常 |

### 6.3 Swift: 值类型与引用类型

**Swift 版本**:

```swift
struct ValueType {  // 值类型，隐式 Copy
    var x: Int
}

class ReferenceType {  // 引用类型
    var x: Int
    init(_ x: Int) { self.x = x }
}

var v = ValueType(x: 5)
var v2 = v  // 复制
v2.x = 10
print(v.x)  // 5，未改变

var r = ReferenceType(5)
var r2 = r  // 共享引用
r2.x = 10
print(r.x)  // 10，已改变

// 需要显式同步
import Foundation
let lock = NSLock()
lock.lock()
// 临界区
lock.unlock()
```

**对比分析**:

| 特性 | Rust | Swift |
|------|------|-------|
| 值类型语义 | Copy trait | 隐式值语义 |
| 内部可变性 | Cell/RefCell | 类成员可变 |
| 线程安全 | 编译期保证 | 运行时责任 |
| ARC 开销 | 无 | 有 |

### 6.4 Go: 通道与互斥

**Go 版本**:

```go
package main

import (
    "sync"
)

type Counter struct {
    mu    sync.Mutex
    count int
}

func (c *Counter) Increment() {
    c.mu.Lock()
    defer c.mu.Unlock()
    c.count++
}

func main() {
    c := &Counter{}
    // Go 不区分共享/可变，全靠程序员
}
```

**对比分析**:

| 特性 | Rust | Go |
|------|------|-----|
| 内部可变性 | 类型系统支持 | 无 |
| 同步原语 | Mutex<T> | sync.Mutex |
| 编译期安全 | 借用检查 | 无 |
| 惯用模式 | 共享状态 | 通道通信 |

---

## 7. 性能影响分析

### 7.1 运行时开销对比

| 类型 | 单线程开销 | 多线程开销 | 使用场景 |
|------|------------|------------|----------|
| `Cell<T>` | 无 | N/A | Copy 类型计数器 |
| `RefCell<T>` | 整数增减 | N/A | 单线程复杂借用 |
| `Mutex<T>` | N/A | 系统调用 + 上下文切换 | 多线程独占访问 |
| `RwLock<T>` | N/A | 读：原子操作，写：系统调用 | 读多写少 |
| `Atomic*` | N/A | 原子指令 | 简单计数器 |

### 7.2 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::cell::RefCell;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};

fn bench_refcell(c: &mut Criterion) {
    let cell = RefCell::new(0usize);
    c.bench_function("refcell_increment", |b| {
        b.iter(|| {
            *cell.borrow_mut() += 1;
        });
    });
}

fn bench_mutex(c: &mut Criterion) {
    let mutex = Arc::new(Mutex::new(0usize));
    c.bench_function("mutex_increment", |b| {
        b.iter(|| {
            *mutex.lock().unwrap() += 1;
        });
    });
}

fn bench_atomic(c: &mut Criterion) {
    let atomic = AtomicUsize::new(0);
    c.bench_function("atomic_increment", |b| {
        b.iter(|| {
            atomic.fetch_add(1, Ordering::Relaxed);
        });
    });
}

criterion_group!(benches, bench_refcell, bench_mutex, bench_atomic);
criterion_main!(benches);
```

**预期结果**（典型值）:

```
refcell_increment    time: [0.5 ns]     # 单线程，非常轻量
mutex_increment      time: [25 ns]      # 系统调用开销
atomic_increment     time: [2 ns]       # 原子指令，跨核同步
```

### 7.3 缓存影响

```rust
// 坏的访问模式：缓存行乒乓
fn cache_unfriendly(data: &[AtomicUsize]) {
    for _ in 0..1000 {
        for item in data {
            item.fetch_add(1, Ordering::SeqCst);  // 强制缓存同步
        }
    }
}

// 好的访问模式：减少同步
fn cache_friendly(data: &[AtomicUsize]) {
    for item in data {
        for _ in 0..1000 {
            item.fetch_add(1, Ordering::Relaxed);  // 允许重排序
        }
    }
}
```

### 7.4 内存布局

```rust
// RefCell<T> 的内存开销
struct RefCell<T> {
    borrow: Cell<isize>,  // 8 bytes（借用计数）
    value: UnsafeCell<T>, // T 的大小 + 对齐
}

// Mutex<T> 的内存开销（平台相关）
struct Mutex<T> {
    inner: sys::Mutex,    // 约 40 bytes（pthread_mutex_t）
    poison: Cell<bool>,   // 1 byte
    data: UnsafeCell<T>,  // T 的大小 + 对齐
}
```

---

## 8. 高级模式

### 8.1 自定义内部可变性类型

```rust
use std::cell::UnsafeCell;

// 简化的单线程计数器
struct MyCell<T> {
    value: UnsafeCell<T>,
}

impl<T: Copy> MyCell<T> {
    fn new(value: T) -> Self {
        MyCell {
            value: UnsafeCell::new(value),
        }
    }

    fn get(&self) -> T {
        unsafe { *self.value.get() }
    }

    fn set(&self, value: T) {
        unsafe {
            *self.value.get() = value;
        }
    }
}

// 故意不实现 Sync
impl<T> !Sync for MyCell<T> {}
```

### 8.2 读写锁的升级/降级

```rust
use std::sync::{Arc, RwLock};

fn upgrade_pattern(data: Arc<RwLock<Vec<i32>>>) {
    // 先获取读锁
    let read_guard = data.read().unwrap();
    let needs_write = read_guard.is_empty();
    drop(read_guard);  // 释放读锁

    if needs_write {
        // 再获取写锁
        let mut write_guard = data.write().unwrap();
        write_guard.push(42);
    }
}
```

### 8.3 无锁数据结构基础

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 简单的无锁栈节点
struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        LockFreeStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            match self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => continue,  // 重试
            }
        }
    }
}
```

### 8.4 作用域线程模式

```rust
use std::sync::Mutex;
use crossbeam::scope;  // crossbeam crate

fn scoped_threads() {
    let data = Mutex::new(vec![1, 2, 3]);

    scope(|s| {
        for i in 0..3 {
            s.spawn(|_| {
                let mut guard = data.lock().unwrap();
                guard[i] *= 2;
            });
        }
    }).unwrap();

    // 所有线程在这里已经 join
    println!("{:?}", data.lock().unwrap());
}
```

---

## 总结

内部可变性模式是 Rust 类型系统的重要组成部分，它提供了：

1. **单线程内部可变性**: `Cell<T>` 和 `RefCell<T>` 用于在 `&T` 上下文中修改数据
2. **线程安全内部可变性**: `Mutex<T>`、`RwLock<T>` 和 `Atomic*` 用于多线程环境
3. **运行时检查**: `RefCell` 和锁提供运行时借用检查
4. **零成本抽象**: `Cell` 和 `Atomic` 在单线程环境下无运行时开销

掌握内部可变性模式是编写灵活、高效的 Rust 代码的关键。

---

*继续学习: [trait-system.md](./trait-system.md)*
