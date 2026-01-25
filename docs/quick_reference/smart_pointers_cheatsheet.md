# 🎯 Rust 智能指针速查卡

> **快速参考** | [完整文档](../../crates/c01_ownership_borrow_scope/docs/) | [代码示例](../../crates/c01_ownership_borrow_scope/examples/)
> **最后更新**: 2026-01-26 | **Rust 版本**: 1.93.0+ | **Edition**: 2024

---

## 📋 目录

- [🎯 Rust 智能指针速查卡](#-rust-智能指针速查卡)
  - [📋 目录](#-目录)
  - [🎯 智能指针概览](#-智能指针概览)
  - [📦 Box - 堆分配](#-box---堆分配)
    - [基本用法](#基本用法)
    - [使用场景](#使用场景)
    - [API](#api)
  - [🔗 Rc - 引用计数（单线程）](#-rc---引用计数单线程)
    - [基本用法](#基本用法-1)
    - [使用场景](#使用场景-1)
    - [API](#api-1)
  - [🔗 Arc - 原子引用计数（多线程）](#-arc---原子引用计数多线程)
    - [基本用法](#基本用法-2)
    - [使用场景](#使用场景-2)
    - [API](#api-2)
  - [🔓 RefCell - 内部可变性（单线程）](#-refcell---内部可变性单线程)
    - [基本用法](#基本用法-3)
    - [使用场景](#使用场景-3)
    - [API](#api-3)
    - [运行时借用检查](#运行时借用检查)
  - [🔒 Mutex - 互斥锁（多线程）](#-mutex---互斥锁多线程)
    - [基本用法](#基本用法-4)
    - [使用场景](#使用场景-4)
    - [API](#api-4)
  - [🔓 RwLock - 读写锁（多线程）](#-rwlock---读写锁多线程)
    - [基本用法](#基本用法-5)
    - [使用场景](#使用场景-5)
    - [API](#api-5)
  - [🔗 Weak - 弱引用](#-weak---弱引用)
    - [基本用法](#基本用法-6)
    - [使用场景](#使用场景-6)
    - [API](#api-6)
  - [🔄 组合模式](#-组合模式)
    - [Rc\<RefCell\> - 单线程内部可变性](#rcrefcell---单线程内部可变性)
    - [Arc\<Mutex\> - 多线程共享可变数据](#arcmutex---多线程共享可变数据)
    - [Arc\<RwLock\> - 多线程读写锁](#arcrwlock---多线程读写锁)
    - [Rc\<RefCell\<Vec\>\> - 共享可变向量](#rcrefcellvec---共享可变向量)
  - [🎯 选择指南](#-选择指南)
    - [决策树](#决策树)
    - [性能对比](#性能对比)
    - [常见组合](#常见组合)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)


---

## 🎯 智能指针概览

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

## 📦 Box<T> - 堆分配

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

### 使用场景

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

## 🔗 Rc<T> - 引用计数（单线程）

### 基本用法

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

### 使用场景

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

### API

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

## 🔗 Arc<T> - 原子引用计数（多线程）

### 基本用法

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

### 使用场景

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

### API

```rust
use std::sync::Arc;

// API 与 Rc 相同，但线程安全
let arc = Arc::new(value);
let arc2 = Arc::clone(&arc);
let count = Arc::strong_count(&arc);
```

---

## 🔓 RefCell<T> - 内部可变性（单线程）

### 基本用法

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

### 使用场景

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

### API

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

## 🔒 Mutex<T> - 互斥锁（多线程）

### 基本用法

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

### 使用场景

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

### API

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

## 🔓 RwLock<T> - 读写锁（多线程）

### 基本用法

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

### 使用场景

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

### API

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

## 🔗 Weak<T> - 弱引用

### 基本用法

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

### 使用场景

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

### API

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

## 🔄 组合模式

### Rc<RefCell<T>> - 单线程内部可变性

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

### Arc<Mutex<T>> - 多线程共享可变数据

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

### Arc<RwLock<T>> - 多线程读写锁

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

### Rc<RefCell<Vec<T>>> - 共享可变向量

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

## 🎯 选择指南

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

| 类型 | 开销 | 线程安全 | 可变性 |
|------|------|---------|--------|
| `Box<T>` | 堆分配 | ✅ | 编译时检查 |
| `Rc<T>` | 引用计数 | ❌ | 编译时检查 |
| `Arc<T>` | 原子引用计数 | ✅ | 编译时检查 |
| `RefCell<T>` | 运行时检查 | ❌ | 运行时检查 |
| `Mutex<T>` | 锁开销 | ✅ | 运行时检查 |
| `RwLock<T>` | 锁开销 | ✅ | 运行时检查 |

### 常见组合

| 场景 | 推荐组合 |
|------|---------|
| 单线程共享可变 | `Rc<RefCell<T>>` |
| 多线程共享可变 | `Arc<Mutex<T>>` |
| 多线程读多写少 | `Arc<RwLock<T>>` |
| 树结构（避免循环） | `Rc<Node>` + `Weak<Node>` |

---

## 📚 相关资源

### 官方文档

- [Rust 智能指针文档](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Rust Reference - Smart Pointers](https://doc.rust-lang.org/reference/types/pointer.html)

### 项目内部文档

- [完整智能指针文档](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/05_智能指针API参考.md)
- [智能指针示例](../../crates/c01_ownership_borrow_scope/examples/)
- [所有权系统研究](../../docs/research_notes/formal_methods/ownership_model.md)

### 相关速查卡

- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与智能指针
- [类型系统速查卡](./type_system.md) - 指针类型
- [线程与并发速查卡](./threads_concurrency_cheatsheet.md) - Arc 在多线程中的应用
- [异步编程速查卡](./async_patterns.md) - Arc 在异步中的应用

---

**最后更新**: 2026-01-26
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.0 更新完成**

🎯 **掌握智能指针，灵活管理内存！**
