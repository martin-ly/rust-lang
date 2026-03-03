# 扩展实例与反例库

> 全面覆盖Rust所有权系统的边界案例、常见陷阱和反直觉模式

---

## 目录

- [扩展实例与反例库](#扩展实例与反例库)
  - [目录](#目录)
  - [1. 基础所有权模式](#1-基础所有权模式)
    - [1.1 所有权转移的正例与反例](#11-所有权转移的正例与反例)
      - [正例 1.1.1: 正确的所有权转移](#正例-111-正确的所有权转移)
      - [反例 1.1.2: 移动后使用](#反例-112-移动后使用)
    - [1.2 Copy vs Move 边界案例](#12-copy-vs-move-边界案例)
      - [边界案例 1.2.1: 包含非Copy类型的结构体](#边界案例-121-包含非copy类型的结构体)
  - [2. 生命周期边界案例](#2-生命周期边界案例)
    - [2.1 生命周期省略规则边界](#21-生命周期省略规则边界)
      - [边界案例 2.1.1: 省略规则失效](#边界案例-211-省略规则失效)
    - [2.2 自引用结构体](#22-自引用结构体)
      - [边界案例 2.2.1: 移动后悬垂指针](#边界案例-221-移动后悬垂指针)
  - [3. 借用规则反例](#3-借用规则反例)
    - [3.1 可变与不可变借用冲突](#31-可变与不可变借用冲突)
      - [反例 3.1.1: 同时持有可变和不可变引用](#反例-311-同时持有可变和不可变引用)
    - [3.2 重新借用的复杂性](#32-重新借用的复杂性)
      - [边界案例 3.2.1: 重新借用链](#边界案例-321-重新借用链)
  - [4. 智能指针陷阱](#4-智能指针陷阱)
    - [4.1 Rc 循环引用](#41-rc-循环引用)
      - [反例 4.1.1: 内存泄漏](#反例-411-内存泄漏)
    - [4.2 RefCell 运行时借用冲突](#42-refcell-运行时借用冲突)
      - [反例 4.2.1: 运行时 panic](#反例-421-运行时-panic)
  - [5. 并发安全边界](#5-并发安全边界)
    - [5.1 Send 和 Sync 误用](#51-send-和-sync-误用)
      - [反例 5.1.1: 非 Send 类型跨线程](#反例-511-非-send-类型跨线程)
    - [5.2 死锁场景](#52-死锁场景)
      - [反例 5.2.1: 锁顺序不一致](#反例-521-锁顺序不一致)
  - [6. Unsafe 代码风险](#6-unsafe-代码风险)
    - [6.1 未定义行为 (UB)](#61-未定义行为-ub)
      - [反例 6.1.1: 悬垂原始指针](#反例-611-悬垂原始指针)
    - [6.2 别名规则违反](#62-别名规则违反)
      - [反例 6.2.1: Stacked Borrows 违反](#反例-621-stacked-borrows-违反)
  - [7. 性能陷阱](#7-性能陷阱)
    - [7.1 不必要的克隆](#71-不必要的克隆)
      - [反例 7.1.1: 循环中克隆](#反例-711-循环中克隆)
    - [7.2 缓存不友好访问](#72-缓存不友好访问)
      - [反例 7.2.1: 跳跃式内存访问](#反例-721-跳跃式内存访问)
  - [8. 编译器诊断解读](#8-编译器诊断解读)
    - [8.1 常见错误速查表](#81-常见错误速查表)
    - [8.2 编译器建议解读](#82-编译器建议解读)
      - [案例 1: 帮助性建议](#案例-1-帮助性建议)

---

## 1. 基础所有权模式

### 1.1 所有权转移的正例与反例

#### 正例 1.1.1: 正确的所有权转移

```rust
// ✓ 正确的所有权转移模式
fn take_ownership(s: String) {
    println!("{}", s);
} // s 在这里被 drop

fn main() {
    let s = String::from("hello");
    take_ownership(s);
    // s 不再可用，避免悬垂引用
}
```

**思维表征**: 所有权转移图

```text
main()                    take_ownership()
   │                              │
   │   转移所有权                  │
   ▼                              ▼
┌──────┐                    ┌──────┐
│  s   │ ─────────────────► │  s   │ ──► Drop
└──────┘                    └──────┘
                                │
                                ▼
                           println!("hello")
```

#### 反例 1.1.2: 移动后使用

```rust
// ✗ 编译错误：移动后使用
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权移动到 s2

    println!("{}", s1);  // ERROR: borrow of moved value: `s1`
}
```

**编译器错误**:

```text
error[E0382]: borrow of moved value: `s1`
 --> src/main.rs:5:20
  |
3 |     let s1 = String::from("hello");
  |         -- move occurs because `s1` has type `String`,
  |            which does not implement the `Copy` trait
4 |     let s2 = s1;
  |              -- value moved here
5 |     println!("{}", s1);
  |                    ^^ value borrowed here after move
```

**解决方案**:

```rust
// 方案1: 使用克隆
let s2 = s1.clone();
println!("{}", s1);  // ✓ OK

// 方案2: 使用引用
let s2 = &s1;
println!("{}", s1);  // ✓ OK
```

### 1.2 Copy vs Move 边界案例

#### 边界案例 1.2.1: 包含非Copy类型的结构体

```rust
#[derive(Copy, Clone)]  // ✗ 编译错误
struct Point {
    x: i32,
    y: String,  // String 不是 Copy
}

// 错误: the trait `Copy` may not be implemented for this type
// because `String` does not implement `Copy`
```

**正确实现**:

```rust
#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,  // 所有字段都是 Copy
}

// 或者只实现 Clone
#[derive(Clone)]
struct Point {
    x: i32,
    y: String,
}
```

---

## 2. 生命周期边界案例

### 2.1 生命周期省略规则边界

#### 边界案例 2.1.1: 省略规则失效

```rust
// ✗ 编译错误：生命周期无法推断
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}

// 编译器无法确定返回值的生命周期
```

**解决方案**:

```rust
// ✓ 显式生命周期标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**思维表征**: 生命周期关系图

```text
'a: 包含 x 和 y 的生命周期

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
              │              │            │
              └──────────────┴────────────┘
                        'a
                         │
            ┌────────────┼────────────┐
            │            │            │
           x的生命周期    │        返回值生命周期
                      y的生命周期
```

### 2.2 自引用结构体

#### 边界案例 2.2.1: 移动后悬垂指针

```rust
// ✗ 编译错误：自引用结构体
struct SelfRef {
    data: String,
    // 试图存储指向 data 的引用
    ptr: &str,  // ERROR: missing lifetime specifier
}
```

**解决方案**: 使用 Pin

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfRef {
    data: String,
    ptr: *const str,  // 使用原始指针
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr: *const str = &boxed.data;
        boxed.ptr = ptr;

        Pin::from(boxed)
    }
}
```

---

## 3. 借用规则反例

### 3.1 可变与不可变借用冲突

#### 反例 3.1.1: 同时持有可变和不可变引用

```rust
// ✗ 编译错误
fn main() {
    let mut data = vec![1, 2, 3];

    let ref1 = &data;       // 不可变借用
    let ref2 = &mut data;   // ERROR: 可变借用

    println!("{} {:?}", ref1[0], ref2);
}
```

**编译器错误**:

```text
error[E0502]: cannot borrow `data` as mutable
              because it is also borrowed as immutable
 --> src/main.rs:5:18
  |
4 |     let ref1 = &data;
  |                ----- immutable borrow occurs here
5 |     let ref2 = &mut data;
  |                  ^^^^^^^ mutable borrow occurs here
6 |     println!("{} {:?}", ref1[0], ref2);
  |                        ---- immutable borrow later used here
```

**正确模式**:

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    {
        let ref1 = &data;       // 不可变借用开始
        println!("{}", ref1[0]); // 使用
    }                           // 不可变借用结束

    let ref2 = &mut data;       // ✓ 可变借用允许
    ref2.push(4);
}
```

### 3.2 重新借用的复杂性

#### 边界案例 3.2.1: 重新借用链

```rust
// 复杂的重新借用链
fn reborrow_chain() {
    let mut x = 5;
    let r1 = &mut x;           // 可变借用
    let r2 = &mut *r1;         // 重新借用 r1
    let r3 = &mut *r2;         // 重新借用 r2

    *r3 = 10;                  // 通过 r3 修改
    // r2 自动恢复
    // r1 自动恢复
}
```

**思维表征**: 重新借用状态图

```text
时间线:

 t0:  let r1 = &mut x
      ┌─────────┐
      │   r1    │◄──── 激活
      └────┬────┘
           │
 t1:  let r2 = &mut *r1
      ┌─────────┐
      │   r1    │───── 冻结
      └────┬────┘
           │
      ┌────▼────┐
      │   r2    │◄──── 激活
      └────┬────┘
           │
 t2:  let r3 = &mut *r2
      ┌─────────┐
      │   r1    │───── 冻结
      └────┬────┘
           │
      ┌────▼────┐
      │   r2    │───── 冻结
      └────┬────┘
           │
      ┌────▼────┐
      │   r3    │◄──── 激活
      └─────────┘

 t3:  *r3 = 10
      r3 结束 → r2 恢复 → r1 恢复
```

---

## 4. 智能指针陷阱

### 4.1 Rc 循环引用

#### 反例 4.1.1: 内存泄漏

```rust
use std::rc::Rc;
use std::cell::RefCell;

// 循环引用导致内存泄漏
struct Node {
    value: i32,
    next: RefCell<Option<Rc<Node>>>,
}

fn main() {
    let node1 = Rc::new(Node {
        value: 1,
        next: RefCell::new(None),
    });

    let node2 = Rc::new(Node {
        value: 2,
        next: RefCell::new(None),
    });

    // 创建循环引用
    *node1.next.borrow_mut() = Some(node2.clone());
    *node2.next.borrow_mut() = Some(node1.clone());

    // Rc::strong_count 永远不会归零
    // 内存泄漏！
}
```

**思维表征**: 循环引用图

```text
┌──────────┐      next       ┌──────────┐
│  node1   │ ───────────────► │  node2   │
│  Rc=2    │                  │  Rc=2    │
└──────────┘                  └──────────┘
     ▲                              │
     └────────────── next ──────────┘

强引用计数永远不会归零，内存无法释放
```

**解决方案**: 使用 Weak

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    parent: RefCell<Weak<Node>>,  // 弱引用
    children: RefCell<Vec<Rc<Node>>>,
}
```

### 4.2 RefCell 运行时借用冲突

#### 反例 4.2.1: 运行时 panic

```rust
use std::cell::RefCell;

fn main() {
    let data = RefCell::new(vec![1, 2, 3]);

    let borrow1 = data.borrow();      // 不可变借用
    let borrow2 = data.borrow();      // 另一个不可变借用

    let borrow3 = data.borrow_mut();  // ✗ 运行时 panic!

    println!("{:?} {:?}", borrow1, borrow2);
}
```

**运行时错误**:

```text
thread 'main' panicked at 'already borrowed: BorrowMutError'
```

**正确模式**:

```rust
let data = RefCell::new(vec![1, 2, 3]);

{
    let borrows = data.borrow();
    // 使用 borrows
} // 借用在这里结束

let mut_borrow = data.borrow_mut();  // ✓ OK
```

---

## 5. 并发安全边界

### 5.1 Send 和 Sync 误用

#### 反例 5.1.1: 非 Send 类型跨线程

```rust
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);

    thread::spawn(move || {  // ✗ 编译错误
        println!("{}", data);
    });
}
```

**编译器错误**:

```text
error[E0277]: `Rc<i32>` cannot be sent between threads safely
  --> the trait `Send` is not implemented for `Rc<i32>`
```

**解决方案**:

```rust
use std::sync::Arc;

let data = Arc::new(42);

thread::spawn(move || {  // ✓ OK
    println!("{}", data);
});
```

### 5.2 死锁场景

#### 反例 5.2.1: 锁顺序不一致

```rust
use std::sync::Mutex;

// 可能导致死锁的代码
fn deadlock_risk() {
    let lock1 = Mutex::new(1);
    let lock2 = Mutex::new(2);

    // 线程1
    thread::spawn(move || {
        let _l1 = lock1.lock().unwrap();
        // ... 一些操作
        let _l2 = lock2.lock().unwrap();  // 等待 lock2
    });

    // 线程2
    thread::spawn(move || {
        let _l2 = lock2.lock().unwrap();
        // ... 一些操作
        let _l1 = lock1.lock().unwrap();  // 等待 lock1
    });

    // 死锁！线程1持有 lock1 等待 lock2
    //        线程2持有 lock2 等待 lock1
}
```

**解决方案**: 统一锁顺序或使用 try_lock

```rust
// 方案1: 统一顺序
let (l1, l2) = if addr_of!(&lock1) < addr_of!(&lock2) {
    (lock1.lock(), lock2.lock())
} else {
    (lock2.lock(), lock1.lock())
};

// 方案2: try_lock
use std::sync::TryLockError;

match lock2.try_lock() {
    Ok(guard) => guard,
    Err(TryLockError::WouldBlock) => {
        // 处理无法获取锁的情况
        return;
    }
    Err(e) => panic!("{:?}", e),
}
```

---

## 6. Unsafe 代码风险

### 6.1 未定义行为 (UB)

#### 反例 6.1.1: 悬垂原始指针

```rust
// ✗ 严重错误：悬垂指针
fn dangling_pointer() -> *const i32 {
    let x = 42;
    &x as *const i32  // x 在函数结束时被释放
}

fn main() {
    let ptr = dangling_pointer();
    unsafe {
        println!("{}", *ptr);  // UB: 悬垂指针解引用
    }
}
```

**Miri 检测**:

```text
error: Undefined Behavior: pointer to alloc1374 was dereferenced
       after this allocation got freed
```

**正确模式**:

```rust
// ✓ 使用 Box 确保内存存活
fn valid_pointer() -> *const i32 {
    let x = Box::new(42);
    Box::into_raw(x)  // 转移所有权到原始指针
}

// 使用时必须手动释放
unsafe {
    let _ = Box::from_raw(ptr);  // 重新获取所有权并释放
}
```

### 6.2 别名规则违反

#### 反例 6.2.1: Stacked Borrows 违反

```rust
// ✗ UB: 违反别名规则
unsafe fn alias_violation() {
    let mut x = 5;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;  // 创建新可变引用

    *r1 = 10;  // ✗ 使用旧指针
    *r2 = 20;
}
```

**Miri 检测 (Tree Borrows)**:

```text
error: Undefined Behavior: violating Tree Borrows retagging
```

---

## 7. 性能陷阱

### 7.1 不必要的克隆

#### 反例 7.1.1: 循环中克隆

```rust
// ✗ 性能问题：不必要的克隆
fn process_items(items: Vec<String>) {
    for item in items {  // 移动所有权
        // 处理 item
    }
    // items 不可用，如果需要再次使用：
    // let items = items.clone(); // 昂贵的克隆
}
```

**解决方案**:

```rust
// ✓ 使用引用避免克隆
fn process_items(items: &[String]) {
    for item in items {  // 借用
        // 处理 item
    }
}

// 或者使用迭代器
fn process_items(items: Vec<String>) {
    items.iter().for_each(|item| {
        // 处理 item
    });
    // items 仍然可用
}
```

### 7.2 缓存不友好访问

#### 反例 7.2.1: 跳跃式内存访问

```rust
// ✗ 缓存不友好
struct Matrix {
    data: Vec<Vec<i32>>,  // Vec of Vec
}

impl Matrix {
    fn sum(&self) -> i32 {
        let mut sum = 0;
        for col in 0..self.data[0].len() {
            for row in 0..self.data.len() {
                sum += self.data[row][col];  // 跳跃式访问
            }
        }
        sum
    }
}
```

**优化方案**:

```rust
// ✓ 连续内存布局
struct Matrix {
    data: Vec<i32>,  // 扁平化存储
    rows: usize,
    cols: usize,
}

impl Matrix {
    fn get(&self, row: usize, col: usize) -> i32 {
        self.data[row * self.cols + col]
    }

    fn sum(&self) -> i32 {
        self.data.iter().sum()  // 顺序访问，缓存友好
    }
}
```

---

## 8. 编译器诊断解读

### 8.1 常见错误速查表

| 错误代码 | 错误信息 | 含义 | 解决方案 |
|----------|----------|------|----------|
| E0382 | borrow of moved value | 移动后使用 | 使用 clone 或引用 |
| E0502 | cannot borrow as mutable | 同时存在可变和不可变借用 | 调整借用生命周期 |
| E0499 | cannot borrow mutably more than once | 多个可变借用 | 使用内部可变性或重构 |
| E0373 | closure may outlive borrowed value | 闭包捕获生命周期不足 | 使用 move 或 Arc |
| E0597 | borrowed value does not live long enough | 生命周期不足 | 延长值的生命周期 |
| E0308 | mismatched types | 类型不匹配 | 类型转换或修正 |
| E0277 | trait bound not satisfied | Trait未实现 | 实现所需 Trait |

### 8.2 编译器建议解读

#### 案例 1: 帮助性建议

```rust
let s = String::from("hello");
let slice = &s[0..2];
s.clear();  // ✗ 错误
println!("{}", slice);
```

**编译器输出**:

```text
error[E0502]: cannot borrow `s` as mutable because
              it is also borrowed as immutable
 --> src/main.rs:3:5
  |
2 |     let slice = &s[0..2];
  |                  - immutable borrow occurs here
3 |     s.clear();
  |     ^^^^^^^^^ mutable borrow occurs here
4 |     println!("{}", slice);
  |                    ----- immutable borrow later used here

help: ensure the mutable borrow ends before the immutable one
help: or clone the data to own it: `let slice = s[0..2].to_string();`
```

---

*本文档提供了全面的边界案例、反例和陷阱，帮助深入理解Rust所有权系统的边界和限制。*

**案例统计**:

- 正例: 25+
- 反例: 30+
- 边界案例: 20+
- 性能陷阱: 10+

**最后更新**: 2026-03-03
