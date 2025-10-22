# 所有权与借用对比矩阵

> **文档类型**: 📊 对比矩阵 | 🔍 内存安全分析
> **创建日期**: 2025-10-19
> **Rust 版本**: 1.90+

---

## 目录

- [所有权与借用对比矩阵](#所有权与借用对比矩阵)
  - [目录](#目录)
  - [📋 核心对比表](#-核心对比表)
    - [所有权模式对比](#所有权模式对比)
    - [借用类型对比](#借用类型对比)
  - [1️⃣ 所有权系统基础](#1️⃣-所有权系统基础)
    - [1.1 所有权规则](#11-所有权规则)
    - [1.2 移动语义](#12-移动语义)
    - [1.3 复制语义](#13-复制语义)
  - [2️⃣ 借用系统详解](#2️⃣-借用系统详解)
    - [2.1 不可变借用](#21-不可变借用)
    - [2.2 可变借用](#22-可变借用)
    - [2.3 借用规则](#23-借用规则)
  - [3️⃣ 所有权 vs 借用](#3️⃣-所有权-vs-借用)
    - [3.1 性能对比](#31-性能对比)
    - [3.2 设计决策](#32-设计决策)
    - [3.3 使用场景](#33-使用场景)
  - [4️⃣ 引用类型对比](#4️⃣-引用类型对比)
    - [4.1 共享引用 (\&T)](#41-共享引用-t)
    - [4.2 可变引用 (\&mut T)](#42-可变引用-mut-t)
    - [4.3 原始指针](#43-原始指针)
  - [5️⃣ 内存安全保证](#5️⃣-内存安全保证)
    - [5.1 悬垂指针防护](#51-悬垂指针防护)
    - [5.2 数据竞争防护](#52-数据竞争防护)
    - [5.3 迭代器失效防护](#53-迭代器失效防护)
  - [6️⃣ 借用检查器](#6️⃣-借用检查器)
    - [6.1 借用检查规则](#61-借用检查规则)
    - [6.2 NLL (Non-Lexical Lifetimes)](#62-nll-non-lexical-lifetimes)
    - [6.3 借用检查器限制](#63-借用检查器限制)
  - [7️⃣ 内部可变性](#7️⃣-内部可变性)
    - [7.1 `Cell<T>`](#71-cellt)
    - [7.2 `RefCell<T>`](#72-refcellt)
    - [7.3 Mutex/RwLock](#73-mutexrwlock)
  - [8️⃣ 智能指针与所有权](#8️⃣-智能指针与所有权)
    - [8.1 `Box<T>`](#81-boxt)
    - [8.2 `Rc<T>`](#82-rct)
    - [8.3 `Arc<T>`](#83-arct)
  - [9️⃣ 所有权模式](#9️⃣-所有权模式)
    - [9.1 构建器模式](#91-构建器模式)
    - [9.2 RAII模式](#92-raii模式)
    - [9.3 所有权转移模式](#93-所有权转移模式)
  - [🔟 借用模式](#-借用模式)
    - [10.1 切片模式](#101-切片模式)
    - [10.2 借用拆分](#102-借用拆分)
    - [10.3 迭代器模式](#103-迭代器模式)
  - [1️⃣1️⃣ 性能优化](#1️⃣1️⃣-性能优化)
    - [11.1 避免不必要的克隆](#111-避免不必要的克隆)
    - [11.2 使用 Cow](#112-使用-cow)
    - [11.3 零拷贝设计](#113-零拷贝设计)
  - [1️⃣2️⃣ 并发场景](#1️⃣2️⃣-并发场景)
    - [12.1 Send 和 Sync](#121-send-和-sync)
    - [12.2 跨线程所有权](#122-跨线程所有权)
    - [12.3 并发借用](#123-并发借用)
  - [1️⃣3️⃣ 常见错误与解决](#1️⃣3️⃣-常见错误与解决)
    - [13.1 移动错误](#131-移动错误)
    - [13.2 借用冲突](#132-借用冲突)
    - [13.3 生命周期错误](#133-生命周期错误)
  - [1️⃣4️⃣ Rust 1.90 改进](#1️⃣4️⃣-rust-190-改进)
    - [14.1 借用检查器增强](#141-借用检查器增强)
    - [14.2 更好的错误消息](#142-更好的错误消息)
    - [14.3 性能优化](#143-性能优化)
  - [📊 总结对比](#-总结对比)
  - [🔗 相关文档](#-相关文档)

---

## 📋 核心对比表

### 所有权模式对比

| 模式 | 定义 | 优势 | 劣势 | 典型场景 |
|------|------|------|------|---------|
| **移动 (Move)** | 转移所有权 | 零开销，清晰语义 | 原值不可用 | 资源管理、API边界 |
| **复制 (Copy)** | 按位复制 | 简单，原值仍可用 | 仅限小型类型 | 基本类型、标量 |
| **克隆 (Clone)** | 深拷贝 | 灵活，原值可用 | 可能昂贵 | 需要独立副本 |
| **借用 (Borrow)** | 临时访问 | 零开销，并发读 | 生命周期约束 | 函数参数、临时访问 |
| **可变借用** | 独占临时访问 | 零开销，保证独占 | 同时只能一个 | 就地修改 |

### 借用类型对比

| 借用类型 | 符号 | 独占性 | 可变性 | 并发 | 生命周期 |
|---------|------|--------|--------|------|---------|
| **共享引用** | `&T` | ❌ 共享 | ❌ 只读 | ✅ 多读 | 编译时检查 |
| **可变引用** | `&mut T` | ✅ 独占 | ✅ 可写 | ❌ 独占 | 编译时检查 |
| **原始指针 (不可变)** | `*const T` | ❌ 共享 | ❌ 只读 | ⚠️ unsafe | 无 |
| **原始指针 (可变)** | `*mut T` | ⚠️ 无保证 | ✅ 可写 | ⚠️ unsafe | 无 |

---

## 1️⃣ 所有权系统基础

### 1.1 所有权规则

**三大规则**:

1. **唯一所有者**: Rust 中每个值都有一个唯一的所有者变量
2. **作用域绑定**: 当所有者离开作用域时，值被自动释放
3. **移动语义**: 赋值或传参默认移动所有权

```rust
// 规则1：唯一所有者
fn rule1_unique_owner() {
    let s1 = String::from("hello");  // s1 是所有者
    // 没有其他变量拥有这个 String
}

// 规则2：作用域绑定 (RAII)
fn rule2_scope_bound() {
    {
        let s = String::from("hello");  // s 进入作用域
        println!("{}", s);
    } // s 离开作用域，String 被自动释放

    // println!("{}", s); // ❌ 错误：s 已不存在
}

// 规则3：移动语义
fn rule3_move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权移动到 s2
    
    // println!("{}", s1); // ❌ 错误：s1 已失效
    println!("{}", s2);    // ✅ s2 现在是所有者
}
```

### 1.2 移动语义

**定义**: 默认情况下，赋值和传参会移动所有权

```rust
// 移动语义示例
fn move_semantics() {
    // 1. 赋值移动
    let s1 = String::from("hello");
    let s2 = s1; // 移动
    // s1 不再可用
    
    // 2. 函数参数移动
    fn takes_ownership(s: String) {
        println!("{}", s);
    } // s 在这里被释放
    
    let s3 = String::from("world");
    takes_ownership(s3); // s3 的所有权移动
    // s3 不再可用
    
    // 3. 返回值移动
    fn gives_ownership() -> String {
        String::from("hello")
    }
    
    let s4 = gives_ownership(); // 所有权移动到 s4
}

// 为什么移动？
fn why_move() {
    let s1 = String::from("hello");
    // String 在堆上分配：
    // s1: [ptr, len, cap] -> 堆: [h, e, l, l, o]
    
    let s2 = s1; // 浅拷贝指针
    // 如果 s1 和 s2 都有效，会导致二次释放！
    // Rust 通过移动语义防止这个问题
}
```

### 1.3 复制语义

**定义**: 实现 `Copy` 特征的类型赋值时进行按位复制

```rust
// Copy 类型：按位复制
fn copy_semantics() {
    // 1. 基本类型都是 Copy
    let x = 5;
    let y = x; // 复制
    println!("{}, {}", x, y); // ✅ 两者都可用
    
    // 2. 元组（元素都是 Copy）
    let t1 = (1, 2, 3);
    let t2 = t1; // 复制
    println!("{:?}, {:?}", t1, t2); // ✅
    
    // 3. 数组（元素是 Copy）
    let a1 = [1, 2, 3];
    let a2 = a1; // 复制
    println!("{:?}, {:?}", a1, a2); // ✅
}

// Copy vs Clone
fn copy_vs_clone() {
    // Copy: 隐式，按位复制，廉价
    let x = 42;
    let y = x; // Copy
    
    // Clone: 显式，可能昂贵
    let s1 = String::from("hello");
    let s2 = s1.clone(); // Clone
    println!("{}, {}", s1, s2); // ✅ 两者都可用
}

// 实现 Copy
#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}

fn use_copy_type() {
    let p1 = Point { x: 0, y: 0 };
    let p2 = p1; // Copy
    println!("{}, {}", p1.x, p2.x); // ✅
}

// 不能实现 Copy 的类型
struct NotCopy {
    data: String, // String 不是 Copy
}

// 规则：如果类型包含非 Copy 字段，则不能实现 Copy
```

---

## 2️⃣ 借用系统详解

### 2.1 不可变借用

**定义**: 通过 `&T` 创建共享引用，允许只读访问

```rust
// 不可变借用基础
fn immutable_borrow() {
    let s = String::from("hello");
    
    let r1 = &s; // 第一个不可变借用
    let r2 = &s; // 第二个不可变借用
    
    println!("{}, {}", r1, r2); // ✅ 可以有多个不可变借用
    
    // r1.push_str("!"); // ❌ 错误：不可变引用不能修改
}

// 函数参数借用
fn calculate_length(s: &String) -> usize {
    s.len()
} // s 离开作用域，但不释放（只是借用）

fn use_borrow() {
    let s = String::from("hello");
    let len = calculate_length(&s);
    println!("Length of '{}' is {}", s, len); // ✅ s 仍然可用
}

// 多重借用
fn multiple_borrows() {
    let s = String::from("hello");
    
    let r1 = &s;
    let r2 = &s;
    let r3 = &s;
    
    println!("{}, {}, {}", r1, r2, r3); // ✅
}
```

### 2.2 可变借用

**定义**: 通过 `&mut T` 创建独占可变引用

```rust
// 可变借用基础
fn mutable_borrow() {
    let mut s = String::from("hello");
    
    let r = &mut s; // 可变借用
    r.push_str(" world");
    
    println!("{}", r); // ✅
}

// 函数参数可变借用
fn modify_string(s: &mut String) {
    s.push_str(" world");
}

fn use_mut_borrow() {
    let mut s = String::from("hello");
    modify_string(&mut s);
    println!("{}", s); // "hello world"
}

// 独占性：同时只能有一个可变借用
fn exclusive_borrow() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;
    // let r2 = &mut s; // ❌ 错误：已有可变借用
    
    r1.push_str(" world");
    println!("{}", r1);
}

// 可变借用期间不能有不可变借用
fn no_shared_while_mut() {
    let mut s = String::from("hello");
    
    let r1 = &s;
    // let r2 = &mut s; // ❌ 错误：已有不可变借用
    
    println!("{}", r1);
}
```

### 2.3 借用规则

**核心规则**:

1. 在任意时刻，要么只有一个可变引用，要么有任意数量的不可变引用
2. 引用必须始终有效

```rust
// 规则1：互斥访问
fn rule1_exclusive_access() {
    let mut s = String::from("hello");
    
    // 场景A：多个不可变借用
    {
        let r1 = &s;
        let r2 = &s;
        println!("{}, {}", r1, r2);
    } // r1, r2 离开作用域
    
    // 场景B：一个可变借用
    {
        let r3 = &mut s;
        r3.push_str(" world");
        println!("{}", r3);
    } // r3 离开作用域
    
    // ❌ 场景C：不可变 + 可变（错误）
    // let r4 = &s;
    // let r5 = &mut s;
    // println!("{}, {}", r4, r5);
}

// 规则2：引用有效性
fn rule2_valid_reference() {
    let r;
    {
        let s = String::from("hello");
        // r = &s; // ❌ 错误：s 的生命周期太短
    }
    // println!("{}", r); // r 会是悬垂引用
}

// NLL (Non-Lexical Lifetimes)
fn nll_example() {
    let mut s = String::from("hello");
    
    let r1 = &s;
    let r2 = &s;
    println!("{}, {}", r1, r2);
    // r1 和 r2 在这里最后一次使用，作用域结束
    
    let r3 = &mut s; // ✅ Rust 2018+: 可以，因为 r1, r2 不再使用
    r3.push_str(" world");
    println!("{}", r3);
}
```

---

## 3️⃣ 所有权 vs 借用

### 3.1 性能对比

```rust
// 所有权：零开销，但消耗原值
fn ownership_perf(s: String) {
    println!("{}", s);
} // s 被释放

// 借用：零开销，原值可用
fn borrow_perf(s: &String) {
    println!("{}", s);
} // 只是借用，不释放

// 性能测试
use std::time::Instant;

fn benchmark() {
    let s = String::from("hello world");
    let n = 1_000_000;
    
    // 借用：零开销
    let start = Instant::now();
    for _ in 0..n {
        borrow_perf(&s);
    }
    println!("Borrow: {:?}", start.elapsed()); // ~50ms
    
    // 所有权 + 克隆：有开销
    let start = Instant::now();
    for _ in 0..n {
        ownership_perf(s.clone());
    }
    println!("Clone + Ownership: {:?}", start.elapsed()); // ~500ms
}
```

### 3.2 设计决策

```rust
// 决策树
use std::borrow::Cow;

// 1. 只读访问：使用借用
fn read_only(s: &str) {
    println!("{}", s);
}

// 2. 需要修改：使用可变借用或所有权
fn modify_borrowed(s: &mut String) {
    s.push_str(" world");
}

fn modify_owned(mut s: String) -> String {
    s.push_str(" world");
    s
}

// 3. 可能修改：使用 Cow
fn maybe_modify(s: Cow<str>) -> Cow<str> {
    if s.starts_with("hello") {
        Cow::Borrowed(s.as_ref())
    } else {
        Cow::Owned(format!("hello {}", s))
    }
}

// 4. 需要持有：使用所有权
fn store_value(s: String) -> Box<dyn Fn() -> String> {
    Box::new(move || s.clone())
}
```

### 3.3 使用场景

| 场景 | 推荐方案 | 理由 |
|------|---------|------|
| **函数只读参数** | `&T` | 零开销，调用方保留所有权 |
| **函数修改参数** | `&mut T` | 就地修改，零开销 |
| **函数获取所有权** | `T` | 明确语义，如构造函数 |
| **返回新值** | `T` | 所有权转移 |
| **返回现有引用** | `&T` | 避免克隆 |
| **可能克隆** | `Cow<T>` | 延迟克隆 |
| **并发读** | `Arc<T>` | 共享所有权 |
| **并发写** | `Arc<Mutex<T>>` | 共享可变性 |

---

## 4️⃣ 引用类型对比

### 4.1 共享引用 (&T)

```rust
// 共享引用特性
fn shared_reference() {
    let x = 42;
    
    // 1. 多个共享引用
    let r1 = &x;
    let r2 = &x;
    let r3 = &x;
    println!("{}, {}, {}", r1, r2, r3);
    
    // 2. 可以复制
    let r4 = r1; // Copy
    println!("{}, {}", r1, r4);
    
    // 3. 自动解引用
    fn takes_i32(x: i32) {
        println!("{}", x);
    }
    takes_i32(*r1); // 显式解引用
}

// Deref 强制转换
fn deref_coercion() {
    let s = String::from("hello");
    
    fn takes_str(s: &str) {
        println!("{}", s);
    }
    
    takes_str(&s); // &String → &str
}
```

### 4.2 可变引用 (&mut T)

```rust
// 可变引用特性
fn mutable_reference() {
    let mut x = 42;
    
    // 1. 独占访问
    let r = &mut x;
    *r += 10;
    println!("{}", r); // 52
    
    // 2. 不能复制（移动）
    let r2 = r; // 移动
    // println!("{}", r); // ❌ r 已失效
    println!("{}", r2);
    
    // 3. 可以强制转换为不可变引用
    let r3 = &mut x;
    let r4: &i32 = r3; // &mut → &
    println!("{}", r4);
}

// 可变引用的作用域
fn mut_ref_scope() {
    let mut s = String::from("hello");
    
    {
        let r = &mut s;
        r.push_str(" world");
    } // r 离开作用域
    
    // 现在可以再次借用
    let r2 = &mut s;
    r2.push_str("!");
    println!("{}", r2);
}
```

### 4.3 原始指针

```rust
// 原始指针：unsafe
fn raw_pointers() {
    let x = 42;
    
    // 1. 不可变原始指针
    let r1: *const i32 = &x;
    
    // 2. 可变原始指针
    let mut y = 100;
    let r2: *mut i32 = &mut y;
    
    // 3. 使用原始指针（需要 unsafe）
    unsafe {
        println!("r1: {}", *r1);
        *r2 = 200;
        println!("r2: {}", *r2);
    }
}

// 原始指针 vs 引用
fn raw_vs_ref() {
    let mut x = 42;
    
    // 引用：安全，编译时检查
    let r1 = &x;
    let r2 = &x; // ✅ 多个不可变引用
    
    // 原始指针：unsafe，无编译时检查
    let p1: *const i32 = &x;
    let p2: *const i32 = &x;
    let p3: *mut i32 = &mut x as *mut i32; // ⚠️ 可以共存
    
    // 使用原始指针需要 unsafe
    unsafe {
        println!("{}, {}, {}", *p1, *p2, *p3);
    }
}

// 何时使用原始指针
fn when_use_raw_pointers() {
    // 1. FFI (与 C 交互)
    extern "C" {
        fn c_function(ptr: *const i32);
    }
    
    // 2. 实现底层数据结构（如链表）
    struct Node {
        value: i32,
        next: *mut Node, // 原始指针避免所有权问题
    }
    
    // 3. unsafe 代码块中
    let x = 42;
    let ptr = &x as *const i32;
    unsafe {
        println!("{}", *ptr);
    }
}
```

---

## 5️⃣ 内存安全保证

### 5.1 悬垂指针防护

```rust
// Rust 防止悬垂指针
fn no_dangling_pointer() {
    // ❌ 示例1：返回局部变量引用
    // fn dangle() -> &String {
    //     let s = String::from("hello");
    //     &s // 错误：s 在函数结束时被释放
    // }
    
    // ✅ 正确：返回所有权
    fn no_dangle() -> String {
        String::from("hello")
    }
    
    // ❌ 示例2：引用生命周期太短
    let r;
    {
        let s = String::from("hello");
        // r = &s; // 错误：s 的生命周期太短
    }
    // println!("{}", r); // 悬垂引用
}

// C/C++ 中的悬垂指针问题
// int* danglingPointer() {
//     int x = 42;
//     return &x; // 返回局部变量地址（悬垂）
// }
```

### 5.2 数据竞争防护

```rust
use std::thread;
use std::sync::{Arc, Mutex};

// Rust 防止数据竞争
fn no_data_race() {
    // ❌ 无法编译：不能在多线程间共享可变引用
    // let mut counter = 0;
    // let handle = thread::spawn(|| {
    //     counter += 1; // 错误：不能捕获可变引用
    // });
    
    // ✅ 正确：使用 Mutex
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = Arc::clone(&counter);
    
    let handle = thread::spawn(move || {
        let mut num = counter_clone.lock().unwrap();
        *num += 1;
    });
    
    handle.join().unwrap();
    println!("Counter: {}", *counter.lock().unwrap());
}

// 编译时防止数据竞争
fn compile_time_prevention() {
    let mut data = vec![1, 2, 3];
    
    // ❌ 不能同时有可变和不可变引用
    // let r1 = &data;
    // let r2 = &mut data;
    // println!("{:?}", r1);
    
    // ✅ 正确：分开使用
    {
        let r1 = &data;
        println!("{:?}", r1);
    }
    {
        let r2 = &mut data;
        r2.push(4);
    }
}
```

### 5.3 迭代器失效防护

```rust
// Rust 防止迭代器失效
fn no_iterator_invalidation() {
    let mut v = vec![1, 2, 3];
    
    // ❌ C++ 中的迭代器失效
    // for (auto it = v.begin(); it != v.end(); ++it) {
    //     v.push_back(*it); // 可能导致迭代器失效
    // }
    
    // ❌ Rust 防止这种情况
    // for i in &v {
    //     v.push(*i); // 错误：不能在不可变借用期间修改
    // }
    
    // ✅ 正确：使用索引
    let len = v.len();
    for i in 0..len {
        v.push(v[i]);
    }
    println!("{:?}", v);
}

// 迭代器与借用
fn iterator_borrowing() {
    let v = vec![1, 2, 3];
    
    // 不可变迭代器
    for i in &v {
        println!("{}", i);
    }
    // v 仍然可用
    
    // 可变迭代器
    let mut v2 = vec![1, 2, 3];
    for i in &mut v2 {
        *i *= 2;
    }
    println!("{:?}", v2); // [2, 4, 6]
}
```

---

## 6️⃣ 借用检查器

### 6.1 借用检查规则

```rust
// 借用检查器分析
fn borrow_checker_analysis() {
    let mut s = String::from("hello");
    
    // 分析点1：创建不可变借用
    let r1 = &s;
    // 分析点2：创建另一个不可变借用
    let r2 = &s;
    // 分析点3：使用不可变借用
    println!("{}, {}", r1, r2);
    // 分析点4：不可变借用结束
    
    // 分析点5：创建可变借用
    let r3 = &mut s;
    // 分析点6：使用可变借用
    r3.push_str(" world");
    println!("{}", r3);
    // 分析点7：可变借用结束
}

// 借用检查器错误
fn borrow_checker_errors() {
    let mut s = String::from("hello");
    
    // ❌ 错误1：可变借用冲突
    // let r1 = &mut s;
    // let r2 = &mut s;
    // println!("{}, {}", r1, r2);
    
    // ❌ 错误2：可变与不可变借用冲突
    // let r3 = &s;
    // let r4 = &mut s;
    // println!("{}, {}", r3, r4);
    
    // ❌ 错误3：使用已移动的值
    let s2 = s;
    // println!("{}", s); // s 已移动
    println!("{}", s2);
}
```

### 6.2 NLL (Non-Lexical Lifetimes)

```rust
// Rust 2015: 词法作用域
fn lexical_lifetimes() {
    let mut s = String::from("hello");
    
    // Rust 2015: 编译错误
    // {
    //     let r = &s;
    //     println!("{}", r);
    // } // r 的词法作用域在这里结束
    // 
    // let r2 = &mut s; // ✅ 现在可以
}

// Rust 2018+: 非词法生命周期
fn non_lexical_lifetimes() {
    let mut s = String::from("hello");
    
    let r = &s;
    println!("{}", r);
    // r 在最后一次使用后就"结束"了
    
    let r2 = &mut s; // ✅ Rust 2018+: 可以
    r2.push_str(" world");
    println!("{}", r2);
}

// NLL 的好处
fn nll_benefits() {
    let mut x = 5;
    
    // 旧版本：错误
    // let y = &x;
    // let z = &mut x;
    // println!("{}", y);
    
    // 新版本：正确
    let y = &x;
    println!("{}", y); // y 的最后使用
    let z = &mut x;    // ✅ 可以
    *z += 1;
    println!("{}", z);
}
```

### 6.3 借用检查器限制

```rust
// 限制1：拆分借用
fn split_borrow_limitation() {
    struct Data {
        field1: i32,
        field2: i32,
    }
    
    let mut data = Data { field1: 1, field2: 2 };
    
    // ❌ 无法同时可变借用整个结构体的不同字段
    // let r1 = &mut data.field1;
    // let r2 = &mut data.field2;
    // *r1 = 10;
    // *r2 = 20;
    
    // ✅ 解决：借用独立字段
    fn split_borrow(data: &mut Data) -> (&mut i32, &mut i32) {
        (&mut data.field1, &mut data.field2)
    }
    
    let (r1, r2) = split_borrow(&mut data);
    *r1 = 10;
    *r2 = 20;
}

// 限制2：闭包捕获
fn closure_capture_limitation() {
    let mut v = vec![1, 2, 3];
    
    // ❌ 闭包捕获整个 v
    // let mut closure = || {
    //     v.push(4);
    // };
    // println!("{:?}", v); // 错误：v 被可变借用
    // closure();
    
    // ✅ 解决：限制闭包作用域
    {
        let mut closure = || {
            v.push(4);
        };
        closure();
    }
    println!("{:?}", v);
}

// 限制3：自引用结构
fn self_referential_limitation() {
    // ❌ 无法直接创建自引用结构
    // struct SelfRef<'a> {
    //     data: String,
    //     reference: &'a str,
    // }
    
    // impl<'a> SelfRef<'a> {
    //     fn new(data: String) -> Self {
    //         let reference = &data[..]; // 错误
    //         Self { data, reference }
    //     }
    // }
    
    // ✅ 解决：使用 Pin 或重新设计
}
```

---

## 7️⃣ 内部可变性

### 7.1 `Cell<T>`

```rust
use std::cell::Cell;

// Cell: 单线程内部可变性
fn cell_example() {
    let x = Cell::new(42);
    
    // 不需要 &mut self 就可以修改
    x.set(100);
    println!("{}", x.get()); // 100
    
    // Cell 通过移动/复制值来实现内部可变性
    let y = x.get(); // 复制值
    x.set(200);
    println!("{}, {}", y, x.get()); // 100, 200
}

// Cell 的限制
fn cell_limitations() {
    // ❌ Cell 只能用于 Copy 类型
    // let s = Cell::new(String::from("hello"));
    
    // ✅ 基本类型可以
    let x = Cell::new(42);
    x.set(100);
}

// Cell 的使用场景
struct Counter {
    count: Cell<i32>,
}

impl Counter {
    fn new() -> Self {
        Self {
            count: Cell::new(0),
        }
    }
    
    fn increment(&self) { // 注意：&self 而不是 &mut self
        self.count.set(self.count.get() + 1);
    }
    
    fn get(&self) -> i32 {
        self.count.get()
    }
}

fn use_counter() {
    let counter = Counter::new();
    counter.increment();
    counter.increment();
    println!("{}", counter.get()); // 2
}
```

### 7.2 `RefCell<T>`

```rust
use std::cell::RefCell;

// RefCell: 运行时借用检查
fn refcell_example() {
    let x = RefCell::new(String::from("hello"));
    
    // 不可变借用
    {
        let r1 = x.borrow();
        let r2 = x.borrow();
        println!("{}, {}", r1, r2);
    } // 借用结束
    
    // 可变借用
    {
        let mut r3 = x.borrow_mut();
        r3.push_str(" world");
        println!("{}", r3);
    }
}

// RefCell 的运行时检查
fn refcell_runtime_check() {
    let x = RefCell::new(42);
    
    let r1 = x.borrow();
    // let r2 = x.borrow_mut(); // ⚠️ 运行时 panic: 已有不可变借用
    println!("{}", r1);
}

// RefCell 的使用场景
struct Node {
    value: i32,
    children: RefCell<Vec<Node>>,
}

impl Node {
    fn new(value: i32) -> Self {
        Self {
            value,
            children: RefCell::new(Vec::new()),
        }
    }
    
    fn add_child(&self, child: Node) {
        self.children.borrow_mut().push(child);
    }
}

fn use_node() {
    let root = Node::new(1);
    root.add_child(Node::new(2));
    root.add_child(Node::new(3));
}
```

### 7.3 Mutex/RwLock

```rust
use std::sync::{Mutex, RwLock};
use std::thread;
use std::sync::Arc;

// Mutex: 多线程内部可变性
fn mutex_example() {
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
    
    println!("Counter: {}", *counter.lock().unwrap()); // 10
}

// RwLock: 读写锁
fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程
    for _ in 0..5 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let vec = data_clone.read().unwrap();
            println!("{:?}", *vec);
        });
        handles.push(handle);
    }
    
    // 一个写线程
    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut vec = data_clone.write().unwrap();
        vec.push(4);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// 内部可变性对比
fn interior_mutability_comparison() {
    // Cell: Copy 类型，单线程
    let cell = Cell::new(42);
    cell.set(100);
    
    // RefCell: 任意类型，单线程，运行时检查
    let refcell = RefCell::new(String::from("hello"));
    refcell.borrow_mut().push_str(" world");
    
    // Mutex: 任意类型，多线程
    let mutex = Arc::new(Mutex::new(0));
    // 跨线程使用...
    
    // RwLock: 任意类型，多线程，读写锁
    let rwlock = Arc::new(RwLock::new(vec![1, 2, 3]));
    // 跨线程使用...
}
```

---

## 8️⃣ 智能指针与所有权

### 8.1 `Box<T>`

```rust
// Box: 堆分配，独占所有权
fn box_ownership() {
    // 1. 创建 Box
    let b = Box::new(42);
    println!("{}", b);
    
    // 2. Box 的移动
    let b2 = b; // 移动所有权
    // println!("{}", b); // ❌ b 已失效
    println!("{}", b2);
    
    // 3. 解引用
    let b3 = Box::new(100);
    let value = *b3; // 解引用（移动值）
    // println!("{}", b3); // ❌ 值已移动
    println!("{}", value);
}

// Box 的使用场景
fn box_use_cases() {
    // 1. 大型数据（避免栈溢出）
    let large_array = Box::new([0; 1000000]);
    
    // 2. 递归类型
    enum List {
        Cons(i32, Box<List>),
        Nil,
    }
    
    let list = List::Cons(1,
        Box::new(List::Cons(2,
            Box::new(List::Cons(3,
                Box::new(List::Nil))))));
    
    // 3. 特征对象
    trait Animal {
        fn speak(&self);
    }
    
    struct Dog;
    impl Animal for Dog {
        fn speak(&self) {
            println!("Woof!");
        }
    }
    
    let animal: Box<dyn Animal> = Box::new(Dog);
    animal.speak();
}
```

### 8.2 `Rc<T>`

```rust
use std::rc::Rc;

// Rc: 引用计数，共享所有权
fn rc_ownership() {
    // 1. 创建 Rc
    let rc1 = Rc::new(String::from("hello"));
    println!("Count: {}", Rc::strong_count(&rc1)); // 1
    
    // 2. 克隆 Rc（增加引用计数）
    let rc2 = Rc::clone(&rc1);
    println!("Count: {}", Rc::strong_count(&rc1)); // 2
    
    // 3. 离开作用域（减少引用计数）
    {
        let rc3 = Rc::clone(&rc1);
        println!("Count: {}", Rc::strong_count(&rc1)); // 3
    }
    println!("Count: {}", Rc::strong_count(&rc1)); // 2
}

// Rc 的使用场景
fn rc_use_cases() {
    // 图结构
    struct Node {
        value: i32,
        neighbors: Vec<Rc<Node>>,
    }
    
    let node1 = Rc::new(Node {
        value: 1,
        neighbors: vec![],
    });
    
    let node2 = Rc::new(Node {
        value: 2,
        neighbors: vec![Rc::clone(&node1)],
    });
    
    let node3 = Rc::new(Node {
        value: 3,
        neighbors: vec![Rc::clone(&node1), Rc::clone(&node2)],
    });
    
    println!("node1 count: {}", Rc::strong_count(&node1)); // 3
}

// Rc 的限制
fn rc_limitations() {
    let rc = Rc::new(String::from("hello"));
    
    // ❌ 不能获取可变引用
    // let r = &mut *rc; // 错误：Rc 不支持
    
    // ✅ 需要内部可变性
    use std::cell::RefCell;
    let rc_refcell = Rc::new(RefCell::new(String::from("hello")));
    rc_refcell.borrow_mut().push_str(" world");
}
```

### 8.3 `Arc<T>`

```rust
use std::sync::Arc;
use std::thread;

// Arc: 原子引用计数，线程安全
fn arc_ownership() {
    let arc1 = Arc::new(String::from("hello"));
    let arc2 = Arc::clone(&arc1);
    
    let handle = thread::spawn(move || {
        println!("{}", arc2);
    });
    
    println!("{}", arc1);
    handle.join().unwrap();
}

// Arc 的使用场景
fn arc_use_cases() {
    // 并发数据共享
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];
    
    for i in 0..5 {
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

// 智能指针对比
fn smart_pointer_comparison() {
    // Box: 独占所有权，单线程
    let b = Box::new(42);
    
    // Rc: 共享所有权，单线程
    let rc = Rc::new(42);
    let rc2 = Rc::clone(&rc);
    
    // Arc: 共享所有权，多线程
    let arc = Arc::new(42);
    let arc2 = Arc::clone(&arc);
    
    // 性能：Box > Rc > Arc
}
```

---

## 9️⃣ 所有权模式

### 9.1 构建器模式

```rust
// 构建器模式：流式 API + 所有权转移
struct Config {
    host: String,
    port: u16,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: None,
        }
    }
    
    fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }
    
    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    fn build(self) -> Config {
        Config {
            host: self.host.unwrap_or_else(|| "localhost".to_string()),
            port: self.port.unwrap_or(8080),
        }
    }
}

fn builder_pattern() {
    let config = ConfigBuilder::new()
        .host("example.com".to_string())
        .port(3000)
        .build();
    
    println!("{}:{}", config.host, config.port);
}
```

### 9.2 RAII模式

```rust
// RAII: 资源获取即初始化
struct File {
    name: String,
}

impl File {
    fn open(name: String) -> Self {
        println!("Opening file: {}", name);
        Self { name }
    }
}

impl Drop for File {
    fn drop(&mut self) {
        println!("Closing file: {}", self.name);
    }
}

fn raii_pattern() {
    {
        let file = File::open("data.txt".to_string());
        // 使用 file...
    } // file 自动关闭
    println!("File closed automatically");
}

// RAII 保证资源释放
fn raii_guarantee() {
    let file = File::open("data.txt".to_string());
    
    // 即使发生 panic，也会调用 drop
    // panic!("Error!");
    
    // file 仍然会被正确释放
}
```

### 9.3 所有权转移模式

```rust
// 所有权转移：明确资源管理
struct Resource {
    data: Vec<u8>,
}

impl Resource {
    fn new() -> Self {
        println!("Resource created");
        Self { data: vec![0; 1000] }
    }
    
    fn process(self) -> ProcessedResource {
        println!("Processing resource");
        ProcessedResource { data: self.data }
    }
}

struct ProcessedResource {
    data: Vec<u8>,
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Resource dropped");
    }
}

impl Drop for ProcessedResource {
    fn drop(&mut self) {
        println!("ProcessedResource dropped");
    }
}

fn ownership_transfer() {
    let resource = Resource::new();
    let processed = resource.process(); // 所有权转移
    // resource 不再可用
    
    // processed 在作用域结束时释放
}
```

---

## 🔟 借用模式

### 10.1 切片模式

```rust
// 切片：借用部分数据
fn slice_pattern() {
    let arr = [1, 2, 3, 4, 5];
    
    // 借用部分
    let slice = &arr[1..4];
    println!("{:?}", slice); // [2, 3, 4]
    
    // 字符串切片
    let s = String::from("hello world");
    let hello = &s[0..5];
    let world = &s[6..11];
    println!("{}, {}", hello, world);
}

// 函数参数使用切片
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &byte) in bytes.iter().enumerate() {
        if byte == b' ' {
            return &s[0..i];
        }
    }
    
    s
}

fn use_first_word() {
    let s = String::from("hello world");
    let word = first_word(&s);
    println!("{}", word); // "hello"
}
```

### 10.2 借用拆分

```rust
// 借用拆分：独立借用结构体字段
struct Point {
    x: i32,
    y: i32,
}

fn borrow_split() {
    let mut point = Point { x: 0, y: 0 };
    
    // 独立借用字段
    let x = &mut point.x;
    let y = &mut point.y;
    
    *x = 10;
    *y = 20;
    
    println!("({}, {})", point.x, point.y);
}

// 数组拆分
fn split_at_mut_example() {
    let mut arr = [1, 2, 3, 4, 5];
    
    let (left, right) = arr.split_at_mut(2);
    
    left[0] = 10;
    right[0] = 30;
    
    println!("{:?}", arr); // [10, 2, 30, 4, 5]
}
```

### 10.3 迭代器模式

```rust
// 迭代器：借用集合
fn iterator_pattern() {
    let v = vec![1, 2, 3, 4, 5];
    
    // 不可变迭代器（借用）
    for i in &v {
        println!("{}", i);
    }
    // v 仍然可用
    
    // 可变迭代器（可变借用）
    let mut v2 = vec![1, 2, 3];
    for i in &mut v2 {
        *i *= 2;
    }
    println!("{:?}", v2); // [2, 4, 6]
    
    // 消耗迭代器（移动）
    let v3 = vec![1, 2, 3];
    for i in v3 {
        println!("{}", i);
    }
    // v3 不再可用
}

// 自定义迭代器
struct Counter {
    count: u32,
}

impl Counter {
    fn new() -> Self {
        Self { count: 0 }
    }
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<u32> {
        self.count += 1;
        if self.count <= 5 {
            Some(self.count)
        } else {
            None
        }
    }
}

fn use_custom_iterator() {
    let counter = Counter::new();
    for i in counter {
        println!("{}", i);
    }
}
```

---

## 1️⃣1️⃣ 性能优化

### 11.1 避免不必要的克隆

```rust
// ❌ 不必要的克隆
fn unnecessary_clone() {
    let s = String::from("hello");
    
    fn process(s: String) {
        println!("{}", s);
    }
    
    process(s.clone()); // 不必要的克隆
    println!("{}", s);
}

// ✅ 使用借用
fn use_borrow_instead() {
    let s = String::from("hello");
    
    fn process(s: &str) {
        println!("{}", s);
    }
    
    process(&s); // 借用，零开销
    println!("{}", s);
}

// 性能对比
use std::time::Instant;

fn benchmark_clone_vs_borrow() {
    let s = String::from("hello world ".repeat(1000));
    let n = 100_000;
    
    // 克隆
    let start = Instant::now();
    for _ in 0..n {
        let _  = s.clone();
    }
    println!("Clone: {:?}", start.elapsed()); // ~500ms
    
    // 借用
    let start = Instant::now();
    for _ in 0..n {
        let _: &str = &s;
    }
    println!("Borrow: {:?}", start.elapsed()); // ~0ms
}
```

### 11.2 使用 Cow

```rust
use std::borrow::Cow;

// Cow: Clone on Write
fn cow_example() {
    fn process(s: Cow<str>) -> Cow<str> {
        if s.starts_with("hello") {
            s // 不需要克隆
        } else {
            Cow::Owned(format!("hello {}", s)) // 需要时克隆
        }
    }
    
    // 不需要克隆
    let s1 = "hello world";
    let result1 = process(Cow::Borrowed(s1));
    println!("{}", result1); // "hello world"
    
    // 需要克隆
    let s2 = "world";
    let result2 = process(Cow::Borrowed(s2));
    println!("{}", result2); // "hello world"
}

// Cow 的性能优势
fn cow_performance() {
    use std::time::Instant;
    
    fn with_string(s: String) -> String {
        if s.starts_with("hello") {
            s
        } else {
            format!("hello {}", s)
        }
    }
    
    fn with_cow(s: Cow<str>) -> Cow<str> {
        if s.starts_with("hello") {
            s
        } else {
            Cow::Owned(format!("hello {}", s))
        }
    }
    
    let strings: Vec<_> = (0..10000)
        .map(|i| {
            if i % 2 == 0 {
                format!("hello {}", i)
            } else {
                format!("world {}", i)
            }
        })
        .collect();
    
    // String 版本
    let start = Instant::now();
    for s in &strings {
        let _ = with_string(s.clone());
    }
    println!("String: {:?}", start.elapsed());
    
    // Cow 版本
    let start = Instant::now();
    for s in &strings {
        let _ = with_cow(Cow::Borrowed(s));
    }
    println!("Cow: {:?}", start.elapsed()); // 更快
}
```

### 11.3 零拷贝设计

```rust
// 零拷贝：使用切片和借用
fn zero_copy_design() {
    // ❌ 拷贝版本
    fn parse_copy(data: Vec<u8>) -> Vec<u8> {
        let mut result = Vec::new();
        for &byte in &data {
            if byte != 0 {
                result.push(byte);
            }
        }
        result
    }
    
    // ✅ 零拷贝版本
    fn parse_zero_copy(data: &[u8]) -> Vec<&u8> {
        data.iter().filter(|&&b| b != 0).collect()
    }
    
    let data = vec![1, 0, 2, 0, 3];
    let result = parse_zero_copy(&data);
    println!("{:?}", result);
}

// 零拷贝字符串处理
fn zero_copy_string() {
    let s = "hello,world,rust";
    
    // ❌ 拷贝版本
    fn split_copy(s: &str) -> Vec<String> {
        s.split(',').map(|s| s.to_string()).collect()
    }
    
    // ✅ 零拷贝版本
    fn split_zero_copy(s: &str) -> Vec<&str> {
        s.split(',').collect()
    }
    
    let result = split_zero_copy(s);
    println!("{:?}", result); // ["hello", "world", "rust"]
}
```

---

## 1️⃣2️⃣ 并发场景

### 12.1 Send 和 Sync

```rust
use std::thread;
use std::sync::Arc;
use std::rc::Rc;

// Send: 可以跨线程转移所有权
// Sync: 可以跨线程共享引用

fn send_sync_basics() {
    // ✅ i32 是 Send 和 Sync
    let x = 42;
    thread::spawn(move || {
        println!("{}", x);
    });
    
    // ✅ Arc<T> 是 Send 和 Sync (如果 T: Send + Sync)
    let arc = Arc::new(42);
    let arc_clone = Arc::clone(&arc);
    thread::spawn(move || {
        println!("{}", arc_clone);
    });
    
    // ❌ Rc<T> 不是 Send
    // let rc = Rc::new(42);
    // thread::spawn(move || {
    //     println!("{}", rc); // 错误：Rc 不能跨线程
    // });
}

// 自定义类型的 Send 和 Sync
struct MyType {
    data: i32,
}

// 自动实现 Send 和 Sync（字段都是 Send/Sync）
// unsafe impl Send for MyType {}
// unsafe impl Sync for MyType {}
```

### 12.2 跨线程所有权

```rust
use std::thread;

// 跨线程转移所有权
fn cross_thread_ownership() {
    let s = String::from("hello");
    
    let handle = thread::spawn(move || {
        println!("{}", s);
    }); // s 的所有权移动到线程
    
    // println!("{}", s); // ❌ s 已移动
    
    handle.join().unwrap();
}

// 跨线程共享所有权
fn cross_thread_shared_ownership() {
    use std::sync::Arc;
    
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for i in 0..5 {
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
```

### 12.3 并发借用

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

// Mutex: 互斥借用
fn mutex_concurrent_borrow() {
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
    
    println!("Counter: {}", *counter.lock().unwrap());
}

// RwLock: 读写锁
fn rwlock_concurrent_borrow() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程
    for i in 0..5 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let vec = data_clone.read().unwrap();
            println!("Reader {}: {:?}", i, *vec);
        });
        handles.push(handle);
    }
    
    // 一个写线程
    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut vec = data_clone.write().unwrap();
        vec.push(4);
        println!("Writer: {:?}", *vec);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

---

## 1️⃣3️⃣ 常见错误与解决

### 13.1 移动错误

```rust
// 错误：使用已移动的值
fn move_error() {
    let s = String::from("hello");
    let s2 = s; // s 移动到 s2
    
    // println!("{}", s); // ❌ 错误：s 已移动
    println!("{}", s2); // ✅
}

// 解决1：克隆
fn solution1_clone() {
    let s = String::from("hello");
    let s2 = s.clone(); // 克隆而不是移动
    
    println!("{}, {}", s, s2); // ✅ 两者都可用
}

// 解决2：借用
fn solution2_borrow() {
    let s = String::from("hello");
    let s2 = &s; // 借用而不是移动
    
    println!("{}, {}", s, s2); // ✅ 两者都可用
}

// 解决3：使用 Copy 类型
fn solution3_copy() {
    let x = 42;
    let y = x; // Copy 而不是移动
    
    println!("{}, {}", x, y); // ✅ 两者都可用
}
```

### 13.2 借用冲突

```rust
// 错误：可变借用冲突
fn borrow_conflict() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;
    // let r2 = &mut s; // ❌ 错误：已有可变借用
    
    r1.push_str(" world");
    println!("{}", r1);
}

// 解决1：限制借用作用域
fn solution1_scope() {
    let mut s = String::from("hello");
    
    {
        let r1 = &mut s;
        r1.push_str(" world");
    } // r1 离开作用域
    
    let r2 = &mut s; // ✅ 现在可以
    r2.push_str("!");
    println!("{}", r2);
}

// 解决2：使用 NLL
fn solution2_nll() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;
    r1.push_str(" world");
    println!("{}", r1); // r1 最后使用
    
    let r2 = &mut s; // ✅ Rust 2018+
    r2.push_str("!");
    println!("{}", r2);
}

// 解决3：重新设计
fn solution3_redesign() {
    let mut s = String::from("hello");
    
    fn append(s: &mut String, text: &str) {
        s.push_str(text);
    }
    
    append(&mut s, " world");
    append(&mut s, "!");
    println!("{}", s);
}
```

### 13.3 生命周期错误

```rust
// 错误：返回悬垂引用
// fn lifetime_error() -> &str {
//     let s = String::from("hello");
//     &s // ❌ 错误：s 在函数结束时被释放
// }

// 解决1：返回所有权
fn solution1_ownership() -> String {
    String::from("hello") // ✅
}

// 解决2：使用 'static
fn solution2_static() -> &'static str {
    "hello" // ✅ 字符串字面量是 'static
}

// 解决3：接受生命周期参数
fn solution3_lifetime_param<'a>(s: &'a str) -> &'a str {
    s // ✅ 返回输入的引用
}
```

---

## 1️⃣4️⃣ Rust 1.90 改进

### 14.1 借用检查器增强

```rust
// Rust 1.90：更智能的借用检查
fn improved_borrow_checker() {
    let mut v = vec![1, 2, 3];
    
    // 旧版本可能报错的代码
    if let Some(first) = v.first() {
        println!("{}", first);
    }
    v.push(4); // ✅ Rust 1.90: 可以
    
    // 更精确的 NLL
    let mut s = String::from("hello");
    let r = &s;
    if !r.is_empty() {
        println!("{}", r);
    }
    let r2 = &mut s; // ✅ 更智能的生命周期分析
    r2.push_str(" world");
}
```

### 14.2 更好的错误消息

```rust
// Rust 1.90：更清晰的错误消息
fn better_error_messages() {
    let s = String::from("hello");
    let s2 = s;
    
    // println!("{}", s); // 错误消息更清晰，提供建议
    
    // 旧版：borrow of moved value: `s`
    // 新版：value borrowed here after move
    //       consider cloning the value if the performance cost is acceptable
    //       using `s.clone()`
}
```

### 14.3 性能优化

```rust
// Rust 1.90：优化的移动语义
fn optimized_move_semantics() {
    // 更好的移动优化
    fn create_vec() -> Vec<i32> {
        vec![1, 2, 3]
    }
    
    let v = create_vec(); // ✅ 零拷贝返回值优化
    println!("{:?}", v);
}

// Rust 1.90：优化的借用检查
fn optimized_borrow_checking() {
    let mut v = vec![1, 2, 3, 4, 5];
    
    // 更快的编译时借用检查
    for i in 0..v.len() {
        v[i] *= 2;
    }
    
    println!("{:?}", v);
}
```

---

## 📊 总结对比

| 概念 | 定义 | 优势 | 劣势 | 典型场景 |
|------|------|------|------|---------|
| **所有权** | 唯一所有者 | 明确语义，零开销 | 原值不可用 | 资源管理 |
| **移动** | 转移所有权 | 零开销 | 原值失效 | API边界 |
| **复制** | 按位复制 | 简单 | 仅限小型类型 | 基本类型 |
| **克隆** | 深拷贝 | 灵活 | 可能昂贵 | 需要副本 |
| **不可变借用** | 共享引用 | 并发读，零开销 | 不能修改 | 只读访问 |
| **可变借用** | 独占引用 | 就地修改，零开销 | 独占限制 | 就地修改 |

**核心建议**:

1. **默认使用借用**: 除非需要所有权，否则使用借用
2. **优先不可变借用**: 尽可能使用不可变借用
3. **避免不必要的克隆**: 使用借用代替克隆
4. **利用 NLL**: Rust 2018+ 的非词法生命周期更灵活
5. **理解 Send/Sync**: 并发编程中的类型安全
6. **使用智能指针**: Box/Rc/Arc 管理复杂所有权
7. **内部可变性**: Cell/RefCell/Mutex 处理特殊需求
8. **零拷贝设计**: 使用切片和借用优化性能

---

## 🔗 相关文档

- [01_concept_ontology.md](01_concept_ontology.md) - 所有权概念定义
- [02_relationship_network.md](02_relationship_network.md) - 所有权关系网络
- [11_generic_trait_matrix.md](11_generic_trait_matrix.md) - 泛型特征对比
- [12_lifetime_variance_matrix.md](12_lifetime_variance_matrix.md) - 生命周期型变
- [13_type_conversion_matrix.md](13_type_conversion_matrix.md) - 类型转换对比
- [24_ownership_system_mindmap.md](24_ownership_system_mindmap.md) - 所有权思维导图（待创建）

---

**文档状态**: ✅ 已完成
**最后更新**: 2025-10-19
**贡献者**: Rust Type System Knowledge Engineering Team
