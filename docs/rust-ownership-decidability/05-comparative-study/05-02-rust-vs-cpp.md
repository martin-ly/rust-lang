# Rust vs C++ 深度对比

> **对比维度**: 内存安全、所有权系统、并发模型、性能特征、抽象机制
> **难度**: 🟡 中等
> **目标读者**: 有 C++ 背景学习 Rust 的开发者
> **文档版本**: 2.0.0 (L2+ 深度)

---

## 目录

- [Rust vs C++ 深度对比](#rust-vs-c-深度对比)
  - [目录](#目录)
  - [1. 执行摘要](#1-执行摘要)
  - [2. 内存安全机制对比](#2-内存安全机制对比)
    - [2.1 核心安全保证对比](#21-核心安全保证对比)
    - [2.2 悬垂指针与使用已释放内存](#22-悬垂指针与使用已释放内存)
    - [2.3 缓冲区溢出防护](#23-缓冲区溢出防护)
    - [2.4 空指针/空引用](#24-空指针空引用)
  - [3. 所有权系统对比](#3-所有权系统对比)
    - [3.1 内存管理哲学](#31-内存管理哲学)
    - [3.2 所有权 vs 智能指针](#32-所有权-vs-智能指针)
    - [3.3 RAII 实现对比](#33-raii-实现对比)
    - [3.4 移动语义对比](#34-移动语义对比)
  - [4. 并发模型对比](#4-并发模型对比)
    - [4.1 线程安全保证机制](#41-线程安全保证机制)
    - [4.2 Send/Sync vs C++ 线程库](#42-sendsync-vs-c-线程库)
    - [4.3 数据竞争防护](#43-数据竞争防护)
    - [4.4 锁管理与死锁预防](#44-锁管理与死锁预防)
  - [5. 性能特征对比](#5-性能特征对比)
    - [5.1 零成本抽象实现](#51-零成本抽象实现)
    - [5.2 运行时开销对比](#52-运行时开销对比)
    - [5.3 编译时计算能力](#53-编译时计算能力)
    - [5.4 缓存友好性](#54-缓存友好性)
  - [6. 代码示例对比](#6-代码示例对比)
    - [6.1 资源管理：文件处理](#61-资源管理文件处理)
    - [6.2 数据结构：链表实现](#62-数据结构链表实现)
    - [6.3 并发：生产者-消费者](#63-并发生产者-消费者)
    - [6.4 错误处理](#64-错误处理)
  - [7. 抽象机制对比](#7-抽象机制对比)
    - [7.1 模板 vs 泛型](#71-模板-vs-泛型)
    - [7.2 Trait vs 概念 (Concepts)](#72-trait-vs-概念-concepts)
    - [7.3 运算符重载](#73-运算符重载)
  - [8. 生态系统与工具链](#8-生态系统与工具链)
  - [9. 安全性分析](#9-安全性分析)
    - [9.1 内存安全漏洞统计](#91-内存安全漏洞统计)
    - [9.2 安全编码实践](#92-安全编码实践)
  - [10. 适用场景建议](#10-适用场景建议)
  - [11. 迁移指南](#11-迁移指南)
    - [11.1 C++ → Rust 思维转换](#111-c--rust-思维转换)
    - [11.2 工具链映射](#112-工具链映射)
    - [11.3 学习路径](#113-学习路径)
  - [总结](#总结)
  - [参考文献](#参考文献)

---

## 1. 执行摘要

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Rust vs C++ 核心对比                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  维度                  Rust                        C++                       │
│  ──────────────────────────────────────────────────────────────────────    │
│                                                                             │
│  内存安全              编译期保证                  程序员责任 + 工具辅助      │
│                       零运行时开销                需要运行时检查工具         │
│                                                                             │
│  所有权模型            语言核心特性                库实现 (智能指针)          │
│                       借用检查器强制              约定俗成                   │
│                                                                             │
│  并发安全              Send/Sync 类型系统          程序员责任                │
│                       编译期数据竞争防护          运行时检测 (TSan)          │
│                                                                             │
│  性能                  零成本抽象                  零成本抽象                │
│                       无运行时                  无运行时                   │
│                                                                             │
│  学习曲线              陡峭 (所有权概念)           平缓但深渊                │
│                                                                             │
│  生态成熟度            快速成长                  成熟庞大                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**关键洞察**: Rust 和 C++ 都追求零成本抽象和高性能，但 Rust 通过所有权系统在编译期强制执行内存安全，而 C++ 依赖程序员的纪律和工具辅助来避免内存错误。

---

## 2. 内存安全机制对比

### 2.1 核心安全保证对比

| 安全问题 | Rust (编译期) | C++ (运行时/工具) | 优势方 |
|---------|--------------|------------------|--------|
| **use-after-free** | ❌ 编译错误 | ✅ ASan/UBSan 检测 | Rust |
| **悬垂指针** | ❌ 编译错误 | ❌ 运行时 UB | Rust |
| **缓冲区溢出** | ✅ 边界检查 (Debug) | ✅ ASan 检测 | 持平 |
| **双重释放** | ❌ 编译错误 | ❌ 运行时崩溃 | Rust |
| **内存泄漏** | ⚠️ 可能 (循环引用) | ⚠️ 可能 | 持平 |
| **空指针解引用** | ❌ 编译错误 (Option) | ❌ 运行时崩溃 | Rust |
| **数据竞争** | ❌ 编译错误 (Send/Sync) | ❌ TSan 检测 | Rust |
| **整数溢出** | ✅ Debug panic / Release wrap | ❌ 未定义行为 | Rust |

### 2.2 悬垂指针与使用已释放内存

**C++ 版本 - 运行时问题:**

```cpp
#include <iostream>
#include <string>

// 危险：返回局部变量引用
const std::string& get_greeting() {
    std::string msg = "Hello, World!";
    return msg;  // 返回局部变量的引用！
}  // msg 在这里被销毁

int main() {
    const std::string& greeting = get_greeting();
    // 悬垂引用！访问已释放内存
    std::cout << greeting << std::endl;  // UB - 可能崩溃或输出垃圾
    return 0;
}
```

**Rust 版本 - 编译期阻止:**

```rust
// 尝试返回局部变量引用 - 编译错误
fn get_greeting() -> &String {
    let msg = String::from("Hello, World!");
    &msg  // 编译错误: cannot return reference to local variable `msg`
}  // msg 在这里被 drop，引用将悬垂

// 正确方式：转移所有权
fn get_greeting_owned() -> String {
    String::from("Hello, World!")
}

// 或使用静态生命周期
fn get_greeting_static() -> &'static str {
    "Hello, World!"  // 字符串字面量有 'static 生命周期
}
```

**编译器错误信息:**

```
error[E0515]: cannot return reference to local variable `msg`
 --> src/main.rs:3:5
  |
3 |     &msg
  |     ^^^^ returns a reference to data owned by the current function
```

### 2.3 缓冲区溢出防护

**C++ 版本 - 潜在溢出:**

```cpp
#include <iostream>

void process_array(int arr[], size_t size) {
    // 无边界检查，可能导致缓冲区溢出
    for (size_t i = 0; i <= size; ++i) {  // 注意: <= 是bug
        std::cout << arr[i] << std::endl;  // 越界访问！
    }
}

int main() {
    int data[] = {1, 2, 3, 4, 5};
    process_array(data, 5);  // 越界读取 data[5]
    return 0;
}
```

**Rust 版本 - 编译期保护:**

```rust
fn process_array(arr: &[i32]) {
    // 迭代器自动处理边界
    for item in arr {
        println!("{}", item);
    }

    // 或显式索引 - 运行时检查
    for i in 0..=arr.len() {  // 注意: ..= 包含结束
        if let Some(val) = arr.get(i) {
            println!("{}", val);
        } else {
            println!("Index {} out of bounds", i);
        }
    }
}

// 更安全的迭代方式
fn process_array_safe(arr: &[i32]) {
    arr.iter().for_each(|item| {
        println!("{}", item);
    });
}

fn main() {
    let data = [1, 2, 3, 4, 5];
    process_array(&data);
}
```

### 2.4 空指针/空引用

**C++ 版本:**

```cpp
#include <iostream>
#include <string>

std::string* find_user(int id) {
    if (id == 1) {
        return new std::string("Alice");
    }
    return nullptr;  // 可能返回空指针
}

int main() {
    auto user = find_user(2);
    // 忘记检查 nullptr！
    std::cout << "Name: " << *user << std::endl;  // 运行时崩溃
    delete user;
    return 0;
}
```

**Rust 版本 - Option 强制处理:**

```rust
fn find_user(id: i32) -> Option<String> {
    if id == 1 {
        Some(String::from("Alice"))
    } else {
        None  // 显式表示可能无值
    }
}

fn main() {
    let user = find_user(2);

    // 方式1: 必须处理 None 才能访问值
    match user {
        Some(name) => println!("Name: {}", name),
        None => println!("User not found"),
    }

    // 方式2: 提供默认值
    let name = user.unwrap_or_else(|| String::from("Unknown"));
    println!("Name: {}", name);

    // 方式3: if let 简洁语法
    if let Some(name) = find_user(1) {
        println!("Found: {}", name);
    }
}
```

---

## 3. 所有权系统对比

### 3.1 内存管理哲学

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                      内存管理哲学对比                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  C++: "信任程序员"                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  提供工具 (智能指针)，但不强制使用                                      │   │
│  │  灵活性高，但容易出错                                                   │   │
│  │  可以绕过安全检查 (unsafe 操作)                                         │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Rust: "不信任，验证"                                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  所有权规则内置于类型系统                                               │   │
│  │  编译器强制执行，无法绕过 (Safe Rust)                                   │   │
│  │  unsafe 块明确标记危险代码                                              │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 所有权 vs 智能指针

**所有权转移对比:**

| 操作 | Rust | C++ |
|-----|------|-----|
| 唯一所有权 | `T` (默认) | `std::unique_ptr<T>` |
| 所有权转移 | `let b = a;` | `auto b = std::move(a);` |
| 共享所有权 | `Rc<T>` / `Arc<T>` | `std::shared_ptr<T>` |
| 弱引用 | `Weak<T>` | `std::weak_ptr<T>` |
| 内部可变性 | `RefCell<T>` / `Mutex<T>` | 无直接等价 |

**C++ 智能指针示例:**

```cpp
#include <iostream>
#include <memory>
#include <vector>

class Resource {
public:
    Resource() { std::cout << "Resource acquired\n"; }
    ~Resource() { std::cout << "Resource released\n"; }
    void use() { std::cout << "Using resource\n"; }
};

void unique_ptr_demo() {
    // unique_ptr: 独占所有权
    auto res = std::make_unique<Resource>();
    res->use();

    // 转移所有权
    auto res2 = std::move(res);
    // res 现在为 nullptr

    // res->use();  // 运行时错误！
}

void shared_ptr_demo() {
    // shared_ptr: 共享所有权
    auto res1 = std::make_shared<Resource>();
    {
        auto res2 = res1;  // 引用计数 +1
        res2->use();
    }  // 引用计数 -1

    // res1 仍然有效
    res1->use();
}  // 引用计数为0，资源释放

// 循环引用问题
struct Node;
struct Node {
    std::shared_ptr<Node> next;  // 强引用
    int value;
    ~Node() { std::cout << "Node " << value << " destroyed\n"; }
};

void circular_reference() {
    auto node1 = std::make_shared<Node>();
    auto node2 = std::make_shared<Node>();
    node1->next = node2;
    node2->next = node1;  // 循环引用！内存泄漏
}  // node1 和 node2 都不会被释放！
```

**Rust 所有权示例:**

```rust
struct Resource;

impl Resource {
    fn new() -> Self {
        println!("Resource acquired");
        Self
    }
    fn use_resource(&self) {
        println!("Using resource");
    }
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Resource released");
    }
}

fn ownership_demo() {
    // 默认：独占所有权
    let res = Resource::new();
    res.use_resource();

    // 转移所有权
    let res2 = res;
    // res 不能再使用！编译错误
    // res.use_resource();  // error: value borrowed after move

    res2.use_resource();
}  // res2 在这里自动 drop

fn rc_demo() {
    use std::rc::Rc;

    // Rc: 单线程共享所有权
    let res1 = Rc::new(Resource::new());
    {
        let res2 = Rc::clone(&res1);  // 引用计数 +1
        res2.use_resource();
    }  // 引用计数 -1

    res1.use_resource();
}  // 引用计数为0，资源释放

// 解决循环引用：编译时区分强/弱引用
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    next: RefCell<Option<Rc<Node>>>,  // 强引用子节点
    prev: RefCell<Option<Weak<Node>>>, // 弱引用父节点
    value: i32,
}

impl Drop for Node {
    fn drop(&mut self) {
        println!("Node {} destroyed", self.value);
    }
}

fn no_circular_reference() {
    let node1 = Rc::new(Node {
        next: RefCell::new(None),
        prev: RefCell::new(None),
        value: 1,
    });

    let node2 = Rc::new(Node {
        next: RefCell::new(None),
        prev: RefCell::new(Some(Rc::downgrade(&node1))),
        value: 2,
    });

    *node1.next.borrow_mut() = Some(node2);
    // node2.prev 是 Weak，不增加引用计数
}  // 正常释放，无内存泄漏
```

### 3.3 RAII 实现对比

**C++ RAII:**

```cpp
#include <fstream>
#include <mutex>
#include <thread>

class FileGuard {
    std::fstream file;
    std::mutex& mtx;
    std::lock_guard<std::mutex> lock;
public:
    FileGuard(const std::string& path, std::mutex& m)
        : file(path), mtx(m), lock(mtx) {}

    ~FileGuard() = default;  // 自动关闭文件和解锁

    // 禁止拷贝
    FileGuard(const FileGuard&) = delete;
    FileGuard& operator=(const FileGuard&) = delete;

    // 允许移动
    FileGuard(FileGuard&&) = default;
    FileGuard& operator=(FileGuard&&) = default;

    void write(const std::string& data) {
        file << data;
    }
};
```

**Rust RAII:**

```rust
use std::fs::File;
use std::io::{Write, Result};
use std::sync::Mutex;
use std::sync::MutexGuard;

struct FileGuard<'a> {
    file: File,
    _lock: MutexGuard<'a, ()>,  // 锁守卫
}

impl<'a> FileGuard<'a> {
    fn new(path: &str, mutex: &'a Mutex<()>) -> Result<Self> {
        let file = File::create(path)?;
        let _lock = mutex.lock().unwrap();
        Ok(Self { file, _lock })
    }

    fn write(&mut self, data: &[u8]) -> Result<()> {
        self.file.write_all(data)
    }
}

// Drop 自动实现：file 关闭，锁释放 (按字段顺序逆序)
// 无需显式编写 Drop，除非需要自定义行为

// 使用示例
fn use_guard() -> Result<()> {
    let mutex = Mutex::new(());
    let mut guard = FileGuard::new("data.txt", &mutex)?;
    guard.write(b"Hello, World!")?;
    Ok(())  // 自动释放
}
```

### 3.4 移动语义对比

| 特性 | Rust | C++ |
|-----|------|-----|
| 默认语义 | 移动 (非Copy类型) | 拷贝 |
| 显式移动 | `let b = a;` (自动) | `std::move(a)` |
| 移动后状态 | 未定义 (不能访问) | 有效但未指定 |
| 复制语义 | `Copy` trait | 默认，可禁用 |
| 右值引用 | 无 (所有权转移) | `T&&` |

**C++ 移动语义:**

```cpp
#include <iostream>
#include <vector>

class Buffer {
    int* data;
    size_t size;
public:
    Buffer(size_t s) : size(s), data(new int[s]) {
        std::cout << "Constructor\n";
    }

    // 拷贝构造
    Buffer(const Buffer& other) : size(other.size), data(new int[other.size]) {
        std::cout << "Copy constructor\n";
        std::copy(other.data, other.data + size, data);
    }

    // 移动构造
    Buffer(Buffer&& other) noexcept : data(other.data), size(other.size) {
        std::cout << "Move constructor\n";
        other.data = nullptr;  // 源对象置空
        other.size = 0;
    }

    ~Buffer() {
        std::cout << "Destructor\n";
        delete[] data;
    }
};

Buffer create_buffer() {
    Buffer b(100);
    return b;  // 移动构造 (RVO优化)
}

int main() {
    Buffer b1 = create_buffer();
    Buffer b2 = std::move(b1);  // 显式移动
    // b1 仍然可以访问，但状态未定义
    return 0;
}
```

**Rust 移动语义:**

```rust
struct Buffer {
    data: Box<[i32]>,
}

impl Buffer {
    fn new(size: usize) -> Self {
        println!("Constructor");
        let vec: Vec<i32> = vec![0; size];
        Self { data: vec.into_boxed_slice() }
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        println!("Destructor");
    }
}

fn create_buffer() -> Buffer {
    let b = Buffer::new(100);
    b  // 所有权转移
}

fn main() {
    let b1 = create_buffer();
    let b2 = b1;  // 所有权转移 (隐式)
    // b1 不能再使用！编译错误
    // println!("{:?}", b1.data);  // error: use of moved value

    // b2 在这里 drop
}
```

---

## 4. 并发模型对比

### 4.1 线程安全保证机制

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                      线程安全保证对比                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  C++: 运行时检测 + 约定                                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  程序员负责正确使用 mutex                                              │   │
│  │  ThreadSanitizer (TSan) 运行时检测数据竞争                              │   │
│  │  可以编写不安全的并发代码并编译通过                                      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Rust: 编译期类型系统保证                                                    │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  Send trait: 可以安全地跨线程转移所有权                                  │   │
│  │  Sync trait: 可以安全地跨线程共享引用                                    │   │
│  │  违反规则会导致编译错误                                                  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 4.2 Send/Sync vs C++ 线程库

**Send/Sync 定义:**

```rust
// Send: 类型可以安全地转移到另一个线程
pub unsafe auto trait Send {
    // 空 trait，仅作为标记
}

// Sync: 类型可以安全地被多个线程共享引用 (&T 是 Send)
pub unsafe auto trait Sync {
    // 空 trait，仅作为标记
}

// 大多数类型自动实现 Send + Sync
// 例外：Rc<T> (非线程安全引用计数)、原始指针等
```

**C++ 线程库:**

```cpp
#include <thread>
#include <vector>
#include <atomic>

// 线程安全的原子类型
std::atomic<int> counter{0};

void increment() {
    for (int i = 0; i < 1000; ++i) {
        ++counter;  // 原子操作，线程安全
    }
}

// 非线程安全的共享数据
int unsafe_counter = 0;

void unsafe_increment() {
    for (int i = 0; i < 1000; ++i) {
        ++unsafe_counter;  // 数据竞争！未定义行为
    }
}

int main() {
    std::vector<std::thread> threads;

    for (int i = 0; i < 10; ++i) {
        threads.emplace_back(unsafe_increment);  // 编译通过！
    }

    for (auto& t : threads) {
        t.join();
    }

    // unsafe_counter 结果不确定！
    std::cout << "Counter: " << unsafe_counter << std::endl;

    return 0;
}
```

**Rust 线程安全:**

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Arc;
use std::thread;

fn safe_concurrency() {
    // 原子类型是 Send + Sync
    let counter = Arc::new(AtomicI32::new(0));

    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(counter.load(Ordering::Relaxed), 10000);
}

// Rc 不是 Send，不能跨线程
fn unsafe_attempt() {
    use std::rc::Rc;

    let data = Rc::new(42);

    // 编译错误！Rc 不是 Send
    // let data2 = Rc::clone(&data);
    // thread::spawn(move || {
    //     println!("{}", data2);
    // });

    // 必须使用 Arc (原子引用计数)
    let data = Arc::new(42);
    let data2 = Arc::clone(&data);
    thread::spawn(move || {
        println!("{}", data2);
    });
}
```

### 4.3 数据竞争防护

**C++ 数据竞争示例 (编译通过，运行时错误):**

```cpp
#include <thread>
#include <vector>
#include <iostream>

class Counter {
public:
    void increment() {
        ++count;  // 非线程安全
    }
    int get() const { return count; }
private:
    int count = 0;
};

int main() {
    Counter counter;
    std::vector<std::thread> threads;

    for (int i = 0; i < 10; ++i) {
        threads.emplace_back([&counter]() {
            for (int j = 0; j < 1000; ++j) {
                counter.increment();  // 数据竞争！
            }
        });
    }

    for (auto& t : threads) t.join();

    std::cout << "Final count: " << counter.get() << std::endl;
    // 结果不确定！
    return 0;
}
```

**Rust 数据竞争防护 (编译期阻止):**

```rust
use std::thread;

struct Counter {
    count: i32,
}

impl Counter {
    fn increment(&mut self) {
        self.count += 1;
    }
}

fn main() {
    let mut counter = Counter { count: 0 };

    // 编译错误！counter 被多次借用
    // let handle1 = thread::spawn(|| {
    //     counter.increment();
    // });
    // let handle2 = thread::spawn(|| {
    //     counter.increment();
    // });

    // 正确方式：使用 Mutex
    use std::sync::Mutex;

    let counter = std::sync::Arc::new(Mutex::new(Counter { count: 0 }));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = std::sync::Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut c = counter.lock().unwrap();
            for _ in 0..1000 {
                c.increment();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", counter.lock().unwrap().count);
    // 确定输出: Final count: 10000
}
```

### 4.4 锁管理与死锁预防

**C++ 锁管理:**

```cpp
#include <mutex>
#include <thread>

std::mutex mtx1;
std::mutex mtx2;

// 潜在死锁：锁顺序不一致
void thread_a() {
    std::lock_guard<std::mutex> lock1(mtx1);
    std::this_thread::sleep_for(std::chrono::milliseconds(10));
    std::lock_guard<std::mutex> lock2(mtx2);  // 可能死锁！
}

void thread_b() {
    std::lock_guard<std::mutex> lock2(mtx2);
    std::this_thread::sleep_for(std::chrono::milliseconds(10));
    std::lock_guard<std::mutex> lock1(mtx1);  // 可能死锁！
}

// 安全方式：使用 std::lock
void safe_thread_a() {
    std::lock(mtx1, mtx2);  // 原子性地锁定多个 mutex
    std::lock_guard<std::mutex> lock1(mtx1, std::adopt_lock);
    std::lock_guard<std::mutex> lock2(mtx2, std::adopt_lock);
}
```

**Rust 锁管理:**

```rust
use std::sync::{Mutex, Arc};
use std::thread;

fn deadlock_example() {
    let mtx1 = Arc::new(Mutex::new(0));
    let mtx2 = Arc::new(Mutex::new(0));

    let m1 = Arc::clone(&mtx1);
    let m2 = Arc::clone(&mtx2);

    let handle1 = thread::spawn(move || {
        let _guard1 = m1.lock().unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let _guard2 = m2.lock().unwrap();  // 可能死锁
    });

    let m1 = Arc::clone(&mtx1);
    let m2 = Arc::clone(&mtx2);

    let handle2 = thread::spawn(move || {
        let _guard2 = m2.lock().unwrap();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let _guard1 = m1.lock().unwrap();  // 可能死锁
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

// 安全方式：使用作用域锁
fn safe_locking() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));

    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        {
            let mut vec = data_clone.lock().unwrap();
            vec.push(4);
        }  // 锁在这里释放
        // 其他工作...
    });

    handle.join().unwrap();
}
```

---

## 5. 性能特征对比

### 5.1 零成本抽象实现

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                      零成本抽象对比                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  抽象层次          C++ 实现              Rust 实现           运行时开销      │
│  ─────────────────────────────────────────────────────────────────────      │
│                                                                             │
│  迭代器           内联优化              内联优化            无              │
│  泛型/模板        单态化                单态化              无              │
│  虚函数           vtable                trait对象            vtable查找      │
│  异常处理         零成本 (表驱动)        Result类型          无/极小         │
│  智能指针          引用计数 (原子)        所有权转移          无              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

**迭代器性能对比:**

```cpp
// C++ - 优化后等价于手写循环
std::vector<int> v = {1, 2, 3, 4, 5};
int sum = std::accumulate(
    v.begin(), v.end(), 0,
    [](int a, int b) { return a + b; }
);
// 编译器内联后等价于:
// int sum = 0;
// for (int x : v) sum += x;
```

```rust
// Rust - 优化后等价于手写循环
let v = vec![1, 2, 3, 4, 5];
let sum: i32 = v.iter().sum();
// 编译器内联后等价于:
// let mut sum = 0;
// for &x in &v { sum += x; }
```

### 5.2 运行时开销对比

| 操作 | Rust 开销 | C++ 开销 | 说明 |
|-----|----------|---------|------|
| 函数调用 | 内联/直接 | 内联/直接 | 相同 |
| 虚调用 | vtable ( trait对象 ) | vtable | 相同 |
| 异常处理 | Result (无开销) | 表驱动/零成本 | Rust 更小 |
| 边界检查 | Debug: 检查 / Release: 可选 | 无 (不安全) | C++ 风险更高 |
| 内存分配 | 相同 | 相同 | 都使用系统分配器 |
| 引用计数 | Arc: 原子操作 | shared_ptr: 原子操作 | 相同 |
| 借用检查 | 编译期 | 运行时 (可选) | Rust 零运行时 |

### 5.3 编译时计算能力

**C++ 模板元编程:**

```cpp
// C++ 编译时计算
constexpr int factorial(int n) {
    return n <= 1 ? 1 : n * factorial(n - 1);
}

constexpr auto fact5 = factorial(5);  // 编译时常量 120

// 编译时类型特征
template<typename T>
struct is_pointer {
    static constexpr bool value = false;
};

template<typename T>
struct is_pointer<T*> {
    static constexpr bool value = true;
};

static_assert(is_pointer<int*>::value, "int* is pointer");
```

**Rust const 泛型:**

```rust
// Rust 编译时计算
const fn factorial(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        _ => n * factorial(n - 1),
    }
}

const FACT_5: u64 = factorial(5);  // 编译时常量 120

// 编译时类型特征
use std::any::TypeId;

fn is_same_type<T: 'static, U: 'static>() -> bool {
    TypeId::of::<T>() == TypeId::of::<U>()
}

// const 泛型
struct Array<T, const N: usize> {
    data: [T; N],
}

fn use_const_generic() {
    let arr: Array<i32, 5> = Array { data: [1, 2, 3, 4, 5] };
}
```

### 5.4 缓存友好性

**内存布局对比:**

| 特性 | Rust | C++ |
|-----|------|-----|
| 结构体布局 | 与 C 兼容 | 与 C 兼容 |
| 填充控制 | `#[repr(C/packed)]` | `#pragma pack` |
| 枚举大小 | 标签 + 最大变体 | `std::variant` 类似 |
| 虚表指针 | trait对象有 | 虚类有 |

```rust
// Rust 控制内存布局
#[repr(C)]  // C 兼容布局
struct Point {
    x: f64,
    y: f64,
}

#[repr(packed)]  // 无填充
struct PackedData {
    a: u8,
    b: u32,  // 通常填充3字节，packed后无填充
}

// 零大小类型
struct ZeroSized;  // size_of::<ZeroSized>() == 0

// 枚举优化
enum SmallEnum {
    A, B, C,  // 通常 u8
}
```

---

## 6. 代码示例对比

### 6.1 资源管理：文件处理

**C++ 版本:**

```cpp
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

class FileProcessor {
public:
    bool process_file(const std::string& path) {
        std::ifstream file(path);
        if (!file.is_open()) {
            std::cerr << "Failed to open: " << path << std::endl;
            return false;
        }

        std::string line;
        std::vector<std::string> lines;

        while (std::getline(file, line)) {
            lines.push_back(line);
        }

        // file 在这里自动关闭 (RAII)
        return process_lines(lines);
    }

private:
    bool process_lines(const std::vector<std::string>& lines) {
        for (const auto& line : lines) {
            if (!process_line(line)) {
                return false;
            }
        }
        return true;
    }

    bool process_line(const std::string& line) {
        // 处理每一行
        std::cout << "Processing: " << line << std::endl;
        return true;
    }
};
```

**Rust 版本:**

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

struct FileProcessor;

impl FileProcessor {
    fn process_file<P: AsRef<Path>>(&self, path: P) -> Result<(), io::Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let lines: Result<Vec<String>, _> = reader.lines().collect();
        let lines = lines?;

        // file 和 reader 在这里自动关闭 (Drop)
        self.process_lines(&lines)
    }

    fn process_lines(&self, lines: &[String]) -> Result<(), io::Error> {
        for line in lines {
            self.process_line(line)?;
        }
        Ok(())
    }

    fn process_line(&self, line: &str) -> Result<(), io::Error> {
        println!("Processing: {}", line);
        Ok(())
    }
}

// 更函数式的风格
fn process_file_functional<P: AsRef<Path>>(path: P) -> Result<(), Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;

    content
        .lines()
        .try_for_each(|line| {
            println!("Processing: {}", line);
            Ok::<(), io::Error>(())
        })?;

    Ok(())
}
```

### 6.2 数据结构：链表实现

**C++ 版本:**

```cpp
#include <memory>
#include <iostream>

template<typename T>
class LinkedList {
    struct Node {
        T data;
        std::unique_ptr<Node> next;
        Node(T d) : data(std::move(d)), next(nullptr) {}
    };

    std::unique_ptr<Node> head;
    size_t size_ = 0;

public:
    void push_front(T value) {
        auto new_node = std::make_unique<Node>(std::move(value));
        new_node->next = std::move(head);
        head = std::move(new_node);
        ++size_;
    }

    void pop_front() {
        if (head) {
            head = std::move(head->next);
            --size_;
        }
    }

    const T* front() const {
        return head ? &head->data : nullptr;
    }

    size_t size() const { return size_; }

    // 迭代器支持
    class Iterator {
        Node* current;
    public:
        Iterator(Node* n) : current(n) {}
        T& operator*() { return current->data; }
        Iterator& operator++() { current = current->next.get(); return *this; }
        bool operator!=(const Iterator& other) { return current != other.current; }
    };

    Iterator begin() { return Iterator(head.get()); }
    Iterator end() { return Iterator(nullptr); }
};
```

**Rust 版本:**

```rust
struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    size: usize,
}

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self {
        Self { head: None, size: 0 }
    }

    fn push_front(&mut self, value: T) {
        let new_node = Box::new(Node {
            data: value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
        self.size += 1;
    }

    fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            self.size -= 1;
            node.data
        })
    }

    fn front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.data)
    }

    fn size(&self) -> usize {
        self.size
    }
}

// 迭代器实现
pub struct Iter<'a, T> {
    current: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.map(|node| {
            self.current = node.next.as_deref();
            &node.data
        })
    }
}

impl<T> LinkedList<T> {
    fn iter(&self) -> Iter<T> {
        Iter {
            current: self.head.as_deref(),
        }
    }
}
```

### 6.3 并发：生产者-消费者

**C++ 版本:**

```cpp
#include <queue>
#include <mutex>
#include <condition_variable>
#include <thread>
#include <iostream>

template<typename T>
class Channel {
    std::queue<T> queue_;
    std::mutex mtx_;
    std::condition_variable cv_;
    bool closed_ = false;

public:
    void send(T value) {
        {
            std::lock_guard<std::mutex> lock(mtx_);
            queue_.push(std::move(value));
        }
        cv_.notify_one();
    }

    bool receive(T& value) {
        std::unique_lock<std::mutex> lock(mtx_);
        cv_.wait(lock, [this] { return !queue_.empty() || closed_; });

        if (queue_.empty()) return false;

        value = std::move(queue_.front());
        queue_.pop();
        return true;
    }

    void close() {
        {
            std::lock_guard<std::mutex> lock(mtx_);
            closed_ = true;
        }
        cv_.notify_all();
    }
};

void producer_consumer_demo() {
    Channel<int> channel;

    std::thread producer([&channel]() {
        for (int i = 0; i < 10; ++i) {
            channel.send(i);
            std::cout << "Produced: " << i << std::endl;
        }
        channel.close();
    });

    std::thread consumer([&channel]() {
        int value;
        while (channel.receive(value)) {
            std::cout << "Consumed: " << value << std::endl;
        }
    });

    producer.join();
    consumer.join();
}
```

**Rust 版本:**

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

fn producer_consumer_demo() {
    let (tx, rx): (Sender<i32>, Receiver<i32>) = channel();

    let producer = thread::spawn(move || {
        for i in 0..10 {
            tx.send(i).unwrap();
            println!("Produced: {}", i);
        }
        // channel 在这里自动关闭 (Sender dropped)
    });

    let consumer = thread::spawn(move || {
        for value in rx {  // 迭代直到 channel 关闭
            println!("Consumed: {}", value);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}

// 多生产者单消费者
fn multi_producer_demo() {
    let (tx, rx) = channel::<i32>();

    let mut handles = vec![];

    // 3 个生产者
    for id in 0..3 {
        let tx = tx.clone();
        let handle = thread::spawn(move || {
            for i in 0..5 {
                tx.send(id * 10 + i).unwrap();
            }
        });
        handles.push(handle);
    }

    // 必须 drop 原始 sender，否则 rx 永远不会结束
    drop(tx);

    // 消费者
    let consumer = thread::spawn(move || {
        for value in rx {
            println!("Received: {}", value);
        }
        println!("Channel closed");
    });

    for handle in handles {
        handle.join().unwrap();
    }
    consumer.join().unwrap();
}
```

### 6.4 错误处理

**C++ 版本:**

```cpp
#include <stdexcept>
#include <string>
#include <variant>
#include <optional>

// 方案1: 异常
class FileError : public std::runtime_error {
public:
    explicit FileError(const std::string& msg)
        : std::runtime_error(msg) {}
};

std::string read_file_except(const std::string& path) {
    if (path.empty()) {
        throw FileError("Empty path");
    }
    // ... 读取文件
    return "file content";
}

// 方案2: 返回错误码
enum class ErrorCode {
    Success,
    NotFound,
    PermissionDenied,
    InvalidPath
};

std::pair<std::string, ErrorCode> read_file_code(const std::string& path) {
    if (path.empty()) {
        return {{}, ErrorCode::InvalidPath};
    }
    // ...
    return {"file content", ErrorCode::Success};
}

// 方案3: std::expected (C++23)
template<typename T, typename E>
using Result = std::variant<T, E>;

Result<std::string, FileError> read_file_result(const std::string& path) {
    if (path.empty()) {
        return FileError("Empty path");
    }
    return std::string("file content");
}
```

**Rust 版本:**

```rust
use std::fs;
use std::io;
use std::path::Path;

// Result<T, E> 是主要错误处理方式
fn read_file<P: AsRef<Path>>(path: P) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

// 自定义错误类型
#[derive(Debug)]
enum FileError {
    InvalidPath,
    NotFound,
    PermissionDenied,
}

fn read_file_custom<P: AsRef<Path>>(path: P) -> Result<String, FileError> {
    let path = path.as_ref();
    if path.as_os_str().is_empty() {
        return Err(FileError::InvalidPath);
    }

    fs::read_to_string(path).map_err(|e| match e.kind() {
        io::ErrorKind::NotFound => FileError::NotFound,
        io::ErrorKind::PermissionDenied => FileError::PermissionDenied,
        _ => FileError::InvalidPath,
    })
}

// ? 操作符简化错误传播
fn process_files(paths: &[&str]) -> Result<Vec<String>, io::Error> {
    let mut contents = vec![];
    for path in paths {
        let content = fs::read_to_string(path)?;  // 自动传播错误
        contents.push(content);
    }
    Ok(contents)
}

// thiserror 简化错误定义 (实际项目中)
// use thiserror::Error;
//
// #[derive(Error, Debug)]
// enum AppError {
//     #[error("IO error: {0}")]
//     Io(#[from] io::Error),
//     #[error("Parse error: {0}")]
//     Parse(String),
// }
```

---

## 7. 抽象机制对比

### 7.1 模板 vs 泛型

| 特性 | C++ 模板 | Rust 泛型 |
|-----|---------|----------|
| 实例化 | 编译时 | 编译时 (单态化) |
| 错误位置 | 使用点 | 定义点 |
| 约束 | 概念 (C++20) | Trait bounds |
| 特化 | 完全/部分特化 | 有限 (特化不稳定) |
| 元编程 | SFINAE | const 泛型 |

**C++ 模板:**

```cpp
#include <concepts>

// C++20 概念
template<typename T>
concept Addable = requires(T a, T b) {
    { a + b } -> std::convertible_to<T>;
};

template<Addable T>
T add(T a, T b) {
    return a + b;  // 错误在定义时发现
}

// 模板特化
template<typename T>
struct TypeName {
    static const char* get() { return "unknown"; }
};

template<>
struct TypeName<int> {
    static const char* get() { return "int"; }
};
```

**Rust 泛型:**

```rust
use std::ops::Add;

// Trait bound
fn add<T: Add<Output = T>>(a: T, b: T) -> T {
    a + b  // 错误在定义时发现
}

// 多个 bounds
fn process<T>(item: T)
where
    T: Clone + Send + 'static,
{
    // ...
}

// 关联类型
trait Container {
    type Item;
    fn get(&self) -> Option<&Self::Item>;
}

struct VecWrapper<T>(Vec<T>);

impl<T> Container for VecWrapper<T> {
    type Item = T;
    fn get(&self) -> Option<&T> {
        self.0.first()
    }
}
```

### 7.2 Trait vs 概念 (Concepts)

**C++ 概念:**

```cpp
#include <concepts>
#include <iterator>

// 概念定义
template<typename T>
concept Drawable = requires(T t) {
    { t.draw() } -> std::same_as<void>;
    { t.area() } -> std::convertible_to<double>;
};

// 使用概念约束
template<Drawable T>
void render(T& shape) {
    shape.draw();
}

// 概念组合
template<typename T>
concept Sortable =
    std::copyable<T> &&
    requires(T a, T b) {
        { a < b } -> std::convertible_to<bool>;
    };
```

**Rust Trait:**

```rust
// Trait 定义
pub trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;

    // 默认实现
    fn describe(&self) {
        println!("Area: {}", self.area());
    }
}

// Trait bound
pub fn render<T: Drawable>(shape: &T) {
    shape.draw();
}

// 多个 trait bound
pub fn process<T>(item: &T)
where
    T: Drawable + Clone + Send + Sync,
{
    item.draw();
}

// Trait 组合
pub trait Sortable: Clone + PartialOrd {}
impl<T: Clone + PartialOrd> Sortable for T {}

// 孤儿规则：impl 必须在类型或 trait 的 crate 中
```

### 7.3 运算符重载

**C++ 运算符重载:**

```cpp
class Vector2D {
    double x, y;
public:
    Vector2D(double x, double y) : x(x), y(y) {}

    // 算术运算符
    Vector2D operator+(const Vector2D& other) const {
        return Vector2D(x + other.x, y + other.y);
    }

    Vector2D operator*(double scalar) const {
        return Vector2D(x * scalar, y * scalar);
    }

    // 比较运算符
    bool operator==(const Vector2D& other) const {
        return x == other.x && y == other.y;
    }

    // 流输出
    friend std::ostream& operator<<(std::ostream& os, const Vector2D& v) {
        return os << "(" << v.x << ", " << v.y << ")";
    }
};
```

**Rust 运算符重载:**

```rust
use std::ops::{Add, Mul};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq)]
struct Vector2D {
    x: f64,
    y: f64,
}

impl Vector2D {
    fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }
}

// 算术运算符
impl Add for Vector2D {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::new(self.x + other.x, self.y + other.y)
    }
}

impl Mul<f64> for Vector2D {
    type Output = Self;

    fn mul(self, scalar: f64) -> Self {
        Self::new(self.x * scalar, self.y * scalar)
    }
}

// 显示实现
impl fmt::Display for Vector2D {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

// 使用
fn use_vector() {
    let v1 = Vector2D::new(1.0, 2.0);
    let v2 = Vector2D::new(3.0, 4.0);
    let v3 = v1 + v2;
    let v4 = v3 * 2.0;
    println!("{}", v4);  // (8, 12)
}
```

---

## 8. 生态系统与工具链

| 工具 | C++ | Rust |
|-----|-----|------|
| **构建系统** | CMake, Bazel, Meson | Cargo |
| **包管理** | Conan, vcpkg | crates.io |
| **格式化** | clang-format | rustfmt |
| **静态分析** | clang-tidy, PVS-Studio | Clippy |
| **编译器** | GCC, Clang, MSVC | rustc (LLVM) |
| **调试器** | GDB, LLDB | GDB, LLDB, cargo-debug |
| **内存检查** | ASan, MSan, Valgrind | Miri, 内置检查 |
| **文档** | Doxygen | rustdoc |
| **测试** | GoogleTest, Catch2 | 内置测试框架 |

**构建配置对比:**

```cmake
# CMakeLists.txt (C++)
cmake_minimum_required(VERSION 3.10)
project(MyProject)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(Boost REQUIRED)
find_package(OpenSSL REQUIRED)

add_executable(myapp src/main.cpp)
target_link_libraries(myapp Boost::Boost OpenSSL::SSL)
```

```toml
# Cargo.toml (Rust)
[package]
name = "myapp"
version = "0.1.0"
edition = "2021"

[dependencies]
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
openssl = "0.10"

[dev-dependencies]
tokio-test = "0.4"
```

---

## 9. 安全性分析

### 9.1 内存安全漏洞统计

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                    内存安全漏洞统计 (据行业报告)                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  CVE 类型                    C++ 占比        Rust 占比                      │
│  ─────────────────────────────────────────────────────────────              │
│                                                                             │
│  缓冲区溢出                   ~60%            <1%                           │
│  Use-after-free              ~20%            <1%                           │
│  双重释放                     ~5%             0%                            │
│  空指针解引用                 ~10%            <1%                           │
│  整数溢出                     ~5%            可控                           │
│                                                                             │
│  数据来源: Microsoft Security Response Center, Google Project Zero          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 9.2 安全编码实践

**C++ 安全编码指南:**

```cpp
// C++ Core Guidelines 推荐

// 1. 优先使用智能指针
void safe_memory() {
    auto ptr = std::make_unique<int>(42);  // 而非 new/delete
    auto shared = std::make_shared<Resource>();
}

// 2. 使用 gsl::span 替代原始指针+长度
void process_array(gsl::span<int> data) {  // 安全
    for (auto& x : data) {
        // ...
    }
}

// 3. 避免裸 new/delete
// ❌ int* p = new int[100];
// ✅ auto p = std::make_unique<int[]>(100);

// 4. 使用 constexpr 进行编译时检查
constexpr int factorial(int n) {
    return n <= 1 ? 1 : n * factorial(n - 1);
}
```

**Rust 安全编码实践:**

```rust
// Rust 默认就是安全的

// 1. 使用标准库抽象
fn safe_collections() {
    let mut vec = vec![1, 2, 3];
    vec.push(4);  // 自动扩容，安全

    if let Some(first) = vec.first() {
        println!("{}", first);
    }
}

// 2. Result 强制错误处理
fn safe_io() -> Result<(), std::io::Error> {
    let content = std::fs::read_to_string("file.txt")?;
    println!("{}", content);
    Ok(())
}

// 3. unsafe 块明确标记
unsafe fn dangerous_operation(ptr: *const i32) -> i32 {
    *ptr  // 程序员负责确保安全
}

// 4. 使用安全包装
fn safe_wrapper() {
    // 99% 的代码不需要 unsafe
    let data = vec![1, 2, 3];
    let slice = &data[0..2];  // 边界检查
}
```

---

## 10. 适用场景建议

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                        技术选型决策树                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  需要与大量现有 C/C++ 代码集成?                                              │
│     ├── 是 → C++                                                             │
│     └── 否 → 继续                                                            │
│                                                                             │
│  内存安全是硬性要求 (安全关键系统)?                                           │
│     ├── 是 → Rust                                                            │
│     └── 否 → 继续                                                            │
│                                                                             │
│  团队有 C++ 专家且时间紧迫?                                                  │
│     ├── 是 → C++                                                             │
│     └── 否 → Rust                                                            │
│                                                                             │
│  需要 WebAssembly/嵌入式/no_std 支持?                                         │
│     ├── 是 → Rust                                                            │
│     └── 否 → 两者皆可                                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

| 场景 | 推荐 | 理由 |
|-----|------|------|
| 操作系统内核 | Rust | 内存安全，无运行时 |
| 游戏引擎 | C++ | 生态成熟，大量现有代码 |
| 嵌入式/IoT | Rust | no_std 支持，安全 |
| 高频交易 | 两者皆可 | 性能相当 |
| 浏览器引擎 | Rust (Firefox) | 安全，并行 |
| 系统工具 | Rust | 安全，易部署 |
| 机器学习推理 | C++ (ONNX) / Rust (burn) | 生态决定 |
| 区块链/加密 | Rust | 安全关键 |

---

## 11. 迁移指南

### 11.1 C++ → Rust 思维转换

```
┌─────────────────────────────────────────────────────────────────┐
│                    思维模式转换                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  C++ 思维                    →    Rust 思维                      │
│  ─────────────────────────────────────────────────────────      │
│                                                                 │
│  手动内存管理               →    所有权自动管理                   │
│  智能指针 (可选)            →    所有权系统 (强制)                │
│  const 正确性              →    &T / &mut T                     │
│  异常处理                  →    Result<T, E>                    │
│  模板元编程                →    宏 / const 泛型                  │
│  虚函数多态                →    Trait 对象 / 泛型                │
│  手动线程同步              →    Send/Sync 编译期检查             │
│  new/delete               →    Box::new / 自动 drop             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 11.2 工具链映射

| C++ 工具 | Rust 等价 | 说明 |
|---------|----------|------|
| `make` / CMake | `cargo build` | Cargo 自动处理依赖 |
| `g++` / `clang++` | `rustc` | 通常通过 Cargo 调用 |
| `apt-get install libxxx` | `cargo add xxx` | 自动下载依赖 |
| `gdb` | `rust-gdb` / `cargo debug` | 相同调试器 |
| `valgrind` | `cargo miri` | Miri 检测未定义行为 |
| `clang-format` | `cargo fmt` | 自动格式化 |
| `clang-tidy` | `cargo clippy` | 静态分析 |
| `cppcheck` | `cargo check` | 快速类型检查 |

### 11.3 学习路径

```
C++ 开发者学习 Rust 路径:

第 1 周: 所有权与借用
├── 理解所有权转移 (vs std::move)
├── 借用规则 (&T, &mut T)
├── 生命周期基础
└── 练习: 将 C++ unique_ptr 代码转换为 Rust

第 2 周: 类型系统
├── enum / Option / Result (vs std::optional/expected)
├── Trait (vs 抽象类/概念)
├── 泛型与约束
└── 练习: 实现容器类

第 3 周: 错误处理与集合
├── Result<T, E> 传播
├── ? 操作符
├── Vec, HashMap, HashSet
└── 练习: 文件处理程序

第 4 周: 并发
├── Send / Sync trait
├── Channel vs BlockingQueue
├── Mutex / RwLock
└── 练习: 生产者-消费者

第 5 周: 高级主题
├── 生命周期标注
├── 智能指针 (Rc, Arc, RefCell)
├── unsafe Rust
└── 练习: 与 C 代码 FFI
```

---

## 总结

| 维度 | C++ | Rust |
|:---|:---|:---|
| **内存安全** | 程序员责任，工具辅助 | 编译器强制执行 |
| **性能** | 零成本抽象 | 零成本抽象 |
| **并发安全** | 运行时检测 | 编译期保证 |
| **学习曲线** | 平缓但深渊 | 陡峭但有回报 |
| **生态成熟度** | 数十年积累 | 快速成长 |
| **工具链** | 分散 | 统一 (Cargo) |
| **适用领域** | 通用系统编程 | 安全关键系统 |

**最终建议**:

- 新项目，特别是安全关键系统 → **Rust**
- 现有 C++ 代码库维护 → **C++**
- 性能关键，需要精细控制 → **两者皆可**
- 快速原型开发 → **根据团队熟悉度选择**

---

## 参考文献

1. Stroustrup, B. (2013). *The C++ Programming Language, 4th Edition*. Addison-Wesley.
2. Klabnik, S., & Nichols, C. (2023). *The Rust Programming Language, 2nd Edition*. No Starch Press.
3. Microsoft Security Response Center. (2019). *A proactive approach to more secure code*.
4. Google Project Zero. (Various). Memory safety vulnerability reports.
5. LLVM Project. (Various). Optimizations in Rust and C++.
6. C++ Core Guidelines. <https://isocpp.github.io/CppCoreGuidelines/>
7. Rust Unsafe Code Guidelines. <https://rust-lang.github.io/unsafe-code-guidelines/>

---

*文档版本: 2.0.0 (L2+ 深度)*
*最后更新: 2026-03-07*
*维护者: Rust Comparative Study Team*
