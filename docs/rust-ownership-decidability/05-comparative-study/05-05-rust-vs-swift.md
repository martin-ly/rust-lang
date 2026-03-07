# Rust vs Swift: 现代系统语言深度对比

> **对比维度**: 内存安全模型、所有权系统、类型系统、并发模型、应用场景
> **目标读者**: Swift 开发者学习 Rust，跨平台开发者技术选型
> **文档版本**: 2.0.0 (L2+ 深度)

---

## 目录

- [Rust vs Swift: 现代系统语言深度对比](#rust-vs-swift-现代系统语言深度对比)
  - [目录](#目录)
  - [1. 执行摘要](#1-执行摘要)
  - [2. 内存安全模型对比](#2-内存安全模型对比)
    - [2.1 核心安全机制](#21-核心安全机制)
    - [2.2 所有权 vs ARC](#22-所有权-vs-arc)
    - [2.3 循环引用解决](#23-循环引用解决)
    - [2.4 内存安全保证对比](#24-内存安全保证对比)
  - [3. 所有权系统深度对比](#3-所有权系统深度对比)
    - [3.1 值类型与引用类型](#31-值类型与引用类型)
    - [3.2 引用语义对比](#32-引用语义对比)
    - [3.3 借用检查 vs ARC](#33-借用检查-vs-arc)
    - [3.4 内部可变性](#34-内部可变性)
  - [4. 类型系统对比](#4-类型系统对比)
    - [4.1 类型系统概览](#41-类型系统概览)
    - [4.2 代数数据类型](#42-代数数据类型)
    - [4.3 泛型与协议/Trait](#43-泛型与协议trait)
    - [4.4 类型推断](#44-类型推断)
    - [4.5 空值安全](#45-空值安全)
  - [5. 并发模型对比](#5-并发模型对比)
    - [5.1 并发安全模型](#51-并发安全模型)
    - [5.2 Swift Actor vs Rust Send/Sync](#52-swift-actor-vs-rust-sendsync)
    - [5.3 异步编程对比](#53-异步编程对比)
  - [6. 错误处理对比](#6-错误处理对比)
    - [6.1 错误处理机制](#61-错误处理机制)
    - [6.2 错误传播](#62-错误传播)
  - [7. 性能特征对比](#7-性能特征对比)
    - [7.1 内存管理开销](#71-内存管理开销)
    - [7.2 运行时特性](#72-运行时特性)
    - [7.3 ARC vs 所有权性能](#73-arc-vs-所有权性能)
  - [8. 代码示例对比](#8-代码示例对比)
    - [8.1 数据结构：链表](#81-数据结构链表)
    - [8.2 并发：安全计数器](#82-并发安全计数器)
    - [8.3 异步网络请求](#83-异步网络请求)
    - [8.4 资源管理](#84-资源管理)
  - [9. 适用场景分析](#9-适用场景分析)
    - [9.1 选择 Rust 的场景](#91-选择-rust-的场景)
    - [9.2 选择 Swift 的场景](#92-选择-swift-的场景)
    - [9.3 跨平台策略](#93-跨平台策略)
  - [10. 迁移指南](#10-迁移指南)
    - [10.1 Swift → Rust 思维转换](#101-swift--rust-思维转换)
    - [10.2 常见模式映射](#102-常见模式映射)
  - [总结](#总结)
  - [参考文献](#参考文献)

---

## 1. 执行摘要

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Rust vs Swift 核心对比                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  维度                  Rust                        Swift                     │
│  ──────────────────────────────────────────────────────────────────────    │
│                                                                             │
│  主要目标              系统编程安全              应用开发效率                │
│                       零成本抽象                 开发者体验优先              │
│                                                                             │
│  内存管理              所有权系统                  自动引用计数 (ARC)         │
│                       编译期确定                 运行时自动                 │
│                       无运行时开销              引用计数开销                │
│                                                                             │
│  内存安全              编译期保证                  运行时 + 编译警告          │
│                       借用检查器强制             ARC + 弱引用               │
│                                                                             │
│  平台                  跨平台原生                 Apple 生态优先             │
│                                                                             │
│  适用场景                                                                  │
│  ├── Rust: 系统编程、嵌入式、区块链、WebAssembly、跨平台后端                 │
│  └── Swift: iOS/macOS 应用、Apple 平台开发、服务端 (Vapor)                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. 内存安全模型对比

### 2.1 核心安全机制

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                       内存安全机制对比                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Rust: 所有权 + 借用检查                                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  编译期规则：                                                        │   │
│  │   1. 每个值有且只有一个所有者                                          │   │
│  │   2. 要么一个可变引用，要么多个不可变引用                               │   │
│  │   3. 引用必须有效 (不能悬垂)                                           │   │
│  │                                                                     │   │
│  │  编译器强制执行，无运行时开销                                          │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Swift: ARC + 可选类型 + 值类型                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  运行时机制：                                                        │   │
│  │   1. 自动引用计数管理对象生命周期                                       │   │
│  │   2. Optional<T> 处理可能为 nil 的值                                  │   │
│  │   3. 值类型 (struct/enum) 复制语义                                     │   │
│  │   4. weak/unowned 解决循环引用                                         │   │
│  │                                                                     │   │
│  │  运行时检查 + 编译警告，有 ARC 开销                                    │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

| 安全机制 | Rust | Swift |
|---------|------|-------|
| **所有权跟踪** | 编译期借用检查器 | ARC 运行时计数 |
| **悬垂指针** | 编译期阻止 | 编译期警告 + 运行时检查 |
| **空值安全** | Option<T> 强制处理 | Optional<T> 可选 |
| **数据竞争** | Send/Sync 编译期保证 | Actor 隔离 + 编译期检查 |
| **循环引用** | 编译期生命周期检查 | weak/unowned 手动标记 |
| **运行时开销** | 无 | ARC 计数操作 |

### 2.2 所有权 vs ARC

**Swift ARC 示例:**

```swift
// Swift: ARC 自动管理引用计数
class Person {
    let name: String
    var friend: Person?  // 强引用

    init(name: String) {
        self.name = name
        print("\(name) initialized")
    }

    deinit {
        print("\(name) deinitialized")
    }
}

func arcDemo() {
    var alice: Person? = Person(name: "Alice")  // 引用计数 = 1
    var bob: Person? = Person(name: "Bob")      // 引用计数 = 1

    alice?.friend = bob   // Bob 引用计数 = 2
    bob?.friend = alice   // Alice 引用计数 = 2

    // 循环引用！内存泄漏
    alice = nil  // Alice 引用计数 = 1，不释放
    bob = nil    // Bob 引用计数 = 1，不释放
}

// 解决循环引用：使用 weak
class PersonSafe {
    let name: String
    weak var friend: PersonSafe?  // 弱引用，不增加引用计数

    init(name: String) {
        self.name = name
    }

    deinit {
        print("\(name) deinitialized")
    }
}
```

**Rust 所有权示例:**

```rust
// Rust: 所有权编译期管理
struct Person {
    name: String,
}

impl Person {
    fn new(name: &str) -> Self {
        println!("{} created", name);
        Self { name: name.to_string() }
    }
}

impl Drop for Person {
    fn drop(&mut self) {
        println!("{} dropped", self.name);
    }
}

// 使用 Box 进行堆分配
struct PersonNode {
    name: String,
    friend: Option<Box<PersonNode>>,  // 所有权关系
}

// 使用 Rc/Weak 处理共享所有权
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct PersonShared {
    name: String,
    friend: RefCell<Option<Rc<PersonShared>>>,
    weak_friend: RefCell<Option<Weak<PersonShared>>>,
}

fn ownership_demo() {
    let alice = Rc::new(PersonShared {
        name: "Alice".to_string(),
        friend: RefCell::new(None),
        weak_friend: RefCell::new(None),
    });

    let bob = Rc::new(PersonShared {
        name: "Bob".to_string(),
        friend: RefCell::new(None),
        weak_friend: RefCell::new(None),
    });

    // 强引用关系
    *alice.friend.borrow_mut() = Some(Rc::clone(&bob));
    // 弱引用关系
    *bob.weak_friend.borrow_mut() = Some(Rc::downgrade(&alice));

    // 正常释放，无内存泄漏
}  // Rc 引用计数为 0，自动 drop
```

### 2.3 循环引用解决

**Swift 解决方案:**

```swift
// Swift 循环引用解决方案

// 1. weak 引用 (可选)
class Apartment {
    let unit: String
    weak var tenant: Person?  // 租户可能搬出

    init(unit: String) {
        self.unit = unit
    }
}

// 2. unowned 引用 (非可选)
class Customer {
    let name: String
    var card: CreditCard?

    init(name: String) {
        self.name = name
    }
}

class CreditCard {
    let number: UInt64
    unowned let customer: Customer  // 信用卡必有持卡人

    init(number: UInt64, customer: Customer) {
        self.number = number
        self.customer = customer
    }
}

// 3. 闭包捕获列表
class HTMLElement {
    let name: String
    let text: String?

    lazy var asHTML: () -> String = { [weak self] in
        guard let self = self else { return "" }
        return "<\(self.name)>\(self.text ?? "")</\(self.name)>"
    }

    init(name: String, text: String? = nil) {
        self.name = name
        self.text = text
    }
}
```

**Rust 解决方案:**

```rust
// Rust 循环引用解决方案

// 1. 所有权转移 (默认)
struct Owner {
    name: String,
    owned: Option<Box<Owned>>,
}

struct Owned {
    name: String,
    // 无反向引用，所有权单向
}

// 2. 使用 Weak
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Option<Weak<Node>>>,  // 弱引用父节点
}

// 3. 使用 arena 分配
use typed_arena::Arena;

fn arena_allocation() {
    let arena = Arena::new();

    let node1 = arena.alloc(Node {
        value: 1,
        children: RefCell::new(vec![]),
        parent: RefCell::new(None),
    });

    let node2 = arena.alloc(Node {
        value: 2,
        children: RefCell::new(vec![]),
        parent: RefCell::new(None),
    });

    // arena 统一释放，无需担心循环引用
}

// 4. 使用索引代替指针
struct Graph {
    nodes: Vec<NodeData>,
    edges: Vec<(usize, usize)>,  // 索引对
}

struct NodeData {
    value: i32,
}
```

### 2.4 内存安全保证对比

| 安全问题 | Rust | Swift |
|---------|------|-------|
| **NullPointerException** | ❌ 编译错误 (Option) | ⚠️ 运行时崩溃 (强制解包 nil) |
| **悬垂指针** | ❌ 编译错误 | ✅ ARC 防止 |
| **Use-after-free** | ❌ 编译错误 | ✅ ARC 防止 |
| **缓冲区溢出** | ✅ 边界检查 | ✅ 边界检查 |
| **数据竞争** | ❌ 编译错误 (Send/Sync) | ✅ Actor 隔离 |
| **循环引用泄漏** | ⚠️ 可能 (Rc 循环) | ⚠️ 可能 (强引用循环) |

---

## 3. 所有权系统深度对比

### 3.1 值类型与引用类型

**Swift 值类型 vs 引用类型:**

```swift
// Swift 值类型 (struct/enum)
struct Point {
    var x: Double
    var y: Double
}

var p1 = Point(x: 0, y: 0)
var p2 = p1    // 复制
p2.x = 10

print(p1.x)    // 0 - 未改变
print(p2.x)    // 10

// Swift 引用类型 (class)
class Person {
    var name: String
    init(name: String) { self.name = name }
}

var person1 = Person(name: "Alice")
var person2 = person1  // 引用同一对象
person2.name = "Bob"

print(person1.name)  // "Bob" - 已改变
print(person2.name)  // "Bob"
```

**Rust 所有权:**

```rust
// Rust 默认移动语义
#[derive(Clone, Copy)]  // 显式标记可复制
struct Point {
    x: f64,
    y: f64,
}

fn value_semantics() {
    let p1 = Point { x: 0.0, y: 0.0 };
    let p2 = p1;     // 复制 (因为实现了 Copy)
    // p1 仍然可用
    println!("{}, {}", p1.x, p2.x);
}

// 非 Copy 类型移动
struct Person {
    name: String,
}

fn move_semantics() {
    let person1 = Person { name: "Alice".to_string() };
    let person2 = person1;  // 所有权转移

    // println!("{}", person1.name);  // 编译错误！
    println!("{}", person2.name);     // 正常
}

// 借用
fn borrowing() {
    let person = Person { name: "Alice".to_string() };

    print_name(&person);  // 不可变借用
    print_name(&person);  // 可以多次借用

    // modify_name(&mut person);  // 需要可变借用
}  // person 在这里 drop

fn print_name(person: &Person) {
    println!("{}", person.name);
}
```

### 3.2 引用语义对比

| 特性 | Swift | Rust |
|-----|-------|------|
| **默认语义** | 值类型复制，引用类型共享 | 移动 (非Copy) |
| **引用类型** | class | 无 (使用智能指针) |
| **不可变引用** | let 引用 | &T |
| **可变引用** | var 引用 | &mut T |
| **共享引用** | 允许多个 | 允许多个 &T |
| **可变共享** | 允许 | 禁止 (编译期) |

### 3.3 借用检查 vs ARC

**Swift 引用:**

```swift
// Swift 无借用检查，运行时 ARC
func process(data: [Int]) -> Int {
    // data 是复制 (值类型) 或引用 (类)
    return data.reduce(0, +)
}

var numbers = [1, 2, 3]
let sum1 = process(data: numbers)  // 可能复制
let sum2 = process(data: numbers)  // 可能再次复制

// inout 参数
func modify(array: inout [Int]) {
    array.append(4)
}

modify(array: &numbers)  // 传递引用
```

**Rust 借用检查:**

```rust
// Rust 编译期借用检查
fn process(data: &[i32]) -> i32 {
    data.iter().sum()
}

fn borrowing_check() {
    let data = vec![1, 2, 3];

    let sum1 = process(&data);  // 不可变借用
    let sum2 = process(&data);  // 可以同时多个不可变借用

    println!("{} {}", sum1, sum2);

    // 可变借用
    let mut data = vec![1, 2, 3];
    modify(&mut data);
    // 这里不能同时有其他借用

    println!("{:?}", data);
}

fn modify(data: &mut Vec<i32>) {
    data.push(4);
}
```

### 3.4 内部可变性

**Swift:**

```swift
// Swift 类天然具有内部可变性
class Counter {
    private(set) var count = 0

    func increment() {
        count += 1
    }
}

let counter = Counter()  // let 引用
// counter = Counter()   // 错误：不能改变引用
counter.increment()       // 正常：可以改变内部状态

// 值类型需要 mutating
struct ValueCounter {
    private(set) var count = 0

    mutating func increment() {
        count += 1
    }
}

var valueCounter = ValueCounter()
valueCounter.increment()
```

**Rust:**

```rust
use std::cell::Cell;
use std::sync::Mutex;

// Cell: 内部可变性，用于 Copy 类型
struct Counter {
    count: Cell<i32>,
}

impl Counter {
    fn new() -> Self {
        Self { count: Cell::new(0) }
    }

    fn increment(&self) {  // &self，不是 &mut self
        self.count.set(self.count.get() + 1);
    }
}

// RefCell: 运行时借用检查
use std::cell::RefCell;

struct Container {
    data: RefCell<Vec<i32>>,
}

impl Container {
    fn add(&self, item: i32) {
        self.data.borrow_mut().push(item);
    }
}

// Mutex: 线程安全内部可变性
use std::sync::Arc;

struct ThreadSafeCounter {
    count: Mutex<i32>,
}

impl ThreadSafeCounter {
    fn increment(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
    }
}

fn use_counter() {
    let counter = Arc::new(ThreadSafeCounter { count: Mutex::new(0) });

    let counter2 = Arc::clone(&counter);
    std::thread::spawn(move || {
        counter2.increment();
    });

    counter.increment();
}
```

---

## 4. 类型系统对比

### 4.1 类型系统概览

| 特性 | Rust | Swift |
|-----|------|-------|
| **类型检查** | 严格静态 | 静态 + 部分推断 |
| **类型推断** | Hindley-Milner | 局部 |
| **泛型** | 单态化 | 具体化 |
| **协议/Trait** | 显式实现 | 隐式满足 |
| **关联类型** | 支持 | 支持 |
| **动态派发** | trait object | any Protocol |
| **类型擦除** | 支持 | 支持 |

### 4.2 代数数据类型

**Swift enum:**

```swift
// Swift 枚举支持关联值
enum Result<T, E: Error> {
    case success(T)
    case failure(E)
}

enum Optional<Wrapped> {
    case some(Wrapped)
    case none
}

// 使用
func fetchData() -> Result<String, Error> {
    // ...
    return .success("data")
}

// 模式匹配
let result = fetchData()
switch result {
case .success(let data):
    print(data)
case .failure(let error):
    print(error)
}

// if case
if case .success(let data) = result {
    print(data)
}
```

**Rust enum:**

```rust
// Rust 枚举相同概念
enum Result<T, E> {
    Ok(T),
    Err(E),
}

enum Option<T> {
    Some(T),
    None,
}

// 使用
fn fetch_data() -> Result<String, Box<dyn std::error::Error>> {
    Ok("data".to_string())
}

// 模式匹配
let result = fetch_data();
match result {
    Ok(data) => println!("{}", data),
    Err(e) => eprintln!("{}", e),
}

// if let
if let Ok(data) = result {
    println!("{}", data);
}
```

### 4.3 泛型与协议/Trait

**Swift 协议:**

```swift
// 协议定义
protocol Drawable {
    func draw()
    func describe()  // 协议扩展提供默认实现
}

extension Drawable {
    func describe() {
        print("A drawable object")
    }
}

// 隐式实现
struct Circle: Drawable {
    func draw() {
        print("Drawing circle")
    }
}

// 泛型约束
func render<T: Drawable>(item: T) {
    item.draw()
}

// 关联类型
protocol Container {
    associatedtype Item
    var items: [Item] { get }
}

// 存在类型 (类型擦除)
let drawables: [any Drawable] = [Circle(), Rectangle()]
```

**Rust Trait:**

```rust
// Trait 定义
pub trait Drawable {
    fn draw(&self);
    fn describe(&self) {
        println!("A drawable object");
    }
}

// 显式实现
pub struct Circle;

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle");
    }
}

// 泛型约束
pub fn render<T: Drawable>(item: &T) {
    item.draw();
}

// 关联类型
pub trait Container {
    type Item;
    fn items(&self) -> &[Self::Item];
}

// Trait 对象 (动态派发)
let drawables: Vec<Box<dyn Drawable>> = vec![
    Box::new(Circle),
    Box::new(Rectangle),
];
```

### 4.4 类型推断

**Swift:**

```swift
// Swift 类型推断
let number = 42           // Int
let text = "Hello"        // String
let numbers = [1, 2, 3]   // [Int]

// 复杂推断
let doubled = numbers.map { $0 * 2 }  // [Int]

// 显式类型
let value: Double = 42
```

**Rust:**

```rust
// Rust 类型推断
let number = 42;           // i32
let text = "Hello";        // &str
let numbers = vec![1, 2, 3];  // Vec<i32>

// 复杂推断
let doubled: Vec<_> = numbers.iter().map(|x| x * 2).collect();

// 泛型推断
let mut vec = Vec::new();  // 需要后续使用推断类型
vec.push(1);               // 现在 Vec<i32>
```

### 4.5 空值安全

**Swift Optional:**

```swift
// Swift Optional
var name: String? = "Alice"
name = nil  // 可以设为 nil

// 强制解包 (危险)
// let unwrapped = name!  // 运行时崩溃如果 nil

// 安全解包
if let unwrapped = name {
    print(unwrapped)
}

// Nil 合并
let displayName = name ?? "Unknown"

// Optional 链
let count = name?.count  // Int?

// Guard
func process(name: String?) {
    guard let name = name else {
        return
    }
    print(name)
}
```

**Rust Option:**

```rust
// Rust Option
let name: Option<String> = Some("Alice".to_string());
let name: Option<String> = None;

// 强制解包 (panic)
// let unwrapped = name.unwrap();  // panic if None

// 安全解包
if let Some(unwrapped) = &name {
    println!("{}", unwrapped);
}

// 默认值
let display_name = name.as_deref().unwrap_or("Unknown");

// Map
let count = name.as_ref().map(|s| s.len());

// ? 操作符传播
fn process(name: Option<String>) -> Option<usize> {
    let name = name?;  // 如果 None 提前返回
    Some(name.len())
}
```

---

## 5. 并发模型对比

### 5.1 并发安全模型

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                       并发安全模型对比                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Swift: Actor 隔离                                                          │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  actor BankAccount {                                                │   │
│  │      private var balance: Double = 0                                │   │
│  │                                                                     │   │
│  │      func deposit(_ amount: Double) {                              │   │
│  │          balance += amount  // 串行执行                             │   │
│  │      }                                                              │   │
│  │  }                                                                  │   │
│  │                                                                     │   │
│  │  编译期检查：标记 Sendable 类型                                       │   │
│  │  Actor 之间通过 async 调用通信                                        │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Rust: Send/Sync Trait                                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                                                                     │   │
│  │  trait Send {}   // 可安全跨线程转移所有权                            │   │
│  │  trait Sync {}   // 可安全跨线程共享引用 (&T is Send)                 │   │
│  │                                                                     │   │
│  │  let data = Arc::new(Mutex::new(vec![]));                          │   │
│  │  thread::spawn(move || {                                            │   │
│  │      data.lock().unwrap().push(1);  // 编译期验证                    │   │
│  │  });                                                                │   │
│  │                                                                     │   │
│  │  违反 Send/Sync 会导致编译错误                                        │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 5.2 Swift Actor vs Rust Send/Sync

**Swift Actor:**

```swift
import Foundation

// Actor 自动隔离状态
actor BankAccount {
    private var balance: Double = 0

    func deposit(_ amount: Double) {
        balance += amount
    }

    func getBalance() -> Double {
        return balance
    }
}

// 使用
func useActor() async {
    let account = BankAccount()

    await account.deposit(100)
    let balance = await account.getBalance()
    print(balance)
}

// Sendable 协议标记线程安全类型
struct User: Sendable {
    let name: String
    let age: Int
}

// @MainActor 标记主线程类型
@MainActor
class UIController {
    func updateUI() {
        // 必须在主线程调用
    }
}
```

**Rust Send/Sync:**

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// Send: 可跨线程转移所有权
// Sync: 可跨线程共享引用

struct BankAccount {
    balance: Mutex<f64>,
}

// 自动实现 Send + Sync，因为 Mutex<f64> 是 Send + Sync
impl BankAccount {
    fn new() -> Self {
        Self { balance: Mutex::new(0.0) }
    }

    fn deposit(&self, amount: f64) {
        let mut balance = self.balance.lock().unwrap();
        *balance += amount;
    }

    fn get_balance(&self) -> f64 {
        *self.balance.lock().unwrap()
    }
}

fn use_thread_safety() {
    let account = Arc::new(BankAccount::new());

    let account2 = Arc::clone(&account);
    let handle = thread::spawn(move || {
        account2.deposit(100.0);
    });

    account.deposit(50.0);

    handle.join().unwrap();
    println!("{}", account.get_balance());
}

// Rc 不是 Send，不能跨线程
use std::rc::Rc;

fn non_send_demo() {
    let data = Rc::new(42);

    // 编译错误！Rc 不是 Send
    // thread::spawn(move || {
    //     println!("{}", data);
    // });

    // 必须使用 Arc
    let data = Arc::new(42);
    thread::spawn(move || {
        println!("{}", data);
    });
}
```

### 5.3 异步编程对比

**Swift async/await:**

```swift
import Foundation

// 异步函数
func fetchUser(id: Int) async throws -> User {
    let url = URL(string: "https://api.example.com/users/\(id)")!
    let (data, _) = try await URLSession.shared.data(from: url)
    return try JSONDecoder().decode(User.self, from: data)
}

// 并发执行
func fetchUsers() async throws -> [User] {
    async let user1 = fetchUser(id: 1)
    async let user2 = fetchUser(id: 2)
    async let user3 = fetchUser(id: 3)

    return try await [user1, user2, user3]
}

// Task 和 TaskGroup
func processInParallel() async {
    await withTaskGroup(of: Int.self) { group in
        for i in 0..<10 {
            group.addTask {
                return await processItem(i)
            }
        }

        for await result in group {
            print(result)
        }
    }
}

// MainActor
@MainActor
func updateUI() async {
    // 在主线程执行
}
```

**Rust async/await:**

```rust
use tokio;

// 异步函数
async fn fetch_user(id: i32) -> Result<User, reqwest::Error> {
    let url = format!("https://api.example.com/users/{}", id);
    let response = reqwest::get(&url).await?;
    let user = response.json::<User>().await?;
    Ok(user)
}

// 并发执行
async fn fetch_users() -> Result<Vec<User>, reqwest::Error> {
    let user1 = fetch_user(1);
    let user2 = fetch_user(2);
    let user3 = fetch_user(3);

    let (u1, u2, u3) = tokio::join!(user1, user2, user3);
    Ok(vec![u1?, u2?, u3?])
}

// 使用 FuturesUnordered 并行处理
use futures::stream::{FuturesUnordered, StreamExt};

async fn process_in_parallel() {
    let mut tasks = FuturesUnordered::new();

    for i in 0..10 {
        tasks.push(process_item(i));
    }

    while let Some(result) = tasks.next().await {
        println!("{}", result);
    }
}

// 在特定运行时执行
fn main() {
    tokio::runtime::Runtime::new()
        .unwrap()
        .block_on(async {
            // 异步代码
        });
}
```

---

## 6. 错误处理对比

### 6.1 错误处理机制

**Swift:**

```swift
// Swift 错误处理
enum FileError: Error {
    case notFound
    case permissionDenied
}

func readFile(path: String) throws -> String {
    guard FileManager.default.fileExists(atPath: path) else {
        throw FileError.notFound
    }
    // ...
    return content
}

// 调用
do {
    let content = try readFile(path: "/tmp/data.txt")
} catch FileError.notFound {
    print("File not found")
} catch {
    print("Unknown error: \(error)")
}

// try? 转换为 Optional
let content = try? readFile(path: "/tmp/data.txt")  // String?

// try! 强制解包 (危险)
// let content = try! readFile(path: "/tmp/data.txt")  // 运行时崩溃

// Result 类型 (函数式)
func readFileResult(path: String) -> Result<String, FileError> {
    guard FileManager.default.fileExists(atPath: path) else {
        return .failure(.notFound)
    }
    return .success("content")
}
```

**Rust:**

```rust
use std::fs;
use std::io;

// Result 类型
fn read_file(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

// 调用
match read_file("/tmp/data.txt") {
    Ok(content) => println!("{}", content),
    Err(e) if e.kind() == io::ErrorKind::NotFound => {
        println!("File not found")
    }
    Err(e) => eprintln!("Error: {}", e),
}

// ok() 转换为 Option
let content = read_file("/tmp/data.txt").ok();  // Option<String>

// unwrap() 强制解包 (panic)
// let content = read_file("/tmp/data.txt").unwrap();  // panic if error

// ? 操作符传播
fn process_files() -> Result<(), io::Error> {
    let content1 = read_file("file1.txt")?;
    let content2 = read_file("file2.txt")?;
    println!("{} {}", content1, content2);
    Ok(())
}
```

### 6.2 错误传播

**Swift:**

```swift
func operationA() throws {
    do {
        try operationB()
    } catch {
        throw AppError.failedInA(error)
    }
}

func operationB() throws {
    try operationC()
}

func operationC() throws {
    throw FileError.notFound
}

// rethrows: 仅传递错误，不生成新错误
func wrapper(_ operation: () throws -> Void) rethrows {
    try operation()
}
```

**Rust:**

```rust
use anyhow::{Context, Result};

fn operation_a() -> Result<()> {
    operation_b().context("Failed in A")?;
    Ok(())
}

fn operation_b() -> Result<()> {
    operation_c()?;
    Ok(())
}

fn operation_c() -> Result<()> {
    Err(io::Error::new(io::ErrorKind::NotFound, "file not found").into())
}
```

---

## 7. 性能特征对比

### 7.1 内存管理开销

| 操作 | Rust | Swift |
|-----|------|-------|
| **堆分配** | 相同 | 相同 |
| **对象释放** | 编译期确定 | ARC 计数 |
| **方法调用** | 直接 | 可能虚调用 |
| **引用计数** | 无 | ~5-10% 开销 |

### 7.2 运行时特性

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                       运行时特性对比                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  特性              Rust                     Swift                            │
│  ─────────────────────────────────────────────────────────────────────      │
│                                                                             │
│  运行时            可选 (no_std)            必须 (Objective-C 运行时)        │
│  标准库依赖        可选                      必须                            │
│  动态派发          trait object              类方法/协议                     │
│  反射              有限                      完整                            │
│  动态链接          支持                      支持 (framework)                │
│                                                                             │
│  启动时间          极快                      中等 (ARC 初始化)               │
│  内存占用          低                        中等                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 7.3 ARC vs 所有权性能

**Swift ARC 开销:**

```swift
// ARC 需要插入 retain/release 调用
class Node {
    var value: Int
    var next: Node?

    init(value: Int) {
        self.value = value
    }
}

// 以下代码有 ARC 开销
func processList(head: Node?) {
    var current = head
    while let node = current {
        print(node.value)
        current = node.next  // retain + release
    }
}
```

**Rust 无 ARC 开销:**

```rust
// Box: 无引用计数
struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

fn process_list(head: Option<Box<Node>>) {
    let mut current = head;
    while let Some(node) = current {
        println!("{}", node.value);
        current = node.next;  // 所有权转移，无计数
    }
}  // 剩余节点在这里 drop

// Rc: 有引用计数 (显式选择)
use std::rc::Rc;

struct SharedNode {
    value: i32,
    next: Option<Rc<SharedNode>>,
}

fn process_shared(head: Option<Rc<SharedNode>>) {
    let mut current = head;
    while let Some(node) = current {
        println!("{}", node.value);
        current = node.next.clone();  // 显式 clone，增加计数
    }
}
```

---

## 8. 代码示例对比

### 8.1 数据结构：链表

**Swift:**

```swift
// Swift 链表 (class + Optional)
class ListNode<T> {
    var value: T
    var next: ListNode<T>?

    init(value: T, next: ListNode<T>? = nil) {
        self.value = value
        self.next = next
    }
}

struct LinkedList<T> {
    private var head: ListNode<T>?

    mutating func push(_ value: T) {
        head = ListNode(value: value, next: head)
    }

    mutating func pop() -> T? {
        let value = head?.value
        head = head?.next
        return value
    }
}
```

**Rust:**

```rust
// Rust 链表
struct ListNode<T> {
    value: T,
    next: Option<Box<ListNode<T>>>,
}

struct LinkedList<T> {
    head: Option<Box<ListNode<T>>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self {
        Self { head: None }
    }

    fn push(&mut self, value: T) {
        let new_node = Box::new(ListNode {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }

    fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.value
        })
    }
}
```

### 8.2 并发：安全计数器

**Swift:**

```swift
import Foundation

// Actor 实现
actor Counter {
    private var value = 0

    func increment() {
        value += 1
    }

    func getValue() -> Int {
        return value
    }
}

// 使用
func useCounter() async {
    let counter = Counter()

    async let t1: () = counter.increment()
    async let t2: () = counter.increment()

    await t1
    await t2

    let value = await counter.getValue()
    print(value)  // 2
}
```

**Rust:**

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct Counter {
    value: Mutex<i32>,
}

impl Counter {
    fn new() -> Self {
        Self { value: Mutex::new(0) }
    }

    fn increment(&self) {
        let mut v = self.value.lock().unwrap();
        *v += 1;
    }

    fn get_value(&self) -> i32 {
        *self.value.lock().unwrap()
    }
}

fn use_counter() {
    let counter = Arc::new(Counter::new());
    let mut handles = vec![];

    for _ in 0..2 {
        let c = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            c.increment();
        });
        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("{}", counter.get_value());  // 2
}
```

### 8.3 异步网络请求

**Swift:**

```swift
import Foundation

struct User: Codable {
    let id: Int
    let name: String
}

func fetchUser(id: Int) async throws -> User {
    let url = URL(string: "https://api.example.com/users/\(id)")!
    let (data, response) = try await URLSession.shared.data(from: url)

    guard let httpResponse = response as? HTTPURLResponse,
          httpResponse.statusCode == 200 else {
        throw URLError(.badServerResponse)
    }

    return try JSONDecoder().decode(User.self, from: data)
}

// 并发获取
func fetchMultipleUsers() async throws -> [User] {
    async let user1 = fetchUser(id: 1)
    async let user2 = fetchUser(id: 2)
    return try await [user1, user2]
}
```

**Rust:**

```rust
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct User {
    id: i32,
    name: String,
}

async fn fetch_user(id: i32) -> Result<User, reqwest::Error> {
    let url = format!("https://api.example.com/users/{}", id);
    let response = reqwest::get(&url).await?;
    let user = response.json::<User>().await?;
    Ok(user)
}

// 并发获取
async fn fetch_multiple_users() -> Result<Vec<User>, reqwest::Error> {
    let user1 = fetch_user(1);
    let user2 = fetch_user(2);

    let (u1, u2) = tokio::join!(user1, user2);
    Ok(vec![u1?, u2?])
}
```

### 8.4 资源管理

**Swift:**

```swift
// Swift defer
func processFile(path: String) throws {
    let file = try FileHandle(forReadingFrom: URL(fileURLWithPath: path))
    defer {
        file.closeFile()
    }

    let data = file.readDataToEndOfFile()
    // 处理数据
}  // defer 自动执行

// 自定义清理
class Resource {
    func cleanup() {
        print("Cleaning up")
    }
}

func useResource() {
    let resource = Resource()
    defer { resource.cleanup() }

    // 使用 resource
}
```

**Rust:**

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader};

// RAII + Drop
fn process_file(path: &str) -> io::Result<()> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    for line in reader.lines() {
        let line = line?;
        println!("{}", line);
    }

    Ok(())  // file 和 reader 自动 drop
}

// 自定义 Drop
struct Resource;

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Cleaning up");
    }
}

fn use_resource() {
    let _resource = Resource;
    // 使用 resource
}  // 自动调用 drop

// 显式 drop
fn explicit_drop() {
    let resource = Resource;
    drop(resource);  // 提前释放
    // resource 不再可用
}
```

---

## 9. 适用场景分析

### 9.1 选择 Rust 的场景

```text
✅ 选择 Rust 当:

1. 跨平台系统编程
   - 跨操作系统开发
   - 无 Apple 平台限制

2. 无运行时需求
   - 嵌入式系统
   - WebAssembly
   - 内核模块

3. 性能关键应用
   - 零成本抽象
   - 无 ARC 开销

4. 安全关键系统
   - 编译期保证
   - 内存安全

5. 区块链/加密
   - 密码学安全
   - 确定性执行

6. 服务端/后端
   - 高并发
   - 低延迟
```

### 9.2 选择 Swift 的场景

```text
✅ 选择 Swift 当:

1. Apple 平台开发
   - iOS 应用
   - macOS 应用
   - watchOS/tvOS

2. 现有 Apple 生态
   - 使用 Foundation
   - Objective-C 互操作
   - UIKit/SwiftUI

3. 快速开发
   - Playground 原型
   - 开发者体验

4. 服务端 (Vapor)
   - Apple 平台部署
   - 类型安全

5. 机器学习 (Core ML)
   - 模型部署
   - Apple Silicon 优化
```

### 9.3 跨平台策略

```text
混合架构:

┌─────────────────────────────────────────────────────────────┐
│                    跨平台业务逻辑                             │
│                      (Rust 共享库)                            │
│                  高性能，安全核心                             │
└─────────────┬───────────────────────────────┬───────────────┘
              │                               │
              ▼                               ▼
┌─────────────────────────┐    ┌─────────────────────────────┐
│      iOS/macOS 应用      │    │      Android/服务端          │
│        (Swift)          │    │       (Kotlin/Rust)         │
│   SwiftUI/UIKit 界面     │    │      原生/跨平台界面          │
│   Rust FFI 调用核心      │    │      直接使用 Rust          │
└─────────────────────────┘    └─────────────────────────────┘

优势:
- 核心逻辑单一代码库
- 原生性能 UI
- 跨平台一致性
```

---

## 10. 迁移指南

### 10.1 Swift → Rust 思维转换

```
┌─────────────────────────────────────────────────────────────────┐
│                    思维模式转换                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Swift 思维                   →    Rust 思维                     │
│  ─────────────────────────────────────────────────────────      │
│                                                                 │
│  ARC 管理                   →    所有权 + 借用                  │
│  class/struct 区分           →    默认移动，Copy trait          │
│  weak/unowned               →    Weak/Rc + 借用检查             │
│  Optional<T>                →    Option<T>                     │
│  throws                     →    Result<T, E>                  │
│  guard let                  →    if let / ?                    │
│  defer                      →    Drop trait                    │
│  actor                      →    Send/Sync + Mutex             │
│  async/await                →    async/await + tokio           │
│  protocol                   →    trait                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 10.2 常见模式映射

| Swift | Rust |
|-------|------|
| `class` | `struct` + 智能指针 |
| `struct` (值类型) | `struct` + `Copy` |
| `enum` | `enum` |
| `protocol` | `trait` |
| `extension` | `impl` |
| `Optional<T>` | `Option<T>` |
| `Result<T, E>` | `Result<T, E>` |
| `Array<T>` | `Vec<T>` |
| `Dictionary<K, V>` | `HashMap<K, V>` |
| `Set<T>` | `HashSet<T>` |
| `weak` | `Weak<T>` |
| `unowned` | 引用生命周期 |
| `throws` | `Result` |
| `defer` | `Drop` |
| `guard let` | `if let` |
| `@MainActor` | `tokio::main` |

---

## 总结

| 维度 | Swift | Rust |
|:---|:---|:---|
| **主要平台** | Apple 生态 | 跨平台 |
| **内存管理** | ARC | 所有权 |
| **内存安全** | 运行时 + 编译警告 | 编译期保证 |
| **运行时** | 需要 | 可选 (no_std) |
| **性能** | 高 | 极高 |
| **学习曲线** | 平缓 | 陡峭 |
| **并发模型** | Actor | Send/Sync |
| **错误处理** | throws / Result | Result |
| **包管理** | Swift Package Manager | Cargo |

**选择建议:**

- Apple 平台原生开发 → **Swift**
- 跨平台/系统编程/嵌入式 → **Rust**
- 两者都支持现代语言特性，选择取决于目标平台

---

## 参考文献

1. The Swift Programming Language. <https://docs.swift.org/swift-book/>
2. The Rust Programming Language. <https://doc.rust-lang.org/book/>
3. Swift ARC Documentation. <https://docs.swift.org/swift-book/LanguageGuide/AutomaticReferenceCounting.html>
4. Rust Ownership Documentation. <https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html>
5. Swift Concurrency. <https://docs.swift.org/swift-book/LanguageGuide/Concurrency.html>
6. Rust Async Book. <https://rust-lang.github.io/async-book/>

---

*文档版本: 2.0.0 (L2+ 深度)*
*最后更新: 2026-03-07*
*维护者: Rust Comparative Study Team*
