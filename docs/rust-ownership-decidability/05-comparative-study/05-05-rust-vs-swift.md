# Rust vs Swift: 现代系统语言对比

> **对比维度**: 内存安全模型、类型系统、性能特征、应用场景
> **目标读者**: Swift 开发者学习 Rust，或跨平台开发者选型

---

## 目录

- [Rust vs Swift: 现代系统语言对比](#rust-vs-swift-现代系统语言对比)
  - [目录](#目录)
  - [1. 内存安全模型对比](#1-内存安全模型对比)
    - [1.1 核心机制](#11-核心机制)
    - [1.2 ARC vs Ownership](#12-arc-vs-ownership)
    - [1.3 循环引用解决](#13-循环引用解决)
  - [2. 类型系统](#2-类型系统)
    - [2.1 代数数据类型](#21-代数数据类型)
    - [2.2 泛型与协议/Trait](#22-泛型与协议trait)
    - [2.3 关键差异](#23-关键差异)
  - [3. 所有权与引用](#3-所有权与引用)
    - [3.1 引用语义](#31-引用语义)
    - [3.2 借用检查](#32-借用检查)
  - [4. 并发模型](#4-并发模型)
    - [4.1 Swift 并发](#41-swift-并发)
    - [4.2 Rust 并发](#42-rust-并发)
    - [4.3 并发安全对比](#43-并发安全对比)
  - [5. 错误处理](#5-错误处理)
    - [5.1 Swift 错误处理](#51-swift-错误处理)
    - [5.2 Rust 错误处理](#52-rust-错误处理)
  - [6. 应用场景与选型](#6-应用场景与选型)
    - [6.1 适用场景](#61-适用场景)
    - [6.2 性能对比](#62-性能对比)
    - [6.3 迁移建议](#63-迁移建议)
  - [总结](#总结)

---

## 1. 内存安全模型对比

### 1.1 核心机制

| 特性 | Swift | Rust |
|:---|:---|:---|
| **内存管理** | ARC（自动引用计数） | 所有权系统 |
| **循环引用** | weak/unowned 手动解决 | 编译时生命周期检查 |
| **悬空指针** | 运行时检测 | 编译时禁止 |
| **内存泄漏** | 可能（循环引用） | 编译时防止 |

### 1.2 ARC vs Ownership

```swift
// Swift: ARC 自动管理
class Person {
    var name: String
    var friend: Person?  // 强引用

    init(name: String) {
        self.name = name
    }
}

var alice: Person? = Person(name: "Alice")
var bob: Person? = Person(name: "Bob")
alice?.friend = bob
bob?.friend = alice  // 循环引用！需要 weak 解决
```

```rust
// Rust: 所有权编译时管理
struct Person {
    name: String,
}

struct Friendship {
    person1: Rc<Person>,
    person2: Weak<Person>,  // 编译时区分强弱引用
}

// 或使用引用生命周期
struct PersonRef<'a> {
    name: &'a str,
}
```

### 1.3 循环引用解决

```swift
// Swift: 手动标记 weak
class Person {
    var name: String
    weak var friend: Person?  // 弱引用，可能为 nil
    unowned var partner: Partner  // 无主引用，非可选

    init(name: String, partner: Partner) {
        self.name = name
        self.partner = partner
    }
}
```

```rust
// Rust: 编译时确保无循环
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Weak<Node>>,  // 编译时知道是弱引用
}

// 或使用 arena 分配器避免引用计数
```

---

## 2. 类型系统

### 2.1 代数数据类型

```swift
// Swift: enum 支持关联值
enum Result<T, E: Error> {
    case success(T)
    case failure(E)
}

enum Optional<Wrapped> {
    case some(Wrapped)
    case none
}

// 模式匹配
switch result {
case .success(let value):
    print(value)
case .failure(let error):
    print(error)
}
```

```rust
// Rust: enum 相同概念
enum Result<T, E> {
    Ok(T),
    Err(E),
}

enum Option<T> {
    Some(T),
    None,
}

// 模式匹配
match result {
    Ok(value) => println!("{}", value),
    Err(e) => println!("{}", e),
}
```

### 2.2 泛型与协议/Trait

```swift
// Swift: Protocol + Extension
protocol Drawable {
    func draw()
}

extension Drawable {
    func describe() {
        print("A drawable object")
    }
}

struct Circle: Drawable {
    func draw() { /* ... */ }
}

// 泛型约束
func render<T: Drawable>(item: T) {
    item.draw()
}
```

```rust
// Rust: Trait
pub trait Drawable {
    fn draw(&self);
    fn describe(&self) {
        println!("A drawable object");
    }
}

struct Circle;

impl Drawable for Circle {
    fn draw(&self) { /* ... */ }
}

// 泛型约束
pub fn render<T: Drawable>(item: &T) {
    item.draw();
}
```

### 2.3 关键差异

| 特性 | Swift | Rust |
|:---|:---|:---|
| **动态派发** | `any Drawable` (存在类型) | `dyn Drawable` (trait object) |
| **静态派发** | 泛型默认静态 | 单态化 (零成本) |
| **关联类型** | `associatedtype` | `type` |
| **泛型特化** | 有限支持 | 完整支持 |

---

## 3. 所有权与引用

### 3.1 引用语义

```swift
// Swift: 值类型 vs 引用类型
struct Point {  // 值类型，复制语义
    var x, y: Double
}

class Node {    // 引用类型，共享语义
    var value: Int
    var next: Node?
}

var p1 = Point(x: 0, y: 0)
var p2 = p1    // 复制
p2.x = 10
print(p1.x)    // 0 (未改变)

var n1 = Node(value: 1)
var n2 = n1    // 引用同一对象
n2.value = 10
print(n1.value) // 10 (已改变)
```

```rust
// Rust: 所有权系统
#[derive(Clone, Copy)]
struct Point {
    x: f64,
    y: f64,
}

struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

let p1 = Point { x: 0.0, y: 0.0 };
let p2 = p1;     // 复制 (实现 Copy)
// p1 仍然可用

let n1 = Box::new(Node { value: 1, next: None });
let n2 = n1;     // 所有权转移
// n1 不再可用 (编译错误)
```

### 3.2 借用检查

```swift
// Swift: 无借用检查，运行时值语义
func process(array: [Int]) -> Int {
    return array.reduce(0, +)
}

var data = [1, 2, 3]
let sum1 = process(array: data)  // 复制
let sum2 = process(array: data)  // 再次复制
```

```rust
// Rust: 借用检查
fn process(array: &[i32]) -> i32 {
    array.iter().sum()
}

let data = vec![1, 2, 3];
let sum1 = process(&data);  // 不可变借用
let sum2 = process(&data);  // 可以同时多个借用
// data 仍然可用

fn modify(array: &mut [i32]) {
    array[0] = 10;
}

let mut data = vec![1, 2, 3];
modify(&mut data);  // 可变借用
// 不能同时有其他借用
```

---

## 4. 并发模型

### 4.1 Swift 并发

```swift
// Swift: async/await + Actor
actor BankAccount {
    private var balance: Double = 0

    func deposit(_ amount: Double) {
        balance += amount
    }

    func getBalance() -> Double {
        return balance
    }
}

func transfer(from: BankAccount, to: BankAccount, amount: Double) async {
    await from.deposit(-amount)
    await to.deposit(amount)
}

// 结构化并发
async let task1 = fetchData()
async let task2 = fetchData()
let (result1, result2) = await (task1, task2)
```

### 4.2 Rust 并发

```rust
// Rust: 所有权 + Send/Sync
tokio::spawn(async move {
    // 异步任务，所有权转移进来
});

// Actor 模式（使用 tokio）
use tokio::sync::mpsc;

struct BankAccount {
    balance: f64,
    receiver: mpsc::Receiver<AccountMsg>,
}

enum AccountMsg {
    Deposit(f64),
    GetBalance(tokio::sync::oneshot::Sender<f64>),
}

impl BankAccount {
    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                AccountMsg::Deposit(amount) => self.balance += amount,
                AccountMsg::GetBalance(sender) => {
                    let _ = sender.send(self.balance);
                }
            }
        }
    }
}
```

### 4.3 并发安全对比

| 特性 | Swift Actor | Rust Send/Sync |
|:---|:---|:---|
| **数据竞争** | 编译时 Actor 隔离 | 编译时 Send/Sync |
| **死锁** | 可能 | 可能 |
| **性能** | 运行时调度 | 零成本抽象 |
| **跨线程** | 自动处理 | 显式标记 |

---

## 5. 错误处理

### 5.1 Swift 错误处理

```swift
// Swift: throws + do-catch
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
    print("Unknown error")
}

// Optional 转换
let content = try? readFile(path: "/tmp/data.txt")  // String?
```

### 5.2 Rust 错误处理

```rust
// Rust: Result<T, E> + ?
#[derive(Debug)]
enum FileError {
    NotFound,
    PermissionDenied,
}

fn read_file(path: &str) -> Result<String, FileError> {
    if !Path::new(path).exists() {
        return Err(FileError::NotFound);
    }
    // ...
    Ok(content)
}

// 调用
match read_file("/tmp/data.txt") {
    Ok(content) => println!("{}", content),
    Err(FileError::NotFound) => println!("File not found"),
    Err(e) => println!("Error: {:?}", e),
}

// ? 传播
fn process_file() -> Result<String, FileError> {
    let content = read_file("/tmp/data.txt")?;  // 自动传播错误
    Ok(content.to_uppercase())
}

// Option 转换
let content = read_file("/tmp/data.txt").ok();  // Option<String>
```

---

## 6. 应用场景与选型

### 6.1 适用场景

| 场景 | Swift | Rust |
|:---|:---|:---|
| **iOS/macOS 开发** | ✅ 首选 | ⚠️ 有限支持 |
| **Android/跨平台** | ⚠️ Kotlin Multiplatform | ✅ 优秀 |
| **后端服务** | ✅ Vapor | ✅ Actix/Axum |
| **系统编程** | ❌ 不适合 | ✅ 核心优势 |
| **嵌入式/IoT** | ⚠️ 有限 | ✅ 核心优势 |
| **WebAssembly** | ⚠️ 实验性 | ✅ 成熟生态 |
| **机器学习** | ⚠️ Core ML | ✅ tch-rs, burn |

### 6.2 性能对比

| 指标 | Swift | Rust |
|:---|:---|:---|
| **启动时间** | 中等 (ARC 初始化) | 极快 |
| **内存占用** | 中等 | 低 |
| **ARC 开销** | ~5-10% | 无 |
| **运行时** | 需要 | 可选 (no_std) |

### 6.3 迁移建议

```
Swift 开发者学习 Rust:

Week 1: 所有权
- 理解所有权转移 vs ARC
- 借用 vs 引用
- 生命周期基础

Week 2: 类型系统
- enum/Option/Result 差异
- Trait vs Protocol
- 泛型单态化

Week 3: 内存管理
- Box/Rc/Arc
- 生命周期标注
- 智能指针模式

Week 4: 错误处理与并发
- Result<T, E> vs throws
- Send/Sync vs Actor
- async/await 差异
```

---

## 总结

| 维度 | Swift | Rust |
|:---|:---|:---|
| **设计理念** | 开发者体验优先 | 零成本安全 |
| **内存安全** | ARC + 运行时检查 | 所有权 + 编译时检查 |
| **学习曲线** | 平缓 | 陡峭 |
| **平台** | Apple 生态优先 | 跨平台系统 |
| **最佳场景** | 客户端应用 | 系统/基础设施 |

**选择建议**:

- Apple 平台客户端开发 → Swift
- 跨平台系统编程 → Rust

---

*文档版本: 1.0.0*
