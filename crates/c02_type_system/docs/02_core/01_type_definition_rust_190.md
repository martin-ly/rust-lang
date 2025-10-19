# Rust 1.90 类型定义系统新特性与增强

**文档版本**: 1.0  
**Rust版本**: 1.90+  
**创建日期**: 2025-10-19  
**难度等级**: 中级到高级

> 📌 **说明**：本文档是 [01_type_definition.md](./01_type_definition.md) 的补充，专注于 Rust 1.90 的新特性、概念矩阵对比和实战应用。

## 📋 目录

- [Rust 1.90 类型定义系统新特性与增强](#rust-190-类型定义系统新特性与增强)
  - [📋 目录](#-目录)
  - [1. Rust 1.90 核心类型特性](#1-rust-190-核心类型特性)
    - [1.1 Edition 2024 类型改进](#11-edition-2024-类型改进)
    - [1.2 Trait Upcasting 稳定化](#12-trait-upcasting-稳定化)
    - [1.3 RPITIT 支持](#13-rpitit-支持)
    - [1.4 异步 Trait 方法](#14-异步-trait-方法)
  - [2. 📊 类型系统概念矩阵](#2--类型系统概念矩阵)
    - [2.1 基本类型对比矩阵](#21-基本类型对比矩阵)
    - [2.2 复合类型对比矩阵](#22-复合类型对比矩阵)
    - [2.3 智能指针对比矩阵](#23-智能指针对比矩阵)
    - [2.4 并发类型对比矩阵](#24-并发类型对比矩阵)
  - [3. 类型转换机制对比](#3-类型转换机制对比)
    - [3.1 转换 Trait 对比](#31-转换-trait-对比)
    - [3.2 强制转换规则](#32-强制转换规则)
  - [4. 高级类型模式](#4-高级类型模式)
    - [4.1 新类型模式（Newtype Pattern）](#41-新类型模式newtype-pattern)
    - [4.2 类型状态模式（Typestate Pattern）](#42-类型状态模式typestate-pattern)
    - [4.3 幻影类型（Phantom Types）](#43-幻影类型phantom-types)
  - [5. 类型安全最佳实践](#5-类型安全最佳实践)
    - [5.1 使用类型系统防止错误](#51-使用类型系统防止错误)
    - [5.2 零大小类型（ZST）优化](#52-零大小类型zst优化)
    - [5.3 类型擦除技术](#53-类型擦除技术)
  - [6. 🗺️ 完整类型系统思维导图](#6-️-完整类型系统思维导图)
  - [7. 实战案例](#7-实战案例)
    - [7.1 类型安全的状态机](#71-类型安全的状态机)
    - [7.2 类型级计算](#72-类型级计算)
    - [7.3 零成本抽象示例](#73-零成本抽象示例)
  - [8. 总结](#8-总结)
    - [核心改进总结](#核心改进总结)
    - [最佳实践](#最佳实践)
    - [性能建议](#性能建议)

---

## 1. Rust 1.90 核心类型特性

### 1.1 Edition 2024 类型改进

**Edition 2024** 带来了多项类型系统改进：

```rust
// Rust 1.90 Edition 2024 新特性

// 1. 改进的闭包捕获
fn closure_improvements() {
    let data = vec![1, 2, 3];
    
    // ✅ Edition 2024: 更精确的捕获
    let closure = || {
        // 只捕获需要的字段
        println!("{}", data.len());
    };
    
    closure();
    // ✅ data 仍然可用
    println!("{:?}", data);
}

// 2. 改进的模式匹配
fn pattern_matching_improvements() {
    enum Message {
        Text(String),
        Number(i32),
    }
    
    let msg = Message::Text(String::from("hello"));
    
    // ✅ Edition 2024: 更简洁的模式
    if let Message::Text(text) = msg {
        println!("{}", text);
    }
}

// 3. async/await 语法改进
async fn async_improvements() {
    // ✅ Edition 2024: 更好的异步类型推断
    let futures = vec![
        async { 1 },
        async { 2 },
        async { 3 },
    ];
    
    for fut in futures {
        let result = fut.await;
        println!("{}", result);
    }
}
```

### 1.2 Trait Upcasting 稳定化

**Trait Upcasting** 允许 trait 对象之间的安全转换：

```rust
// Rust 1.90: Trait Upcasting 稳定化

trait Animal {
    fn eat(&self);
}

trait Mammal: Animal {
    fn give_birth(&self);
}

trait Dog: Mammal {
    fn bark(&self);
}

struct GoldenRetriever;

impl Animal for GoldenRetriever {
    fn eat(&self) {
        println!("Eating");
    }
}

impl Mammal for GoldenRetriever {
    fn give_birth(&self) {
        println!("Giving birth");
    }
}

impl Dog for GoldenRetriever {
    fn bark(&self) {
        println!("Woof!");
    }
}

fn trait_upcasting_demo() {
    let dog: &dyn Dog = &GoldenRetriever;
    
    // ✅ Rust 1.90: 直接上转型
    let mammal: &dyn Mammal = dog;
    let animal: &dyn Animal = mammal;
    
    animal.eat();
}

// 实际应用：多态集合
fn polymorphic_collections() {
    let animals: Vec<Box<dyn Animal>> = vec![
        Box::new(GoldenRetriever),
        // 可以添加其他实现 Animal 的类型
    ];
    
    for animal in animals {
        animal.eat();
    }
}
```

### 1.3 RPITIT 支持

**RPITIT (Return Position impl Trait in Traits)** 允许在 trait 方法中返回 `impl Trait`：

```rust
// Rust 1.90: RPITIT 稳定化

trait Repository {
    type Item;
    
    // ✅ 返回位置的 impl Trait
    fn find_all(&self) -> impl Iterator<Item = Self::Item>;
    
    // ✅ 也可以是异步的
    async fn find_by_id(&self, id: u64) -> Option<Self::Item>;
}

struct UserRepository;

impl Repository for UserRepository {
    type Item = String;
    
    fn find_all(&self) -> impl Iterator<Item = Self::Item> {
        vec!["Alice".to_string(), "Bob".to_string()].into_iter()
    }
    
    async fn find_by_id(&self, id: u64) -> Option<Self::Item> {
        if id == 1 {
            Some("Alice".to_string())
        } else {
            None
        }
    }
}

// 实际应用
fn use_rpitit() {
    let repo = UserRepository;
    
    // ✅ 简洁的迭代器使用
    for user in repo.find_all() {
        println!("User: {}", user);
    }
}

// 更复杂的示例：链式调用
trait Processor {
    fn process(&self, input: &str) -> impl Iterator<Item = String> + '_;
}

struct TextProcessor;

impl Processor for TextProcessor {
    fn process(&self, input: &str) -> impl Iterator<Item = String> + '_ {
        input.split_whitespace().map(|s| s.to_string())
    }
}
```

### 1.4 异步 Trait 方法

```rust
// Rust 1.90: 原生异步 trait 方法

trait AsyncDataSource {
    async fn fetch(&self) -> Vec<u8>;
    async fn store(&mut self, data: Vec<u8>) -> Result<(), String>;
}

struct FileDataSource {
    path: String,
}

impl AsyncDataSource for FileDataSource {
    async fn fetch(&self) -> Vec<u8> {
        // 异步读取文件
        vec![1, 2, 3, 4, 5]
    }
    
    async fn store(&mut self, data: Vec<u8>) -> Result<(), String> {
        // 异步写入文件
        println!("Storing {} bytes to {}", data.len(), self.path);
        Ok(())
    }
}

// 使用示例
async fn use_async_trait() {
    let source = FileDataSource {
        path: "data.bin".to_string(),
    };
    
    let data = source.fetch().await;
    println!("Fetched {} bytes", data.len());
}
```

---

## 2. 📊 类型系统概念矩阵

### 2.1 基本类型对比矩阵

| 类型 | 大小(字节) | 对齐 | 值域 | Copy | Drop | 默认值 | 用途 |
|------|-----------|------|------|------|------|--------|------|
| `i8` | 1 | 1 | -128 ~ 127 | ✅ | ❌ | 0 | 小整数 |
| `i16` | 2 | 2 | -32768 ~ 32767 | ✅ | ❌ | 0 | 中整数 |
| `i32` | 4 | 4 | -2³¹ ~ 2³¹-1 | ✅ | ❌ | 0 | 默认整数 |
| `i64` | 8 | 8 | -2⁶³ ~ 2⁶³-1 | ✅ | ❌ | 0 | 大整数 |
| `i128` | 16 | 16 | -2¹²⁷ ~ 2¹²⁷-1 | ✅ | ❌ | 0 | 超大整数 |
| `isize` | 4/8 | 4/8 | 平台相关 | ✅ | ❌ | 0 | 指针大小 |
| `u8` | 1 | 1 | 0 ~ 255 | ✅ | ❌ | 0 | 字节 |
| `u32` | 4 | 4 | 0 ~ 2³²-1 | ✅ | ❌ | 0 | 无符号整数 |
| `f32` | 4 | 4 | IEEE 754 | ✅ | ❌ | 0.0 | 单精度浮点 |
| `f64` | 8 | 8 | IEEE 754 | ✅ | ❌ | 0.0 | 双精度浮点 |
| `bool` | 1 | 1 | true/false | ✅ | ❌ | false | 布尔值 |
| `char` | 4 | 4 | Unicode | ✅ | ❌ | '\0' | Unicode字符 |
| `()` | 0 | 1 | () | ✅ | ❌ | () | 单元类型 |

### 2.2 复合类型对比矩阵

| 类型 | 大小 | 堆分配 | 可变长度 | Copy | 所有权 | 主要用途 |
|------|------|--------|---------|------|--------|---------|
| `[T; N]` | `N * size_of::<T>()` | ❌ | ❌ 固定 | 取决于T | 拥有 | 固定数组 |
| `&[T]` | 16 (ptr+len) | ❌ | ❌ | ✅ | 借用 | 切片引用 |
| `Vec<T>` | 24 (ptr+len+cap) | ✅ | ✅ | ❌ | 拥有 | 动态数组 |
| `String` | 24 | ✅ | ✅ | ❌ | 拥有 | 可增长字符串 |
| `&str` | 16 | ❌ | ❌ | ✅ | 借用 | 字符串切片 |
| `(T, U)` | `size_of::<T>() + size_of::<U>() + padding` | 取决于T,U | ❌ | 取决于T,U | 拥有 | 元组 |
| `Option<T>` | `size_of::<T>() + discriminant` | 取决于T | ❌ | 取决于T | 拥有 | 可选值 |
| `Result<T, E>` | `max(size_of::<T>(), size_of::<E>()) + discriminant` | 取决于T,E | ❌ | 取决于T,E | 拥有 | 错误处理 |

### 2.3 智能指针对比矩阵

| 类型 | 堆分配 | 引用计数 | 线程安全 | 开销 | 主要用途 | 特殊能力 |
|------|--------|---------|---------|------|---------|---------|
| `Box<T>` | ✅ | ❌ | ❌ | 最小 | 单一所有权 | 堆分配 |
| `Rc<T>` | ✅ | ✅ 非原子 | ❌ | 中等 | 多个所有者 | 引用计数 |
| `Arc<T>` | ✅ | ✅ 原子 | ✅ | 较高 | 线程间共享 | 原子引用计数 |
| `Cow<T>` | 按需 | ❌ | ❌ | 最小 | 写时复制 | 延迟克隆 |
| `Cell<T>` | ❌ | ❌ | ❌ | 最小 | 内部可变性 | Copy 类型 |
| `RefCell<T>` | ❌ | ✅ 借用计数 | ❌ | 中等 | 运行时借用检查 | 动态借用 |
| `Mutex<T>` | ❌ | ❌ | ✅ | 较高 | 互斥访问 | 线程同步 |
| `RwLock<T>` | ❌ | ❌ | ✅ | 较高 | 读写锁 | 多读单写 |

### 2.4 并发类型对比矩阵

| 类型 | Send | Sync | 用途 | 性能 | 适用场景 |
|------|------|------|------|------|---------|
| `Arc<T>` | ✅ (if T: Send+Sync) | ✅ (if T: Send+Sync) | 共享所有权 | 中等 | 多线程共享数据 |
| `Mutex<T>` | ✅ (if T: Send) | ✅ (if T: Send) | 互斥锁 | 中等 | 可变共享状态 |
| `RwLock<T>` | ✅ (if T: Send) | ✅ (if T: Send+Sync) | 读写锁 | 高（读多） | 读多写少 |
| `AtomicBool` | ✅ | ✅ | 原子布尔 | 很高 | 简单标志 |
| `AtomicUsize` | ✅ | ✅ | 原子整数 | 很高 | 计数器 |
| `Barrier` | ✅ | ✅ | 屏障 | 中等 | 同步点 |
| `Condvar` | ✅ | ✅ | 条件变量 | 中等 | 等待条件 |
| `mpsc::Sender<T>` | ✅ (if T: Send) | ❌ | 发送端 | 高 | 消息传递 |
| `mpsc::Receiver<T>` | ✅ (if T: Send) | ❌ | 接收端 | 高 | 消息传递 |

---

## 3. 类型转换机制对比

### 3.1 转换 Trait 对比

| Trait | 语法 | 失败处理 | 性能 | 使用场景 | 示例 |
|-------|------|---------|------|---------|------|
| `From<T>` | `T::from(value)` | 不会失败 | 零成本 | 无损转换 | `String::from("hello")` |
| `Into<T>` | `value.into()` | 不会失败 | 零成本 | 自动推导 | `"hello".into()` |
| `TryFrom<T>` | `T::try_from(value)` | `Result` | 零成本 | 可能失败 | `u8::try_from(256)` |
| `TryInto<T>` | `value.try_into()` | `Result` | 零成本 | 可能失败 | `256.try_into()` |
| `AsRef<T>` | `value.as_ref()` | 不会失败 | 零成本 | 借用转换 | `String.as_ref()` |
| `AsMut<T>` | `value.as_mut()` | 不会失败 | 零成本 | 可变借用 | `Vec.as_mut()` |
| `Deref` | `*value` | 不会失败 | 零成本 | 自动解引用 | `Box<T>` |
| `as` | `value as Type` | 截断/饱和 | 零成本 | 基本类型 | `42 as f64` |

### 3.2 强制转换规则

```rust
// Rust 类型强制转换（Coercion）示例

fn coercion_examples() {
    // 1. 引用强制转换
    let s = String::from("hello");
    let slice: &str = &s;  // ✅ &String → &str
    
    // 2. 可变到不可变
    let mut x = 42;
    let r: &i32 = &mut x;  // ✅ &mut T → &T
    
    // 3. 数组到切片
    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr;  // ✅ &[T; N] → &[T]
    
    // 4. 具体类型到 trait 对象
    trait Animal {}
    struct Dog;
    impl Animal for Dog {}
    
    let dog = Dog;
    let animal: &dyn Animal = &dog;  // ✅ &T → &dyn Trait
    
    // 5. 函数项到函数指针
    fn add(a: i32, b: i32) -> i32 { a + b }
    let func_ptr: fn(i32, i32) -> i32 = add;  // ✅ fn item → fn pointer
    
    // 6. Deref 强制转换
    let boxed = Box::new(vec![1, 2, 3]);
    let slice: &[i32] = &boxed;  // ✅ Box<Vec<T>> → &[T]
}
```

---

## 4. 高级类型模式

### 4.1 新类型模式（Newtype Pattern）

```rust
// 新类型模式：类型安全的包装

// 问题：i32 可以表示任何整数，缺乏语义
fn bad_api(user_id: i32, age: i32, salary: i32) {
    // 容易混淆参数顺序
}

// ✅ 解决方案：使用新类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UserId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Age(u8);

#[derive(Debug, Clone, Copy)]
struct Salary(u64);

// 类型安全的 API
fn good_api(user_id: UserId, age: Age, salary: Salary) {
    println!("User {:?}, Age {:?}, Salary {:?}", user_id, age, salary);
}

// 为新类型实现方法
impl UserId {
    fn new(id: u64) -> Self {
        UserId(id)
    }
    
    fn as_u64(&self) -> u64 {
        self.0
    }
}

impl Age {
    fn new(age: u8) -> Option<Self> {
        if age > 0 && age < 150 {
            Some(Age(age))
        } else {
            None
        }
    }
    
    fn is_adult(&self) -> bool {
        self.0 >= 18
    }
}

// 使用示例
fn use_newtype() {
    let user_id = UserId::new(12345);
    let age = Age::new(25).unwrap();
    let salary = Salary(50000);
    
    good_api(user_id, age, salary);
    
    // ❌ 编译错误：类型不匹配
    // good_api(age, user_id, salary);
}
```

### 4.2 类型状态模式（Typestate Pattern）

```rust
// 类型状态模式：使用类型系统表示状态

// 连接的不同状态
struct Disconnected;
struct Connected;
struct Authenticated;

// 数据库连接
struct DatabaseConnection<State = Disconnected> {
    _state: std::marker::PhantomData<State>,
    url: String,
}

// 每个状态只允许特定操作
impl DatabaseConnection<Disconnected> {
    fn new(url: String) -> Self {
        DatabaseConnection {
            _state: std::marker::PhantomData,
            url,
        }
    }
    
    // ✅ 只有断开状态可以连接
    fn connect(self) -> DatabaseConnection<Connected> {
        println!("Connecting to {}", self.url);
        DatabaseConnection {
            _state: std::marker::PhantomData,
            url: self.url,
        }
    }
}

impl DatabaseConnection<Connected> {
    // ✅ 只有连接状态可以认证
    fn authenticate(self, password: &str) -> DatabaseConnection<Authenticated> {
        println!("Authenticating with password");
        DatabaseConnection {
            _state: std::marker::PhantomData,
            url: self.url,
        }
    }
    
    // ✅ 可以断开连接
    fn disconnect(self) -> DatabaseConnection<Disconnected> {
        println!("Disconnecting");
        DatabaseConnection {
            _state: std::marker::PhantomData,
            url: self.url,
        }
    }
}

impl DatabaseConnection<Authenticated> {
    // ✅ 只有认证状态可以查询
    fn query(&self, sql: &str) -> Vec<String> {
        println!("Executing query: {}", sql);
        vec!["result1".to_string(), "result2".to_string()]
    }
    
    fn disconnect(self) -> DatabaseConnection<Disconnected> {
        println!("Disconnecting");
        DatabaseConnection {
            _state: std::marker::PhantomData,
            url: self.url,
        }
    }
}

// 使用示例
fn use_typestate() {
    let conn = DatabaseConnection::new("localhost:5432".to_string());
    
    // ❌ 编译错误：Disconnected 状态不能 query
    // conn.query("SELECT * FROM users");
    
    let conn = conn.connect();
    
    // ❌ 编译错误：Connected 状态不能 query
    // conn.query("SELECT * FROM users");
    
    let conn = conn.authenticate("password");
    
    // ✅ Authenticated 状态可以 query
    let results = conn.query("SELECT * FROM users");
    println!("Results: {:?}", results);
}
```

### 4.3 幻影类型（Phantom Types）

```rust
use std::marker::PhantomData;

// 幻影类型：在编译时携带类型信息

// 定义单位类型
struct Meters;
struct Feet;
struct Seconds;

// 带单位的距离
#[derive(Debug)]
struct Distance<Unit> {
    value: f64,
    _unit: PhantomData<Unit>,
}

impl<Unit> Distance<Unit> {
    fn new(value: f64) -> Self {
        Distance {
            value,
            _unit: PhantomData,
        }
    }
}

// 单位转换
impl Distance<Meters> {
    fn to_feet(self) -> Distance<Feet> {
        Distance::new(self.value * 3.28084)
    }
}

impl Distance<Feet> {
    fn to_meters(self) -> Distance<Meters> {
        Distance::new(self.value / 3.28084)
    }
}

// 只有相同单位才能相加
impl<Unit> std::ops::Add for Distance<Unit> {
    type Output = Distance<Unit>;
    
    fn add(self, other: Self) -> Self::Output {
        Distance::new(self.value + other.value)
    }
}

// 使用示例
fn use_phantom_types() {
    let d1 = Distance::<Meters>::new(100.0);
    let d2 = Distance::<Meters>::new(50.0);
    
    // ✅ 相同单位可以相加
    let total = d1 + d2;
    println!("Total distance: {:?}", total);
    
    let d3 = Distance::<Feet>::new(100.0);
    
    // ❌ 编译错误：不同单位不能相加
    // let mixed = total + d3;
    
    // ✅ 需要先转换单位
    let d3_meters = d3.to_meters();
    let correct_total = total + d3_meters;
    println!("Correct total: {:?}", correct_total);
}
```

---

## 5. 类型安全最佳实践

### 5.1 使用类型系统防止错误

```rust
// 示例：防止空指针错误

// ❌ 不好：使用 Option<T> 到处传递
fn bad_design(maybe_user: Option<String>) -> Option<String> {
    if let Some(user) = maybe_user {
        Some(format!("Hello, {}", user))
    } else {
        None
    }
}

// ✅ 好：使用类型系统表达"已验证"的状态
struct ValidatedUser {
    name: String,
}

impl ValidatedUser {
    fn new(name: String) -> Option<Self> {
        if !name.is_empty() {
            Some(ValidatedUser { name })
        } else {
            None
        }
    }
    
    // 保证 name 不为空
    fn name(&self) -> &str {
        &self.name
    }
}

fn good_design(user: ValidatedUser) -> String {
    format!("Hello, {}", user.name())
}

// 示例：使用类型防止业务逻辑错误
#[derive(Debug)]
struct Price {
    cents: u64,  // 使用 cents 避免浮点数精度问题
}

impl Price {
    fn new(dollars: f64) -> Self {
        Price {
            cents: (dollars * 100.0) as u64,
        }
    }
    
    fn from_cents(cents: u64) -> Self {
        Price { cents }
    }
    
    fn as_dollars(&self) -> f64 {
        self.cents as f64 / 100.0
    }
}

// 防止负价格
impl std::ops::Add for Price {
    type Output = Price;
    
    fn add(self, other: Self) -> Self::Output {
        Price::from_cents(self.cents + other.cents)
    }
}
```

### 5.2 零大小类型（ZST）优化

```rust
// 零大小类型：没有运行时开销

struct Nothing;  // ZST

fn zst_examples() {
    // ✅ 零大小类型不占用内存
    assert_eq!(std::mem::size_of::<Nothing>(), 0);
    
    // ✅ Vec<ZST> 不分配堆内存
    let vec: Vec<Nothing> = vec![Nothing; 1000];
    assert_eq!(std::mem::size_of_val(&vec), 24);  // 只有 Vec 的元数据
}

// 实际应用：状态标记
struct ReadOnly;
struct ReadWrite;

struct Buffer<Access> {
    data: Vec<u8>,
    _access: std::marker::PhantomData<Access>,
}

impl<Access> Buffer<Access> {
    fn len(&self) -> usize {
        self.data.len()
    }
}

impl Buffer<ReadOnly> {
    fn from_data(data: Vec<u8>) -> Self {
        Buffer {
            data,
            _access: std::marker::PhantomData,
        }
    }
    
    fn read(&self, index: usize) -> Option<&u8> {
        self.data.get(index)
    }
}

impl Buffer<ReadWrite> {
    fn new() -> Self {
        Buffer {
            data: Vec::new(),
            _access: std::marker::PhantomData,
        }
    }
    
    fn write(&mut self, value: u8) {
        self.data.push(value);
    }
}

// ✅ 零成本：PhantomData<Access> 不占用空间
fn zst_buffer_usage() {
    let mut buf = Buffer::<ReadWrite>::new();
    buf.write(42);
    
    assert_eq!(std::mem::size_of_val(&buf), 24);  // 只有 Vec 的大小
}
```

### 5.3 类型擦除技术

```rust
// 类型擦除：在运行时隐藏具体类型

trait Handler {
    fn handle(&self, input: &str) -> String;
}

struct ConcreteHandler;

impl Handler for ConcreteHandler {
    fn handle(&self, input: &str) -> String {
        format!("Handled: {}", input)
    }
}

// 类型擦除容器
struct ErasedHandler {
    handler: Box<dyn Handler>,
}

impl ErasedHandler {
    fn new<H: Handler + 'static>(handler: H) -> Self {
        ErasedHandler {
            handler: Box::new(handler),
        }
    }
    
    fn handle(&self, input: &str) -> String {
        self.handler.handle(input)
    }
}

// 使用示例
fn use_type_erasure() {
    let erased = ErasedHandler::new(ConcreteHandler);
    let result = erased.handle("test");
    println!("{}", result);
}
```

---

## 6. 🗺️ 完整类型系统思维导图

```text
Rust 类型定义系统 (Rust 1.90)
│
├── 📚 基本类型
│   ├── 标量类型
│   │   ├── 整数：i8~i128, u8~u128, isize, usize
│   │   ├── 浮点：f32, f64
│   │   ├── 布尔：bool
│   │   └── 字符：char (Unicode)
│   │
│   └── 复合类型
│       ├── 元组：(T, U, ...)
│       ├── 数组：[T; N]
│       ├── 切片：&[T]
│       └── 字符串：String, &str
│
├── 🏗️ 自定义类型
│   ├── 结构体
│   │   ├── 命名字段：struct Point { x: i32, y: i32 }
│   │   ├── 元组结构：struct Color(u8, u8, u8)
│   │   └── 单元结构：struct Marker;
│   │
│   ├── 枚举
│   │   ├── 无数据：enum Status { Active, Inactive }
│   │   ├── 有数据：enum Option<T> { Some(T), None }
│   │   └── 混合：enum Message { Text(String), Quit }
│   │
│   ├── 联合体：union MyUnion { f1: u32, f2: f32 }
│   └── 类型别名：type UserId = u64
│
├── 🧩 泛型与 Trait
│   ├── 泛型类型
│   │   ├── 结构体：struct Wrapper<T> { value: T }
│   │   ├── 枚举：enum Result<T, E> { Ok(T), Err(E) }
│   │   └── 函数：fn process<T>(value: T)
│   │
│   ├── Trait 对象
│   │   ├── dyn Trait：动态分发
│   │   ├── impl Trait：静态分发
│   │   └── 🆕 RPITIT：返回位置 impl Trait
│   │
│   └── 🆕 Rust 1.90 特性
│       ├── Trait Upcasting 稳定化
│       ├── 异步 Trait 方法
│       └── Edition 2024 改进
│
├── 🔗 智能指针
│   ├── 单一所有权
│   │   └── Box<T>：堆分配
│   │
│   ├── 共享所有权
│   │   ├── Rc<T>：引用计数
│   │   └── Arc<T>：原子引用计数
│   │
│   ├── 内部可变性
│   │   ├── Cell<T>：Copy 类型
│   │   ├── RefCell<T>：运行时借用
│   │   ├── Mutex<T>：线程安全
│   │   └── RwLock<T>：读写锁
│   │
│   └── 其他
│       ├── Cow<T>：写时复制
│       └── Pin<T>：固定内存位置
│
├── 🔄 类型转换
│   ├── Trait 转换
│   │   ├── From/Into：无损转换
│   │   ├── TryFrom/TryInto：可能失败
│   │   ├── AsRef/AsMut：借用转换
│   │   └── Deref/DerefMut：解引用
│   │
│   ├── 强制转换
│   │   ├── &String → &str
│   │   ├── &mut T → &T
│   │   ├── &[T; N] → &[T]
│   │   └── &T → &dyn Trait
│   │
│   └── as 转换：基本类型
│
├── 🎯 高级模式
│   ├── 新类型模式：struct UserId(u64)
│   ├── 类型状态模式：状态机
│   ├── 幻影类型：PhantomData<T>
│   ├── 零大小类型：优化
│   └── 类型擦除：Box<dyn Trait>
│
├── 📊 性能与优化
│   ├── Copy vs Clone
│   ├── 零成本抽象
│   ├── 内存布局
│   └── repr 属性
│
└── 🛡️ 安全性
    ├── 所有权系统
    ├── 借用检查
    ├── 生命周期
    └── Unsafe Rust
```

---

## 7. 实战案例

### 7.1 类型安全的状态机

```rust
// 完整示例：类型安全的 TCP 连接状态机

use std::marker::PhantomData;

// 状态类型
struct Closed;
struct Listen;
struct SynReceived;
struct Established;

// TCP 连接
struct TcpConnection<State> {
    local_addr: String,
    remote_addr: Option<String>,
    _state: PhantomData<State>,
}

// Closed 状态
impl TcpConnection<Closed> {
    fn new(local_addr: String) -> Self {
        TcpConnection {
            local_addr,
            remote_addr: None,
            _state: PhantomData,
        }
    }
    
    fn listen(self) -> TcpConnection<Listen> {
        println!("Listening on {}", self.local_addr);
        TcpConnection {
            local_addr: self.local_addr,
            remote_addr: None,
            _state: PhantomData,
        }
    }
}

// Listen 状态
impl TcpConnection<Listen> {
    fn accept(self, remote_addr: String) -> TcpConnection<SynReceived> {
        println!("Received connection from {}", remote_addr);
        TcpConnection {
            local_addr: self.local_addr,
            remote_addr: Some(remote_addr),
            _state: PhantomData,
        }
    }
}

// SynReceived 状态
impl TcpConnection<SynReceived> {
    fn complete_handshake(self) -> TcpConnection<Established> {
        println!("Handshake complete");
        TcpConnection {
            local_addr: self.local_addr,
            remote_addr: self.remote_addr,
            _state: PhantomData,
        }
    }
}

// Established 状态
impl TcpConnection<Established> {
    fn send(&self, data: &[u8]) {
        println!("Sending {} bytes", data.len());
    }
    
    fn receive(&self) -> Vec<u8> {
        println!("Receiving data");
        vec![1, 2, 3, 4, 5]
    }
    
    fn close(self) -> TcpConnection<Closed> {
        println!("Closing connection");
        TcpConnection {
            local_addr: self.local_addr,
            remote_addr: None,
            _state: PhantomData,
        }
    }
}

// 使用示例
fn tcp_state_machine() {
    let conn = TcpConnection::<Closed>::new("127.0.0.1:8080".to_string());
    
    // ❌ 编译错误：Closed 状态不能 send
    // conn.send(b"data");
    
    let conn = conn.listen();
    let conn = conn.accept("192.168.1.100:12345".to_string());
    let conn = conn.complete_handshake();
    
    // ✅ Established 状态可以 send
    conn.send(b"Hello, World!");
    let data = conn.receive();
    println!("Received: {:?}", data);
    
    let _conn = conn.close();
}
```

### 7.2 类型级计算

```rust
// 使用类型系统进行编译时计算

use std::marker::PhantomData;

// 自然数类型
struct Zero;
struct Succ<N>(PhantomData<N>);

// 类型级别的加法
trait Add<N> {
    type Output;
}

impl<N> Add<Zero> for N {
    type Output = N;
}

impl<N, M> Add<Succ<M>> for N
where
    N: Add<M>,
{
    type Output = Succ<<N as Add<M>>::Output>;
}

// 类型级别的向量
struct Vector<N, T> {
    data: Vec<T>,
    _size: PhantomData<N>,
}

impl<N, T> Vector<N, T> {
    fn new(data: Vec<T>) -> Self {
        Vector {
            data,
            _size: PhantomData,
        }
    }
}

// 只有相同长度的向量可以相加
impl<N, T> std::ops::Add for Vector<N, T>
where
    T: std::ops::Add<Output = T> + Clone,
{
    type Output = Vector<N, T>;
    
    fn add(self, other: Self) -> Self::Output {
        let data = self
            .data
            .iter()
            .zip(other.data.iter())
            .map(|(a, b)| a.clone() + b.clone())
            .collect();
        Vector::new(data)
    }
}

// 使用示例
fn type_level_computation() {
    type One = Succ<Zero>;
    type Two = Succ<One>;
    type Three = Succ<Two>;
    
    let v1: Vector<Three, i32> = Vector::new(vec![1, 2, 3]);
    let v2: Vector<Three, i32> = Vector::new(vec![4, 5, 6]);
    
    // ✅ 相同长度可以相加
    let v3 = v1 + v2;
    println!("Result: {:?}", v3.data);
    
    // ❌ 编译错误：不同长度不能相加
    // let v4: Vector<Two, i32> = Vector::new(vec![7, 8]);
    // let v5 = v3 + v4;
}
```

### 7.3 零成本抽象示例

```rust
// 零成本抽象：编译时优化的迭代器

fn zero_cost_abstraction() {
    let numbers: Vec<i32> = (1..1000).collect();
    
    // 高级抽象
    let result: i32 = numbers
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * 2)
        .take(10)
        .sum();
    
    // 等效的低级代码（编译器生成）
    let mut result_manual = 0;
    let mut count = 0;
    for &n in &numbers {
        if n % 2 == 0 {
            let doubled = n * 2;
            result_manual += doubled;
            count += 1;
            if count >= 10 {
                break;
            }
        }
    }
    
    // ✅ 性能完全相同
    assert_eq!(result, result_manual);
    
    println!("Result: {}", result);
}

// 性能测试
use std::time::Instant;

fn benchmark_zero_cost() {
    let numbers: Vec<i32> = (1..10_000_000).collect();
    
    // 高级抽象
    let start = Instant::now();
    let _: i32 = numbers.iter().filter(|&&x| x % 2 == 0).sum();
    let high_level_time = start.elapsed();
    
    // 低级循环
    let start = Instant::now();
    let mut sum = 0;
    for &n in &numbers {
        if n % 2 == 0 {
            sum += n;
        }
    }
    let low_level_time = start.elapsed();
    
    println!("High-level: {:?}", high_level_time);
    println!("Low-level: {:?}", low_level_time);
    println!("Difference: {:?}", high_level_time.saturating_sub(low_level_time));
}
```

---

## 8. 总结

### 核心改进总结

**Rust 1.90 类型系统增强**：

1. ✅ **Edition 2024**：改进的闭包捕获、模式匹配、异步支持
2. ✅ **Trait Upcasting**：trait 对象间的安全转换
3. ✅ **RPITIT**：trait 方法返回 `impl Trait`
4. ✅ **异步 Trait**：原生异步 trait 方法支持

### 最佳实践

1. 🟢 **利用新类型模式**：增强类型安全
2. 🟢 **使用类型状态模式**：在编译时防止状态错误
3. 🟢 **应用零大小类型**：零成本的类型标记
4. 🟢 **掌握类型转换**：选择合适的转换方式

### 性能建议

- ⚡ **零成本抽象**：高级抽象不牺牲性能
- ⚡ **类型擦除**：必要时使用 trait 对象
- ⚡ **内联优化**：编译器自动内联小函数
- ⚡ **SIMD**：利用向量化指令（需要 unsafe）

---

**维护状态**: 🟢 活跃维护中  
**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

*本文档是 [01_type_definition.md](./01_type_definition.md) 的补充* 🦀
