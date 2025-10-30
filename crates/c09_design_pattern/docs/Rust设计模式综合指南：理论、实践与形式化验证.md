# Rust设计模式综合指南：理论、实践与形式化验证

## 文档概览

本指南是对Rust设计模式的全面梳理，涵盖：

1. **经典设计模式**：GoF 23种模式的Rust实现
2. **并发模式**：异步、并行、Actor、Reactor等
3. **形式化理论**：语义模型、等价关系、形式化证明
4. **实践指南**：最佳实践、性能分析、选型决策

**适用版本**：Rust 1.90+ (Edition 2024)
**文档版本**：2.0
**最后更新**：2025-10-02

---

## 目录

- [Rust设计模式综合指南：理论、实践与形式化验证](#rust设计模式综合指南理论实践与形式化验证)
  - [文档概览](#文档概览)
  - [目录](#目录)
  - [第一部分：经典设计模式](#第一部分经典设计模式)
    - [1. 创建型模式（Creational Patterns）](#1-创建型模式creational-patterns)
      - [1.1 单例模式（Singleton）](#11-单例模式singleton)
      - [1.2 工厂模式（Factory）](#12-工厂模式factory)
      - [1.3 建造者模式（Builder）](#13-建造者模式builder)
    - [2. 结构型模式（Structural Patterns）](#2-结构型模式structural-patterns)
      - [2.1 适配器模式（Adapter）](#21-适配器模式adapter)
      - [2.2 装饰器模式（Decorator）](#22-装饰器模式decorator)
    - [3. 行为型模式（Behavioral Patterns）](#3-行为型模式behavioral-patterns)
      - [3.1 观察者模式（Observer）](#31-观察者模式observer)
      - [3.2 策略模式（Strategy）](#32-策略模式strategy)
  - [第二部分：并发与异步模式](#第二部分并发与异步模式)
    - [1. 异步模式全景](#1-异步模式全景)
      - [1.1 执行模型分类](#11-执行模型分类)
      - [1.2 异步原语对比](#12-异步原语对比)
    - [2. 异步递归](#2-异步递归)
  - [第三部分：形式化理论](#第三部分形式化理论)
    - [1. 类型系统与证明](#1-类型系统与证明)
      - [1.1 Curry-Howard同构](#11-curry-howard同构)
      - [1.2 线性类型与资源管理](#12-线性类型与资源管理)
    - [2. 不变量与Hoare逻辑](#2-不变量与hoare逻辑)
  - [第四部分：实践指南](#第四部分实践指南)
    - [1. 设计模式选择决策树](#1-设计模式选择决策树)
    - [2. 并发模式选择](#2-并发模式选择)
    - [3. 性能优化指南](#3-性能优化指南)
      - [3.1 零成本抽象原则](#31-零成本抽象原则)
      - [3.2 内存布局优化](#32-内存布局优化)
  - [第五部分：高级主题](#第五部分高级主题)
    - [1. 会话类型（Session Types）](#1-会话类型session-types)
    - [2. 效应系统（Effect Systems）](#2-效应系统effect-systems)
  - [附录A：快速参考](#附录a快速参考)
    - [模式速查表](#模式速查表)
    - [常用命令](#常用命令)
  - [参考文献](#参考文献)

---

## 第一部分：经典设计模式

### 1. 创建型模式（Creational Patterns）

#### 1.1 单例模式（Singleton）

**理论定义**：保证一个类只有一个实例，并提供全局访问点。

**数学表示**：

```text
Singleton = { instance() → &'static T | ∀ call₁, call₂: instance() = instance() }
```

**Rust 1.90实现**：

```rust
use std::sync::OnceLock;

pub struct Config {
    pub api_key: String,
    pub timeout: u64,
}

static CONFIG: OnceLock<Config> = OnceLock::new();

impl Config {
    /// 获取全局配置实例
    pub fn global() -> &'static Config {
        CONFIG.get_or_init(|| Config {
            api_key: std::env::var("API_KEY").unwrap_or_default(),
            timeout: 30,
        })
    }
}

// 使用示例
fn main() {
    let config = Config::global();
    println!("API Key: {}", config.api_key);
}
```

**形式化性质**：

- **唯一性**：`∀x, y: global() = global() ⟹ addr(x) = addr(y)`
- **线程安全**：`OnceLock::get_or_init` 保证原子初始化
- **惰性求值**：首次访问时才初始化

**适用场景**：

- 全局配置管理
- 日志记录器
- 资源池管理

---

#### 1.2 工厂模式（Factory）

**理论定义**：定义创建对象的接口，让子类决定实例化哪个类。

**数学表示**：

```text
Factory<T> = { create(config: Config) → T | T implements Product }
```

**Rust实现**：

```rust
pub trait Database {
    fn connect(&self, url: &str) -> Result<Connection, Error>;
    fn name(&self) -> &str;
}

pub struct PostgresDb;
pub struct MySqlDb;

impl Database for PostgresDb {
    fn connect(&self, url: &str) -> Result<Connection, Error> {
        println!("Connecting to Postgres: {}", url);
        Ok(Connection::Postgres)
    }

    fn name(&self) -> &str { "PostgreSQL" }
}

impl Database for MySqlDb {
    fn connect(&self, url: &str) -> Result<Connection, Error> {
        println!("Connecting to MySQL: {}", url);
        Ok(Connection::MySql)
    }

    fn name(&self) -> &str { "MySQL" }
}

pub struct DatabaseFactory;

impl DatabaseFactory {
    pub fn create(db_type: &str) -> Box<dyn Database> {
        match db_type {
            "postgres" => Box::new(PostgresDb),
            "mysql" => Box::new(MySqlDb),
            _ => panic!("Unknown database type"),
        }
    }
}
```

**类型级工厂**（零成本抽象）：

```rust
pub trait DatabaseFactory {
    type Db: Database;
    fn create() -> Self::Db;
}

pub struct PostgresFactory;

impl DatabaseFactory for PostgresFactory {
    type Db = PostgresDb;

    fn create() -> Self::Db {
        PostgresDb
    }
}

// 编译时多态，零运行时开销
fn use_database<F: DatabaseFactory>() {
    let db = F::create();
    db.connect("localhost:5432").unwrap();
}
```

---

#### 1.3 建造者模式（Builder）

**理论定义**：将复杂对象的构建与表示分离。

**数学表示**：

```text
Builder<T> = {
    step₁: Self → Self,
    step₂: Self → Self,
    ...
    build: Self → T
}
```

**Rust惯用法**（类型状态Builder）：

```rust
use std::marker::PhantomData;

// 状态标记
pub struct Unset;
pub struct Set;

pub struct HttpRequestBuilder<UrlState, MethodState> {
    url: Option<String>,
    method: Option<String>,
    headers: Vec<(String, String)>,
    _url_state: PhantomData<UrlState>,
    _method_state: PhantomData<MethodState>,
}

impl HttpRequestBuilder<Unset, Unset> {
    pub fn new() -> Self {
        HttpRequestBuilder {
            url: None,
            method: None,
            headers: Vec::new(),
            _url_state: PhantomData,
            _method_state: PhantomData,
        }
    }
}

impl<M> HttpRequestBuilder<Unset, M> {
    pub fn url(self, url: String) -> HttpRequestBuilder<Set, M> {
        HttpRequestBuilder {
            url: Some(url),
            method: self.method,
            headers: self.headers,
            _url_state: PhantomData,
            _method_state: PhantomData,
        }
    }
}

impl<U> HttpRequestBuilder<U, Unset> {
    pub fn method(self, method: String) -> HttpRequestBuilder<U, Set> {
        HttpRequestBuilder {
            url: self.url,
            method: Some(method),
            headers: self.headers,
            _url_state: PhantomData,
            _method_state: PhantomData,
        }
    }
}

// 只有URL和Method都设置后才能build
impl HttpRequestBuilder<Set, Set> {
    pub fn build(self) -> HttpRequest {
        HttpRequest {
            url: self.url.unwrap(),
            method: self.method.unwrap(),
            headers: self.headers,
        }
    }
}

// 使用示例
fn main() {
    let request = HttpRequestBuilder::new()
        .url("https://api.example.com".to_string())
        .method("GET".to_string())
        .build();

    // 编译错误：缺少url
    // let invalid = HttpRequestBuilder::new().method("GET".to_string()).build();
}
```

**形式化保证**：

- 类型系统保证必填字段
- 编译时检查，零运行时开销
- 防止构造不完整对象

---

### 2. 结构型模式（Structural Patterns）

#### 2.1 适配器模式（Adapter）

**理论定义**：将一个接口转换为另一个接口。

**Rust实现**：

```rust
// 旧接口
pub trait LegacyLogger {
    fn log_message(&self, msg: &str);
}

// 新接口
pub trait ModernLogger {
    fn log(&self, level: LogLevel, msg: &str);
}

pub enum LogLevel {
    Info,
    Warning,
    Error,
}

// 适配器
pub struct LoggerAdapter<L: LegacyLogger> {
    legacy: L,
}

impl<L: LegacyLogger> LoggerAdapter<L> {
    pub fn new(legacy: L) -> Self {
        LoggerAdapter { legacy }
    }
}

impl<L: LegacyLogger> ModernLogger for LoggerAdapter<L> {
    fn log(&self, level: LogLevel, msg: &str) {
        let formatted = format!("[{:?}] {}", level, msg);
        self.legacy.log_message(&formatted);
    }
}
```

---

#### 2.2 装饰器模式（Decorator）

**理论定义**：动态地给对象添加职责。

**Rust实现（组合）**：

```rust
pub trait DataSource {
    fn read(&self) -> String;
    fn write(&mut self, data: &str);
}

pub struct FileDataSource {
    filename: String,
}

impl DataSource for FileDataSource {
    fn read(&self) -> String {
        format!("Reading from {}", self.filename)
    }

    fn write(&mut self, data: &str) {
        println!("Writing to {}: {}", self.filename, data);
    }
}

// 加密装饰器
pub struct EncryptionDecorator<D: DataSource> {
    wrapped: D,
}

impl<D: DataSource> EncryptionDecorator<D> {
    pub fn new(wrapped: D) -> Self {
        EncryptionDecorator { wrapped }
    }
}

impl<D: DataSource> DataSource for EncryptionDecorator<D> {
    fn read(&self) -> String {
        let data = self.wrapped.read();
        format!("Decrypted({})", data)
    }

    fn write(&mut self, data: &str) {
        let encrypted = format!("Encrypted({})", data);
        self.wrapped.write(&encrypted);
    }
}

// 压缩装饰器
pub struct CompressionDecorator<D: DataSource> {
    wrapped: D,
}

impl<D: DataSource> DataSource for CompressionDecorator<D> {
    fn read(&self) -> String {
        let data = self.wrapped.read();
        format!("Decompressed({})", data)
    }

    fn write(&mut self, data: &str) {
        let compressed = format!("Compressed({})", data);
        self.wrapped.write(&compressed);
    }
}

// 使用示例：组合多个装饰器
fn main() {
    let file = FileDataSource { filename: "data.txt".to_string() };
    let encrypted = EncryptionDecorator::new(file);
    let compressed = CompressionDecorator::new(encrypted);

    println!("{}", compressed.read());
    // 输出：Decompressed(Decrypted(Reading from data.txt))
}
```

---

### 3. 行为型模式（Behavioral Patterns）

#### 3.1 观察者模式（Observer）

**完整实现（包含GATs版本）**：

参见 `src/behavioral/observer/define.rs`，包含：

- 传统克隆版本
- GATs借用视图版本（零拷贝）

#### 3.2 策略模式（Strategy）

**理论定义**：定义算法族，使它们可以互换。

**Rust实现（trait对象）**：

```rust
pub trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

pub struct QuickSort;
impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) {
        data.sort_unstable();
        println!("QuickSort applied");
    }
}

pub struct BubbleSort;
impl SortStrategy for BubbleSort {
    fn sort(&self, data: &mut [i32]) {
        let len = data.len();
        for i in 0..len {
            for j in 0..len - i - 1 {
                if data[j] > data[j + 1] {
                    data.swap(j, j + 1);
                }
            }
        }
        println!("BubbleSort applied");
    }
}

pub struct Sorter {
    strategy: Box<dyn SortStrategy>,
}

impl Sorter {
    pub fn new(strategy: Box<dyn SortStrategy>) -> Self {
        Sorter { strategy }
    }

    pub fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}
```

**零成本策略（泛型）**：

```rust
pub struct GenericSorter<S: SortStrategy> {
    strategy: S,
}

impl<S: SortStrategy> GenericSorter<S> {
    pub fn new(strategy: S) -> Self {
        GenericSorter { strategy }
    }

    pub fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}

// 编译时单态化，零运行时开销
fn main() {
    let sorter = GenericSorter::new(QuickSort);
    let mut data = vec![5, 2, 8, 1, 9];
    sorter.sort(&mut data);
}
```

---

## 第二部分：并发与异步模式

### 1. 异步模式全景

#### 1.1 执行模型分类

| 模型 | 特征 | 适用场景 | 示例 |
|------|------|---------|------|
| **同步阻塞** | 线程阻塞等待 | CPU密集 | `std::thread` |
| **异步非阻塞** | 协作式调度 | IO密集 | `async/await` |
| **并行** | 多核并发 | 数据并行 | `rayon` |
| **Actor** | 消息传递 | 分布式 | 自定义Actor系统 |
| **Reactor** | 事件驱动 | 高并发IO | Tokio reactor |

#### 1.2 异步原语对比

详见：

- `docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md` - 异步与同步等价关系
- `docs/ACTOR_REACTOR_PATTERNS.md` - Actor与Reactor模式
- `docs/CSP_VS_ASYNC_ANALYSIS.md` - CSP语义模型对比

### 2. 异步递归

详见：`docs/ASYNC_RECURSION_ANALYSIS.md`

**核心要点**：

- 异步递归需要 `Box::pin` 或 `async-recursion` crate
- 尾递归可优化为迭代
- 性能：异步递归比同步慢10-50倍（Box开销）

**示例**：

```rust
use std::future::Future;
use std::pin::Pin;

fn factorial_async(n: u64) -> Pin<Box<dyn Future<Output = u64> + Send>> {
    Box::pin(async move {
        if n == 0 {
            1
        } else {
            n * factorial_async(n - 1).await
        }
    })
}
```

---

## 第三部分：形式化理论

### 1. 类型系统与证明

#### 1.1 Curry-Howard同构

**类型 ≅ 命题**：

- `T` → 命题"存在类型T的值"
- `f: A → B` → 命题"若A成立，则B成立"
- `()` → 真命题（总是成立）
- `!` → 假命题（永不成立）

**程序 ≅ 证明**：

- 构造类型T的值 → 证明命题T
- 类型检查 → 证明验证

**示例**：

```rust
// 命题：若A且B，则A
fn and_elim_left<A, B>(pair: (A, B)) -> A {
    pair.0
}

// 命题：A → (B → A)
fn const_fn<A: Clone, B>(a: A) -> impl Fn(B) -> A {
    move |_| a.clone()
}
```

#### 1.2 线性类型与资源管理

Rust的所有权系统实现了线性类型：

```rust
// 资源必须被精确使用一次
fn consume<T>(t: T) {
    // T 被move，之后不可再用
}

let x = String::from("hello");
consume(x);
// x.len(); // 编译错误：x已被move
```

**形式化性质**：

```text
线性类型规则：Γ, x: T ⊢ e: U
               ──────────────────
               Γ ⊢ λx.e: T → U

其中x在e中出现恰好一次
```

### 2. 不变量与Hoare逻辑

**Hoare三元组**：`{P} C {Q}`

- P：前置条件
- C：程序
- Q：后置条件

**示例**：

```rust
/// 不变量：self.count <= self.capacity
pub struct BoundedCounter {
    count: usize,
    capacity: usize,
}

impl BoundedCounter {
    /// 前置条件：capacity > 0
    /// 后置条件：self.count == 0 && self.capacity == capacity
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);
        BoundedCounter { count: 0, capacity }
    }

    /// 前置条件：self.count < self.capacity
    /// 后置条件：self.count == old(self.count) + 1
    pub fn increment(&mut self) -> Result<(), &'static str> {
        if self.count < self.capacity {
            self.count += 1;
            Ok(())
        } else {
            Err("Counter at capacity")
        }
    }
}
```

---

## 第四部分：实践指南

### 1. 设计模式选择决策树

```text
需要创建对象？
├─ 是
│  ├─ 全局唯一实例？ → 单例模式
│  ├─ 创建逻辑复杂？
│  │  ├─ 参数多？ → 建造者模式
│  │  └─ 根据类型选择？ → 工厂模式
│  └─ 复制现有对象？ → 原型模式
└─ 否
   ├─ 需要组合功能？
   │  ├─ 动态添加？ → 装饰器模式
   │  └─ 统一接口？ → 适配器模式
   └─ 需要定义行为？
      ├─ 算法可替换？ → 策略模式
      ├─ 状态转换？ → 状态模式
      └─ 对象间通信？ → 观察者模式
```

### 2. 并发模式选择

```text
需要并发？
├─ IO密集？
│  ├─ 高并发连接？ → 异步（async/await + Tokio）
│  └─ 简单任务？ → 线程池
├─ CPU密集？
│  ├─ 数据并行？ → Rayon（并行迭代器）
│  └─ 任务并行？ → std::thread 或 Tokio spawn_blocking
└─ 复杂状态管理？
   ├─ 分布式？ → Actor模式
   └─ 单机？ → Channel + Task
```

### 3. 性能优化指南

#### 3.1 零成本抽象原则

**优先级**：

1. **编译时多态**（泛型）> 运行时多态（trait对象）
2. **栈分配** > 堆分配
3. **所有权转移** > 借用 > 克隆

**示例**：

```rust
// 好：编译时多态，零开销
fn process<T: Iterator<Item = i32>>(iter: T) -> i32 {
    iter.sum()
}

// 避免：运行时多态，有vtable开销
fn process_dyn(iter: &mut dyn Iterator<Item = i32>) -> i32 {
    iter.sum()
}
```

#### 3.2 内存布局优化

```rust
// 不好：每个字段单独分配
struct BadCache {
    data: Vec<Box<Entry>>,
}

// 好：连续内存布局
struct GoodCache {
    data: Vec<Entry>,
}
```

---

## 第五部分：高级主题

### 1. 会话类型（Session Types）

会话类型确保通信协议在编译时正确：

```rust
use std::marker::PhantomData;

// 协议状态
pub struct Init;
pub struct Connected;
pub struct Authenticated;

pub struct Session<S> {
    _state: PhantomData<S>,
}

impl Session<Init> {
    pub fn new() -> Self {
        Session { _state: PhantomData }
    }

    pub fn connect(self) -> Session<Connected> {
        println!("Connecting...");
        Session { _state: PhantomData }
    }
}

impl Session<Connected> {
    pub fn authenticate(self, credentials: &str) -> Session<Authenticated> {
        println!("Authenticating with: {}", credentials);
        Session { _state: PhantomData }
    }
}

impl Session<Authenticated> {
    pub fn send_data(&self, data: &str) {
        println!("Sending: {}", data);
    }
}

// 使用示例
fn main() {
    let session = Session::<Init>::new()
        .connect()
        .authenticate("password");

    session.send_data("Hello, World!");

    // 编译错误：未认证不能发送数据
    // Session::<Init>::new().connect().send_data("fail");
}
```

### 2. 效应系统（Effect Systems）

追踪副作用：

```rust
pub trait Effect {}

pub struct Pure;
pub struct IO;
pub struct Async;

impl Effect for Pure {}
impl Effect for IO {}
impl Effect for Async {}

pub struct Computation<E: Effect, T> {
    _effect: PhantomData<E>,
    value: T,
}

impl<T> Computation<Pure, T> {
    pub fn pure(value: T) -> Self {
        Computation { _effect: PhantomData, value }
    }
}

impl<T> Computation<IO, T> {
    pub fn from_io(f: impl FnOnce() -> T) -> Self {
        Computation { _effect: PhantomData, value: f() }
    }
}

// 纯计算可以提升到任何效应
impl<E: Effect, T: Clone> Computation<Pure, T> {
    pub fn lift<E2: Effect>(self) -> Computation<E2, T> {
        Computation { _effect: PhantomData, value: self.value }
    }
}
```

---

## 附录A：快速参考

### 模式速查表

| 模式 | 意图 | Rust实现关键 | 复杂度 |
|------|------|------------|--------|
| 单例 | 全局唯一实例 | `OnceLock` | ⭐ |
| 工厂 | 对象创建抽象 | Trait + 泛型 | ⭐⭐ |
| 建造者 | 复杂对象构建 | 类型状态 | ⭐⭐⭐ |
| 适配器 | 接口转换 | Trait实现 | ⭐⭐ |
| 装饰器 | 动态添加功能 | 组合 | ⭐⭐ |
| 观察者 | 事件通知 | Callback/Channel | ⭐⭐⭐ |
| 策略 | 算法可替换 | Trait对象/泛型 | ⭐⭐ |
| Actor | 消息传递并发 | Channel + Task | ⭐⭐⭐⭐ |

### 常用命令

```bash
# 运行示例
cargo run --example pattern_name

# 运行测试
cargo test --all-features

# 运行基准测试
cargo bench

# 生成文档
cargo doc --no-deps --open

# 检查形式化验证示例
cargo test --test formal_verification_examples
```

---

## 参考文献

1. **经典书籍**
   - Gang of Four, "Design Patterns" (1994)
   - Benjamin C. Pierce, "Types and Programming Languages" (2002)
   - Simon Marlow, "Parallel and Concurrent Programming in Haskell" (2013)

2. **Rust特定**
   - Rust Design Patterns Book: <https://rust-unofficial.github.io/patterns/>
   - Rust Async Book: <https://rust-lang.github.io/async-book/>
   - Rust Nomicon: <https://doc.rust-lang.org/nomicon/>

3. **形式化方法**
   - C.A.R. Hoare, "An Axiomatic Basis for Computer Programming" (1969)
   - Peter O'Hearn, "Separation Logic" (2019)
   - RustBelt Project: <https://plv.mpi-sws.org/rustbelt/>

---

**贡献者**：Rust设计模式社区
**许可证**：MIT/Apache-2.0
**仓库**：<https://github.com/your-org/rust-design-patterns>

---

*本指南持续更新中。欢迎提出问题和改进建议！*
