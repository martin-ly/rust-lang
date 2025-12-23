# C09 设计模式: 术语表 (Glossary)

> **文档定位**: 设计模式核心术语快速参考，涵盖模式、并发、形式化等关键概念
> **使用方式**: 通过术语索引快速查找定义，理解设计模式核心概念
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

## 📊 目录

- [C09 设计模式: 术语表 (Glossary)](#c09-设计模式-术语表-glossary)
  - [📊 目录](#-目录)
  - [📋 术语索引](#-术语索引)
  - [设计模式基础](#设计模式基础)
    - [设计模式 (Design Pattern)](#设计模式-design-pattern)
    - [GoF (Gang of Four)](#gof-gang-of-four)
    - [单例模式 (Singleton)](#单例模式-singleton)
    - [观察者模式 (Observer)](#观察者模式-observer)
    - [策略模式 (Strategy)](#策略模式-strategy)
    - [建造者模式 (Builder)](#建造者模式-builder)
    - [类型状态模式 (Typestate Pattern)](#类型状态模式-typestate-pattern)
  - [并发与异步](#并发与异步)
    - [Actor 模式](#actor-模式)
    - [Reactor 模式](#reactor-模式)
    - [CSP (Communicating Sequential Processes)](#csp-communicating-sequential-processes)
    - [Future](#future)
    - [async/await](#asyncawait)
  - [Rust 特性](#rust-特性)
    - [Trait 对象](#trait-对象)
    - [零成本抽象 (Zero-Cost Abstraction)](#零成本抽象-zero-cost-abstraction)
    - [GATs (Generic Associated Types)](#gats-generic-associated-types)
    - [RPITIT (Return Position Impl Trait in Trait)](#rpitit-return-position-impl-trait-in-trait)
    - [OnceLock](#oncelock)
  - [形式化理论](#形式化理论)
    - [CPS 变换](#cps-变换)
    - [Monad](#monad)
    - [状态机 (State Machine)](#状态机-state-machine)
    - [语义等价 (Semantic Equivalence)](#语义等价-semantic-equivalence)
    - [Pin](#pin)
  - [📚 延伸阅读](#-延伸阅读)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+ (Edition 2024)
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[A](#actor-模式) | [C](#cps-变换) | [D](#设计模式-design-pattern) | [F](#future) | [G](#gats-generic-associated-types) | [M](#monad) | [R](#reactor-模式) | [T](#trait-对象) | [Z](#零成本抽象-zero-cost-abstraction)

**快速跳转**:

- [设计模式基础](#设计模式基础)
- [并发与异步](#并发与异步)
- [Rust 特性](#rust-特性)
- [形式化理论](#形式化理论)

---

## 设计模式基础

### 设计模式 (Design Pattern)

**定义**: 在软件设计中反复出现的问题的通用解决方案，是一套被反复使用、经过分类的代码设计经验总结。

**分类**:

- **创建型**: 对象创建机制
- **结构型**: 对象组合方式
- **行为型**: 对象间通信方式

**Rust 特点**: 需要考虑所有权、借用、生命周期

**相关**: [00_MASTER_INDEX.md](./00_MASTER_INDEX.md)

---

### GoF (Gang of Four)

**定义**: 《设计模式：可复用面向对象软件的基础》一书的四位作者，书中总结了 23 种经典设计模式。

**23种模式**:

- 创建型 (5): 单例、工厂方法、抽象工厂、建造者、原型
- 结构型 (7): 适配器、桥接、组合、装饰器、外观、享元、代理
- 行为型 (11): 责任链、命令、解释器、迭代器、中介者、备忘录、观察者、状态、策略、模板方法、访问者

**相关**: [COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md)

---

### 单例模式 (Singleton)

**定义**: 确保一个类只有一个实例，并提供全局访问点。

**Rust 实现**: `OnceLock`, `lazy_static`, `OnceCell`

**示例**:

```rust
use std::sync::OnceLock;

static INSTANCE: OnceLock<Config> = OnceLock::new();

pub fn get_instance() -> &'static Config {
    INSTANCE.get_or_init(|| Config::new())
}
```

**相关**: [src/creational/singleton/](../src/creational/singleton/)

---

### 观察者模式 (Observer)

**定义**: 定义对象间一对多的依赖关系，当一个对象状态改变时，所有依赖它的对象都得到通知。

**Rust 实现**: Channel、GATs 借用视图

**示例**:

```rust
use std::sync::mpsc::Sender;

struct Subject {
    observers: Vec<Sender<Event>>,
}

impl Subject {
    fn notify(&self, event: Event) {
        for observer in &self.observers {
            let _ = observer.send(event.clone());
        }
    }
}
```

**相关**: [src/behavioral/observer/](../src/behavioral/observer/), [examples/gats_observer_demo.rs](../examples/gats_observer_demo.rs)

---

### 策略模式 (Strategy)

**定义**: 定义一系列算法，把它们封装起来，并使它们可以互换。

**Rust 实现**: 泛型（编译时多态）或 trait 对象（运行时多态）

**示例**:

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

// 编译时多态
fn sort_data<S: SortStrategy>(strategy: &S, data: &mut [i32]) {
    strategy.sort(data);
}

// 运行时多态
fn sort_data_dynamic(strategy: &dyn SortStrategy, data: &mut [i32]) {
    strategy.sort(data);
}
```

**相关**: [src/behavioral/strategy/](../src/behavioral/strategy/)

---

### 建造者模式 (Builder)

**定义**: 将复杂对象的构建过程与表示分离，使得同样的构建过程可以创建不同的表示。

**Rust 实现**: 类型状态模式（Typestate Pattern）

**示例**:

```rust
struct PersonBuilder {
    name: Option<String>,
    age: Option<u32>,
}

impl PersonBuilder {
    fn new() -> Self {
        Self { name: None, age: None }
    }

    fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    fn age(mut self, age: u32) -> Self {
        self.age = Some(age);
        self
    }

    fn build(self) -> Result<Person, &'static str> {
        Ok(Person {
            name: self.name.ok_or("name is required")?,
            age: self.age.ok_or("age is required")?,
        })
    }
}
```

**相关**: [src/creational/builder/](../src/creational/builder/)

---

### 类型状态模式 (Typestate Pattern)

**定义**: 使用 Rust 的类型系统在编译时保证状态转换的正确性。

**特点**:

- 编译时验证
- 零运行时开销
- 防止非法状态转换

**示例**:

```rust
struct Document<S> {
    content: String,
    _state: std::marker::PhantomData<S>,
}

struct Draft;
struct Published;

impl Document<Draft> {
    fn new(content: String) -> Self {
        Document {
            content,
            _state: std::marker::PhantomData,
        }
    }

    fn publish(self) -> Document<Published> {
        Document {
            content: self.content,
            _state: std::marker::PhantomData,
        }
    }
}

impl Document<Published> {
    // 只有已发布的文档才能归档
    fn archive(self) {
        // ...
    }
}
```

**相关**: [src/behavioral/state/](../src/behavioral/state/)

---

## 并发与异步

### Actor 模式

**定义**: 并发计算模型，每个 Actor 是独立的计算单元，通过消息传递通信。

**特点**:

- 消息传递，无共享状态
- 每个 Actor 有独立的邮箱
- 异步消息处理

**Rust 实现**:

```rust
use tokio::sync::mpsc;

struct Actor {
    receiver: mpsc::Receiver<Message>,
}

impl Actor {
    async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle(msg).await;
        }
    }

    async fn handle(&mut self, msg: Message) {
        // 处理消息
    }
}
```

**相关**: [docs/ACTOR_REACTOR_PATTERNS.md](./ACTOR_REACTOR_PATTERNS.md)

---

### Reactor 模式

**定义**: 事件驱动的并发模型，通过事件循环和回调处理多个事件源。

**特点**:

- 事件多路复用（epoll/kqueue）
- 单线程高并发
- 回调驱动

**Rust 中**: Tokio 运行时基于 Reactor 模式

**相关**: [docs/ACTOR_REACTOR_PATTERNS.md](./ACTOR_REACTOR_PATTERNS.md)

---

### CSP (Communicating Sequential Processes)

**定义**: 并发编程模型，通过通道（Channel）进行通信。

**特点**:

- 进程通过通道通信
- 不共享内存
- Golang 的并发模型

**Rust 中**:

```rust
use std::sync::mpsc::channel;

let (tx, rx) = channel();

std::thread::spawn(move || {
    tx.send(42).unwrap();
});

let value = rx.recv().unwrap();
```

**相关**: [docs/CSP_VS_ASYNC_ANALYSIS.md](./CSP_VS_ASYNC_ANALYSIS.md)

---

### Future

**定义**: 表示一个异步计算，可能尚未完成。

**Rust 中**: `Future` trait

```rust
pub trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**状态机**: async/await 编译为状态机

**相关**: [src/concurrency/asynchronous/](../src/concurrency/asynchronous/)

---

### async/await

**定义**: Rust 的异步编程语法糖，使异步代码看起来像同步代码。

**工作原理**: 编译器将 async 函数转换为状态机

**示例**:

```rust
async fn fetch_data() -> Result<Data> {
    let response = http_get("url").await?;
    let data = response.json().await?;
    Ok(data)
}
```

**相关**: [docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)

---

## Rust 特性

### Trait 对象

**定义**: 运行时多态机制，通过 `dyn Trait` 实现动态分派。

**特点**:

- 运行时开销（虚函数表）
- 类型擦除
- 灵活但有性能代价

**示例**:

```rust
trait Handler {
    fn handle(&self, data: &Data);
}

fn process(handler: &dyn Handler) {
    handler.handle(&data); // 动态分派
}
```

**相关**: [FAQ.md](./FAQ.md#q13-设计模式会影响性能吗)

---

### 零成本抽象 (Zero-Cost Abstraction)

**定义**: 抽象不会带来运行时开销，编译后与手写的底层代码性能相同。

**Rust 中实现**:

- 泛型单态化
- 内联优化
- 编译时计算

**示例**:

```rust
// 零成本抽象：泛型
fn process<T: Handler>(handler: &T) {
    handler.handle(); // 编译时确定，可内联
}

// 有成本：trait 对象
fn process_dyn(handler: &dyn Handler) {
    handler.handle(); // 运行时分派
}
```

**相关**: [benches/pattern_benchmarks.rs](../benches/pattern_benchmarks.rs)

---

### GATs (Generic Associated Types)

**定义**: 泛型关联类型，允许关联类型带有泛型参数。

**应用**: 观察者模式的借用视图

**示例**:

```rust
trait Observer {
    type View<'a>: 'a where Self: 'a;
    fn update(&self, data: Self::View<'_>);
}

struct StringObserver;

impl Observer for StringObserver {
    type View<'a> = &'a str;

    fn update(&self, data: &str) {
        println!("Received: {}", data);
    }
}
```

**相关**: [src/behavioral/observer/](../src/behavioral/observer/), [examples/gats_observer_demo.rs](../examples/gats_observer_demo.rs)

---

### RPITIT (Return Position Impl Trait in Trait)

**定义**: Rust 1.90+ 特性，允许在 trait 方法中返回 `impl Trait`。

**优点**:

- 避免关联类型的复杂性
- 更好的类型推导
- 更简洁的 API

**示例**:

```rust
trait TextSource {
    fn words(&self) -> impl Iterator<Item = &str>;
}

struct Document {
    text: String,
}

impl TextSource for Document {
    fn words(&self) -> impl Iterator<Item = &str> {
        self.text.split_whitespace()
    }
}
```

**相关**: [src/rust_190_features.rs](../src/rust_190_features.rs)

---

### OnceLock

**定义**: Rust 1.90+ 标准库提供的线程安全的单次初始化类型。

**用途**: 全局单例、延迟初始化

**示例**:

```rust
use std::sync::OnceLock;

static CONFIG: OnceLock<Config> = OnceLock::new();

fn get_config() -> &'static Config {
    CONFIG.get_or_init(|| {
        Config::from_file("config.toml")
    })
}
```

**vs lazy_static**: 标准库支持，无需外部依赖

**相关**: [src/creational/singleton/](../src/creational/singleton/)

---

## 形式化理论

### CPS 变换

**定义**: Continuation-Passing Style，将控制流显式化为续延（continuation）。

**应用**: 理解 async/await 的语义

**示例**:

```rust
// 直接风格
fn compute() -> i32 {
    let x = step1();
    let y = step2(x);
    step3(y)
}

// CPS 风格
fn compute_cps<F>(cont: F)
where
    F: FnOnce(i32),
{
    step1_cps(|x| {
        step2_cps(x, |y| {
            step3_cps(y, cont)
        })
    })
}
```

**相关**: [docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)

---

### Monad

**定义**: 函数式编程中的抽象，封装计算效果（如 `Option`、`Result`、`Future`）。

**Rust 中的 Monad**:

- `Option<T>`: 可能的值
- `Result<T, E>`: 可能失败的计算
- `Future<Output = T>`: 异步计算

**Monad 法则**:

1. 左单位元: `return a >>= f ≡ f a`
2. 右单位元: `m >>= return ≡ m`
3. 结合律: `(m >>= f) >>= g ≡ m >>= (\x -> f x >>= g)`

**Rust 中**:

```rust
// Option Monad
fn chain<T, U>(opt: Option<T>, f: impl FnOnce(T) -> Option<U>) -> Option<U> {
    opt.and_then(f)
}
```

**相关**: [docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)

---

### 状态机 (State Machine)

**定义**: 系统在不同状态之间转换的模型。

**Rust 中**: async/await 被编译为状态机

**示例**:

```rust
// async fn 编译前
async fn example() {
    step1().await;
    step2().await;
}

// 编译后（简化）
enum ExampleStateMachine {
    Start,
    AwaitingStep1(Step1Future),
    AwaitingStep2(Step2Future),
    Done,
}

impl Future for ExampleStateMachine {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<()> {
        // 状态转换逻辑
    }
}
```

**相关**: [docs/ASYNC_RECURSION_ANALYSIS.md](./ASYNC_RECURSION_ANALYSIS.md)

---

### 语义等价 (Semantic Equivalence)

**定义**: 两个程序在所有可观察行为上相同。

**应用**: 证明异步和同步代码的等价性

**示例**:

```rust
// 同步版本
fn sync_version() -> i32 {
    let x = compute1();
    let y = compute2(x);
    x + y
}

// 异步版本
async fn async_version() -> i32 {
    let x = compute1_async().await;
    let y = compute2_async(x).await;
    x + y
}
```

**证明方法**: CPS 变换、Monad 同态

**相关**: [docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)

---

### Pin

**定义**: 保证被指向的值在内存中不会移动。

**用途**: 自引用结构、async 状态机

**示例**:

```rust
use std::pin::Pin;

struct SelfReferential {
    data: String,
    pointer: *const String,
}

fn use_pinned(pinned: Pin<&mut SelfReferential>) {
    // pinned 保证不会移动
}
```

**相关**: [docs/ASYNC_RECURSION_ANALYSIS.md](./ASYNC_RECURSION_ANALYSIS.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](./README.md) - 项目概述
- [综合指南](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md) - 深度学习
- [形式化理论文档](./ASYNC_SYNC_EQUIVALENCE_THEORY.md) - 理论基础

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [源码实现](../src/)
