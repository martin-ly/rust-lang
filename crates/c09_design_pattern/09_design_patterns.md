# 设计模式

## 目录

- [设计模式](#设计模式)
  - [目录](#目录)
  - [0. 执行模型综述：同步 vs 异步](#0-执行模型综述同步-vs-异步)
  - [1. 创建型模式](#1-创建型模式)
    - [1.1 工厂模式的形式化](#11-工厂模式的形式化)
    - [1.2 工厂方法模式的形式化](#12-工厂方法模式的形式化)
    - [1.3 建造者模式的数学表示](#13-建造者模式的数学表示)
    - [1.4 原型模式的理论基础](#14-原型模式的理论基础)
    - [1.5 单例模式的理论基础](#15-单例模式的理论基础)
  - [2. 结构型模式](#2-结构型模式)
    - [2.1 适配器模式的形式化](#21-适配器模式的形式化)
    - [2.2 桥接模式的理论基础](#22-桥接模式的理论基础)
    - [2.3 组合模式的形式化](#23-组合模式的形式化)
    - [2.4 装饰器模式的理论基础](#24-装饰器模式的理论基础)
    - [2.5 外观模式的形式化](#25-外观模式的形式化)
    - [2.6 享元模式的理论基础](#26-享元模式的理论基础)
    - [2.7 代理模式的形式化](#27-代理模式的形式化)
  - [3. 行为型模式](#3-行为型模式)
    - [3.1 责任链模式的理论基础](#31-责任链模式的理论基础)
    - [3.2 命令模式的形式化](#32-命令模式的形式化)
    - [3.3 解释器模式的理论基础](#33-解释器模式的理论基础)
    - [3.4 迭代器模式的形式化](#34-迭代器模式的形式化)
    - [3.5 中介者模式的理论基础](#35-中介者模式的理论基础)
    - [3.6 备忘录模式的形式化](#36-备忘录模式的形式化)
    - [3.7 观察者模式的理论基础](#37-观察者模式的理论基础)
    - [3.8 状态模式的形式化](#38-状态模式的形式化)
    - [3.9 策略模式的理论基础](#39-策略模式的理论基础)
    - [3.10 模板方法模式的形式化](#310-模板方法模式的形式化)
    - [3.11 访问者模式的理论基础](#311-访问者模式的理论基础)
  - [4. 并发模式](#4-并发模式)
    - [4.1 主动对象模式](#41-主动对象模式)
    - [4.2 领导者-跟随者模式](#42-领导者-跟随者模式)
    - [4.3 生产者-消费者模式](#43-生产者-消费者模式)
  - [5. 总结](#5-总结)
  - [附录A：生态框架落地（Rust 1.90，Edition 2024）](#附录a生态框架落地rust-190edition-2024)

## 0. 执行模型综述：同步 vs 异步

**定义**：

- 同步 (Sync)：调用方在当前线程上阻塞直至完成。
- 异步 (Async)：调用立即返回，通过 `Future`、回调或事件循环在准备好时继续。
- 混合 (Hybrid)：对外暴露某一模型，内部通过边界适配器桥接另一个模型。

**判定准则**：

- 若主要交互对象是 CPU 计算且不需要等待 IO，则倾向同步。
- 若主要交互对象涉及网络/磁盘/计时器等 IO 等待，则倾向异步。
- 若模式需要既服务同步调用者又复用异步基础设施，选择混合。

**Rust 实践**：

```rust
use c09_design_pattern::{ExecutionModel, get_patterns_by_execution_model};

// 异步侧：Actor/Channel 等模式
let async_side = get_patterns_by_execution_model(ExecutionModel::Async);

// 同步侧：Singleton/Factory/Builder/并行迭代器 等
let sync_side = get_patterns_by_execution_model(ExecutionModel::Sync);

// 混合：Proxy/Decorator/Observer/Repository 等
let hybrid_side = get_patterns_by_execution_model(ExecutionModel::Hybrid);
```

**设计影响**：

- API 形态：`fn foo(&self) -> T` vs `async fn foo(&self) -> T`。
- 错误传播：同步 `Result<T, E>` vs 异步 `Result<T, E>` 包裹在 `Future` 中。
- 资源管理：同步临界区用 `Mutex`，异步需 `tokio::sync::Mutex` 或避免阻塞。

**对比表（概要）**：

| 维度 | 同步 (Sync) | 异步 (Async) | 混合 (Hybrid) |
|---|---|---|---|
| 典型场景 | CPU 计算、确定性步骤 | IO 密集、高并发连接 | 同步对外 + 异步内部或反向 |
| API 形态 | 阻塞函数 | `async fn`/`Future` | 组合/适配 |
| 复杂度 | 低 | 中-高 | 中-高 |
| 线程模型 | 多线程/无特定要求 | 事件循环 + 任务 | 双栈：同步/异步边界 |
| 典型模式 | Singleton/Factory/Builder | Actor/Channel/Event-driven | Proxy/Decorator/Observer/Repository |

> 选择建议：优先按“是否等待 IO”为一号判断，其次看是否需兼容现有同步接口，再考虑团队对异步生态（Tokio、异步锁、执行器）的掌握程度。

## 1. 创建型模式

### 1.1 工厂模式的形式化

**理论定义**：
工厂模式通过工厂类创建对象，将对象的创建与使用分离，提高系统的灵活性和可维护性。

**数学符号**：

```text
Factory<T> = { create() → T }
```

**Rust 伪代码**：

```rust
trait Product {
    fn name(&self) -> &str;
    fn operation(&self) -> String;
}

trait Factory {
    fn create(&self) -> Box<dyn Product>;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn name(&self) -> &str { "ProductA" }
    fn operation(&self) -> String { "Operation A".to_string() }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn name(&self) -> &str { "ProductB" }
    fn operation(&self) -> String { "Operation B".to_string() }
}

struct ConcreteFactoryA;
impl Factory for ConcreteFactoryA {
    fn create(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

struct ConcreteFactoryB;
impl Factory for ConcreteFactoryB {
    fn create(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}

// 使用示例
fn client_code(factory: &dyn Factory) {
    let product = factory.create();
    println!("Created: {}", product.name());
    println!("Operation: {}", product.operation());
}
```

**简要说明**：
工厂模式通过抽象工厂接口，支持产品族的灵活扩展，符合开闭原则。

### 1.2 工厂方法模式的形式化

**理论定义**：
工厂方法模式通过定义一个用于创建对象的接口，让子类决定实例化哪一个类。工厂方法使一个类的实例化延迟到其子类。

**数学符号**：
`Factory<T>` = { create() → T }

**Rust 伪代码**：

```rust
trait Product { fn name(&self) -> &str; }
trait Factory { fn create(&self) -> Box<dyn Product>; }
struct ConcreteProduct;
impl Product for ConcreteProduct { fn name(&self) -> &str { "A" } }
struct ConcreteFactory;
impl Factory for ConcreteFactory {
    fn create(&self) -> Box<dyn Product> { Box::new(ConcreteProduct) }
}
```

**简要说明**：
工厂方法模式通过抽象工厂接口，支持产品族的灵活扩展。

### 1.3 建造者模式的数学表示

**理论定义**：
建造者模式将一个复杂对象的构建与其表示分离，使同样的构建过程可以创建不同的表示。

**数学符号**：
`Builder<T>` = { step₁(), step₂(), ..., build() → T }

**Rust 伪代码**：

```rust
struct Product { part_a: String, part_b: String }
struct ProductBuilder { a: String, b: String }
impl ProductBuilder {
    fn new() -> Self { Self { a: String::new(), b: String::new() } }
    fn part_a(mut self, v: &str) -> Self { self.a = v.into(); self }
    fn part_b(mut self, v: &str) -> Self { self.b = v.into(); self }
    fn build(self) -> Product { Product { part_a: self.a, part_b: self.b } }
}
```

**简要说明**：
建造者模式适合构建步骤复杂且可变的对象。

### 1.4 原型模式的理论基础

**理论定义**：
原型模式通过复制现有对象来创建新对象，避免重复初始化。

**数学符号**：
`Prototype<T>` = { clone() → T }

**Rust 伪代码**：

```rust
trait Prototype: Clone {}
#[derive(Clone)]
struct ConcretePrototype { data: i32 }
impl Prototype for ConcretePrototype {}
let p1 = ConcretePrototype { data: 42 };
let p2 = p1.clone();
```

**简要说明**：
原型模式适合对象创建成本高或结构复杂的场景。

### 1.5 单例模式的理论基础

**理论定义**：
单例模式保证一个类只有一个实例，并提供全局访问点。

**数学符号**：
`Singleton<T>` = { instance() → &T }

**Rust 伪代码**：

```rust
use std::sync::OnceLock;
struct Singleton { data: i32 }
static INSTANCE: OnceLock<Singleton> = OnceLock::new();
impl Singleton {
    fn instance() -> &'static Singleton {
        INSTANCE.get_or_init(|| Singleton { data: 0 })
    }
}
```

**简要说明**：
单例模式常用于全局配置、资源管理等场景。

## 2. 结构型模式

### 2.1 适配器模式的形式化

**理论定义**：
适配器模式将一个类的接口转换成客户希望的另一个接口，使不兼容的接口可以协同工作。

**数学符号**：
Adapter = { adapt(OldInterface) → NewInterface }

**Rust 伪代码**：

```rust
// 旧接口
trait OldInterface {
    fn old_method(&self) -> String;
}

// 新接口
trait NewInterface {
    fn new_method(&self) -> String;
}

// 旧实现
struct OldImplementation;
impl OldInterface for OldImplementation {
    fn old_method(&self) -> String { "old".to_string() }
}

// 适配器
struct Adapter {
    old: Box<dyn OldInterface>
}

impl Adapter {
    fn new(old: Box<dyn OldInterface>) -> Self {
        Self { old }
    }
}

impl NewInterface for Adapter {
    fn new_method(&self) -> String {
        // 将旧接口适配为新接口
        format!("adapted: {}", self.old.old_method())
    }
}
```

**简要说明**：
适配器模式解决了接口不兼容的问题，提高了系统的可扩展性。

### 2.2 桥接模式的理论基础

**理论定义**：
桥接模式将抽象部分与实现部分分离，使它们都可以独立地变化。

**数学符号**：
Bridge = { Abstraction × Implementation → ConcreteAbstraction }

**Rust 伪代码**：

```rust
// 实现接口
trait Implementation {
    fn operation_impl(&self) -> String;
}

// 抽象接口
trait Abstraction {
    fn operation(&self) -> String;
}

// 具体实现
struct ConcreteImplementationA;
impl Implementation for ConcreteImplementationA {
    fn operation_impl(&self) -> String { "Implementation A".to_string() }
}

struct ConcreteImplementationB;
impl Implementation for ConcreteImplementationB {
    fn operation_impl(&self) -> String { "Implementation B".to_string() }
}

// 具体抽象
struct ConcreteAbstraction {
    implementation: Box<dyn Implementation>
}

impl ConcreteAbstraction {
    fn new(implementation: Box<dyn Implementation>) -> Self {
        Self { implementation }
    }
}

impl Abstraction for ConcreteAbstraction {
    fn operation(&self) -> String {
        format!("Abstraction: {}", self.implementation.operation_impl())
    }
}
```

**简要说明**：
桥接模式通过组合关系替代继承关系，提高了系统的灵活性。

### 2.3 组合模式的形式化

**理论定义**：
组合模式将对象组合成树形结构以表示"部分-整体"的层次结构，使得用户对单个对象和组合对象具有一致的访问性。

**数学符号**：

```text
Component = { Leaf } ∪ { Composite(children: Vec<Component>) }
```

**Rust 伪代码**：

```rust
trait Component {
    fn operation(&self) -> String;
}

struct Leaf {
    name: String
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf: {}", self.name)
    }
}

struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>
}

impl Composite {
    fn new(name: String) -> Self {
        Self { name, children: Vec::new() }
    }

    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }

    fn remove(&mut self, index: usize) {
        if index < self.children.len() {
            self.children.remove(index);
        }
    }
}

impl Component for Composite {
    fn operation(&self) -> String {
        let mut result = format!("Composite: {}", self.name);
        for child in &self.children {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
}
```

**简要说明**：
组合模式统一了叶子节点和容器节点的处理方式。

### 2.4 装饰器模式的理论基础

**理论定义**：
装饰器模式动态地给对象添加额外的职责，而不改变其接口。

**数学符号**：
Decorator = { Component } × { Decorator(component: Component) }

**Rust 伪代码**：

```rust
trait Component {
    fn operation(&self) -> String;
}

struct ConcreteComponent;
impl Component for ConcreteComponent {
    fn operation(&self) -> String { "ConcreteComponent".to_string() }
}

struct DecoratorA {
    component: Box<dyn Component>
}

impl DecoratorA {
    fn new(component: Box<dyn Component>) -> Self {
        Self { component }
    }
}

impl Component for DecoratorA {
    fn operation(&self) -> String {
        format!("DecoratorA({})", self.component.operation())
    }
}

struct DecoratorB {
    component: Box<dyn Component>
}

impl DecoratorB {
    fn new(component: Box<dyn Component>) -> Self {
        Self { component }
    }
}

impl Component for DecoratorB {
    fn operation(&self) -> String {
        format!("DecoratorB({})", self.component.operation())
    }
}
```

**简要说明**：
装饰器模式提供了比继承更灵活的扩展功能的方式。

### 2.5 外观模式的形式化

**理论定义**：
外观模式为子系统中的一组接口提供一个一致的界面，简化了子系统的使用。

**数学符号**：
Facade = { subsystem₁, subsystem₂, ..., subsystemₙ } → { simplified_interface() }

**Rust 伪代码**：

```rust
// 子系统
struct SubsystemA;
impl SubsystemA {
    fn operation_a(&self) -> String { "SubsystemA operation".to_string() }
}

struct SubsystemB;
impl SubsystemB {
    fn operation_b(&self) -> String { "SubsystemB operation".to_string() }
}

struct SubsystemC;
impl SubsystemC {
    fn operation_c(&self) -> String { "SubsystemC operation".to_string() }
}

// 外观
struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC
}

impl Facade {
    fn new() -> Self {
        Self {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC
        }
    }

    fn operation(&self) -> String {
        format!("Facade: {} + {} + {}",
            self.subsystem_a.operation_a(),
            self.subsystem_b.operation_b(),
            self.subsystem_c.operation_c())
    }
}
```

**简要说明**：
外观模式简化了复杂子系统的使用，降低了系统的耦合度。

### 2.6 享元模式的理论基础

**理论定义**：
享元模式通过共享技术有效地支持大量细粒度对象的复用。

**数学符号**：
Flyweight = { intrinsic_state } × { extrinsic_state }

**Rust 伪代码**：

```rust
use std::collections::HashMap;

// 享元接口
trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
}

// 具体享元
struct ConcreteFlyweight {
    intrinsic_state: String
}

impl ConcreteFlyweight {
    fn new(intrinsic_state: String) -> Self {
        Self { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!("Flyweight({}) with extrinsic: {}",
            self.intrinsic_state, extrinsic_state)
    }
}

// 享元工厂
struct FlyweightFactory {
    flyweights: HashMap<String, Box<dyn Flyweight>>
}

impl FlyweightFactory {
    fn new() -> Self {
        Self { flyweights: HashMap::new() }
    }

    fn get_flyweight(&mut self, key: &str) -> &dyn Flyweight {
        if !self.flyweights.contains_key(key) {
            self.flyweights.insert(
                key.to_string(),
                Box::new(ConcreteFlyweight::new(key.to_string()))
            );
        }
        self.flyweights.get(key).unwrap().as_ref()
    }
}
```

**简要说明**：
享元模式通过共享内部状态减少了内存使用，提高了系统性能。

### 2.7 代理模式的形式化

**理论定义**：
代理模式为其他对象提供一种代理以控制对这个对象的访问。

**数学符号**：
Proxy = { Subject } × { access_control() }

**Rust 伪代码**：

```rust
// 主题接口
trait Subject {
    fn request(&self) -> String;
}

// 真实主题
struct RealSubject;
impl Subject for RealSubject {
    fn request(&self) -> String { "RealSubject request".to_string() }
}

// 代理
struct Proxy {
    real_subject: Option<RealSubject>
}

impl Proxy {
    fn new() -> Self {
        Self { real_subject: None }
    }

    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(RealSubject);
        }
    }
}

impl Subject for Proxy {
    fn request(&self) -> String {
        // 这里需要可变引用，实际实现中可能需要内部可变性
        "Proxy: controlling access to RealSubject".to_string()
    }
}
```

**简要说明**：
代理模式提供了对对象的访问控制，常用于远程代理、虚拟代理等场景。

## 3. 行为型模式

### 3.1 责任链模式的理论基础

**理论定义**：
责任链模式将请求的发送者和接收者解耦，沿着链传递请求直到被处理。

**数学符号**：
Chain = { Handler₁ → Handler₂ → ... → Handlerₙ }

**Rust 伪代码**：

```rust
trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>);
    fn handle(&self, request: &str) -> Option<String>;
}

struct ConcreteHandlerA {
    next: Option<Box<dyn Handler>>
}

impl ConcreteHandlerA {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for ConcreteHandlerA {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }

    fn handle(&self, request: &str) -> Option<String> {
        if request.contains("A") {
            Some("HandlerA processed".to_string())
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}

struct ConcreteHandlerB {
    next: Option<Box<dyn Handler>>
}

impl ConcreteHandlerB {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for ConcreteHandlerB {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }

    fn handle(&self, request: &str) -> Option<String> {
        if request.contains("B") {
            Some("HandlerB processed".to_string())
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}
```

**简要说明**：
责任链模式实现了请求的自动传递和处理。

### 3.2 命令模式的形式化

**理论定义**：
命令模式将请求封装成对象，从而可以用不同的请求对客户进行参数化。

**数学符号**：
Command = { execute() } × { Receiver }

**Rust 伪代码**：

```rust
// 命令接口
trait Command {
    fn execute(&self);
}

// 接收者
struct Receiver;
impl Receiver {
    fn action(&self) { println!("Receiver action"); }
}

// 具体命令
struct ConcreteCommand {
    receiver: Receiver
}

impl ConcreteCommand {
    fn new(receiver: Receiver) -> Self {
        Self { receiver }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) {
        self.receiver.action();
    }
}

// 调用者
struct Invoker {
    command: Option<Box<dyn Command>>
}

impl Invoker {
    fn new() -> Self {
        Self { command: None }
    }

    fn set_command(&mut self, command: Box<dyn Command>) {
        self.command = Some(command);
    }

    fn execute_command(&self) {
        if let Some(ref command) = self.command {
            command.execute();
        }
    }
}
```

**简要说明**：
命令模式将请求封装成对象，支持请求的排队、记录日志、撤销等操作。

### 3.3 解释器模式的理论基础

**理论定义**：
解释器模式为语言创建解释器，定义语法表示和解释方法。

**数学符号**：
Interpreter = { Context } × { Expression } → { Result }

**Rust 伪代码**：

```rust
// 抽象表达式
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
}

// 上下文
struct Context {
    variables: std::collections::HashMap<String, i32>
}

impl Context {
    fn new() -> Self {
        Self { variables: std::collections::HashMap::new() }
    }

    fn set_variable(&mut self, name: &str, value: i32) {
        self.variables.insert(name.to_string(), value);
    }

    fn get_variable(&self, name: &str) -> i32 {
        *self.variables.get(name).unwrap_or(&0)
    }
}

// 终结表达式
struct VariableExpression {
    name: String
}

impl VariableExpression {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Expression for VariableExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get_variable(&self.name)
    }
}

// 非终结表达式
struct AddExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>
}

impl AddExpression {
    fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        Self { left, right }
    }
}

impl Expression for AddExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }
}
```

**简要说明**：
解释器模式适用于需要解释简单语言的场景。

### 3.4 迭代器模式的形式化

**理论定义**：
迭代器模式提供一种方法顺序访问聚合对象中的元素，而不暴露其内部表示。

**数学符号**：
Iterator = { has_next() → bool, next() → T }

**Rust 伪代码**：

```rust
// 迭代器接口
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// 聚合接口
trait Aggregate {
    type Iterator: Iterator;
    fn create_iterator(&self) -> Self::Iterator;
}

// 具体聚合
struct ConcreteAggregate {
    data: Vec<i32>
}

impl ConcreteAggregate {
    fn new(data: Vec<i32>) -> Self {
        Self { data }
    }
}

// 具体迭代器
struct ConcreteIterator {
    aggregate: ConcreteAggregate,
    index: usize
}

impl ConcreteIterator {
    fn new(aggregate: ConcreteAggregate) -> Self {
        Self { aggregate, index: 0 }
    }
}

impl Iterator for ConcreteIterator {
    type Item = i32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.aggregate.data.len() {
            let item = self.aggregate.data[self.index];
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl Aggregate for ConcreteAggregate {
    type Iterator = ConcreteIterator;

    fn create_iterator(&self) -> Self::Iterator {
        ConcreteIterator::new(ConcreteAggregate {
            data: self.data.clone()
        })
    }
}
```

**简要说明**：
迭代器模式封装了集合的遍历逻辑，提供了统一的访问接口。

### 3.5 中介者模式的理论基础

**理论定义**：
中介者模式用一个中介对象封装一系列对象交互，中介者使各对象不需要显式地相互引用。

**数学符号**：
Mediator = { Colleague₁, Colleague₂, ..., Colleagueₙ } → { coordinate() }

**Rust 伪代码**：

```rust
// 中介者接口
trait Mediator {
    fn notify(&self, sender: &str, event: &str);
}

// 同事接口
trait Colleague {
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>);
    fn send(&self, event: &str);
    fn receive(&self, event: &str);
}

// 具体中介者
struct ConcreteMediator {
    colleague_a: Option<Box<dyn Colleague>>,
    colleague_b: Option<Box<dyn Colleague>>
}

impl ConcreteMediator {
    fn new() -> Self {
        Self {
            colleague_a: None,
            colleague_b: None
        }
    }

    fn set_colleague_a(&mut self, colleague: Box<dyn Colleague>) {
        self.colleague_a = Some(colleague);
    }

    fn set_colleague_b(&mut self, colleague: Box<dyn Colleague>) {
        self.colleague_b = Some(colleague);
    }
}

impl Mediator for ConcreteMediator {
    fn notify(&self, sender: &str, event: &str) {
        match sender {
            "A" => {
                if let Some(ref b) = self.colleague_b {
                    b.receive(event);
                }
            },
            "B" => {
                if let Some(ref a) = self.colleague_a {
                    a.receive(event);
                }
            },
            _ => {}
        }
    }
}

// 具体同事
struct ConcreteColleagueA {
    mediator: Option<Box<dyn Mediator>>,
    name: String
}

impl ConcreteColleagueA {
    fn new(name: String) -> Self {
        Self { mediator: None, name }
    }
}

impl Colleague for ConcreteColleagueA {
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.mediator = Some(mediator);
    }

    fn send(&self, event: &str) {
        if let Some(ref mediator) = self.mediator {
            mediator.notify("A", event);
        }
    }

    fn receive(&self, event: &str) {
        println!("ColleagueA {} received: {}", self.name, event);
    }
}
```

**简要说明**：
中介者模式降低了对象间的耦合度，简化了对象间的交互。

### 3.6 备忘录模式的形式化

**理论定义**：
备忘录模式在不破坏封装的前提下，捕获并外部化对象的内部状态，以便以后可以恢复到这个状态。

**数学符号**：
Memento = { state } × { Originator } → { restore() }

**Rust 伪代码**：

```rust
// 备忘录
struct Memento {
    state: String
}

impl Memento {
    fn new(state: String) -> Self {
        Self { state }
    }

    fn get_state(&self) -> &str {
        &self.state
    }
}

// 发起人
struct Originator {
    state: String
}

impl Originator {
    fn new(state: String) -> Self {
        Self { state }
    }

    fn set_state(&mut self, state: String) {
        self.state = state;
    }

    fn get_state(&self) -> &str {
        &self.state
    }

    fn save_to_memento(&self) -> Memento {
        Memento::new(self.state.clone())
    }

    fn restore_from_memento(&mut self, memento: &Memento) {
        self.state = memento.get_state().to_string();
    }
}

// 管理者
struct Caretaker {
    mementos: Vec<Memento>
}

impl Caretaker {
    fn new() -> Self {
        Self { mementos: Vec::new() }
    }

    fn add_memento(&mut self, memento: Memento) {
        self.mementos.push(memento);
    }

    fn get_memento(&self, index: usize) -> Option<&Memento> {
        self.mementos.get(index)
    }
}
```

**简要说明**：
备忘录模式实现了对象状态的保存和恢复功能。

### 3.7 观察者模式的理论基础

**理论定义**：
观察者模式定义对象间的一种一对多的依赖关系，当一个对象状态改变时，所有依赖于它的对象都得到通知并自动更新。

**数学符号**：

```text
Subject = { observers: Vec<Observer> } × { notify() }
```

**Rust 伪代码**：

```rust
use std::collections::HashMap;

// 观察者接口
trait Observer {
    fn update(&self, data: &str);
}

// 主题接口
trait Subject {
    fn attach(&mut self, observer: Box<dyn Observer>);
    fn detach(&mut self, observer_id: &str);
    fn notify(&self, data: &str);
}

// 具体主题
struct ConcreteSubject {
    observers: HashMap<String, Box<dyn Observer>>,
    state: String
}

impl ConcreteSubject {
    fn new() -> Self {
        Self {
            observers: HashMap::new(),
            state: String::new()
        }
    }

    fn set_state(&mut self, state: String) {
        self.state = state.clone();
        self.notify(&state);
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Box<dyn Observer>) {
        // 简化实现，实际中需要唯一标识符
        self.observers.insert("observer".to_string(), observer);
    }

    fn detach(&mut self, observer_id: &str) {
        self.observers.remove(observer_id);
    }

    fn notify(&self, data: &str) {
        for observer in self.observers.values() {
            observer.update(data);
        }
    }
}

// 具体观察者
struct ConcreteObserverA {
    name: String
}

impl ConcreteObserverA {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserverA {
    fn update(&self, data: &str) {
        println!("ObserverA {} received: {}", self.name, data);
    }
}

struct ConcreteObserverB {
    name: String
}

impl ConcreteObserverB {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserverB {
    fn update(&self, data: &str) {
        println!("ObserverB {} received: {}", self.name, data);
    }
}
```

**简要说明**：
观察者模式实现了对象间的松耦合通信机制。

### 3.8 状态模式的形式化

**理论定义**：
状态模式允许对象在内部状态改变时改变其行为，对象看起来好像修改了其类。

**数学符号**：
State = { Context } × { State } → { handle() }

**Rust 伪代码**：

```rust
// 状态接口
trait State {
    fn handle(&self, context: &mut Context);
}

// 上下文
struct Context {
    state: Box<dyn State>
}

impl Context {
    fn new() -> Self {
        Self {
            state: Box::new(ConcreteStateA)
        }
    }

    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }

    fn request(&mut self) {
        self.state.handle(self);
    }
}

// 具体状态
struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) {
        println!("StateA handling request");
        context.set_state(Box::new(ConcreteStateB));
    }
}

struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) {
        println!("StateB handling request");
        context.set_state(Box::new(ConcreteStateA));
    }
}
```

**简要说明**：
状态模式封装了状态转换逻辑，使状态变化更加清晰。

### 3.9 策略模式的理论基础

**理论定义**：
策略模式定义一系列算法，将每一个算法封装起来，并使它们可以互换。

**数学符号**：
Strategy = { Context } × { Algorithm } → { execute() }

**Rust 伪代码**：

```rust
// 策略接口
trait Strategy {
    fn algorithm(&self) -> String;
}

// 上下文
struct Context {
    strategy: Box<dyn Strategy>
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Self { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }

    fn execute_strategy(&self) -> String {
        self.strategy.algorithm()
    }
}

// 具体策略
struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn algorithm(&self) -> String {
        "Strategy A".to_string()
    }
}

struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn algorithm(&self) -> String {
        "Strategy B".to_string()
    }
}

struct ConcreteStrategyC;

impl Strategy for ConcreteStrategyC {
    fn algorithm(&self) -> String {
        "Strategy C".to_string()
    }
}
```

**简要说明**：
策略模式封装了算法族，使算法可以独立于使用它的客户而变化。

### 3.10 模板方法模式的形式化

**理论定义**：
模板方法模式定义一个操作中的算法骨架，将某些步骤延迟到子类中实现。

**数学符号**：
TemplateMethod = { template() } × { primitive_operations() }

**Rust 伪代码**：

```rust
// 抽象类
trait AbstractClass {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation_1());
        result.push_str(&self.primitive_operation_2());
        result.push_str(&self.primitive_operation_3());
        result
    }

    fn primitive_operation_1(&self) -> String;
    fn primitive_operation_2(&self) -> String;
    fn primitive_operation_3(&self) -> String;
}

// 具体类
struct ConcreteClassA;

impl AbstractClass for ConcreteClassA {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassA: Operation 1".to_string()
    }

    fn primitive_operation_2(&self) -> String {
        "ConcreteClassA: Operation 2".to_string()
    }

    fn primitive_operation_3(&self) -> String {
        "ConcreteClassA: Operation 3".to_string()
    }
}

struct ConcreteClassB;

impl AbstractClass for ConcreteClassB {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassB: Operation 1".to_string()
    }

    fn primitive_operation_2(&self) -> String {
        "ConcreteClassB: Operation 2".to_string()
    }

    fn primitive_operation_3(&self) -> String {
        "ConcreteClassB: Operation 3".to_string()
    }
}
```

**简要说明**：
模板方法模式定义了算法的骨架，子类可以重定义算法的特定步骤。

### 3.11 访问者模式的理论基础

**理论定义**：
访问者模式表示一个作用于某对象结构中的各元素的操作，它使你可以在不改变各元素的类的前提下定义作用于这些元素的新操作。

**数学符号**：
Visitor = { Element } × { visit() } → { operation() }

**Rust 伪代码**：

```rust
// 元素接口
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者接口
trait Visitor {
    fn visit_element_a(&self, element: &ConcreteElementA);
    fn visit_element_b(&self, element: &ConcreteElementB);
}

// 具体元素
struct ConcreteElementA {
    name: String
}

impl ConcreteElementA {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Element for ConcreteElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_a(self);
    }
}

struct ConcreteElementB {
    name: String
}

impl ConcreteElementB {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Element for ConcreteElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_b(self);
    }
}

// 具体访问者
struct ConcreteVisitorA;

impl Visitor for ConcreteVisitorA {
    fn visit_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorA visiting ElementA: {}", element.name);
    }

    fn visit_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorA visiting ElementB: {}", element.name);
    }
}

struct ConcreteVisitorB;

impl Visitor for ConcreteVisitorB {
    fn visit_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorB visiting ElementA: {}", element.name);
    }

    fn visit_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorB visiting ElementB: {}", element.name);
    }
}

// 对象结构
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>
}

impl ObjectStructure {
    fn new() -> Self {
        Self { elements: Vec::new() }
    }

    fn add_element(&mut self, element: Box<dyn Element>) {
        self.elements.push(element);
    }

    fn accept(&self, visitor: &dyn Visitor) {
        for element in &self.elements {
            element.accept(visitor);
        }
    }
}
```

**简要说明**：
访问者模式将数据结构与数据操作分离，便于添加新的操作。

## 4. 并发模式

### 4.1 主动对象模式

**理论定义**：
主动对象模式将方法调用与执行分离，每个主动对象都有自己的控制线程。

**数学符号**：
ActiveObject = { Proxy } × { Scheduler } × { Servant }

**Rust 伪代码**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::collections::VecDeque;

// 服务接口
trait Service {
    fn operation(&self, data: String) -> String;
}

// 具体服务
struct ConcreteService;

impl Service for ConcreteService {
    fn operation(&self, data: String) -> String {
        format!("Processed: {}", data)
    }
}

// 方法请求
struct MethodRequest {
    data: String,
    result: Arc<Mutex<Option<String>>>
}

impl MethodRequest {
    fn new(data: String) -> Self {
        Self {
            data,
            result: Arc::new(Mutex::new(None))
        }
    }
}

// 调度器
struct Scheduler {
    queue: Arc<Mutex<VecDeque<MethodRequest>>>,
    servant: ConcreteService
}

impl Scheduler {
    fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            servant: ConcreteService
        }
    }

    fn enqueue(&self, request: MethodRequest) {
        self.queue.lock().unwrap().push_back(request);
    }

    fn run(&self) {
        let queue = Arc::clone(&self.queue);
        let servant = self.servant;

        thread::spawn(move || {
            loop {
                if let Some(request) = queue.lock().unwrap().pop_front() {
                    let result = servant.operation(request.data);
                    *request.result.lock().unwrap() = Some(result);
                }
            }
        });
    }
}

// 代理
struct Proxy {
    scheduler: Arc<Scheduler>
}

impl Proxy {
    fn new() -> Self {
        let scheduler = Arc::new(Scheduler::new());
        scheduler.run();
        Self { scheduler }
    }

    fn operation(&self, data: String) -> Arc<Mutex<Option<String>>> {
        let request = MethodRequest::new(data);
        let result = Arc::clone(&request.result);
        self.scheduler.enqueue(request);
        result
    }
}
```

**简要说明**：
主动对象模式实现了异步方法调用，提高了系统的响应性。

### 4.2 领导者-跟随者模式

**理论定义**：
领导者-跟随者模式使用一个线程池来处理多个事件源，其中一个线程作为领导者等待事件，其他线程作为跟随者。

**数学符号**：
LeaderFollower = { Leader } × { Followers } × { EventQueue }

**Rust 伪代码**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::collections::VecDeque;

// 事件
struct Event {
    id: u32,
    data: String
}

impl Event {
    fn new(id: u32, data: String) -> Self {
        Self { id, data }
    }
}

// 事件处理器
trait EventHandler {
    fn handle(&self, event: &Event);
}

struct ConcreteEventHandler;

impl EventHandler for ConcreteEventHandler {
    fn handle(&self, event: &Event) {
        println!("Handling event {}: {}", event.id, event.data);
    }
}

// 领导者-跟随者模式
struct LeaderFollower {
    event_queue: Arc<Mutex<VecDeque<Event>>>,
    handler: ConcreteEventHandler,
    num_followers: usize
}

impl LeaderFollower {
    fn new(num_followers: usize) -> Self {
        Self {
            event_queue: Arc::new(Mutex::new(VecDeque::new())),
            handler: ConcreteEventHandler,
            num_followers
        }
    }

    fn start(&self) {
        let queue = Arc::clone(&self.event_queue);
        let handler = self.handler;

        // 启动跟随者线程
        for i in 0..self.num_followers {
            let queue = Arc::clone(&queue);
            let handler = handler;

            thread::spawn(move || {
                loop {
                    if let Some(event) = queue.lock().unwrap().pop_front() {
                        handler.handle(&event);
                    }
                }
            });
        }

        // 领导者线程
        let queue = Arc::clone(&queue);
        thread::spawn(move || {
            loop {
                // 模拟事件到达
                let event = Event::new(1, "test event".to_string());
                queue.lock().unwrap().push_back(event);
                thread::sleep(std::time::Duration::from_millis(100));
            }
        });
    }
}
```

**简要说明**：
领导者-跟随者模式提高了事件处理的并发性能。

### 4.3 生产者-消费者模式

**理论定义**：
生产者-消费者模式通过共享缓冲区协调生产者和消费者的执行。

**数学符号**：
ProducerConsumer = { Producer } × { Consumer } × { Buffer }

**Rust 伪代码**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::collections::VecDeque;

// 缓冲区
struct Buffer<T> {
    data: Arc<Mutex<VecDeque<T>>>,
    capacity: usize
}

impl<T> Buffer<T> {
    fn new(capacity: usize) -> Self {
        Self {
            data: Arc::new(Mutex::new(VecDeque::new())),
            capacity
        }
    }

    fn push(&self, item: T) -> bool {
        let mut data = self.data.lock().unwrap();
        if data.len() < self.capacity {
            data.push_back(item);
            true
        } else {
            false
        }
    }

    fn pop(&self) -> Option<T> {
        self.data.lock().unwrap().pop_front()
    }
}

// 生产者
struct Producer {
    id: u32,
    buffer: Arc<Buffer<String>>
}

impl Producer {
    fn new(id: u32, buffer: Arc<Buffer<String>>) -> Self {
        Self { id, buffer }
    }

    fn produce(&self) {
        let item = format!("Item from producer {}", self.id);
        if self.buffer.push(item) {
            println!("Producer {} produced item", self.id);
        } else {
            println!("Producer {} failed to produce - buffer full", self.id);
        }
    }
}

// 消费者
struct Consumer {
    id: u32,
    buffer: Arc<Buffer<String>>
}

impl Consumer {
    fn new(id: u32, buffer: Arc<Buffer<String>>) -> Self {
        Self { id, buffer }
    }

    fn consume(&self) {
        if let Some(item) = self.buffer.pop() {
            println!("Consumer {} consumed: {}", self.id, item);
        } else {
            println!("Consumer {} found no items", self.id);
        }
    }
}

// 主程序
fn main() {
    let buffer = Arc::new(Buffer::new(5));

    // 启动生产者
    for i in 0..3 {
        let buffer = Arc::clone(&buffer);
        thread::spawn(move || {
            let producer = Producer::new(i, buffer);
            loop {
                producer.produce();
                thread::sleep(std::time::Duration::from_millis(100));
            }
        });
    }

    // 启动消费者
    for i in 0..2 {
        let buffer = Arc::clone(&buffer);
        thread::spawn(move || {
            let consumer = Consumer::new(i, buffer);
            loop {
                consumer.consume();
                thread::sleep(std::time::Duration::from_millis(150));
            }
        });
    }

    // 主线程等待
    thread::sleep(std::time::Duration::from_secs(10));
}
```

**简要说明**：
生产者-消费者模式实现了线程间的安全通信。

## 5. 总结

本文档提供了设计模式的完整形式化理论框架，包括：

1. **创建型模式**：工厂、建造者、原型、单例模式
2. **结构型模式**：适配器、桥接、组合、装饰器、外观、享元、代理模式
3. **行为型模式**：责任链、命令、解释器、迭代器、中介者、备忘录、观察者、状态、策略、模板方法、访问者模式
4. **并发模式**：主动对象、领导者-跟随者、生产者-消费者模式

每个模式都包含：

- 严格的理论定义
- 数学符号表示
- 完整的Rust代码实现
- 实际应用说明

这个框架为Rust语言中的设计模式实现提供了坚实的理论基础和实践指导。

---

## 附录A：生态框架落地（Rust 1.90，Edition 2024）

为便于将本文档中的模式直接落地到工程项目，给出与成熟生态的映射建议（保持中立、可替换）：

- 创建/结构/行为模式：
  - 借助 `thiserror`/`anyhow` 管理跨模式错误；`tracing` 统一观测；`serde` 用于配置/快照（备忘录）序列化。
  - 组合/访问者在 AST/DSL 场景可结合 `rowan`/`syn`。
- 并发与异步模式：
  - 执行器与原语：`tokio`（全功能）、`async-std`（备选），配合 `tokio::sync`/`futures` 原语实现观察者/事件驱动/生产者-消费者。
  - 数据并行与流水线：`rayon` 用于并行迭代与归约；跨线程通信优先 `crossbeam`，需要异步可选 `tokio::sync::mpsc`。
  - 会话类型/协议安全（Actor/消息/中介者等高阶落地）：可参考学术成熟实现 `Rumpsteak`、`Ferrite` 以获得通讯协议在类型层面的保证（生产中择优评估稳定性与维护活性）。
- I/O 与系统互操作：
  - 统一句柄：利用 1.89/1.90 稳定的 `AsFd/AsHandle/AsSocket` 族接口改善代理/外观在系统抽象层的适配。
  - 网络栈：`hyper`/`reqwest`（客户端）/`axum`（服务端）与代理/装饰器/责任链模式天然契合（中间件链）。

落地清单（建议）：

1. 在模式实现层面保留最小依赖，暴露 trait 边界；在应用层对接上述框架。
2. 对每个模式补充“同步/异步/混合”的接口门面，并在 README 的决策树进行引用。
3. 基于 `tracing` 提供可观测样例：为责任链/装饰器/代理等链式调用标注 span，验证时延与错误传播路径。
4. 基于 `criterion` 建立基准：分别覆盖 rayon 并行与 tokio 异步路径，确保无回归。

兼容性与版本建议（2025-09）：

- Rust：MSRV 1.90（Edition 2024）。
- Tokio：1.x（features: full）；Rayon：1.x；Crossbeam：0.8；Serde：1.x；Tracing：0.1。
- 学术型库（Rumpsteak、Ferrite）用于参考与实验分支，避免引入核心库的强依赖。
