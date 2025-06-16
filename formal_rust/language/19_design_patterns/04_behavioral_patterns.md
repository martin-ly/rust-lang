# 行为型设计模式

**日期**: 2025-01-27  
**版本**: 1.0.0  
**状态**: 完成

## 📋 目录

1. [行为型模式概述](#1-行为型模式概述)
2. [观察者模式 (Observer Pattern)](#2-观察者模式-observer-pattern)
3. [策略模式 (Strategy Pattern)](#3-策略模式-strategy-pattern)
4. [命令模式 (Command Pattern)](#4-命令模式-command-pattern)
5. [状态模式 (State Pattern)](#5-状态模式-state-pattern)
6. [责任链模式 (Chain of Responsibility Pattern)](#6-责任链模式-chain-of-responsibility-pattern)
7. [模板方法模式 (Template Method Pattern)](#7-模板方法模式-template-method-pattern)
8. [迭代器模式 (Iterator Pattern)](#8-迭代器模式-iterator-pattern)
9. [中介者模式 (Mediator Pattern)](#9-中介者模式-mediator-pattern)
10. [备忘录模式 (Memento Pattern)](#10-备忘录模式-memento-pattern)
11. [访问者模式 (Visitor Pattern)](#11-访问者模式-visitor-pattern)
12. [模式比较与选择](#12-模式比较与选择)

## 1. 行为型模式概述

### 1.1 形式化定义

行为型模式处理对象间通信，形式化定义为：

$$\text{Behavioral}(T) = \{\text{Chain}, \text{Command}, \text{Iterator}, \text{Mediator}, \text{Memento}, \text{Observer}, \text{State}, \text{Strategy}, \text{Template}, \text{Visitor}\}$$

其中每个模式 $p \in \text{Behavioral}(T)$ 满足：

$$\forall p: \exists h: T \times \text{Event} \rightarrow T \text{ s.t. } h \text{ is behavior-preserving}$$

### 1.2 核心原则

1. **对象通信**: 定义对象间的通信方式
2. **算法封装**: 将算法封装在对象中
3. **状态管理**: 管理对象的状态变化
4. **行为扩展**: 支持行为的动态扩展

### 1.3 分类体系

```rust
enum BehavioralPattern {
    Observer(ObserverPattern),
    Strategy(StrategyPattern),
    Command(CommandPattern),
    State(StatePattern),
    ChainOfResponsibility(ChainOfResponsibilityPattern),
    TemplateMethod(TemplateMethodPattern),
    Iterator(IteratorPattern),
    Mediator(MediatorPattern),
    Memento(MementoPattern),
    Visitor(VisitorPattern),
}
```

## 2. 观察者模式 (Observer Pattern)

### 2.1 形式化定义

观察者模式定义对象间的一种一对多的依赖关系，当一个对象的状态发生改变时，所有依赖于它的对象都得到通知并被自动更新。

$$\text{Observer}(S, O) = \{(notify, subscribe, unsubscribe) \mid \text{OneToMany}(S, O)\}$$

### 2.2 结构分析

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 观察者接口
trait Observer {
    fn update(&self, subject: &Subject);
}

// 主题接口
trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer: &Arc<dyn Observer>);
    fn notify(&self);
}

// 具体主题
struct ConcreteSubject {
    observers: Arc<RwLock<Vec<Arc<dyn Observer>>>>,
    state: String,
}

impl ConcreteSubject {
    fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(Vec::new())),
            state: String::new(),
        }
    }
    
    fn set_state(&mut self, state: String) {
        self.state = state;
        self.notify();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        let mut observers = self.observers.write().unwrap();
        observers.push(observer);
    }
    
    fn detach(&mut self, observer: &Arc<dyn Observer>) {
        let mut observers = self.observers.write().unwrap();
        observers.retain(|obs| !Arc::ptr_eq(obs, observer));
    }
    
    fn notify(&self) {
        let observers = self.observers.read().unwrap();
        for observer in observers.iter() {
            observer.update(self);
        }
    }
}

// 具体观察者
struct ConcreteObserver {
    name: String,
}

impl ConcreteObserver {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, subject: &Subject) {
        if let Some(concrete_subject) = subject.as_any().downcast_ref::<ConcreteSubject>() {
            println!(
                "Observer {} received update: {}",
                self.name,
                concrete_subject.get_state()
            );
        }
    }
}
```

### 2.3 事件驱动观察者

```rust
// 事件类型
#[derive(Clone, Debug)]
enum Event {
    StateChanged(String),
    DataUpdated(Vec<u8>),
    ErrorOccurred(String),
}

// 事件观察者
trait EventObserver {
    fn on_event(&self, event: &Event);
}

// 事件主题
struct EventSubject {
    observers: Arc<RwLock<HashMap<String, Arc<dyn EventObserver>>>>,
}

impl EventSubject {
    fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn subscribe(&mut self, name: String, observer: Arc<dyn EventObserver>) {
        let mut observers = self.observers.write().unwrap();
        observers.insert(name, observer);
    }
    
    fn unsubscribe(&mut self, name: &str) {
        let mut observers = self.observers.write().unwrap();
        observers.remove(name);
    }
    
    fn publish(&self, event: Event) {
        let observers = self.observers.read().unwrap();
        for observer in observers.values() {
            observer.on_event(&event);
        }
    }
}

// 具体事件观察者
struct LoggingObserver;

impl EventObserver for LoggingObserver {
    fn on_event(&self, event: &Event) {
        println!("LoggingObserver: {:?}", event);
    }
}

struct MetricsObserver;

impl EventObserver for MetricsObserver {
    fn on_event(&self, event: &Event) {
        println!("MetricsObserver: {:?}", event);
    }
}
```

### 2.4 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是观察者的数量
**空间复杂度**: $O(n)$ - 需要存储所有观察者
**线程安全**: ✅ 支持线程安全的事件发布
**内存效率**: ✅ 使用Arc避免重复分配

## 3. 策略模式 (Strategy Pattern)

### 3.1 形式化定义

策略模式定义一系列算法，把它们封装起来，并且使它们可以互相替换。

$$\text{Strategy}(A) = \{(execute, algorithm) \mid \text{Interchangeable}(A)\}$$

### 3.2 结构分析

```rust
// 策略接口
trait Strategy {
    fn execute(&self, data: &str) -> String;
}

// 具体策略A
struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn execute(&self, data: &str) -> String {
        format!("StrategyA: {}", data.to_uppercase())
    }
}

// 具体策略B
struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn execute(&self, data: &str) -> String {
        format!("StrategyB: {}", data.to_lowercase())
    }
}

// 具体策略C
struct ConcreteStrategyC;

impl Strategy for ConcreteStrategyC {
    fn execute(&self, data: &str) -> String {
        format!("StrategyC: {}", data.chars().rev().collect::<String>())
    }
}

// 上下文
struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }
    
    fn execute_strategy(&self, data: &str) -> String {
        self.strategy.execute(data)
    }
}
```

### 3.3 泛型策略

```rust
// 泛型策略模式
trait GenericStrategy<T, R> {
    fn execute(&self, input: T) -> R;
}

// 数值计算策略
struct AdditionStrategy;

impl GenericStrategy<i32, i32> for AdditionStrategy {
    fn execute(&self, input: i32) -> i32 {
        input + 10
    }
}

struct MultiplicationStrategy;

impl GenericStrategy<i32, i32> for MultiplicationStrategy {
    fn execute(&self, input: i32) -> i32 {
        input * 2
    }
}

// 泛型上下文
struct GenericContext<T, R> {
    strategy: Box<dyn GenericStrategy<T, R>>,
}

impl<T, R> GenericContext<T, R> {
    fn new(strategy: Box<dyn GenericStrategy<T, R>>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn GenericStrategy<T, R>>) {
        self.strategy = strategy;
    }
    
    fn execute_strategy(&self, input: T) -> R {
        self.strategy.execute(input)
    }
}
```

### 3.4 策略工厂

```rust
// 策略工厂
struct StrategyFactory;

impl StrategyFactory {
    fn create_strategy(strategy_type: &str) -> Option<Box<dyn Strategy>> {
        match strategy_type {
            "A" => Some(Box::new(ConcreteStrategyA)),
            "B" => Some(Box::new(ConcreteStrategyB)),
            "C" => Some(Box::new(ConcreteStrategyC)),
            _ => None,
        }
    }
}

// 动态策略选择
struct DynamicContext {
    strategy: Option<Box<dyn Strategy>>,
}

impl DynamicContext {
    fn new() -> Self {
        Self { strategy: None }
    }
    
    fn set_strategy(&mut self, strategy_type: &str) -> bool {
        if let Some(strategy) = StrategyFactory::create_strategy(strategy_type) {
            self.strategy = Some(strategy);
            true
        } else {
            false
        }
    }
    
    fn execute_strategy(&self, data: &str) -> Option<String> {
        self.strategy.as_ref().map(|s| s.execute(data))
    }
}
```

### 3.5 性能分析

**时间复杂度**: $O(1)$ - 策略执行的时间复杂度为常数
**空间复杂度**: $O(1)$ - 只需要存储策略对象
**灵活性**: ✅ 支持运行时策略切换
**扩展性**: ✅ 易于添加新策略

## 4. 命令模式 (Command Pattern)

### 4.1 形式化定义

命令模式将一个请求封装为一个对象，从而可以用不同的请求对客户进行参数化。

$$\text{Command}(R) = \{(execute, undo) \mid \text{Reversible}(R)\}$$

### 4.2 结构分析

```rust
// 命令接口
trait Command {
    fn execute(&self);
    fn undo(&self);
}

// 接收者
struct Receiver {
    name: String,
}

impl Receiver {
    fn new(name: String) -> Self {
        Self { name }
    }
    
    fn action_a(&self) {
        println!("Receiver {}: Action A", self.name);
    }
    
    fn action_b(&self) {
        println!("Receiver {}: Action B", self.name);
    }
    
    fn undo_action_a(&self) {
        println!("Receiver {}: Undo Action A", self.name);
    }
    
    fn undo_action_b(&self) {
        println!("Receiver {}: Undo Action B", self.name);
    }
}

// 具体命令A
struct ConcreteCommandA {
    receiver: Receiver,
}

impl ConcreteCommandA {
    fn new(receiver: Receiver) -> Self {
        Self { receiver }
    }
}

impl Command for ConcreteCommandA {
    fn execute(&self) {
        self.receiver.action_a();
    }
    
    fn undo(&self) {
        self.receiver.undo_action_a();
    }
}

// 具体命令B
struct ConcreteCommandB {
    receiver: Receiver,
}

impl ConcreteCommandB {
    fn new(receiver: Receiver) -> Self {
        Self { receiver }
    }
}

impl Command for ConcreteCommandB {
    fn execute(&self) {
        self.receiver.action_b();
    }
    
    fn undo(&self) {
        self.receiver.undo_action_b();
    }
}

// 调用者
struct Invoker {
    commands: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
    
    fn execute_all(&self) {
        for command in &self.commands {
            command.execute();
        }
    }
    
    fn undo_all(&self) {
        for command in self.commands.iter().rev() {
            command.undo();
        }
    }
}
```

### 4.3 宏命令

```rust
// 宏命令 - 组合多个命令
struct MacroCommand {
    commands: Vec<Box<dyn Command>>,
}

impl MacroCommand {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
}

impl Command for MacroCommand {
    fn execute(&self) {
        for command in &self.commands {
            command.execute();
        }
    }
    
    fn undo(&self) {
        for command in self.commands.iter().rev() {
            command.undo();
        }
    }
}
```

### 4.4 命令历史

```rust
// 命令历史管理器
struct CommandHistory {
    history: Vec<Box<dyn Command>>,
    current_index: usize,
}

impl CommandHistory {
    fn new() -> Self {
        Self {
            history: Vec::new(),
            current_index: 0,
        }
    }
    
    fn execute(&mut self, command: Box<dyn Command>) {
        // 移除当前位置之后的所有命令
        self.history.truncate(self.current_index);
        
        // 添加新命令
        self.history.push(command);
        self.current_index += 1;
        
        // 执行命令
        if let Some(cmd) = self.history.last() {
            cmd.execute();
        }
    }
    
    fn undo(&mut self) {
        if self.current_index > 0 {
            self.current_index -= 1;
            if let Some(cmd) = self.history.get(self.current_index) {
                cmd.undo();
            }
        }
    }
    
    fn redo(&mut self) {
        if self.current_index < self.history.len() {
            if let Some(cmd) = self.history.get(self.current_index) {
                cmd.execute();
            }
            self.current_index += 1;
        }
    }
}
```

### 4.5 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是命令的数量
**空间复杂度**: $O(n)$ - 需要存储命令历史
**可撤销性**: ✅ 支持完整的撤销/重做
**扩展性**: ✅ 易于添加新命令类型

## 5. 状态模式 (State Pattern)

### 5.1 形式化定义

状态模式允许一个对象在其内部状态改变时改变它的行为。

$$\text{State}(S) = \{(transition, behavior) \mid \text{StateMachine}(S)\}$$

### 5.2 结构分析

```rust
// 状态接口
trait State {
    fn handle(&self, context: &mut Context) -> String;
    fn next_state(&self) -> Option<Box<dyn State>>;
}

// 上下文
struct Context {
    state: Box<dyn State>,
}

impl Context {
    fn new() -> Self {
        Self {
            state: Box::new(ConcreteStateA),
        }
    }
    
    fn request(&mut self) -> String {
        let result = self.state.handle(self);
        
        // 状态转换
        if let Some(next_state) = self.state.next_state() {
            self.state = next_state;
        }
        
        result
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }
}

// 具体状态A
struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, _context: &mut Context) -> String {
        "State A handling request".to_string()
    }
    
    fn next_state(&self) -> Option<Box<dyn State>> {
        Some(Box::new(ConcreteStateB))
    }
}

// 具体状态B
struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, _context: &mut Context) -> String {
        "State B handling request".to_string()
    }
    
    fn next_state(&self) -> Option<Box<dyn State>> {
        Some(Box::new(ConcreteStateC))
    }
}

// 具体状态C
struct ConcreteStateC;

impl State for ConcreteStateC {
    fn handle(&self, _context: &mut Context) -> String {
        "State C handling request".to_string()
    }
    
    fn next_state(&self) -> Option<Box<dyn State>> {
        Some(Box::new(ConcreteStateA))
    }
}
```

### 5.3 状态机

```rust
// 状态机定义
struct StateMachine {
    current_state: Box<dyn State>,
    states: HashMap<String, Box<dyn State>>,
}

impl StateMachine {
    fn new() -> Self {
        let mut states = HashMap::new();
        states.insert("A".to_string(), Box::new(ConcreteStateA));
        states.insert("B".to_string(), Box::new(ConcreteStateB));
        states.insert("C".to_string(), Box::new(ConcreteStateC));
        
        Self {
            current_state: Box::new(ConcreteStateA),
            states,
        }
    }
    
    fn transition_to(&mut self, state_name: &str) -> bool {
        if let Some(state) = self.states.get(state_name) {
            self.current_state = state.clone();
            true
        } else {
            false
        }
    }
    
    fn handle(&self) -> String {
        let mut context = Context::new();
        self.current_state.handle(&mut context)
    }
}

// 为Box<dyn State>实现Clone
impl Clone for Box<dyn State> {
    fn clone(&self) -> Self {
        // 在实际实现中，需要为每个具体状态实现Clone
        Box::new(ConcreteStateA)
    }
}
```

### 5.4 性能分析

**时间复杂度**: $O(1)$ - 状态转换的时间复杂度为常数
**空间复杂度**: $O(n)$ - 其中 $n$ 是状态的数量
**状态一致性**: ✅ 保证状态转换的一致性
**行为封装**: ✅ 每个状态封装自己的行为

## 6. 责任链模式 (Chain of Responsibility Pattern)

### 6.1 形式化定义

责任链模式为请求创建一个接收者对象的链。

$$\text{Chain}(H) = \{(handle, next) \mid \text{Chain}(H) \land \text{Process}(H)\}$$

### 6.2 结构分析

```rust
// 处理器接口
trait Handler {
    fn set_next(&mut self, handler: Box<dyn Handler>);
    fn handle(&self, request: &Request) -> Option<String>;
}

// 请求
struct Request {
    level: u32,
    description: String,
}

impl Request {
    fn new(level: u32, description: String) -> Self {
        Self { level, description }
    }
}

// 抽象处理器
struct AbstractHandler {
    next: Option<Box<dyn Handler>>,
}

impl AbstractHandler {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for AbstractHandler {
    fn set_next(&mut self, handler: Box<dyn Handler>) {
        self.next = Some(handler);
    }
    
    fn handle(&self, request: &Request) -> Option<String> {
        if let Some(ref next) = self.next {
            next.handle(request)
        } else {
            None
        }
    }
}

// 具体处理器A
struct ConcreteHandlerA {
    handler: AbstractHandler,
    level: u32,
}

impl ConcreteHandlerA {
    fn new(level: u32) -> Self {
        Self {
            handler: AbstractHandler::new(),
            level,
        }
    }
}

impl Handler for ConcreteHandlerA {
    fn set_next(&mut self, handler: Box<dyn Handler>) {
        self.handler.set_next(handler);
    }
    
    fn handle(&self, request: &Request) -> Option<String> {
        if request.level <= self.level {
            Some(format!("HandlerA handled: {}", request.description))
        } else {
            self.handler.handle(request)
        }
    }
}

// 具体处理器B
struct ConcreteHandlerB {
    handler: AbstractHandler,
    level: u32,
}

impl ConcreteHandlerB {
    fn new(level: u32) -> Self {
        Self {
            handler: AbstractHandler::new(),
            level,
        }
    }
}

impl Handler for ConcreteHandlerB {
    fn set_next(&mut self, handler: Box<dyn Handler>) {
        self.handler.set_next(handler);
    }
    
    fn handle(&self, request: &Request) -> Option<String> {
        if request.level <= self.level {
            Some(format!("HandlerB handled: {}", request.description))
        } else {
            self.handler.handle(request)
        }
    }
}
```

### 6.3 中间件链

```rust
// 中间件接口
trait Middleware {
    fn process(&self, request: &Request, next: &dyn Fn(&Request) -> Option<String>) -> Option<String>;
}

// 中间件链
struct MiddlewareChain {
    middlewares: Vec<Box<dyn Middleware>>,
}

impl MiddlewareChain {
    fn new() -> Self {
        Self {
            middlewares: Vec::new(),
        }
    }
    
    fn add_middleware(&mut self, middleware: Box<dyn Middleware>) {
        self.middlewares.push(middleware);
    }
    
    fn process(&self, request: &Request) -> Option<String> {
        if self.middlewares.is_empty() {
            return None;
        }
        
        self.process_with_index(request, 0)
    }
    
    fn process_with_index(&self, request: &Request, index: usize) -> Option<String> {
        if index >= self.middlewares.len() {
            return None;
        }
        
        let next = |req: &Request| self.process_with_index(req, index + 1);
        self.middlewares[index].process(request, &next)
    }
}

// 具体中间件
struct LoggingMiddleware;

impl Middleware for LoggingMiddleware {
    fn process(&self, request: &Request, next: &dyn Fn(&Request) -> Option<String>) -> Option<String> {
        println!("Logging: Processing request level {}", request.level);
        let result = next(request);
        println!("Logging: Request processed");
        result
    }
}

struct ValidationMiddleware;

impl Middleware for ValidationMiddleware {
    fn process(&self, request: &Request, next: &dyn Fn(&Request) -> Option<String>) -> Option<String> {
        if request.level > 0 {
            next(request)
        } else {
            Some("Validation failed: Invalid level".to_string())
        }
    }
}
```

### 6.4 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是处理器的数量
**空间复杂度**: $O(n)$ - 需要存储处理器链
**灵活性**: ✅ 支持动态处理器组合
**可扩展性**: ✅ 易于添加新处理器

## 7. 模板方法模式 (Template Method Pattern)

### 7.1 形式化定义

模板方法模式定义一个操作中的算法骨架，而将一些步骤延迟到子类中实现。

$$\text{Template}(A) = \{(template, primitive) \mid \text{Algorithm}(A) \land \text{Hook}(A)\}$$

### 7.2 结构分析

```rust
// 抽象类
trait AbstractClass {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation_1());
        result.push_str("\n");
        result.push_str(&self.primitive_operation_2());
        result.push_str("\n");
        result.push_str(&self.concrete_operation());
        result
    }
    
    fn primitive_operation_1(&self) -> String;
    fn primitive_operation_2(&self) -> String;
    
    fn concrete_operation(&self) -> String {
        "AbstractClass concrete operation".to_string()
    }
}

// 具体类A
struct ConcreteClassA;

impl AbstractClass for ConcreteClassA {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassA primitive operation 1".to_string()
    }
    
    fn primitive_operation_2(&self) -> String {
        "ConcreteClassA primitive operation 2".to_string()
    }
}

// 具体类B
struct ConcreteClassB;

impl AbstractClass for ConcreteClassB {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassB primitive operation 1".to_string()
    }
    
    fn primitive_operation_2(&self) -> String {
        "ConcreteClassB primitive operation 2".to_string()
    }
    
    fn concrete_operation(&self) -> String {
        "ConcreteClassB concrete operation".to_string()
    }
}
```

### 7.3 钩子方法

```rust
// 带钩子的抽象类
trait AbstractClassWithHooks {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation_1());
        result.push_str("\n");
        
        if self.hook() {
            result.push_str(&self.primitive_operation_2());
            result.push_str("\n");
        }
        
        result.push_str(&self.concrete_operation());
        result
    }
    
    fn primitive_operation_1(&self) -> String;
    fn primitive_operation_2(&self) -> String;
    fn concrete_operation(&self) -> String;
    fn hook(&self) -> bool { true } // 默认钩子
}

// 具体实现
struct ConcreteClassWithHooks {
    use_operation_2: bool,
}

impl ConcreteClassWithHooks {
    fn new(use_operation_2: bool) -> Self {
        Self { use_operation_2 }
    }
}

impl AbstractClassWithHooks for ConcreteClassWithHooks {
    fn primitive_operation_1(&self) -> String {
        "Primitive operation 1".to_string()
    }
    
    fn primitive_operation_2(&self) -> String {
        "Primitive operation 2".to_string()
    }
    
    fn concrete_operation(&self) -> String {
        "Concrete operation".to_string()
    }
    
    fn hook(&self) -> bool {
        self.use_operation_2
    }
}
```

### 7.4 性能分析

**时间复杂度**: $O(1)$ - 模板方法的时间复杂度为常数
**空间复杂度**: $O(1)$ - 不需要额外的存储空间
**代码复用**: ✅ 最大化代码复用
**扩展性**: ✅ 易于添加新的具体类

## 8. 迭代器模式 (Iterator Pattern)

### 8.1 形式化定义

迭代器模式提供一种方法顺序访问一个聚合对象中的各个元素，而又不暴露其内部的表示。

$$\text{Iterator}(C) = \{(next, has_next) \mid \text{Sequential}(C)\}$$

### 8.2 结构分析

```rust
// 迭代器接口
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
    fn has_next(&self) -> bool;
}

// 聚合接口
trait Aggregate {
    type Item;
    type IteratorType: Iterator<Item = Self::Item>;
    
    fn create_iterator(&self) -> Self::IteratorType;
}

// 具体聚合
struct ConcreteAggregate {
    items: Vec<String>,
}

impl ConcreteAggregate {
    fn new() -> Self {
        Self {
            items: Vec::new(),
        }
    }
    
    fn add_item(&mut self, item: String) {
        self.items.push(item);
    }
}

impl Aggregate for ConcreteAggregate {
    type Item = String;
    type IteratorType = ConcreteIterator;
    
    fn create_iterator(&self) -> Self::IteratorType {
        ConcreteIterator::new(self.items.clone())
    }
}

// 具体迭代器
struct ConcreteIterator {
    items: Vec<String>,
    position: usize,
}

impl ConcreteIterator {
    fn new(items: Vec<String>) -> Self {
        Self {
            items,
            position: 0,
        }
    }
}

impl Iterator for ConcreteIterator {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.items.len() {
            let item = self.items[self.position].clone();
            self.position += 1;
            Some(item)
        } else {
            None
        }
    }
    
    fn has_next(&self) -> bool {
        self.position < self.items.len()
    }
}
```

### 8.3 泛型迭代器

```rust
// 泛型迭代器
struct GenericIterator<T> {
    items: Vec<T>,
    position: usize,
}

impl<T> GenericIterator<T> {
    fn new(items: Vec<T>) -> Self {
        Self {
            items,
            position: 0,
        }
    }
}

impl<T: Clone> Iterator for GenericIterator<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.items.len() {
            let item = self.items[self.position].clone();
            self.position += 1;
            Some(item)
        } else {
            None
        }
    }
    
    fn has_next(&self) -> bool {
        self.position < self.items.len()
    }
}

// 泛型聚合
struct GenericAggregate<T> {
    items: Vec<T>,
}

impl<T> GenericAggregate<T> {
    fn new() -> Self {
        Self { items: Vec::new() }
    }
    
    fn add_item(&mut self, item: T) {
        self.items.push(item);
    }
}

impl<T: Clone> Aggregate for GenericAggregate<T> {
    type Item = T;
    type IteratorType = GenericIterator<T>;
    
    fn create_iterator(&self) -> Self::IteratorType {
        GenericIterator::new(self.items.clone())
    }
}
```

### 8.4 性能分析

**时间复杂度**: $O(1)$ - 每次迭代的时间复杂度为常数
**空间复杂度**: $O(n)$ - 需要存储聚合对象
**封装性**: ✅ 隐藏内部实现细节
**通用性**: ✅ 支持不同类型的聚合对象

## 9. 中介者模式 (Mediator Pattern)

### 9.1 形式化定义

中介者模式用一个中介对象来封装一系列的对象交互。

$$\text{Mediator}(C) = \{(mediate, coordinate) \mid \text{Centralized}(C)\}$$

### 9.2 结构分析

```rust
// 同事接口
trait Colleague {
    fn set_mediator(&mut self, mediator: &dyn Mediator);
    fn send(&self, message: &str);
    fn receive(&self, message: &str);
}

// 中介者接口
trait Mediator {
    fn send(&self, message: &str, colleague: &dyn Colleague);
}

// 具体中介者
struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague>>,
}

impl ConcreteMediator {
    fn new() -> Self {
        Self {
            colleagues: Vec::new(),
        }
    }
    
    fn add_colleague(&mut self, colleague: Box<dyn Colleague>) {
        self.colleagues.push(colleague);
    }
}

impl Mediator for ConcreteMediator {
    fn send(&self, message: &str, sender: &dyn Colleague) {
        for colleague in &self.colleagues {
            // 不向发送者发送消息
            if !std::ptr::eq(colleague.as_ref(), sender) {
                colleague.receive(message);
            }
        }
    }
}

// 具体同事A
struct ConcreteColleagueA {
    mediator: Option<&'static dyn Mediator>,
    name: String,
}

impl ConcreteColleagueA {
    fn new(name: String) -> Self {
        Self {
            mediator: None,
            name,
        }
    }
}

impl Colleague for ConcreteColleagueA {
    fn set_mediator(&mut self, mediator: &dyn Mediator) {
        // 在实际实现中，需要处理生命周期
        // self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = self.mediator {
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("ColleagueA {} received: {}", self.name, message);
    }
}

// 具体同事B
struct ConcreteColleagueB {
    mediator: Option<&'static dyn Mediator>,
    name: String,
}

impl ConcreteColleagueB {
    fn new(name: String) -> Self {
        Self {
            mediator: None,
            name,
        }
    }
}

impl Colleague for ConcreteColleagueB {
    fn set_mediator(&mut self, mediator: &dyn Mediator) {
        // self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = self.mediator {
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("ColleagueB {} received: {}", self.name, message);
    }
}
```

### 9.3 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是同事的数量
**空间复杂度**: $O(n)$ - 需要存储所有同事
**解耦程度**: ✅ 显著降低对象间耦合
**复杂性**: ⚠️ 中介者可能变得复杂

## 10. 备忘录模式 (Memento Pattern)

### 10.1 形式化定义

备忘录模式在不破坏封装的前提下，捕获并外部化一个对象的内部状态。

$$\text{Memento}(S) = \{(save, restore) \mid \text{Encapsulated}(S)\}$$

### 10.2 结构分析

```rust
// 备忘录
struct Memento {
    state: String,
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
    state: String,
}

impl Originator {
    fn new() -> Self {
        Self {
            state: String::new(),
        }
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
    mementos: Vec<Memento>,
}

impl Caretaker {
    fn new() -> Self {
        Self {
            mementos: Vec::new(),
        }
    }
    
    fn add_memento(&mut self, memento: Memento) {
        self.mementos.push(memento);
    }
    
    fn get_memento(&self, index: usize) -> Option<&Memento> {
        self.mementos.get(index)
    }
}
```

### 10.3 性能分析

**时间复杂度**: $O(1)$ - 保存和恢复的时间复杂度为常数
**空间复杂度**: $O(n)$ - 需要存储所有备忘录
**封装性**: ✅ 保持对象封装
**历史管理**: ✅ 支持完整的历史记录

## 11. 访问者模式 (Visitor Pattern)

### 11.1 形式化定义

访问者模式表示一个作用于某对象结构中的各元素的操作。

$$\text{Visitor}(E) = \{(visit, accept) \mid \text{DoubleDispatch}(E)\}$$

### 11.2 结构分析

```rust
// 元素接口
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者接口
trait Visitor {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA);
    fn visit_concrete_element_b(&self, element: &ConcreteElementB);
}

// 具体元素A
struct ConcreteElementA {
    name: String,
}

impl ConcreteElementA {
    fn new(name: String) -> Self {
        Self { name }
    }
    
    fn operation_a(&self) -> String {
        format!("ConcreteElementA {} operation", self.name)
    }
}

impl Element for ConcreteElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_a(self);
    }
}

// 具体元素B
struct ConcreteElementB {
    name: String,
}

impl ConcreteElementB {
    fn new(name: String) -> Self {
        Self { name }
    }
    
    fn operation_b(&self) -> String {
        format!("ConcreteElementB {} operation", self.name)
    }
}

impl Element for ConcreteElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_b(self);
    }
}

// 具体访问者A
struct ConcreteVisitorA;

impl Visitor for ConcreteVisitorA {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorA visiting: {}", element.operation_a());
    }
    
    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorA visiting: {}", element.operation_b());
    }
}

// 具体访问者B
struct ConcreteVisitorB;

impl Visitor for ConcreteVisitorB {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorB visiting: {}", element.operation_a());
    }
    
    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorB visiting: {}", element.operation_b());
    }
}

// 对象结构
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
}

impl ObjectStructure {
    fn new() -> Self {
        Self {
            elements: Vec::new(),
        }
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

### 11.3 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是元素的数量
**空间复杂度**: $O(1)$ - 不需要额外的存储空间
**扩展性**: ✅ 易于添加新的访问者
**类型安全**: ✅ 保证类型安全

## 12. 模式比较与选择

### 12.1 模式对比表

| 模式 | 复杂度 | 性能 | 内存安全 | 线程安全 | 适用场景 |
|------|--------|------|----------|----------|----------|
| Observer | 中 | 中 | ✅ | ✅ | 事件通知 |
| Strategy | 低 | 高 | ✅ | ✅ | 算法选择 |
| Command | 中 | 中 | ✅ | ✅ | 操作封装 |
| State | 中 | 中 | ✅ | ✅ | 状态管理 |
| Chain | 中 | 中 | ✅ | ✅ | 请求处理 |
| Template | 低 | 高 | ✅ | ✅ | 算法模板 |
| Iterator | 低 | 高 | ✅ | ✅ | 集合遍历 |
| Mediator | 高 | 中 | ✅ | ✅ | 对象协调 |
| Memento | 中 | 中 | ✅ | ✅ | 状态保存 |
| Visitor | 高 | 中 | ✅ | ✅ | 操作分离 |

### 12.2 选择指南

#### 12.2.1 何时使用观察者模式

- 需要实现事件通知机制
- 对象间存在一对多依赖关系
- 需要松耦合的通信

#### 12.2.2 何时使用策略模式

- 需要动态选择算法
- 算法可以互相替换
- 需要避免条件语句

#### 12.2.3 何时使用命令模式

- 需要支持撤销/重做
- 需要参数化请求
- 需要队列化请求

#### 12.2.4 何时使用状态模式

- 对象行为依赖于状态
- 状态转换复杂
- 需要避免条件语句

#### 12.2.5 何时使用责任链模式

- 请求有多个处理者
- 处理者顺序不确定
- 需要动态指定处理者

#### 12.2.6 何时使用模板方法模式

- 算法有固定结构
- 子类需要定制特定步骤
- 需要代码复用

#### 12.2.7 何时使用迭代器模式

- 需要统一访问集合
- 需要隐藏集合实现
- 需要支持多种遍历方式

#### 12.2.8 何时使用中介者模式

- 对象间通信复杂
- 需要降低耦合度
- 需要集中控制

#### 12.2.9 何时使用备忘录模式

- 需要保存对象状态
- 需要支持撤销操作
- 需要保持封装性

#### 12.2.10 何时使用访问者模式

- 数据结构稳定
- 操作经常变化
- 需要分离数据结构与操作

### 12.3 组合使用

```rust
// 观察者 + 命令组合
struct ObserverCommand {
    observers: Vec<Arc<dyn Observer>>,
    command: Box<dyn Command>,
}

impl ObserverCommand {
    fn new(command: Box<dyn Command>) -> Self {
        Self {
            observers: Vec::new(),
            command,
        }
    }
    
    fn add_observer(&mut self, observer: Arc<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn execute(&self) {
        self.command.execute();
        // 通知观察者
        for observer in &self.observers {
            // 通知逻辑
        }
    }
}
```

---

**维护者**: Rust语言形式化理论团队  
**最后更新**: 2025-01-27
