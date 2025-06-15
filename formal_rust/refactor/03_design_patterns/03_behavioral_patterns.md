# 03. 行为型设计模式

## 目录

1. [引言](#1-引言)
2. [责任链模式](#2-责任链模式)
3. [命令模式](#3-命令模式)
4. [解释器模式](#4-解释器模式)
5. [迭代器模式](#5-迭代器模式)
6. [中介者模式](#6-中介者模式)
7. [备忘录模式](#7-备忘录模式)
8. [观察者模式](#8-观察者模式)
9. [状态模式](#9-状态模式)
10. [策略模式](#10-策略模式)
11. [模板方法模式](#11-模板方法模式)
12. [访问者模式](#12-访问者模式)
13. [总结与展望](#13-总结与展望)

## 1. 引言

### 1.1 行为型模式在Rust中的重要性

行为型设计模式关注对象间的通信和职责分配，在Rust中具有特殊的意义：

**形式化定义**：
```
Behavioral_Patterns(Rust) = {
    Chain_of_Responsibility_Pattern,
    Command_Pattern,
    Interpreter_Pattern,
    Iterator_Pattern,
    Mediator_Pattern,
    Memento_Pattern,
    Observer_Pattern,
    State_Pattern,
    Strategy_Pattern,
    Template_Method_Pattern,
    Visitor_Pattern
}
```

### 1.2 核心行为型概念

Rust中的行为型模式包含以下核心概念：

1. **职责分配**：对象间职责的合理分配
2. **通信机制**：对象间的通信方式
3. **算法封装**：算法的封装和选择
4. **状态管理**：对象状态的管理
5. **行为扩展**：行为的动态扩展

## 2. 责任链模式

### 2.1 责任链模式定义

**定义 2.1.1** (责任链)
```
Chain_of_Responsibility = {handlers: Vec<Handler>, successor: Handler → Handler}
```

**定义 2.1.2** (处理保证)
```
Handling_Guarantee = {
    Request_Processing: ∀r ∈ Request, ∃h ∈ Handler, Process(h, r),
    Chain_Traversal: ∀h ∈ Handler, Successor(h) → Next_Handler(h),
    Termination: ∃h ∈ Handler, Final_Handler(h) ∨ No_Successor(h)
}
```

### 2.2 Rust中的责任链实现

**示例 2.2.1** (责任链模式)
```rust
// 请求结构
struct Request {
    level: u32,
    description: String,
}

// 处理器特征
trait Handler {
    fn set_successor(&mut self, successor: Box<dyn Handler>);
    fn handle(&self, request: &Request) -> Option<String>;
}

// 具体处理器A
struct ConcreteHandlerA {
    successor: Option<Box<dyn Handler>>,
    level: u32,
}

impl ConcreteHandlerA {
    fn new(level: u32) -> Self {
        ConcreteHandlerA {
            successor: None,
            level,
        }
    }
}

impl Handler for ConcreteHandlerA {
    fn set_successor(&mut self, successor: Box<dyn Handler>) {
        self.successor = Some(successor);
    }
    
    fn handle(&self, request: &Request) -> Option<String> {
        if request.level <= self.level {
            Some(format!("ConcreteHandlerA handled: {}", request.description))
        } else {
            // 传递给下一个处理器
            self.successor.as_ref().and_then(|s| s.handle(request))
        }
    }
}

// 具体处理器B
struct ConcreteHandlerB {
    successor: Option<Box<dyn Handler>>,
    level: u32,
}

impl ConcreteHandlerB {
    fn new(level: u32) -> Self {
        ConcreteHandlerB {
            successor: None,
            level,
        }
    }
}

impl Handler for ConcreteHandlerB {
    fn set_successor(&mut self, successor: Box<dyn Handler>) {
        self.successor = Some(successor);
    }
    
    fn handle(&self, request: &Request) -> Option<String> {
        if request.level <= self.level {
            Some(format!("ConcreteHandlerB handled: {}", request.description))
        } else {
            self.successor.as_ref().and_then(|s| s.handle(request))
        }
    }
}
```

## 3. 命令模式

### 3.1 命令模式定义

**定义 3.1.1** (命令)
```
Command = {execute: () → Result, undo: () → Result}
```

**定义 3.1.2** (命令保证)
```
Command_Guarantee = {
    Encapsulation: ∀c ∈ Command, Encapsulate(c, Request),
    Invocation: ∀c ∈ Command, Execute(c) → Result,
    Reversibility: ∀c ∈ Command, Undo(c) → Previous_State
}
```

### 3.2 Rust中的命令实现

**示例 3.2.1** (命令模式)
```rust
// 接收者
struct Receiver {
    state: String,
}

impl Receiver {
    fn new() -> Self {
        Receiver {
            state: "initial".to_string(),
        }
    }
    
    fn action_a(&mut self) {
        self.state = "action_a".to_string();
    }
    
    fn action_b(&mut self) {
        self.state = "action_b".to_string();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

// 命令特征
trait Command {
    fn execute(&mut self);
    fn undo(&mut self);
}

// 具体命令A
struct ConcreteCommandA {
    receiver: Receiver,
}

impl ConcreteCommandA {
    fn new(receiver: Receiver) -> Self {
        ConcreteCommandA { receiver }
    }
}

impl Command for ConcreteCommandA {
    fn execute(&mut self) {
        self.receiver.action_a();
    }
    
    fn undo(&mut self) {
        self.receiver.state = "initial".to_string();
    }
}

// 具体命令B
struct ConcreteCommandB {
    receiver: Receiver,
}

impl ConcreteCommandB {
    fn new(receiver: Receiver) -> Self {
        ConcreteCommandB { receiver }
    }
}

impl Command for ConcreteCommandB {
    fn execute(&mut self) {
        self.receiver.action_b();
    }
    
    fn undo(&mut self) {
        self.receiver.state = "initial".to_string();
    }
}

// 调用者
struct Invoker {
    commands: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Invoker {
            commands: Vec::new(),
        }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
    
    fn execute_all(&mut self) {
        for command in &mut self.commands {
            command.execute();
        }
    }
    
    fn undo_all(&mut self) {
        for command in &mut self.commands {
            command.undo();
        }
    }
}
```

## 4. 解释器模式

### 4.1 解释器模式定义

**定义 4.1.1** (解释器)
```
Interpreter = {interpret: Expression → Result}
```

**定义 4.1.2** (表达式层次)
```
Expression_Hierarchy = {
    Terminal_Expression: Expression,
    Non_Terminal_Expression: Expression + Children,
    Context: Expression_Context
}
```

### 4.2 Rust中的解释器实现

**示例 4.2.1** (解释器模式)
```rust
// 上下文
struct Context {
    variables: std::collections::HashMap<String, i32>,
}

impl Context {
    fn new() -> Self {
        Context {
            variables: std::collections::HashMap::new(),
        }
    }
    
    fn set_variable(&mut self, name: &str, value: i32) {
        self.variables.insert(name.to_string(), value);
    }
    
    fn get_variable(&self, name: &str) -> Option<&i32> {
        self.variables.get(name)
    }
}

// 表达式特征
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
}

// 终端表达式
struct TerminalExpression {
    name: String,
}

impl TerminalExpression {
    fn new(name: String) -> Self {
        TerminalExpression { name }
    }
}

impl Expression for TerminalExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get_variable(&self.name).copied().unwrap_or(0)
    }
}

// 非终端表达式：加法
struct AddExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl AddExpression {
    fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        AddExpression { left, right }
    }
}

impl Expression for AddExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }
}

// 非终端表达式：减法
struct SubtractExpression {
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
}

impl SubtractExpression {
    fn new(left: Box<dyn Expression>, right: Box<dyn Expression>) -> Self {
        SubtractExpression { left, right }
    }
}

impl Expression for SubtractExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) - self.right.interpret(context)
    }
}
```

## 5. 迭代器模式

### 5.1 迭代器模式定义

**定义 5.1.1** (迭代器)
```
Iterator = {next: () → Option<Item>, has_next: () → bool}
```

**定义 5.1.2** (迭代器保证)
```
Iterator_Guarantee = {
    Traversal: ∀i ∈ Iterator, Next(i) → Option<Item>,
    Termination: ∀i ∈ Iterator, Has_Next(i) → bool,
    Consistency: ∀i ∈ Iterator, Consistent(i)
}
```

### 5.2 Rust中的迭代器实现

**示例 5.2.1** (迭代器模式)
```rust
// 聚合接口
trait Aggregate {
    fn create_iterator(&self) -> Box<dyn Iterator>;
}

// 具体聚合
struct ConcreteAggregate {
    items: Vec<String>,
}

impl ConcreteAggregate {
    fn new() -> Self {
        ConcreteAggregate {
            items: Vec::new(),
        }
    }
    
    fn add_item(&mut self, item: String) {
        self.items.push(item);
    }
    
    fn get_items(&self) -> &Vec<String> {
        &self.items
    }
}

impl Aggregate for ConcreteAggregate {
    fn create_iterator(&self) -> Box<dyn Iterator> {
        Box::new(ConcreteIterator::new(self.items.clone()))
    }
}

// 迭代器特征
trait Iterator {
    fn next(&mut self) -> Option<String>;
    fn has_next(&self) -> bool;
}

// 具体迭代器
struct ConcreteIterator {
    items: Vec<String>,
    position: usize,
}

impl ConcreteIterator {
    fn new(items: Vec<String>) -> Self {
        ConcreteIterator {
            items,
            position: 0,
        }
    }
}

impl Iterator for ConcreteIterator {
    fn next(&mut self) -> Option<String> {
        if self.has_next() {
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

## 6. 中介者模式

### 6.1 中介者模式定义

**定义 6.1.1** (中介者)
```
Mediator = {mediate: Colleague → Colleague → Message}
```

**定义 6.1.2** (中介者保证)
```
Mediator_Guarantee = {
    Decoupling: ∀c1, c2 ∈ Colleague, ¬Direct_Communication(c1, c2),
    Centralization: ∀m ∈ Message, Mediate(Mediator, m),
    Coordination: ∀c ∈ Colleague, Coordinate(Mediator, c)
}
```

### 6.2 Rust中的中介者实现

**示例 6.2.1** (中介者模式)
```rust
// 中介者特征
trait Mediator {
    fn send(&self, message: &str, colleague: &dyn Colleague);
}

// 同事特征
trait Colleague {
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>);
    fn send(&self, message: &str);
    fn receive(&self, message: &str);
    fn get_name(&self) -> &str;
}

// 具体中介者
struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague>>,
}

impl ConcreteMediator {
    fn new() -> Self {
        ConcreteMediator {
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
            if colleague.get_name() != sender.get_name() {
                colleague.receive(message);
            }
        }
    }
}

// 具体同事A
struct ConcreteColleagueA {
    mediator: Option<Box<dyn Mediator>>,
    name: String,
}

impl ConcreteColleagueA {
    fn new(name: String) -> Self {
        ConcreteColleagueA {
            mediator: None,
            name,
        }
    }
}

impl Colleague for ConcreteColleagueA {
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = &self.mediator {
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("ColleagueA {} received: {}", self.name, message);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 具体同事B
struct ConcreteColleagueB {
    mediator: Option<Box<dyn Mediator>>,
    name: String,
}

impl ConcreteColleagueB {
    fn new(name: String) -> Self {
        ConcreteColleagueB {
            mediator: None,
            name,
        }
    }
}

impl Colleague for ConcreteColleagueB {
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = &self.mediator {
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("ColleagueB {} received: {}", self.name, message);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}
```

## 7. 备忘录模式

### 7.1 备忘录模式定义

**定义 7.1.1** (备忘录)
```
Memento = {state: State, restore: () → State}
```

**定义 7.1.2** (备忘录保证)
```
Memento_Guarantee = {
    State_Preservation: ∀m ∈ Memento, Preserve(m, State),
    Restoration: ∀m ∈ Memento, Restore(m) → Previous_State,
    Encapsulation: ∀m ∈ Memento, Encapsulate(m, State)
}
```

### 7.2 Rust中的备忘录实现

**示例 7.2.1** (备忘录模式)
```rust
// 备忘录
struct Memento {
    state: String,
}

impl Memento {
    fn new(state: String) -> Self {
        Memento { state }
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
        Originator {
            state: "initial".to_string(),
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
        Caretaker {
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

## 8. 观察者模式

### 8.1 观察者模式定义

**定义 8.1.1** (观察者)
```
Observer = {update: Subject → Notification}
```

**定义 8.1.2** (观察者保证)
```
Observer_Guarantee = {
    Notification: ∀s ∈ Subject, ∀o ∈ Observer, Notify(s, o),
    Decoupling: ∀s ∈ Subject, ∀o ∈ Observer, ¬Direct_Dependency(s, o),
    Consistency: ∀s ∈ Subject, Consistent(s, Observers(s))
}
```

### 8.2 Rust中的观察者实现

**示例 8.2.1** (观察者模式)
```rust
use std::collections::HashMap;

// 观察者特征
trait Observer {
    fn update(&self, subject: &dyn Subject);
    fn get_id(&self) -> &str;
}

// 主题特征
trait Subject {
    fn attach(&mut self, observer: Box<dyn Observer>);
    fn detach(&mut self, observer_id: &str);
    fn notify(&self);
    fn get_state(&self) -> &str;
    fn set_state(&mut self, state: String);
}

// 具体主题
struct ConcreteSubject {
    observers: HashMap<String, Box<dyn Observer>>,
    state: String,
}

impl ConcreteSubject {
    fn new() -> Self {
        ConcreteSubject {
            observers: HashMap::new(),
            state: "initial".to_string(),
        }
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Box<dyn Observer>) {
        let id = observer.get_id().to_string();
        self.observers.insert(id, observer);
    }
    
    fn detach(&mut self, observer_id: &str) {
        self.observers.remove(observer_id);
    }
    
    fn notify(&self) {
        for observer in self.observers.values() {
            observer.update(self);
        }
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
    
    fn set_state(&mut self, state: String) {
        self.state = state;
        self.notify();
    }
}

// 具体观察者A
struct ConcreteObserverA {
    id: String,
}

impl ConcreteObserverA {
    fn new(id: String) -> Self {
        ConcreteObserverA { id }
    }
}

impl Observer for ConcreteObserverA {
    fn update(&self, subject: &dyn Subject) {
        println!("ObserverA {} received update: {}", self.id, subject.get_state());
    }
    
    fn get_id(&self) -> &str {
        &self.id
    }
}

// 具体观察者B
struct ConcreteObserverB {
    id: String,
}

impl ConcreteObserverB {
    fn new(id: String) -> Self {
        ConcreteObserverB { id }
    }
}

impl Observer for ConcreteObserverB {
    fn update(&self, subject: &dyn Subject) {
        println!("ObserverB {} received update: {}", self.id, subject.get_state());
    }
    
    fn get_id(&self) -> &str {
        &self.id
    }
}
```

## 9. 状态模式

### 9.1 状态模式定义

**定义 9.1.1** (状态)
```
State = {handle: Context → Result, transition: Context → State}
```

**定义 9.1.2** (状态保证)
```
State_Guarantee = {
    State_Transition: ∀c ∈ Context, ∀s ∈ State, Transition(c, s) → New_State,
    Behavior_Change: ∀c ∈ Context, ∀s ∈ State, Behavior(c, s),
    Consistency: ∀c ∈ Context, Consistent(c, Current_State(c))
}
```

### 9.2 Rust中的状态实现

**示例 9.2.1** (状态模式)
```rust
// 状态特征
trait State {
    fn handle(&self, context: &mut Context);
    fn get_name(&self) -> &str;
}

// 上下文
struct Context {
    state: Box<dyn State>,
}

impl Context {
    fn new() -> Self {
        Context {
            state: Box::new(ConcreteStateA),
        }
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }
    
    fn request(&mut self) {
        self.state.handle(self);
    }
}

// 具体状态A
struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) {
        println!("StateA: handling request");
        context.set_state(Box::new(ConcreteStateB));
    }
    
    fn get_name(&self) -> &str {
        "StateA"
    }
}

// 具体状态B
struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) {
        println!("StateB: handling request");
        context.set_state(Box::new(ConcreteStateA));
    }
    
    fn get_name(&self) -> &str {
        "StateB"
    }
}
```

## 10. 策略模式

### 10.1 策略模式定义

**定义 10.1.1** (策略)
```
Strategy = {algorithm: Input → Output}
```

**定义 10.1.2** (策略保证)
```
Strategy_Guarantee = {
    Algorithm_Selection: ∀s ∈ Strategy, Select(s) → Algorithm(s),
    Interchangeability: ∀s1, s2 ∈ Strategy, Interchangeable(s1, s2),
    Encapsulation: ∀s ∈ Strategy, Encapsulate(s, Algorithm)
}
```

### 10.2 Rust中的策略实现

**示例 10.2.1** (策略模式)
```rust
// 策略特征
trait Strategy {
    fn algorithm(&self, data: &[i32]) -> i32;
}

// 具体策略A：求和
struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn algorithm(&self, data: &[i32]) -> i32 {
        data.iter().sum()
    }
}

// 具体策略B：求最大值
struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn algorithm(&self, data: &[i32]) -> i32 {
        data.iter().max().copied().unwrap_or(0)
    }
}

// 具体策略C：求最小值
struct ConcreteStrategyC;

impl Strategy for ConcreteStrategyC {
    fn algorithm(&self, data: &[i32]) -> i32 {
        data.iter().min().copied().unwrap_or(0)
    }
}

// 上下文
struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Context { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }
    
    fn execute_strategy(&self, data: &[i32]) -> i32 {
        self.strategy.algorithm(data)
    }
}
```

## 11. 模板方法模式

### 11.1 模板方法模式定义

**定义 11.1.1** (模板方法)
```
Template_Method = {template: () → Result, primitive_operations: Vec<Operation>}
```

**定义 11.1.2** (模板保证)
```
Template_Guarantee = {
    Algorithm_Skeleton: ∀t ∈ Template, Skeleton(t) → Fixed_Structure,
    Primitive_Operations: ∀t ∈ Template, Primitives(t) → Overridable,
    Invariant_Order: ∀t ∈ Template, Invariant(t, Operation_Order)
}
```

### 11.2 Rust中的模板方法实现

**示例 11.2.1** (模板方法模式)
```rust
// 抽象类
trait AbstractClass {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation_1());
        result.push_str("\n");
        result.push_str(&self.primitive_operation_2());
        result.push_str("\n");
        result.push_str(&self.hook());
        result
    }
    
    fn primitive_operation_1(&self) -> String;
    fn primitive_operation_2(&self) -> String;
    
    // 钩子方法
    fn hook(&self) -> String {
        "AbstractClass: hook".to_string()
    }
}

// 具体类A
struct ConcreteClassA;

impl AbstractClass for ConcreteClassA {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassA: primitive_operation_1".to_string()
    }
    
    fn primitive_operation_2(&self) -> String {
        "ConcreteClassA: primitive_operation_2".to_string()
    }
}

// 具体类B
struct ConcreteClassB;

impl AbstractClass for ConcreteClassB {
    fn primitive_operation_1(&self) -> String {
        "ConcreteClassB: primitive_operation_1".to_string()
    }
    
    fn primitive_operation_2(&self) -> String {
        "ConcreteClassB: primitive_operation_2".to_string()
    }
    
    fn hook(&self) -> String {
        "ConcreteClassB: overridden hook".to_string()
    }
}
```

## 12. 访问者模式

### 12.1 访问者模式定义

**定义 12.1.1** (访问者)
```
Visitor = {visit: Element → Result}
```

**定义 12.1.2** (访问者保证)
```
Visitor_Guarantee = {
    Operation_Separation: ∀v ∈ Visitor, ∀e ∈ Element, Separate(v, e),
    Extensibility: ∀v ∈ Visitor, Extensible(v, New_Operation),
    Double_Dispatch: ∀v ∈ Visitor, ∀e ∈ Element, Double_Dispatch(v, e)
}
```

### 12.2 Rust中的访问者实现

**示例 12.2.1** (访问者模式)
```rust
// 元素特征
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
    fn get_name(&self) -> &str;
}

// 访问者特征
trait Visitor {
    fn visit_element_a(&self, element: &ConcreteElementA);
    fn visit_element_b(&self, element: &ConcreteElementB);
}

// 具体元素A
struct ConcreteElementA {
    name: String,
}

impl ConcreteElementA {
    fn new(name: String) -> Self {
        ConcreteElementA { name }
    }
}

impl Element for ConcreteElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_a(self);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 具体元素B
struct ConcreteElementB {
    name: String,
}

impl ConcreteElementB {
    fn new(name: String) -> Self {
        ConcreteElementB { name }
    }
}

impl Element for ConcreteElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_b(self);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 具体访问者A
struct ConcreteVisitorA;

impl Visitor for ConcreteVisitorA {
    fn visit_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorA visiting ElementA: {}", element.get_name());
    }
    
    fn visit_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorA visiting ElementB: {}", element.get_name());
    }
}

// 具体访问者B
struct ConcreteVisitorB;

impl Visitor for ConcreteVisitorB {
    fn visit_element_a(&self, element: &ConcreteElementA) {
        println!("VisitorB visiting ElementA: {}", element.get_name());
    }
    
    fn visit_element_b(&self, element: &ConcreteElementB) {
        println!("VisitorB visiting ElementB: {}", element.get_name());
    }
}

// 对象结构
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
}

impl ObjectStructure {
    fn new() -> Self {
        ObjectStructure {
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

## 13. 总结与展望

### 13.1 行为型模式成就

Rust中行为型模式的成就：

1. **职责分配**：清晰的对象间职责分配
2. **通信机制**：灵活的对象间通信方式
3. **算法封装**：优雅的算法封装和选择
4. **状态管理**：有效的对象状态管理
5. **行为扩展**：动态的行为扩展能力

### 13.2 未来发展方向

行为型模式在Rust中的发展方向：

1. **模式组合**：更复杂的行为模式组合
2. **性能优化**：更高效的行为模式实现
3. **类型安全**：更强的编译时行为检查

### 13.3 行为型价值

行为型模式在Rust中的价值：

**形式化总结**：
```
Behavioral_Value = {
    Responsibility_Distribution: Clear,
    Communication_Mechanism: Flexible,
    Algorithm_Encapsulation: Elegant,
    State_Management: Effective,
    Behavior_Extension: Dynamic
}
```

---

## 参考文献

1. Gamma, E. et al. (1994). "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Rust Team (2021). "The Rust Programming Language"
3. Freeman, A. (2009). "Pro Design Patterns in C#"
4. Nystrom, R. (2014). "Game Programming Patterns"

## 相关文档

- [01_creational_patterns.md](./01_creational_patterns.md) - 创建型设计模式
- [02_structural_patterns.md](./02_structural_patterns.md) - 结构型设计模式
- [04_concurrent_patterns.md](./04_concurrent_patterns.md) - 并发设计模式
- [05_functional_patterns.md](./05_functional_patterns.md) - 函数式设计模式 