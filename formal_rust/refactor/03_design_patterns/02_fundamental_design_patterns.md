# 03. 基础设计模式

## 📚 相关文档引用

### 🏛️ 理论基础

- [Rust语言哲学基础](../01_foundational_theory/03_rust_language_philosophy.md) - 设计模式的哲学基础
- [理论基础概述](../01_foundational_theory/00_readme.md) - 理论基础整体框架

### 🔄 编程范式

- [Rust哲学形式化](../02_programming_paradigms/04_rust_philosophy_formalization.md) - 哲学思想的形式化表达
- [设计原则形式化](../02_programming_paradigms/07_design_principles_formalization.md) - 设计原则的形式化理论
- [架构模式形式化](../02_programming_paradigms/06_architectural_patterns_formalization.md) - 架构模式形式化

### 🎨 设计模式

- [设计模式概述](../03_design_patterns/00_readme.md) - 设计模式整体概述
- [创建型模式](../03_design_patterns/03_creational_patterns.md) - 创建型模式详细内容
- [结构型模式](../03_design_patterns/04_structural_patterns.md) - 结构型模式详细内容
- [行为型模式](../03_design_patterns/05_behavioral_patterns.md) - 行为型模式详细内容
- [创建型模式形式化](../03_design_patterns/06_creational_patterns_formalization.md) - 创建型模式形式化
- [结构型模式形式化](../03_design_patterns/07_structural_patterns_formalization.md) - 结构型模式形式化
- [行为型模式形式化](../03_design_patterns/08_behavioral_patterns_formalization.md) - 行为型模式形式化
- [高级创建型模式](../03_design_patterns/09_creational_patterns_advanced.md) - 高级创建型模式

### 🦀 Rust语言理论

- [所有权系统形式化](../08_rust_language_theory/01_ownership_system_formalization.md) - 所有权系统在设计模式中的应用
- [类型系统形式化](../08_rust_language_theory/03_type_system_formalization.md) - 类型系统在设计模式中的应用
- [Trait系统形式化](../08_rust_language_theory/08_trait_system_formalization.md) - Trait系统在设计模式中的应用
- [泛型系统形式化](../08_rust_language_theory/09_generic_system_formalization.md) - 泛型系统在设计模式中的应用

### ⚡ 并发模式

- [高级并发形式化](../05_concurrent_patterns/02_advanced_concurrency_formalization.md) - 并发模式与设计模式的结合
- [Actor模型形式化](../05_concurrent_patterns/14_actor_model_formalization.md) - Actor模式与设计模式的结合
- [Future/Promise模式形式化](../05_concurrent_patterns/13_future_promise_pattern_formalization.md) - Future/Promise模式与设计模式的结合

### 🏭 行业应用

- [金融科技形式化](../04_industry_applications/09_fintech_formalization.md) - 设计模式在金融科技中的应用
- [AI/ML形式化](../04_industry_applications/17_ai_ml_formalization.md) - 设计模式在AI/ML中的应用
- [区块链形式化](../04_industry_applications/19_blockchain_formalization.md) - 设计模式在区块链中的应用

### 🎯 高级模式

- [创建型模式形式化](../12_advanced_patterns/01_creational_patterns_formalization.md) - 高级创建型模式形式化
- [结构型模式形式化](../12_advanced_patterns/04_structural_patterns_formalization.md) - 高级结构型模式形式化
- [响应式模式](../12_advanced_patterns/03_reactive_patterns.md) - 响应式设计模式

---

## 目录

### 1. 设计模式理论基础

#### 1.1 概念与定义

#### 1.2 分类体系

#### 1.3 形式化表达

### 2. 创建型模式 (Creational Patterns)

#### 2.1 单例模式 (Singleton)

#### 2.2 工厂方法模式 (Factory Method)

#### 2.3 抽象工厂模式 (Abstract Factory)

#### 2.4 建造者模式 (Builder)

#### 2.5 原型模式 (Prototype)

### 3. 结构型模式 (Structural Patterns)

#### 3.1 适配器模式 (Adapter)

#### 3.2 桥接模式 (Bridge)

#### 3.3 组合模式 (Composite)

#### 3.4 装饰器模式 (Decorator)

#### 3.5 外观模式 (Facade)

#### 3.6 享元模式 (Flyweight)

#### 3.7 代理模式 (Proxy)

### 4. 行为型模式 (Behavioral Patterns)

#### 4.1 责任链模式 (Chain of Responsibility)

#### 4.2 命令模式 (Command)

#### 4.3 解释器模式 (Interpreter)

#### 4.4 迭代器模式 (Iterator)

#### 4.5 中介者模式 (Mediator)

#### 4.6 备忘录模式 (Memento)

#### 4.7 观察者模式 (Observer)

#### 4.8 状态模式 (State)

#### 4.9 策略模式 (Strategy)

#### 4.10 模板方法模式 (Template Method)

#### 4.11 访问者模式 (Visitor)

---

## 1. 设计模式理论基础

### 1.1 概念与定义

**设计模式定义**：

```
DesignPattern : Problem → Solution
∀problem ∈ DesignProblem | DesignPattern(problem) = 
  {solution, context, consequences}
```

> **哲学基础**: 关于设计模式的哲学思考，请参考 [Rust语言哲学基础](../01_foundational_theory/03_rust_language_philosophy.md) 中的 [约束性设计原则](#32-有效形式模型的探索原则)。

**模式结构**：

```
PatternStructure : Pattern → Components
∀pattern ∈ Pattern | PatternStructure(pattern) = {
  name: String,
  intent: Problem,
  motivation: Context,
  applicability: Conditions,
  structure: UML,
  participants: Classes,
  collaborations: Interactions,
  consequences: Tradeoffs
}
```

**形式化表达**：

```
Pattern : (Context, Problem, Solution) → Design
∀c ∈ Context, ∀p ∈ Problem, ∀s ∈ Solution | 
  Pattern(c, p, s) = {context: c, problem: p, solution: s}
```

> **形式化理论**: 关于设计模式的形式化理论，请参考 [Rust哲学形式化](../02_programming_paradigms/04_rust_philosophy_formalization.md) 和 [设计原则形式化](../02_programming_paradigms/07_design_principles_formalization.md)。

### 1.2 分类体系

**按目的分类**：

```
PatternClassification : Pattern → Category
∀pattern ∈ Pattern | PatternClassification(pattern) ∈ {
  Creational, Structural, Behavioral
}
```

**按范围分类**：

```
PatternScope : Pattern → Scope
∀pattern ∈ Pattern | PatternScope(pattern) ∈ {
  Class, Object
}
```

**分类函数**：

```
CategorizePattern : Pattern → (Purpose, Scope)
∀p ∈ Pattern | CategorizePattern(p) = 
  (p.purpose, p.scope)
```

> **详细分类**: 关于各种模式的详细分类，请参考 [创建型模式](../03_design_patterns/03_creational_patterns.md)、[结构型模式](../03_design_patterns/04_structural_patterns.md) 和 [行为型模式](../03_design_patterns/05_behavioral_patterns.md)。

### 1.3 形式化表达

**模式实例化**：

```
PatternInstantiation : Pattern → Instance
∀pattern ∈ Pattern | PatternInstantiation(pattern) = 
  apply_pattern(pattern, concrete_context)
```

**模式组合**：

```
PatternComposition : [Pattern] → CompositePattern
∀patterns ∈ [Pattern] | PatternComposition(patterns) = 
  combine_patterns(patterns)
```

> **高级模式**: 关于高级模式的形式化，请参考 [创建型模式形式化](../03_design_patterns/06_creational_patterns_formalization.md)、[结构型模式形式化](../03_design_patterns/07_structural_patterns_formalization.md) 和 [行为型模式形式化](../03_design_patterns/08_behavioral_patterns_formalization.md)。

---

## 2. 创建型模式 (Creational Patterns)

### 2.1 单例模式 (Singleton)

**定义**：保证一个类仅有一个实例，并提供一个访问它的全局访问点。

**形式化表达**：

```
Singleton : Class → Instance
∀class ∈ Class | Singleton(class) = {
  instance: Option<Instance>,
  get_instance: () → Instance
}
```

**约束条件**：

```
SingletonConstraints : Class → Boolean
∀class ∈ Class | SingletonConstraints(class) = 
  |instances(class)| = 1 ∧ 
  global_access(class) ∧ 
  lazy_initialization(class)
```

> **所有权应用**: 关于单例模式中所有权系统的应用，请参考 [所有权系统形式化](../08_rust_language_theory/01_ownership_system_formalization.md)。

**Rust实现**：

```rust
use std::sync::{Mutex, Once, ONCE_INIT};
use std::mem;

#[derive(Debug)]
struct SingletonLogger {
    level: String,
}

static mut SINGLETON_INSTANCE: *const Mutex<SingletonLogger> = 0 as *const _;
static ONCE: Once = ONCE_INIT;

impl SingletonLogger {
    fn get_instance() -> &'static Mutex<SingletonLogger> {
        ONCE.call_once(|| {
            let singleton = Mutex::new(SingletonLogger {
                level: "INFO".to_string(),
            });
            unsafe {
                SINGLETON_INSTANCE = Box::into_raw(Box::new(singleton));
            }
        });
        unsafe { &*SINGLETON_INSTANCE }
    }

    fn log(&self, message: &str) {
        println!("[{}] {}", self.level, message);
    }
}
```

**形式化验证**：

```
Theorem: SingletonUniqueness
∀s1, s2 ∈ SingletonInstance | s1 = s2
```

### 2.2 工厂方法模式 (Factory Method)

**定义**：定义一个用于创建对象的接口，让子类决定实例化哪一个类。

**形式化表达**：

```
FactoryMethod : Creator → Product
∀creator ∈ Creator | FactoryMethod(creator) = 
  creator.factory_method()
```

**类型关系**：

```
FactoryMethodTypes : (Creator, Product) → Relationship
∀creator ∈ Creator, ∀product ∈ Product | 
  FactoryMethodTypes(creator, product) = 
    creator → product : creates
```

**Rust实现**：

```rust
// 产品trait
trait Product {
    fn operation(&self) -> String;
}

// 具体产品A
struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "ConcreteProductA operation".to_string()
    }
}

// 具体产品B
struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "ConcreteProductB operation".to_string()
    }
}

// 创建者trait
trait Creator {
    type ProductType: Product;
    fn factory_method(&self) -> Self::ProductType;
}

// 具体创建者A
struct ConcreteCreatorA;
impl Creator for ConcreteCreatorA {
    type ProductType = ConcreteProductA;
    fn factory_method(&self) -> Self::ProductType {
        ConcreteProductA
    }
}

// 具体创建者B
struct ConcreteCreatorB;
impl Creator for ConcreteCreatorB {
    type ProductType = ConcreteProductB;
    fn factory_method(&self) -> Self::ProductType {
        ConcreteProductB
    }
}
```

### 2.3 抽象工厂模式 (Abstract Factory)

**定义**：提供一个创建一系列相关或相互依赖对象的接口，而无需指定它们的具体类。

**形式化表达**：

```
AbstractFactory : Factory → ProductFamily
∀factory ∈ Factory | AbstractFactory(factory) = 
  {product_a: factory.create_product_a(),
   product_b: factory.create_product_b()}
```

**产品族约束**：

```
ProductFamilyConstraint : ProductFamily → Boolean
∀family ∈ ProductFamily | ProductFamilyConstraint(family) = 
  compatible(family.product_a, family.product_b)
```

### 2.4 建造者模式 (Builder)

**定义**：将一个复杂对象的构建与它的表示分离，使得同样的构建过程可以创建不同的表示。

**形式化表达**：

```
Builder : Builder → Product
∀builder ∈ Builder | Builder(builder) = 
  builder.build()
```

**构建过程**：

```
BuildProcess : Builder → [Step]
∀builder ∈ Builder | BuildProcess(builder) = 
  [step_1, step_2, ..., step_n]
```

### 2.5 原型模式 (Prototype)

**定义**：用原型实例指定创建对象的种类，并且通过复制这些原型创建新的对象。

**形式化表达**：

```
Prototype : Prototype → Clone
∀prototype ∈ Prototype | Prototype(prototype) = 
  prototype.clone()
```

**克隆操作**：

```
CloneOperation : Object → Object
∀obj ∈ Object | CloneOperation(obj) = 
  deep_copy(obj) ∨ shallow_copy(obj)
```

---

## 3. 结构型模式 (Structural Patterns)

### 3.1 适配器模式 (Adapter)

**定义**：将一个类的接口转换成客户希望的另外一个接口。

**形式化表达**：

```
Adapter : (Target, Adaptee) → Adapted
∀target ∈ Target, ∀adaptee ∈ Adaptee | 
  Adapter(target, adaptee) = adapt_interface(adaptee, target)
```

**接口映射**：

```
InterfaceMapping : (SourceInterface, TargetInterface) → Mapping
∀source ∈ SourceInterface, ∀target ∈ TargetInterface | 
  InterfaceMapping(source, target) = 
    {source.method → target.method}
```

### 3.2 桥接模式 (Bridge)

**定义**：将抽象部分与实现部分分离，使它们都可以独立地变化。

**形式化表达**：

```
Bridge : (Abstraction, Implementation) → Bridge
∀abstraction ∈ Abstraction, ∀implementation ∈ Implementation | 
  Bridge(abstraction, implementation) = 
    {abstraction, implementation, bridge_method}
```

**解耦关系**：

```
Decoupling : (Abstraction, Implementation) → Boolean
∀abs ∈ Abstraction, ∀impl ∈ Implementation | 
  Decoupling(abs, impl) = independent(abs, impl)
```

### 3.3 组合模式 (Composite)

**定义**：将对象组合成树形结构以表示"部分-整体"的层次结构。

**形式化表达**：

```
Composite : Component → Tree
∀component ∈ Component | Composite(component) = 
  if is_leaf(component) then leaf(component)
  else node(component, children(component))
```

**树结构**：

```
TreeStructure : Component → Structure
∀component ∈ Component | TreeStructure(component) = {
  root: component,
  children: [Component],
  operations: [Operation]
}
```

### 3.4 装饰器模式 (Decorator)

**定义**：动态地给一个对象添加一些额外的职责。

**形式化表达**：

```
Decorator : (Component, Decorator) → DecoratedComponent
∀component ∈ Component, ∀decorator ∈ Decorator | 
  Decorator(component, decorator) = 
    decorator.wrap(component)
```

**装饰链**：

```
DecorationChain : [Decorator] → Component → DecoratedComponent
∀decorators ∈ [Decorator], ∀component ∈ Component | 
  DecorationChain(decorators, component) = 
    fold(decorators, component, |acc, d| d.wrap(acc))
```

### 3.5 外观模式 (Facade)

**定义**：为子系统中的一组接口提供一个一致的界面。

**形式化表达**：

```
Facade : Subsystem → Interface
∀subsystem ∈ Subsystem | Facade(subsystem) = 
  unified_interface(subsystem)
```

**简化接口**：

```
SimplifiedInterface : ComplexInterface → SimpleInterface
∀complex ∈ ComplexInterface | SimplifiedInterface(complex) = 
  {essential_methods(complex)}
```

### 3.6 享元模式 (Flyweight)

**定义**：运用共享技术有效地支持大量细粒度对象的复用。

**形式化表达**：

```
Flyweight : (IntrinsicState, ExtrinsicState) → Flyweight
∀intrinsic ∈ IntrinsicState, ∀extrinsic ∈ ExtrinsicState | 
  Flyweight(intrinsic, extrinsic) = 
    {shared: intrinsic, unique: extrinsic}
```

**共享池**：

```
SharedPool : Flyweight → Pool
∀flyweight ∈ Flyweight | SharedPool(flyweight) = 
  pool.get_or_create(flyweight.intrinsic_state)
```

### 3.7 代理模式 (Proxy)

**定义**：为其他对象提供一种代理以控制对这个对象的访问。

**形式化表达**：

```
Proxy : Subject → ControlledAccess
∀subject ∈ Subject | Proxy(subject) = 
  {access_control, subject}
```

**访问控制**：

```
AccessControl : (Subject, Client) → Permission
∀subject ∈ Subject, ∀client ∈ Client | 
  AccessControl(subject, client) = 
    check_permission(client, subject)
```

---

## 4. 行为型模式 (Behavioral Patterns)

### 4.1 责任链模式 (Chain of Responsibility)

**定义**：使多个对象都有机会处理请求，从而避免请求的发送者和接收者之间的耦合关系。

**形式化表达**：

```
ChainOfResponsibility : [Handler] → Request → Response
∀handlers ∈ [Handler], ∀request ∈ Request | 
  ChainOfResponsibility(handlers, request) = 
    process_chain(handlers, request)
```

**处理链**：

```
ProcessingChain : Handler → Handler
∀handler ∈ Handler | ProcessingChain(handler) = 
  if can_handle(handler, request) then handle(handler, request)
  else next_handler(handler).process(request)
```

### 4.2 命令模式 (Command)

**定义**：将一个请求封装为一个对象，从而使你可用不同的请求对客户进行参数化。

**形式化表达**：

```
Command : (Receiver, Action) → Command
∀receiver ∈ Receiver, ∀action ∈ Action | 
  Command(receiver, action) = 
    {execute: λ() → action(receiver)}
```

**命令执行**：

```
CommandExecution : Command → Result
∀command ∈ Command | CommandExecution(command) = 
  command.execute()
```

### 4.3 解释器模式 (Interpreter)

**定义**：给定一个语言，定义它的文法的一种表示，并定义一个解释器，这个解释器使用该表示来解释语言中的句子。

**形式化表达**：

```
Interpreter : (Grammar, Expression) → Result
∀grammar ∈ Grammar, ∀expression ∈ Expression | 
  Interpreter(grammar, expression) = 
    interpret(grammar, expression)
```

**语法树**：

```
SyntaxTree : Expression → Tree
∀expression ∈ Expression | SyntaxTree(expression) = 
  parse(expression)
```

### 4.4 迭代器模式 (Iterator)

**定义**：提供一种方法顺序访问一个聚合对象中的各个元素，而又不暴露其内部的表示。

**形式化表达**：

```
Iterator : Aggregate → Iterator
∀aggregate ∈ Aggregate | Iterator(aggregate) = 
  aggregate.create_iterator()
```

**迭代操作**：

```
IterationOperations : Iterator → Operations
∀iterator ∈ Iterator | IterationOperations(iterator) = {
  next: () → Option<Element>,
  has_next: () → Boolean,
  reset: () → Unit
}
```

### 4.5 中介者模式 (Mediator)

**定义**：用一个中介对象来封装一系列的对象交互。

**形式化表达**：

```
Mediator : [Colleague] → Mediator
∀colleagues ∈ [Colleague] | Mediator(colleagues) = 
  {mediate: λ(from, to, message) → route_message(from, to, message)}
```

**消息路由**：

```
MessageRouting : (From, To, Message) → RoutedMessage
∀from ∈ Colleague, ∀to ∈ Colleague, ∀message ∈ Message | 
  MessageRouting(from, to, message) = 
    mediator.route(from, to, message)
```

### 4.6 备忘录模式 (Memento)

**定义**：在不破坏封装的前提下，捕获并外部化对象的内部状态。

**形式化表达**：

```
Memento : Originator → Memento
∀originator ∈ Originator | Memento(originator) = 
  {state: originator.get_state()}
```

**状态保存**：

```
StatePreservation : Originator → Memento
∀originator ∈ Originator | StatePreservation(originator) = 
  save_state(originator)
```

### 4.7 观察者模式 (Observer)

**定义**：定义对象间的一种一对多的依赖关系，当一个对象的状态发生改变时，所有依赖于它的对象都得到通知并被自动更新。

**形式化表达**：

```
Observer : (Subject, [Observer]) → Notification
∀subject ∈ Subject, ∀observers ∈ [Observer] | 
  Observer(subject, observers) = 
    notify_all(subject, observers)
```

**通知机制**：

```
NotificationMechanism : Subject → [Observer] → Unit
∀subject ∈ Subject, ∀observers ∈ [Observer] | 
  NotificationMechanism(subject, observers) = 
    for observer in observers { observer.update(subject.state) }
```

### 4.8 状态模式 (State)

**定义**：允许一个对象在其内部状态改变时改变它的行为。

**形式化表达**：

```
State : Context → State
∀context ∈ Context | State(context) = 
  context.current_state
```

**状态转换**：

```
StateTransition : (Context, Event) → NewState
∀context ∈ Context, ∀event ∈ Event | 
  StateTransition(context, event) = 
    context.current_state.handle(event)
```

### 4.9 策略模式 (Strategy)

**定义**：定义一系列的算法，把它们一个个封装起来，并且使它们可以互相替换。

**形式化表达**：

```
Strategy : [Algorithm] → Context
∀algorithms ∈ [Algorithm] | Strategy(algorithms) = 
  {execute: λ(algorithm) → algorithm.compute()}
```

**算法选择**：

```
AlgorithmSelection : Context → Algorithm
∀context ∈ Context | AlgorithmSelection(context) = 
  context.select_algorithm()
```

### 4.10 模板方法模式 (Template Method)

**定义**：定义一个操作中的算法的骨架，而将一些步骤延迟到子类中。

**形式化表达**：

```
TemplateMethod : AbstractClass → Template
∀abstract_class ∈ AbstractClass | TemplateMethod(abstract_class) = 
  {template_method: λ() → {
    step1(),
    step2(),
    step3()
  }}
```

**步骤定义**：

```
StepDefinition : AbstractClass → [Step]
∀abstract_class ∈ AbstractClass | StepDefinition(abstract_class) = 
  [abstract_class.step1, abstract_class.step2, abstract_class.step3]
```

### 4.11 访问者模式 (Visitor)

**定义**：表示一个作用于某对象结构中的各元素的操作。

**形式化表达**：

```
Visitor : (Visitor, Element) → Result
∀visitor ∈ Visitor, ∀element ∈ Element | 
  Visitor(visitor, element) = 
    element.accept(visitor)
```

**双重分发**：

```
DoubleDispatch : (Visitor, Element) → Operation
∀visitor ∈ Visitor, ∀element ∈ Element | 
  DoubleDispatch(visitor, element) = 
    element.accept(visitor) ∧ visitor.visit(element)
```

---

## 结论

基础设计模式为软件设计提供了经过验证的解决方案。通过形式化的表达和Rust的具体实现，我们能够更好地理解和应用这些模式。

**核心设计原则**：

1. 开闭原则：对扩展开放，对修改封闭
2. 单一职责原则：一个类只负责一个职责
3. 里氏替换原则：子类可以替换父类
4. 接口隔离原则：客户端不应依赖它不需要的接口
5. 依赖倒置原则：依赖抽象而非具体实现

这些模式为后续的高级设计模式、并发模式和分布式模式提供了基础。
