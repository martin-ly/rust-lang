# 结构型设计模式

**日期**: 2025-01-27  
**版本**: 1.0.0  
**状态**: 完成

## 📋 目录

1. [结构型模式概述](#1-结构型模式概述)
2. [适配器模式 (Adapter Pattern)](#2-适配器模式-adapter-pattern)
3. [桥接模式 (Bridge Pattern)](#3-桥接模式-bridge-pattern)
4. [组合模式 (Composite Pattern)](#4-组合模式-composite-pattern)
5. [装饰器模式 (Decorator Pattern)](#5-装饰器模式-decorator-pattern)
6. [外观模式 (Facade Pattern)](#6-外观模式-facade-pattern)
7. [享元模式 (Flyweight Pattern)](#7-享元模式-flyweight-pattern)
8. [代理模式 (Proxy Pattern)](#8-代理模式-proxy-pattern)
9. [模式比较与选择](#9-模式比较与选择)

## 1. 结构型模式概述

### 1.1 形式化定义

结构型模式处理对象组合，形式化定义为：

$$\text{Structural}(T_1, T_2) = \{\text{Adapter}, \text{Bridge}, \text{Composite}, \text{Decorator}, \text{Facade}, \text{Flyweight}, \text{Proxy}\}$$

其中每个模式 $p \in \text{Structural}(T_1, T_2)$ 满足：

$$\forall p: \exists g: T_1 \rightarrow T_2 \text{ s.t. } g \text{ preserves structure}$$

### 1.2 核心原则

1. **接口适配**: 使不兼容的接口能够协同工作
2. **结构组合**: 将对象组合成树形结构
3. **功能扩展**: 动态地给对象添加新功能
4. **访问控制**: 控制对对象的访问

### 1.3 分类体系

```rust
enum StructuralPattern {
    Adapter(AdapterPattern),
    Bridge(BridgePattern),
    Composite(CompositePattern),
    Decorator(DecoratorPattern),
    Facade(FacadePattern),
    Flyweight(FlyweightPattern),
    Proxy(ProxyPattern),
}
```

## 2. 适配器模式 (Adapter Pattern)

### 2.1 形式化定义

适配器模式将一个类的接口转换成客户希望的另外一个接口。

$$\text{Adapter}(T_1, T_2) = \{(adapt, target) \mid adapt: T_1 \rightarrow T_2 \text{ s.t. } \text{Compatible}(T_1, T_2)\}$$

### 2.2 结构分析

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配的类
struct Adaptee {
    specific_request: String,
}

impl Adaptee {
    fn new() -> Self {
        Self {
            specific_request: "Specific request".to_string(),
        }
    }
    
    fn specific_request(&self) -> String {
        self.specific_request.clone()
    }
}

// 适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将特定的请求转换为目标接口
        format!("Adapter: {}", self.adaptee.specific_request())
    }
}
```

### 2.3 对象适配器

```rust
// 对象适配器 - 使用组合
struct ObjectAdapter {
    adaptee: Box<dyn AdapteeInterface>,
}

trait AdapteeInterface {
    fn specific_request(&self) -> String;
}

impl AdapteeInterface for Adaptee {
    fn specific_request(&self) -> String {
        self.specific_request.clone()
    }
}

impl Target for ObjectAdapter {
    fn request(&self) -> String {
        format!("ObjectAdapter: {}", self.adaptee.specific_request())
    }
}
```

### 2.4 类适配器

```rust
// 类适配器 - 使用继承（在Rust中通过trait实现）
trait AdapteeTrait {
    fn specific_request(&self) -> String;
}

impl AdapteeTrait for Adaptee {
    fn specific_request(&self) -> String {
        self.specific_request.clone()
    }
}

struct ClassAdapter {
    adaptee: Adaptee,
}

impl ClassAdapter {
    fn new() -> Self {
        Self {
            adaptee: Adaptee::new(),
        }
    }
}

impl Target for ClassAdapter {
    fn request(&self) -> String {
        format!("ClassAdapter: {}", self.adaptee.specific_request())
    }
}

impl AdapteeTrait for ClassAdapter {
    fn specific_request(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

### 2.5 双向适配器

```rust
// 双向适配器 - 支持两个方向的适配
struct BidirectionalAdapter {
    target: Box<dyn Target>,
    adaptee: Box<dyn AdapteeInterface>,
}

impl BidirectionalAdapter {
    fn new(target: Box<dyn Target>, adaptee: Box<dyn AdapteeInterface>) -> Self {
        Self { target, adaptee }
    }
    
    fn adapt_to_target(&self) -> String {
        self.target.request()
    }
    
    fn adapt_to_adaptee(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

### 2.6 性能分析

**时间复杂度**: $O(1)$ - 适配操作的时间复杂度为常数
**空间复杂度**: $O(1)$ - 只需要存储适配器对象
**内存安全**: ✅ 保证内存安全
**类型安全**: ✅ 保证类型安全

## 3. 桥接模式 (Bridge Pattern)

### 3.1 形式化定义

桥接模式将抽象部分与实现部分分离，使它们都可以独立地变化。

$$\text{Bridge}(A, I) = \{(abstract, implement) \mid abstract: A \rightarrow \text{Behavior}, implement: I \rightarrow \text{Behavior}\}$$

### 3.2 结构分析

```rust
// 实现接口
trait Implementor {
    fn operation_impl(&self) -> String;
}

// 具体实现A
struct ConcreteImplementorA;

impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorA operation".to_string()
    }
}

// 具体实现B
struct ConcreteImplementorB;

impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorB operation".to_string()
    }
}

// 抽象类
struct Abstraction {
    implementor: Box<dyn Implementor>,
}

impl Abstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Self { implementor }
    }
    
    fn operation(&self) -> String {
        format!("Abstraction: {}", self.implementor.operation_impl())
    }
}

// 扩展抽象类
struct RefinedAbstraction {
    abstraction: Abstraction,
}

impl RefinedAbstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Self {
            abstraction: Abstraction::new(implementor),
        }
    }
    
    fn refined_operation(&self) -> String {
        format!("Refined: {}", self.abstraction.operation())
    }
}
```

### 3.3 泛型桥接

```rust
// 泛型桥接模式
struct GenericAbstraction<T: Implementor> {
    implementor: T,
}

impl<T: Implementor> GenericAbstraction<T> {
    fn new(implementor: T) -> Self {
        Self { implementor }
    }
    
    fn operation(&self) -> String {
        format!("GenericAbstraction: {}", self.implementor.operation_impl())
    }
}

// 多实现桥接
trait MultiImplementor {
    fn operation_a(&self) -> String;
    fn operation_b(&self) -> String;
}

struct ConcreteMultiImplementor;

impl MultiImplementor for ConcreteMultiImplementor {
    fn operation_a(&self) -> String {
        "Operation A".to_string()
    }
    
    fn operation_b(&self) -> String {
        "Operation B".to_string()
    }
}

struct MultiAbstraction {
    implementor: Box<dyn MultiImplementor>,
}

impl MultiAbstraction {
    fn new(implementor: Box<dyn MultiImplementor>) -> Self {
        Self { implementor }
    }
    
    fn operation_a(&self) -> String {
        format!("MultiAbstraction: {}", self.implementor.operation_a())
    }
    
    fn operation_b(&self) -> String {
        format!("MultiAbstraction: {}", self.implementor.operation_b())
    }
}
```

### 3.4 性能分析

**时间复杂度**: $O(1)$ - 桥接操作的时间复杂度为常数
**空间复杂度**: $O(1)$ - 只需要存储实现对象
**解耦程度**: ✅ 抽象与实现完全分离
**扩展性**: ✅ 易于添加新的抽象和实现

## 4. 组合模式 (Composite Pattern)

### 4.1 形式化定义

组合模式将对象组合成树形结构以表示"部分-整体"的层次结构。

$$\text{Composite}(T) = \{(component, leaf, composite) \mid \text{Tree}(T) \land \text{Uniform}(T)\}$$

### 4.2 结构分析

```rust
// 组件接口
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>);
    fn remove(&mut self, component: &Box<dyn Component>);
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>>;
}

// 叶子节点
struct Leaf {
    name: String,
}

impl Leaf {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf {} operation", self.name)
    }
    
    fn add(&mut self, _component: Box<dyn Component>) {
        // 叶子节点不支持添加子组件
    }
    
    fn remove(&mut self, _component: &Box<dyn Component>) {
        // 叶子节点不支持移除子组件
    }
    
    fn get_child(&self, _index: usize) -> Option<&Box<dyn Component>> {
        None
    }
}

// 复合节点
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Composite {
    fn new(name: String) -> Self {
        Self {
            name,
            children: Vec::new(),
        }
    }
}

impl Component for Composite {
    fn operation(&self) -> String {
        let mut result = format!("Composite {} operation", self.name);
        for child in &self.children {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
    
    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }
    
    fn remove(&mut self, component: &Box<dyn Component>) {
        // 在实际实现中，需要比较组件来移除
        // 这里简化处理
    }
    
    fn get_child(&self, index: usize) -> Option<&Box<dyn Component>> {
        self.children.get(index)
    }
}
```

### 4.3 安全组合模式

```rust
// 安全组合模式 - 区分叶子节点和复合节点
trait ComponentSafe {
    fn operation(&self) -> String;
}

trait LeafComponent: ComponentSafe {}

trait CompositeComponent: ComponentSafe {
    fn add(&mut self, component: Box<dyn ComponentSafe>);
    fn remove(&mut self, index: usize);
    fn get_child(&self, index: usize) -> Option<&Box<dyn ComponentSafe>>;
}

struct SafeLeaf {
    name: String,
}

impl ComponentSafe for SafeLeaf {
    fn operation(&self) -> String {
        format!("SafeLeaf {} operation", self.name)
    }
}

impl LeafComponent for SafeLeaf {}

struct SafeComposite {
    name: String,
    children: Vec<Box<dyn ComponentSafe>>,
}

impl ComponentSafe for SafeComposite {
    fn operation(&self) -> String {
        let mut result = format!("SafeComposite {} operation", self.name);
        for child in &self.children {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
}

impl CompositeComponent for SafeComposite {
    fn add(&mut self, component: Box<dyn ComponentSafe>) {
        self.children.push(component);
    }
    
    fn remove(&mut self, index: usize) {
        if index < self.children.len() {
            self.children.remove(index);
        }
    }
    
    fn get_child(&self, index: usize) -> Option<&Box<dyn ComponentSafe>> {
        self.children.get(index)
    }
}
```

### 4.4 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是树中节点的数量
**空间复杂度**: $O(n)$ - 需要存储所有节点
**遍历效率**: ✅ 支持高效的树遍历
**内存效率**: ⚠️ 可能产生大量对象

## 5. 装饰器模式 (Decorator Pattern)

### 5.1 形式化定义

装饰器模式动态地给对象添加额外的职责。

$$\text{Decorator}(T) = \{(decorate, component) \mid decorate: T \rightarrow T \text{ s.t. } \text{Enhanced}(T)\}$$

### 5.2 结构分析

```rust
// 组件接口
trait Component {
    fn operation(&self) -> String;
}

// 具体组件
struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

// 装饰器基类
struct Decorator {
    component: Box<dyn Component>,
}

impl Decorator {
    fn new(component: Box<dyn Component>) -> Self {
        Self { component }
    }
}

impl Component for Decorator {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

// 具体装饰器A
struct ConcreteDecoratorA {
    decorator: Decorator,
}

impl ConcreteDecoratorA {
    fn new(component: Box<dyn Component>) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl Component for ConcreteDecoratorA {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorA({})", self.decorator.operation())
    }
}

// 具体装饰器B
struct ConcreteDecoratorB {
    decorator: Decorator,
}

impl ConcreteDecoratorB {
    fn new(component: Box<dyn Component>) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl Component for ConcreteDecoratorB {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorB({})", self.decorator.operation())
    }
}
```

### 5.3 泛型装饰器

```rust
// 泛型装饰器模式
struct GenericDecorator<T: Component> {
    component: T,
}

impl<T: Component> GenericDecorator<T> {
    fn new(component: T) -> Self {
        Self { component }
    }
}

impl<T: Component> Component for GenericDecorator<T> {
    fn operation(&self) -> String {
        format!("GenericDecorator({})", self.component.operation())
    }
}

// 功能装饰器
trait FunctionalDecorator<T> {
    fn decorate(&self, component: T) -> T;
}

struct LoggingDecorator;

impl<T: Component + Clone> FunctionalDecorator<T> for LoggingDecorator {
    fn decorate(&self, component: T) -> T {
        println!("Logging: {}", component.operation());
        component
    }
}

struct CachingDecorator {
    cache: HashMap<String, String>,
}

impl CachingDecorator {
    fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }
}

impl<T: Component + Clone> FunctionalDecorator<T> for CachingDecorator {
    fn decorate(&self, component: T) -> T {
        let operation = component.operation();
        if let Some(cached) = self.cache.get(&operation) {
            println!("Cached: {}", cached);
        } else {
            println!("New: {}", operation);
        }
        component
    }
}
```

### 5.4 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是装饰器的数量
**空间复杂度**: $O(n)$ - 需要存储所有装饰器
**灵活性**: ✅ 支持动态组合
**性能开销**: ⚠️ 多层装饰可能影响性能

## 6. 外观模式 (Facade Pattern)

### 6.1 形式化定义

外观模式为子系统中的一组接口提供一个一致的界面。

$$\text{Facade}(S) = \{(simplify, subsystem) \mid simplify: S \rightarrow \text{SimpleInterface}\}$$

### 6.2 结构分析

```rust
// 子系统A
struct SubsystemA;

impl SubsystemA {
    fn operation_a1(&self) -> String {
        "SubsystemA operation1".to_string()
    }
    
    fn operation_a2(&self) -> String {
        "SubsystemA operation2".to_string()
    }
}

// 子系统B
struct SubsystemB;

impl SubsystemB {
    fn operation_b1(&self) -> String {
        "SubsystemB operation1".to_string()
    }
    
    fn operation_b2(&self) -> String {
        "SubsystemB operation2".to_string()
    }
}

// 子系统C
struct SubsystemC;

impl SubsystemC {
    fn operation_c1(&self) -> String {
        "SubsystemC operation1".to_string()
    }
    
    fn operation_c2(&self) -> String {
        "SubsystemC operation2".to_string()
    }
}

// 外观
struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC,
}

impl Facade {
    fn new() -> Self {
        Self {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC,
        }
    }
    
    fn operation1(&self) -> String {
        format!(
            "Facade operation1:\n  {}\n  {}\n  {}",
            self.subsystem_a.operation_a1(),
            self.subsystem_b.operation_b1(),
            self.subsystem_c.operation_c1()
        )
    }
    
    fn operation2(&self) -> String {
        format!(
            "Facade operation2:\n  {}\n  {}\n  {}",
            self.subsystem_a.operation_a2(),
            self.subsystem_b.operation_b2(),
            self.subsystem_c.operation_c2()
        )
    }
}
```

### 6.3 智能外观

```rust
// 智能外观 - 根据上下文选择不同的操作
struct SmartFacade {
    subsystems: HashMap<String, Box<dyn Subsystem>>,
}

trait Subsystem {
    fn operation(&self) -> String;
}

impl Subsystem for SubsystemA {
    fn operation(&self) -> String {
        self.operation_a1()
    }
}

impl Subsystem for SubsystemB {
    fn operation(&self) -> String {
        self.operation_b1()
    }
}

impl Subsystem for SubsystemC {
    fn operation(&self) -> String {
        self.operation_c1()
    }
}

impl SmartFacade {
    fn new() -> Self {
        let mut subsystems = HashMap::new();
        subsystems.insert("A".to_string(), Box::new(SubsystemA));
        subsystems.insert("B".to_string(), Box::new(SubsystemB));
        subsystems.insert("C".to_string(), Box::new(SubsystemC));
        
        Self { subsystems }
    }
    
    fn operation(&self, context: &str) -> String {
        if let Some(subsystem) = self.subsystems.get(context) {
            format!("SmartFacade: {}", subsystem.operation())
        } else {
            "Unknown subsystem".to_string()
        }
    }
}
```

### 6.4 性能分析

**时间复杂度**: $O(1)$ - 外观操作的时间复杂度为常数
**空间复杂度**: $O(n)$ - 需要存储所有子系统
**简化程度**: ✅ 显著简化客户端接口
**耦合度**: ⚠️ 可能增加系统耦合

## 7. 享元模式 (Flyweight Pattern)

### 7.1 形式化定义

享元模式运用共享技术有效地支持大量细粒度对象的复用。

$$\text{Flyweight}(T) = \{(share, intrinsic, extrinsic) \mid \text{Shared}(T) \land \text{Intrinsic}(T)\}$$

### 7.2 结构分析

```rust
// 享元接口
trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
}

// 具体享元
struct ConcreteFlyweight {
    intrinsic_state: String,
}

impl ConcreteFlyweight {
    fn new(intrinsic_state: String) -> Self {
        Self { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!(
            "ConcreteFlyweight: intrinsic={}, extrinsic={}",
            self.intrinsic_state, extrinsic_state
        )
    }
}

// 享元工厂
struct FlyweightFactory {
    flyweights: HashMap<String, Box<dyn Flyweight>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        Self {
            flyweights: HashMap::new(),
        }
    }
    
    fn get_flyweight(&mut self, key: &str) -> &Box<dyn Flyweight> {
        if !self.flyweights.contains_key(key) {
            let flyweight = Box::new(ConcreteFlyweight::new(key.to_string()));
            self.flyweights.insert(key.to_string(), flyweight);
        }
        self.flyweights.get(key).unwrap()
    }
    
    fn count(&self) -> usize {
        self.flyweights.len()
    }
}
```

### 7.3 线程安全享元

```rust
use std::sync::{Arc, RwLock};

// 线程安全享元工厂
struct ThreadSafeFlyweightFactory {
    flyweights: Arc<RwLock<HashMap<String, Arc<dyn Flyweight + Send + Sync>>>>,
}

impl ThreadSafeFlyweightFactory {
    fn new() -> Self {
        Self {
            flyweights: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn get_flyweight(&self, key: &str) -> Arc<dyn Flyweight + Send + Sync> {
        {
            let flyweights = self.flyweights.read().unwrap();
            if let Some(flyweight) = flyweights.get(key) {
                return flyweight.clone();
            }
        }
        
        let flyweight = Arc::new(ConcreteFlyweight::new(key.to_string()));
        {
            let mut flyweights = self.flyweights.write().unwrap();
            flyweights.insert(key.to_string(), flyweight.clone());
        }
        flyweight
    }
}

// 为ConcreteFlyweight实现Send和Sync
unsafe impl Send for ConcreteFlyweight {}
unsafe impl Sync for ConcreteFlyweight {}
```

### 7.4 性能分析

**时间复杂度**: $O(1)$ - 享元查找的时间复杂度为常数
**空间复杂度**: $O(n)$ - 其中 $n$ 是不同享元的数量
**内存效率**: ✅ 显著减少内存使用
**线程安全**: ✅ 支持线程安全访问

## 8. 代理模式 (Proxy Pattern)

### 8.1 形式化定义

代理模式为其他对象提供一种代理以控制对这个对象的访问。

$$\text{Proxy}(T) = \{(control, subject) \mid control: \text{Access} \rightarrow T \text{ s.t. } \text{Controlled}(T)\}$$

### 8.2 结构分析

```rust
// 主题接口
trait Subject {
    fn request(&self) -> String;
}

// 真实主题
struct RealSubject;

impl Subject for RealSubject {
    fn request(&self) -> String {
        "RealSubject request".to_string()
    }
}

// 代理
struct Proxy {
    real_subject: Option<RealSubject>,
}

impl Proxy {
    fn new() -> Self {
        Self {
            real_subject: None,
        }
    }
    
    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(RealSubject);
        }
    }
}

impl Subject for Proxy {
    fn request(&self) -> String {
        if let Some(ref real_subject) = self.real_subject {
            format!("Proxy: {}", real_subject.request())
        } else {
            "Proxy: RealSubject not initialized".to_string()
        }
    }
}
```

### 8.3 虚拟代理

```rust
// 虚拟代理 - 延迟加载
struct VirtualProxy {
    real_subject: Option<RealSubject>,
}

impl VirtualProxy {
    fn new() -> Self {
        Self {
            real_subject: None,
        }
    }
    
    fn ensure_loaded(&mut self) {
        if self.real_subject.is_none() {
            println!("Loading RealSubject...");
            self.real_subject = Some(RealSubject);
        }
    }
}

impl Subject for VirtualProxy {
    fn request(&self) -> String {
        if let Some(ref real_subject) = self.real_subject {
            format!("VirtualProxy: {}", real_subject.request())
        } else {
            "VirtualProxy: RealSubject not loaded".to_string()
        }
    }
}
```

### 8.4 保护代理

```rust
// 保护代理 - 访问控制
struct ProtectionProxy {
    real_subject: RealSubject,
    access_level: AccessLevel,
}

#[derive(Clone, Copy, PartialEq)]
enum AccessLevel {
    Guest,
    User,
    Admin,
}

impl ProtectionProxy {
    fn new(access_level: AccessLevel) -> Self {
        Self {
            real_subject: RealSubject,
            access_level,
        }
    }
    
    fn check_access(&self, required_level: AccessLevel) -> bool {
        self.access_level as u8 >= required_level as u8
    }
}

impl Subject for ProtectionProxy {
    fn request(&self) -> String {
        if self.check_access(AccessLevel::User) {
            format!("ProtectionProxy: {}", self.real_subject.request())
        } else {
            "ProtectionProxy: Access denied".to_string()
        }
    }
}
```

### 8.5 缓存代理

```rust
use std::collections::HashMap;

// 缓存代理 - 结果缓存
struct CacheProxy {
    real_subject: RealSubject,
    cache: HashMap<String, String>,
}

impl CacheProxy {
    fn new() -> Self {
        Self {
            real_subject: RealSubject,
            cache: HashMap::new(),
        }
    }
}

impl Subject for CacheProxy {
    fn request(&self) -> String {
        let cache_key = "request".to_string();
        
        if let Some(cached_result) = self.cache.get(&cache_key) {
            format!("CacheProxy (cached): {}", cached_result)
        } else {
            let result = self.real_subject.request();
            // 在实际实现中，这里需要可变引用来更新缓存
            format!("CacheProxy (fresh): {}", result)
        }
    }
}
```

### 8.6 性能分析

**时间复杂度**: $O(1)$ - 代理操作的时间复杂度为常数
**空间复杂度**: $O(1)$ - 只需要存储代理对象
**访问控制**: ✅ 提供细粒度的访问控制
**性能优化**: ✅ 支持缓存和延迟加载

## 9. 模式比较与选择

### 9.1 模式对比表

| 模式 | 复杂度 | 性能 | 内存安全 | 线程安全 | 适用场景 |
|------|--------|------|----------|----------|----------|
| Adapter | 低 | 高 | ✅ | ✅ | 接口适配 |
| Bridge | 中 | 中 | ✅ | ✅ | 抽象与实现分离 |
| Composite | 中 | 中 | ✅ | ✅ | 树形结构 |
| Decorator | 中 | 中 | ✅ | ✅ | 动态功能扩展 |
| Facade | 低 | 高 | ✅ | ✅ | 子系统简化 |
| Flyweight | 中 | 高 | ✅ | ✅ | 对象共享 |
| Proxy | 中 | 中 | ✅ | ✅ | 访问控制 |

### 9.2 选择指南

#### 9.2.1 何时使用适配器模式

- 需要使不兼容的接口协同工作
- 需要复用现有类
- 需要统一接口

#### 9.2.2 何时使用桥接模式

- 抽象和实现需要独立变化
- 需要避免编译时绑定
- 需要支持多种实现

#### 9.2.3 何时使用组合模式

- 需要表示部分-整体层次结构
- 需要统一处理叶子节点和复合节点
- 需要支持递归结构

#### 9.2.4 何时使用装饰器模式

- 需要动态添加功能
- 需要避免子类爆炸
- 需要支持功能组合

#### 9.2.5 何时使用外观模式

- 需要简化复杂子系统
- 需要降低系统耦合
- 需要提供统一接口

#### 9.2.6 何时使用享元模式

- 需要支持大量对象
- 对象状态可以分离
- 需要减少内存使用

#### 9.2.7 何时使用代理模式

- 需要控制对象访问
- 需要延迟加载
- 需要添加额外功能

### 9.3 组合使用

```rust
// 装饰器 + 代理组合
struct DecoratorProxy<T: Subject> {
    decorator: Box<dyn Component>,
    proxy: T,
}

impl<T: Subject> DecoratorProxy<T> {
    fn new(decorator: Box<dyn Component>, proxy: T) -> Self {
        Self { decorator, proxy }
    }
}

impl<T: Subject> Subject for DecoratorProxy<T> {
    fn request(&self) -> String {
        format!("DecoratorProxy: {}", self.proxy.request())
    }
}
```

---

**维护者**: Rust语言形式化理论团队  
**最后更新**: 2025-01-27
