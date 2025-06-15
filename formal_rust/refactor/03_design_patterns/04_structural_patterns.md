# 02. 结构型设计模式

## 目录

1. [引言](#1-引言)
2. [适配器模式](#2-适配器模式)
3. [桥接模式](#3-桥接模式)
4. [组合模式](#4-组合模式)
5. [装饰器模式](#5-装饰器模式)
6. [外观模式](#6-外观模式)
7. [享元模式](#7-享元模式)
8. [代理模式](#8-代理模式)
9. [总结与展望](#9-总结与展望)

## 1. 引言

### 1.1 结构型模式在Rust中的重要性

结构型设计模式关注类和对象的组合，在Rust中具有特殊的意义：

**形式化定义**：
```
Structural_Patterns(Rust) = {
    Adapter_Pattern,
    Bridge_Pattern,
    Composite_Pattern,
    Decorator_Pattern,
    Facade_Pattern,
    Flyweight_Pattern,
    Proxy_Pattern
}
```

### 1.2 核心结构型概念

Rust中的结构型模式包含以下核心概念：

1. **接口适配**：不同接口之间的适配
2. **抽象分离**：抽象与实现的分离
3. **对象组合**：对象的层次结构组合
4. **功能扩展**：动态功能扩展
5. **接口简化**：复杂接口的简化

## 2. 适配器模式

### 2.1 适配器模式定义

****定义 2**.1.1** (适配器)
```
Adapter = {adapt: Incompatible_Interface → Compatible_Interface}
```

****定义 2**.1.2** (适配器保证)
```
Adapter_Guarantee = {
    Interface_Compatibility: ∀i ∈ Incompatible, ∃a ∈ Adapter, Compatible(a(i)),
    Functionality_Preservation: ∀f ∈ Function, Preserve(f) → Maintain(f),
    Performance_Acceptable: Performance(Adapter) ≥ Threshold
}
```

### 2.2 Rust中的适配器实现

**示例 2.2.1** (对象适配器)
```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 需要适配的类
struct Adaptee {
    specific_request: String,
}

impl Adaptee {
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
        Adapter { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将特定的请求转换为目标接口
        format!("Adapter: {}", self.adaptee.specific_request())
    }
}
```

### 2.3 类适配器

**示例 2.3.1** (类适配器)
```rust
trait Target {
    fn request(&self) -> String;
}

struct Adaptee {
    specific_request: String,
}

impl Adaptee {
    fn specific_request(&self) -> String {
        self.specific_request.clone()
    }
}

// 类适配器通过继承实现
struct ClassAdapter {
    adaptee: Adaptee,
}

impl ClassAdapter {
    fn new(adaptee: Adaptee) -> Self {
        ClassAdapter { adaptee }
    }
}

impl Target for ClassAdapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

## 3. 桥接模式

### 3.1 桥接模式定义

****定义 3**.1.1** (桥接)
```
Bridge = {abstraction: Abstract_Interface, implementation: Implementation_Interface}
```

****定义 3**.1.2** (桥接关系)
```
Bridge_Relationship = {
    Abstraction: {operation: () → Result},
    Implementation: {operation_impl: () → Result},
    Bridge: Abstraction → Implementation
}
```

### 3.2 Rust中的桥接实现

**示例 3.2.1** (桥接模式)
```rust
// 实现接口
trait Implementation {
    fn operation_impl(&self) -> String;
}

// 具体实现A
struct ConcreteImplementationA;

impl Implementation for ConcreteImplementationA {
    fn operation_impl(&self) -> String {
        "ConcreteImplementationA".to_string()
    }
}

// 具体实现B
struct ConcreteImplementationB;

impl Implementation for ConcreteImplementationB {
    fn operation_impl(&self) -> String {
        "ConcreteImplementationB".to_string()
    }
}

// 抽象接口
trait Abstraction {
    fn operation(&self) -> String;
}

// 精确抽象
struct RefinedAbstraction {
    implementation: Box<dyn Implementation>,
}

impl RefinedAbstraction {
    fn new(implementation: Box<dyn Implementation>) -> Self {
        RefinedAbstraction { implementation }
    }
}

impl Abstraction for RefinedAbstraction {
    fn operation(&self) -> String {
        format!("RefinedAbstraction: {}", self.implementation.operation_impl())
    }
}
```

## 4. 组合模式

### 4.1 组合模式定义

****定义 4**.1.1** (组合)
```
Composite = {component: Component, children: Vec<Component>}
```

****定义 4**.1.2** (组件层次)
```
Component_Hierarchy = {
    Leaf: Component,
    Composite: Component + Children,
    Operation: Component → Result
}
```

### 4.2 Rust中的组合实现

**示例 4.2.1** (组合模式)
```rust
use std::collections::HashMap;

// 组件特征
trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>);
    fn remove(&mut self, component: &str);
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>>;
}

// 叶子组件
struct Leaf {
    name: String,
}

impl Leaf {
    fn new(name: String) -> Self {
        Leaf { name }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf: {}", self.name)
    }
    
    fn add(&mut self, _component: Box<dyn Component>) {
        // 叶子节点不支持添加子组件
    }
    
    fn remove(&mut self, _name: &str) {
        // 叶子节点不支持删除子组件
    }
    
    fn get_child(&self, _name: &str) -> Option<&Box<dyn Component>> {
        None
    }
}

// 复合组件
struct Composite {
    name: String,
    children: HashMap<String, Box<dyn Component>>,
}

impl Composite {
    fn new(name: String) -> Self {
        Composite {
            name,
            children: HashMap::new(),
        }
    }
}

impl Component for Composite {
    fn operation(&self) -> String {
        let mut result = format!("Composite: {}", self.name);
        for child in self.children.values() {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
    
    fn add(&mut self, component: Box<dyn Component>) {
        // 这里需要获取组件的名称，简化处理
        self.children.insert("child".to_string(), component);
    }
    
    fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }
    
    fn get_child(&self, name: &str) -> Option<&Box<dyn Component>> {
        self.children.get(name)
    }
}
```

## 5. 装饰器模式

### 5.1 装饰器模式定义

****定义 5**.1.1** (装饰器)
```
Decorator = {component: Component, decorator: Component → Component}
```

****定义 5**.1.2** (装饰器链)
```
Decorator_Chain = {
    Base_Component: Component,
    Decorator_1: Component → Component,
    Decorator_2: Component → Component,
    ...
}
```

### 5.2 Rust中的装饰器实现

**示例 5.2.1** (装饰器模式)
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
        Decorator { component }
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
        ConcreteDecoratorA {
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
        ConcreteDecoratorB {
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

## 6. 外观模式

### 6.1 外观模式定义

****定义 6**.1.1** (外观)
```
Facade = {simplify: Complex_Subsystem → Simple_Interface}
```

****定义 6**.1.2** (子系统封装)
```
Subsystem_Encapsulation = {
    Subsystem_1: Complex_Interface_1,
    Subsystem_2: Complex_Interface_2,
    ...
    Facade: Simple_Interface
}
```

### 6.2 Rust中的外观实现

**示例 6.2.1** (外观模式)
```rust
// 子系统A
struct SubsystemA;

impl SubsystemA {
    fn operation_a1(&self) -> String {
        "SubsystemA: operation_a1".to_string()
    }
    
    fn operation_a2(&self) -> String {
        "SubsystemA: operation_a2".to_string()
    }
}

// 子系统B
struct SubsystemB;

impl SubsystemB {
    fn operation_b1(&self) -> String {
        "SubsystemB: operation_b1".to_string()
    }
    
    fn operation_b2(&self) -> String {
        "SubsystemB: operation_b2".to_string()
    }
}

// 子系统C
struct SubsystemC;

impl SubsystemC {
    fn operation_c1(&self) -> String {
        "SubsystemC: operation_c1".to_string()
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
        Facade {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC,
        }
    }
    
    fn operation1(&self) -> String {
        format!("Facade: {}\n  {}\n  {}", 
            self.subsystem_a.operation_a1(),
            self.subsystem_b.operation_b1(),
            self.subsystem_c.operation_c1()
        )
    }
    
    fn operation2(&self) -> String {
        format!("Facade: {}\n  {}", 
            self.subsystem_a.operation_a2(),
            self.subsystem_b.operation_b2()
        )
    }
}
```

## 7. 享元模式

### 7.1 享元模式定义

****定义 7**.1.1** (享元)
```
Flyweight = {intrinsic: Intrinsic_State, extrinsic: Extrinsic_State}
```

****定义 7**.1.2** (享元工厂)
```
Flyweight_Factory = {
    flyweights: HashMap<Key, Flyweight>,
    get_flyweight: Key → Flyweight
}
```

### 7.2 Rust中的享元实现

**示例 7.2.1** (享元模式)
```rust
use std::collections::HashMap;

// 享元特征
trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
}

// 具体享元
struct ConcreteFlyweight {
    intrinsic_state: String,
}

impl ConcreteFlyweight {
    fn new(intrinsic_state: String) -> Self {
        ConcreteFlyweight { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!("ConcreteFlyweight: intrinsic={}, extrinsic={}", 
            self.intrinsic_state, extrinsic_state)
    }
}

// 享元工厂
struct FlyweightFactory {
    flyweights: HashMap<String, Box<dyn Flyweight>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        FlyweightFactory {
            flyweights: HashMap::new(),
        }
    }
    
    fn get_flyweight(&mut self, key: &str) -> &Box<dyn Flyweight> {
        if !self.flyweights.contains_key(key) {
            self.flyweights.insert(
                key.to_string(),
                Box::new(ConcreteFlyweight::new(key.to_string()))
            );
        }
        self.flyweights.get(key).unwrap()
    }
    
    fn count(&self) -> usize {
        self.flyweights.len()
    }
}
```

## 8. 代理模式

### 8.1 代理模式定义

****定义 8**.1.1** (代理)
```
Proxy = {subject: Subject, proxy: Subject → Subject}
```

****定义 8**.1.2** (代理类型)
```
Proxy_Types = {
    Virtual_Proxy: Lazy_Loading,
    Protection_Proxy: Access_Control,
    Remote_Proxy: Network_Communication,
    Caching_Proxy: Performance_Optimization
}
```

### 8.2 Rust中的代理实现

**示例 8.2.1** (虚拟代理)
```rust
// 主题接口
trait Subject {
    fn request(&self) -> String;
}

// 真实主题
struct RealSubject;

impl Subject for RealSubject {
    fn request(&self) -> String {
        "RealSubject: request".to_string()
    }
}

// 虚拟代理
struct VirtualProxy {
    real_subject: Option<RealSubject>,
}

impl VirtualProxy {
    fn new() -> Self {
        VirtualProxy {
            real_subject: None,
        }
    }
    
    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            self.real_subject = Some(RealSubject);
        }
    }
}

impl Subject for VirtualProxy {
    fn request(&self) -> String {
        // 这里需要可变引用，简化处理
        "VirtualProxy: request (lazy loaded)".to_string()
    }
}
```

**示例 8.2.2** (保护代理)
```rust
// 保护代理
struct ProtectionProxy {
    real_subject: RealSubject,
    access_level: String,
}

impl ProtectionProxy {
    fn new(access_level: String) -> Self {
        ProtectionProxy {
            real_subject: RealSubject,
            access_level,
        }
    }
}

impl Subject for ProtectionProxy {
    fn request(&self) -> String {
        if self.access_level == "admin" {
            self.real_subject.request()
        } else {
            "Access denied".to_string()
        }
    }
}
```

## 9. 总结与展望

### 9.1 结构型模式成就

Rust中结构型模式的成就：

1. **接口适配**：灵活处理不同接口之间的适配
2. **抽象分离**：清晰的抽象与实现分离
3. **对象组合**：强大的对象层次结构组合能力
4. **功能扩展**：动态功能扩展的优雅实现
5. **接口简化**：复杂接口的有效简化

### 9.2 未来发展方向

结构型模式在Rust中的发展方向：

1. **模式组合**：更复杂的模式组合应用
2. **性能优化**：更高效的实现方式
3. **类型安全**：更强的编译时类型检查

### 9.3 结构型价值

结构型模式在Rust中的价值：

**形式化总结**：
```
Structural_Value = {
    Interface_Adaptation: Flexible,
    Abstraction_Separation: Clear,
    Object_Composition: Powerful,
    Function_Extension: Dynamic,
    Interface_Simplification: Effective
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
- [03_behavioral_patterns.md](./03_behavioral_patterns.md) - 行为型设计模式
- [04_concurrent_patterns.md](./04_concurrent_patterns.md) - 并发设计模式
- [05_functional_patterns.md](./05_functional_patterns.md) - 函数式设计模式 
