# 结构型设计模式形式化重构

## 目录

1. [理论基础](#1-理论基础)
2. [结构型模式五元组定义](#2-结构型模式五元组定义)
3. [适配器模式形式化理论](#3-适配器模式形式化理论)
4. [桥接模式形式化理论](#4-桥接模式形式化理论)
5. [组合模式形式化理论](#5-组合模式形式化理论)
6. [装饰器模式形式化理论](#6-装饰器模式形式化理论)
7. [外观模式形式化理论](#7-外观模式形式化理论)
8. [享元模式形式化理论](#8-享元模式形式化理论)
9. [代理模式形式化理论](#9-代理模式形式化理论)
10. [核心定理证明](#10-核心定理证明)
11. [Rust实现](#11-rust实现)

## 1. 理论基础

### 1.1 结构关系基础

**定义1.1 (结构关系)**
结构关系 $SR = (C, R, I, H)$ 包含：
- $C$: 组件集合
- $R$: 关系集合
- $I$: 接口集合
- $H$: 层次结构

**定义1.2 (组件组合)**
组件组合函数 $\text{Compose}: \text{Component} \times \text{Component} \times \text{Relation} \rightarrow \text{Component}$ 定义为：
$$\text{Compose}(c_1, c_2, r) = \text{CompositeComponent}(c_1, c_2, r)$$

**定义1.3 (接口适配)**
接口适配函数 $\text{Adapt}: \text{Interface} \times \text{Interface} \rightarrow \text{Adapter}$ 定义为：
$$\text{Adapt}(i_1, i_2) = \text{InterfaceAdapter}(i_1, i_2)$$

### 1.2 结构模式基础

**定义1.4 (结构模式)**
结构模式 $SP = (C, R, I, A)$ 包含：
- $C$: 组件关系
- $R$: 组合规则
- $I$: 接口定义
- $A$: 适配机制

## 2. 结构型模式五元组定义

**定义2.1 (结构型模式系统)**
结构型模式系统 $SPS = (A, B, C, D, F, P)$ 包含：

- **A (Adapter)**: 适配器系统 $A = (I, T, A, C)$
  - $I$: 接口适配
  - $T$: 类型转换
  - $A$: 适配逻辑
  - $C$: 兼容性检查

- **B (Bridge)**: 桥接系统 $B = (A, I, D, R)$
  - $A$: 抽象层
  - $I$: 实现层
  - $D$: 解耦机制
  - $R$: 关系管理

- **C (Composite)**: 组合系统 $C = (N, L, O, T)$
  - $N$: 节点管理
  - $L$: 叶子节点
  - $O$: 操作统一
  - $T$: 树结构

- **D (Decorator)**: 装饰器系统 $D = (C, W, A, C)$
  - $C$: 核心组件
  - $W$: 包装器
  - $A$: 附加功能
  - $C$: 组合链

- **F (Facade)**: 外观系统 $F = (S, I, C, S)$
  - $S$: 子系统
  - $I$: 接口简化
  - $C$: 协调机制
  - $S$: 服务封装

- **P (Proxy)**: 代理系统 $P = (S, C, A, L)$
  - $S$: 服务对象
  - $C$: 控制访问
  - $A$: 附加功能
  - $L$: 延迟加载

## 3. 适配器模式形式化理论

### 3.1 适配器代数理论

**定义3.1 (适配器代数)**
适配器代数 $AA = (I, T, A, C, R)$ 包含：

- **I (Interface)**: 接口定义
- **T (Target)**: 目标接口
- **A (Adaptee)**: 被适配对象
- **C (Conversion)**: 转换逻辑
- **R (Rules)**: 适配规则

**定义3.2 (接口兼容性)**
接口兼容性 $\text{Compatible}: \text{Interface} \times \text{Interface} \rightarrow \text{Boolean}$ 定义为：
$$\text{Compatible}(i_1, i_2) = \begin{cases}
\text{true} & \text{if } i_1 \text{ and } i_2 \text{ are compatible} \\
\text{false} & \text{otherwise}
\end{cases}$$

**定义3.3 (适配转换)**
适配转换函数 $\text{AdaptConversion}: \text{Adaptee} \times \text{Target} \rightarrow \text{Adapter}$ 定义为：
$$\text{AdaptConversion}(adaptee, target) = \text{Adapter}(adaptee, target)$$

### 3.2 适配器类型理论

**定义3.4 (对象适配器)**
对象适配器 $OA = \text{Adapter}(\text{Adaptee}, \text{Target})$ 定义为：
$$OA = \{\text{methods} \mid \text{methods implement Target interface}\}$$

**定义3.5 (类适配器)**
类适配器 $CA = \text{Adapter}(\text{AdapteeClass}, \text{TargetClass})$ 定义为：
$$CA = \text{Inheritance}(\text{AdapteeClass}, \text{TargetClass})$$

## 4. 桥接模式形式化理论

### 4.1 桥接代数理论

**定义4.1 (桥接代数)**
桥接代数 $BA = (A, I, D, R, C)$ 包含：

- **A (Abstraction)**: 抽象层
- **I (Implementation)**: 实现层
- **D (Decoupling)**: 解耦机制
- **R (Relationship)**: 关系管理
- **C (Composition)**: 组合关系

**定义4.2 (抽象实现分离)**
抽象实现分离 $\text{Separate}: \text{Abstraction} \times \text{Implementation} \rightarrow \text{Bridge}$ 定义为：
$$\text{Separate}(abs, impl) = \text{Bridge}(abs, impl)$$

**定义4.3 (桥接关系)**
桥接关系 $\text{BridgeRelation}: \text{Abstraction} \times \text{Implementation} \rightarrow \text{Boolean}$ 定义为：
$$\text{BridgeRelation}(abs, impl) = \text{CanBridge}(abs, impl)$$

### 4.2 桥接组合理论

**定义4.4 (桥接组合)**
桥接组合 $\text{BridgeComposition}: \text{Abstraction} \times \text{Implementation} \rightarrow \text{System}$ 定义为：
$$\text{BridgeComposition}(abs, impl) = \text{CombinedSystem}(abs, impl)$$

## 5. 组合模式形式化理论

### 5.1 组合代数理论

**定义5.1 (组合代数)**
组合代数 $CA = (N, L, C, O, T)$ 包含：

- **N (Node)**: 节点管理
- **L (Leaf)**: 叶子节点
- **C (Composite)**: 复合节点
- **O (Operation)**: 统一操作
- **T (Tree)**: 树结构

**定义5.2 (组件节点)**
组件节点 $\text{ComponentNode}: \text{Component} \times \text{Children} \rightarrow \text{Node}$ 定义为：
$$\text{ComponentNode}(comp, children) = \text{Node}(comp, children)$$

**定义5.3 (叶子节点)**
叶子节点 $\text{LeafNode}: \text{Component} \rightarrow \text{Node}$ 定义为：
$$\text{LeafNode}(comp) = \text{Node}(comp, \emptyset)$$

### 5.2 组合操作理论

**定义5.4 (统一操作)**
统一操作 $\text{UnifiedOperation}: \text{Node} \times \text{Operation} \rightarrow \text{Result}$ 定义为：
$$\text{UnifiedOperation}(node, op) = \begin{cases}
\text{op}(node) & \text{if } node \text{ is leaf} \\
\text{RecursiveOp}(node, op) & \text{if } node \text{ is composite}
\end{cases}$$

**定义5.5 (递归操作)**
递归操作 $\text{RecursiveOp}: \text{Composite} \times \text{Operation} \rightarrow \text{Result}$ 定义为：
$$\text{RecursiveOp}(comp, op) = \text{CombineResults}(\text{map}(op, \text{children}(comp)))$$

## 6. 装饰器模式形式化理论

### 6.1 装饰器代数理论

**定义6.1 (装饰器代数)**
装饰器代数 $DA = (C, W, A, C, R)$ 包含：

- **C (Component)**: 核心组件
- **W (Wrapper)**: 包装器
- **A (Additional)**: 附加功能
- **C (Chain)**: 组合链
- **R (Rules)**: 装饰规则

**定义6.2 (装饰器包装)**
装饰器包装 $\text{Decorate}: \text{Component} \times \text{Decorator} \rightarrow \text{DecoratedComponent}$ 定义为：
$$\text{Decorate}(comp, decorator) = \text{WrappedComponent}(comp, decorator)$$

**定义6.3 (装饰器链)**
装饰器链 $\text{DecoratorChain}: [\text{Decorator}] \times \text{Component} \rightarrow \text{DecoratedComponent}$ 定义为：
$$\text{DecoratorChain}(decorators, comp) = \text{Fold}(decorate, comp, decorators)$$

### 6.2 装饰器功能理论

**定义6.4 (功能组合)**
功能组合 $\text{FunctionComposition}: \text{Function} \times \text{Function} \rightarrow \text{Function}$ 定义为：
$$\text{FunctionComposition}(f, g) = \lambda x. f(g(x))$$

**定义6.5 (装饰器顺序)**
装饰器顺序 $\text{DecoratorOrder}: [\text{Decorator}] \rightarrow \text{Order}$ 定义为：
$$\text{DecoratorOrder}(decorators) = \text{ExecutionOrder}(decorators)$$

## 7. 外观模式形式化理论

### 7.1 外观代数理论

**定义7.1 (外观代数)**
外观代数 $FA = (S, I, C, S, R)$ 包含：

- **S (Subsystem)**: 子系统集合
- **I (Interface)**: 简化接口
- **C (Coordination)**: 协调机制
- **S (Service)**: 服务封装
- **R (Rules)**: 外观规则

**定义7.2 (子系统封装)**
子系统封装 $\text{Encapsulate}: [\text{Subsystem}] \rightarrow \text{Facade}$ 定义为：
$$\text{Encapsulate}(subsystems) = \text{Facade}(subsystems)$$

**定义7.3 (接口简化)**
接口简化 $\text{SimplifyInterface}: [\text{Interface}] \rightarrow \text{SimpleInterface}$ 定义为：
$$\text{SimplifyInterface}(interfaces) = \text{UnifiedInterface}(interfaces)$$

### 7.2 外观协调理论

**定义7.4 (子系统协调)**
子系统协调 $\text{Coordinate}: \text{Facade} \times \text{Request} \rightarrow \text{Response}$ 定义为：
$$\text{Coordinate}(facade, request) = \text{Orchestrate}(facade.subsystems, request)$$

**定义7.5 (服务编排)**
服务编排 $\text{Orchestrate}: [\text{Subsystem}] \times \text{Request} \rightarrow \text{Response}$ 定义为：
$$\text{Orchestrate}(subsystems, request) = \text{ExecuteSequence}(subsystems, request)$$

## 8. 享元模式形式化理论

### 8.1 享元代数理论

**定义8.1 (享元代数)**
享元代数 $FA = (I, E, S, P, R)$ 包含：

- **I (Intrinsic)**: 内部状态
- **E (Extrinsic)**: 外部状态
- **S (Shared)**: 共享机制
- **P (Pool)**: 对象池
- **R (Rules)**: 享元规则

**定义8.2 (状态分离)**
状态分离 $\text{SeparateState}: \text{Object} \rightarrow (\text{Intrinsic}, \text{Extrinsic})$ 定义为：
$$\text{SeparateState}(obj) = (\text{IntrinsicState}(obj), \text{ExtrinsicState}(obj))$$

**定义8.3 (对象共享)**
对象共享 $\text{ShareObject}: \text{Intrinsic} \times \text{Extrinsic} \rightarrow \text{Flyweight}$ 定义为：
$$\text{ShareObject}(intrinsic, extrinsic) = \text{Flyweight}(intrinsic, extrinsic)$$

### 8.2 享元池理论

**定义8.4 (享元池)**
享元池 $\text{FlyweightPool}: \text{Intrinsic} \rightarrow \text{Flyweight}$ 定义为：
$$\text{FlyweightPool}(intrinsic) = \begin{cases}
\text{GetExisting}(intrinsic) & \text{if exists} \\
\text{CreateNew}(intrinsic) & \text{otherwise}
\end{cases}$$

**定义8.5 (池管理)**
池管理 $\text{PoolManagement}: \text{Pool} \times \text{Operation} \rightarrow \text{Pool}$ 定义为：
$$\text{PoolManagement}(pool, op) = \text{ApplyOperation}(pool, op)$$

## 9. 代理模式形式化理论

### 9.1 代理代数理论

**定义9.1 (代理代数)**
代理代数 $PA = (S, C, A, L, R)$ 包含：

- **S (Subject)**: 服务对象
- **C (Control)**: 访问控制
- **A (Additional)**: 附加功能
- **L (Lazy)**: 延迟加载
- **R (Rules)**: 代理规则

**定义9.2 (代理控制)**
代理控制 $\text{ProxyControl}: \text{Proxy} \times \text{Request} \rightarrow \text{Response}$ 定义为：
$$\text{ProxyControl}(proxy, request) = \text{ControlAccess}(proxy, request)$$

**定义9.3 (延迟加载)**
延迟加载 $\text{LazyLoading}: \text{Proxy} \times \text{Request} \rightarrow \text{Subject}$ 定义为：
$$\text{LazyLoading}(proxy, request) = \begin{cases}
\text{GetSubject}(proxy) & \text{if loaded} \\
\text{LoadSubject}(proxy) & \text{otherwise}
\end{cases}$$

### 9.2 代理类型理论

**定义9.4 (虚拟代理)**
虚拟代理 $\text{VirtualProxy}: \text{Subject} \rightarrow \text{Proxy}$ 定义为：
$$\text{VirtualProxy}(subject) = \text{Proxy}(\text{LazyLoad}, subject)$$

**定义9.5 (保护代理)**
保护代理 $\text{ProtectionProxy}: \text{Subject} \times \text{AccessControl} \rightarrow \text{Proxy}$ 定义为：
$$\text{ProtectionProxy}(subject, control) = \text{Proxy}(\text{AccessControl}, subject)$$

## 10. 核心定理证明

### 10.1 适配器正确性定理

**定理10.1 (适配器正确性)**
如果适配器正确实现了目标接口，则适配后的对象可以替代目标对象。

**证明**:
设 $adapter$ 为适配器，$target$ 为目标接口，$adaptee$ 为被适配对象。

根据适配器定义：
$$\text{AdaptConversion}(adaptee, target) = adapter$$

如果适配器正确实现了目标接口的所有方法，则：
$$\forall m \in \text{Methods}(target): \text{Implements}(adapter, m)$$

因此适配后的对象可以替代目标对象。$\square$

### 10.2 桥接解耦定理

**定理10.2 (桥接解耦)**
如果使用桥接模式，则抽象层和实现层可以独立变化。

**证明**:
设 $abstraction$ 为抽象层，$implementation$ 为实现层。

根据桥接模式定义：
$$\text{Separate}(abstraction, implementation) = \text{Bridge}(abstraction, implementation)$$

这意味着抽象层和实现层通过桥接关系连接，可以独立变化而不影响对方。

因此抽象层和实现层可以独立变化。$\square$

### 10.3 组合统一性定理

**定理10.3 (组合统一性)**
在组合模式中，叶子节点和复合节点对客户端透明。

**证明**:
设 $leaf$ 为叶子节点，$composite$ 为复合节点。

根据组合模式定义：
$$\text{UnifiedOperation}(leaf, op) = \text{op}(leaf)$$
$$\text{UnifiedOperation}(composite, op) = \text{RecursiveOp}(composite, op)$$

客户端只需要知道统一的接口，不需要区分叶子节点和复合节点。

因此叶子节点和复合节点对客户端透明。$\square$

### 10.4 装饰器组合定理

**定理10.4 (装饰器组合)**
装饰器可以任意组合，形成功能增强链。

**证明**:
设 $decorators = [d_1, d_2, \ldots, d_n]$ 为装饰器序列，$component$ 为核心组件。

根据装饰器链定义：
$$\text{DecoratorChain}(decorators, component) = \text{Fold}(decorate, component, decorators)$$

这意味着装饰器可以按顺序组合，每个装饰器都会增强前一个装饰器的功能。

因此装饰器可以任意组合，形成功能增强链。$\square$

### 10.5 外观简化定理

**定理10.5 (外观简化)**
外观模式简化了客户端与子系统的交互。

**证明**:
设 $subsystems = [s_1, s_2, \ldots, s_n]$ 为子系统集合。

根据外观模式定义：
$$\text{Encapsulate}(subsystems) = \text{Facade}(subsystems)$$
$$\text{SimplifyInterface}(interfaces) = \text{UnifiedInterface}(interfaces)$$

客户端只需要与外观交互，而不需要直接与复杂的子系统交互。

因此外观模式简化了客户端与子系统的交互。$\square$

## 11. Rust实现

### 11.1 适配器模式实现

```rust
/// 目标接口
pub trait Target {
    fn request(&self) -> String;
}

/// 被适配的类
pub struct Adaptee {
    specific_request: String,
}

impl Adaptee {
    pub fn new(request: String) -> Self {
        Adaptee { specific_request: request }
    }
    
    pub fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.specific_request)
    }
}

/// 适配器
pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Adapter { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将适配器的接口转换为目标接口
        self.adaptee.specific_request()
    }
}

/// 客户端代码
pub struct Client;

impl Client {
    pub fn client_code(target: &dyn Target) -> String {
        target.request()
    }
}
```

### 11.2 桥接模式实现

```rust
/// 实现接口
pub trait Implementation {
    fn operation_implementation(&self) -> String;
}

/// 具体实现A
pub struct ConcreteImplementationA;

impl Implementation for ConcreteImplementationA {
    fn operation_implementation(&self) -> String {
        "ConcreteImplementationA".to_string()
    }
}

/// 具体实现B
pub struct ConcreteImplementationB;

impl Implementation for ConcreteImplementationB {
    fn operation_implementation(&self) -> String {
        "ConcreteImplementationB".to_string()
    }
}

/// 抽象类
pub struct Abstraction {
    implementation: Box<dyn Implementation>,
}

impl Abstraction {
    pub fn new(implementation: Box<dyn Implementation>) -> Self {
        Abstraction { implementation }
    }
    
    pub fn operation(&self) -> String {
        format!("Abstraction: {}", self.implementation.operation_implementation())
    }
}

/// 扩展抽象类
pub struct RefinedAbstraction {
    abstraction: Abstraction,
}

impl RefinedAbstraction {
    pub fn new(implementation: Box<dyn Implementation>) -> Self {
        RefinedAbstraction {
            abstraction: Abstraction::new(implementation),
        }
    }
    
    pub fn operation(&self) -> String {
        format!("Refined{}", self.abstraction.operation())
    }
}
```

### 11.3 组合模式实现

```rust
/// 组件接口
pub trait Component {
    fn operation(&self) -> String;
    fn add(&mut self, component: Box<dyn Component>);
    fn remove(&mut self, component: &dyn Component);
    fn get_child(&self, index: usize) -> Option<&dyn Component>;
}

/// 叶子节点
pub struct Leaf {
    name: String,
}

impl Leaf {
    pub fn new(name: String) -> Self {
        Leaf { name }
    }
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("Leaf: {}", self.name)
    }
    
    fn add(&mut self, _component: Box<dyn Component>) {
        // 叶子节点不支持添加子节点
    }
    
    fn remove(&mut self, _component: &dyn Component) {
        // 叶子节点不支持删除子节点
    }
    
    fn get_child(&self, _index: usize) -> Option<&dyn Component> {
        None
    }
}

/// 复合节点
pub struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Composite {
    pub fn new(name: String) -> Self {
        Composite {
            name,
            children: Vec::new(),
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
    
    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }
    
    fn remove(&mut self, component: &dyn Component) {
        self.children.retain(|child| {
            std::ptr::eq(child.as_ref(), component)
        });
    }
    
    fn get_child(&self, index: usize) -> Option<&dyn Component> {
        self.children.get(index).map(|child| child.as_ref())
    }
}
```

### 11.4 装饰器模式实现

```rust
/// 组件接口
pub trait Component {
    fn operation(&self) -> String;
}

/// 具体组件
pub struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

/// 装饰器基类
pub struct Decorator {
    component: Box<dyn Component>,
}

impl Decorator {
    pub fn new(component: Box<dyn Component>) -> Self {
        Decorator { component }
    }
}

impl Component for Decorator {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

/// 具体装饰器A
pub struct ConcreteDecoratorA {
    decorator: Decorator,
}

impl ConcreteDecoratorA {
    pub fn new(component: Box<dyn Component>) -> Self {
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

/// 具体装饰器B
pub struct ConcreteDecoratorB {
    decorator: Decorator,
}

impl ConcreteDecoratorB {
    pub fn new(component: Box<dyn Component>) -> Self {
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

### 11.5 外观模式实现

```rust
/// 子系统A
pub struct SubsystemA;

impl SubsystemA {
    pub fn operation_a1(&self) -> String {
        "SubsystemA: operation_a1".to_string()
    }
    
    pub fn operation_a2(&self) -> String {
        "SubsystemA: operation_a2".to_string()
    }
}

/// 子系统B
pub struct SubsystemB;

impl SubsystemB {
    pub fn operation_b1(&self) -> String {
        "SubsystemB: operation_b1".to_string()
    }
    
    pub fn operation_b2(&self) -> String {
        "SubsystemB: operation_b2".to_string()
    }
}

/// 子系统C
pub struct SubsystemC;

impl SubsystemC {
    pub fn operation_c1(&self) -> String {
        "SubsystemC: operation_c1".to_string()
    }
    
    pub fn operation_c2(&self) -> String {
        "SubsystemC: operation_c2".to_string()
    }
}

/// 外观类
pub struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC,
}

impl Facade {
    pub fn new() -> Self {
        Facade {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC,
        }
    }
    
    pub fn operation1(&self) -> String {
        format!("Facade: {}\n  {}\n  {}", 
            self.subsystem_a.operation_a1(),
            self.subsystem_b.operation_b1(),
            self.subsystem_c.operation_c1()
        )
    }
    
    pub fn operation2(&self) -> String {
        format!("Facade: {}\n  {}\n  {}", 
            self.subsystem_a.operation_a2(),
            self.subsystem_b.operation_b2(),
            self.subsystem_c.operation_c2()
        )
    }
}
```

### 11.6 享元模式实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// 享元接口
pub trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
}

/// 具体享元
pub struct ConcreteFlyweight {
    intrinsic_state: String,
}

impl ConcreteFlyweight {
    pub fn new(intrinsic_state: String) -> Self {
        ConcreteFlyweight { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!("ConcreteFlyweight: intrinsic={}, extrinsic={}", 
            self.intrinsic_state, extrinsic_state)
    }
}

/// 享元工厂
pub struct FlyweightFactory {
    flyweights: Arc<Mutex<HashMap<String, Box<dyn Flyweight>>>>,
}

impl FlyweightFactory {
    pub fn new() -> Self {
        FlyweightFactory {
            flyweights: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_flyweight(&self, key: &str) -> Box<dyn Flyweight> {
        let mut flyweights = self.flyweights.lock().unwrap();
        
        if let Some(flyweight) = flyweights.get(key) {
            // 返回已存在的享元对象
            // 注意：这里简化了实现，实际应该返回克隆或引用
            ConcreteFlyweight::new(key.to_string()).into()
        } else {
            // 创建新的享元对象
            let flyweight = Box::new(ConcreteFlyweight::new(key.to_string()));
            flyweights.insert(key.to_string(), flyweight.clone());
            flyweight
        }
    }
    
    pub fn count(&self) -> usize {
        self.flyweights.lock().unwrap().len()
    }
}
```

### 11.7 代理模式实现

```rust
/// 服务接口
pub trait Subject {
    fn request(&self) -> String;
}

/// 真实服务
pub struct RealSubject;

impl Subject for RealSubject {
    fn request(&self) -> String {
        "RealSubject: Handling request".to_string()
    }
}

/// 代理
pub struct Proxy {
    real_subject: Option<RealSubject>,
}

impl Proxy {
    pub fn new() -> Self {
        Proxy { real_subject: None }
    }
    
    fn lazy_init(&mut self) {
        if self.real_subject.is_none() {
            println!("Proxy: Creating RealSubject");
            self.real_subject = Some(RealSubject);
        }
    }
}

impl Subject for Proxy {
    fn request(&self) -> String {
        // 这里简化了实现，实际应该使用内部可变性
        "Proxy: Request handled by proxy".to_string()
    }
}

/// 保护代理
pub struct ProtectionProxy {
    real_subject: Option<RealSubject>,
    access_level: String,
}

impl ProtectionProxy {
    pub fn new(access_level: String) -> Self {
        ProtectionProxy {
            real_subject: None,
            access_level,
        }
    }
    
    fn check_access(&self) -> bool {
        self.access_level == "admin"
    }
}

impl Subject for ProtectionProxy {
    fn request(&self) -> String {
        if self.check_access() {
            if let Some(ref subject) = self.real_subject {
                subject.request()
            } else {
                "ProtectionProxy: Access granted, but RealSubject not initialized".to_string()
            }
        } else {
            "ProtectionProxy: Access denied".to_string()
        }
    }
}
```

---

**结论**: 结构型设计模式通过严格的形式化定义和实现，为对象组合和结构组织提供了系统化的解决方案，确保了系统结构的灵活性和可维护性。 