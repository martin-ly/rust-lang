# 设计模式（形式化推进目录）

## 1. 创建型模式

- 1.1 工厂模式的形式化  [TODO]
- 1.2 工厂方法模式的形式化

**理论定义**：
工厂方法模式通过定义一个用于创建对象的接口，让子类决定实例化哪一个类。工厂方法使一个类的实例化延迟到其子类。

**结构符号**：
`Factory<T>` = { create() -> T }

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

- 1.3 建造者模式的数学表示

**理论定义**：
建造者模式将一个复杂对象的构建与其表示分离，使同样的构建过程可以创建不同的表示。

**结构符号**：
`Builder<T>` = { step₁(), step₂(), ..., build() -> T }

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

- 1.4 原型模式的理论基础

**理论定义**：
原型模式通过复制现有对象来创建新对象，避免重复初始化。

**结构符号**：
`Prototype<T>` = { clone() -> T }

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

- 1.5 单例模式的理论基础

**理论定义**：
单例模式保证一个类只有一个实例，并提供全局访问点。

**结构符号**：
`Singleton<T>` = { instance() -> &T }

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

### 1.1 工厂模式的形式化

**理论定义**：
工厂模式（Factory Pattern）通过抽象工厂接口 I_Factory: T → P，将类型 T 的构造委托给工厂对象，实现解耦。

**UML/范畴论符号**：

- I_Factory: T → P，T 为产品对象集合，P 为产品类型。
- 存在自然变换 η: I_Factory → New(T)

**Rust 伪代码**：

```rust
trait Product { fn name(&self) -> &'static str; }
struct ConcreteA; impl Product for ConcreteA { fn name(&self) -> &'static str { "A" } }
struct FactoryA;
impl FactoryA { fn create() -> Box<dyn Product> { Box::new(ConcreteA) } }
```

**简要说明**：
工厂模式将对象创建与使用分离，便于扩展和测试。

## 2. 结构型模式

### 2.1 适配器模式的理论基础

**理论定义**：
适配器模式通过包装一个对象，将其接口转换为客户端期望的另一个接口。

**结构符号**：
`Adapter<T, U>` = { adaptee: T, adapt() -> U }

**Rust 伪代码**：

```rust
trait Target { fn request(&self) -> String; }
struct Adaptee;
impl Adaptee { fn specific_request(&self) -> String { "adaptee".into() } }
struct Adapter { adaptee: Adaptee }
impl Target for Adapter {
    fn request(&self) -> String { self.adaptee.specific_request() }
}
```

**简要说明**：
适配器模式实现了接口兼容与系统解耦。

### 2.2 装饰器模式的理论基础

**理论定义**：
装饰器模式通过包装对象动态扩展其功能，保持原有接口。

**结构符号**：
`Decorator<T>` = { component: T, op() }

**Rust 伪代码**：

```rust
trait Component { fn op(&self) -> String; }
struct ConcreteComponent;
impl Component for ConcreteComponent { fn op(&self) -> String { "base".into() } }
struct Decorator<T: Component> { component: T }
impl<T: Component> Component for Decorator<T> {
    fn op(&self) -> String { format!("decorated {}", self.component.op()) }
}
```

**简要说明**：
装饰器模式支持对象功能的灵活扩展。

### 2.3 组合模式的数学模型

**理论定义**：
组合模式将对象组合成树形结构以表示“部分-整体”层次。

**结构符号**：
`Component` = `{ op() }`
`Composite` = `{ children: Vec<Component> }`

**Rust 伪代码**：

```rust
trait Component { fn op(&self) -> String; }
struct Leaf;
impl Component for Leaf { fn op(&self) -> String { "leaf".into() } }
struct Composite { children: Vec<Box<dyn Component>> }
impl Component for Composite {
    fn op(&self) -> String {
        self.children.iter().map(|c| c.op()).collect::<Vec<_>>().join(",")
    }
}
```

**简要说明**：
组合模式支持递归结构和统一操作。

### 2.4 桥接模式的理论基础

**理论定义**：
桥接模式将抽象与实现解耦，使二者可以独立变化。

**结构符号**：
`Abstraction` = { impl: Implementor }
`Implementor` = { op() }

**Rust 伪代码**：

```rust
trait Implementor { fn op(&self) -> String; }
struct ConcreteImpl;
impl Implementor for ConcreteImpl { fn op(&self) -> String { "impl".into() } }
struct Abstraction<I: Implementor> { imp: I }
impl<I: Implementor> Abstraction<I> {
    fn op(&self) -> String { self.imp.op() }
}
```

**简要说明**：
桥接模式支持多维度扩展和灵活组合。

### 2.5 外观模式的理论基础

**理论定义**：
外观模式为子系统提供统一接口，简化复杂系统的使用。

**结构符号**：
`Facade` = `{ subsystem: Subsystem, op() }`

**Rust 伪代码**：

```rust
struct Subsystem;
impl Subsystem { fn op1(&self) {} fn op2(&self) {} }
struct Facade { subsystem: Subsystem }
impl Facade {
    fn op(&self) { self.subsystem.op1(); self.subsystem.op2(); }
}
```

**简要说明**：
外观模式提升了系统的易用性和解耦性。

### 2.6 享元模式的理论基础

**理论定义**：
享元模式通过共享对象，减少内存消耗，适用于大量细粒度对象。

**结构符号**：
`FlyweightFactory` = `{ pool: HashMap<Key, Flyweight> }`

**Rust 伪代码**：

```rust
use std::collections::HashMap;
struct Flyweight { data: String }
struct FlyweightFactory { pool: HashMap<String, Flyweight> }
impl FlyweightFactory {
    fn get(&mut self, key: &str) -> &Flyweight {
        self.pool.entry(key.to_string()).or_insert(Flyweight { data: key.into() })
    }
}
```

**简要说明**：
享元模式适合资源受限场景下的对象复用。

### 2.7 代理模式的理论基础

**理论定义**：
代理模式通过代理对象控制对目标对象的访问，支持延迟加载、安全控制等。

**结构符号**：
`Proxy<T>` = `{ real: T, op() }`

**Rust 伪代码**：

```rust
trait Subject { fn op(&self) -> String; }
struct RealSubject;
impl Subject for RealSubject { fn op(&self) -> String { "real".into() } }
struct Proxy<T: Subject> { real: T }
impl<T: Subject> Subject for Proxy<T> {
    fn op(&self) -> String {
        // 可添加访问控制、缓存等逻辑
        self.real.op()
    }
}
```

**简要说明**：
代理模式适合权限控制、远程代理、延迟加载等场景。

## 3. 行为型模式

### 3.1 责任链模式的理论基础

**理论定义**：
责任链模式将请求沿链传递，直到有对象处理为止。

**结构符号**：
`Handler` = `{ next: Option<Box<Handler>>, handle(req) }`

**Rust 伪代码**：

```rust
trait Handler { fn handle(&self, req: &str) -> bool; }
struct ConcreteHandler { next: Option<Box<dyn Handler>> }
impl Handler for ConcreteHandler {
    fn handle(&self, req: &str) -> bool {
        if req == "ok" { true }
        else if let Some(ref n) = self.next { n.handle(req) } else { false }
    }
}
```

**简要说明**：
责任链模式适合请求处理流程可扩展的场景。

### 3.2 状态模式的形式化

**理论定义**：
状态模式允许对象在内部状态改变时改变其行为。

**结构符号**：
`State` = `{ handle(ctx) }`
`Context` = `{ state: Box<State> }`

**Rust 伪代码**：

```rust
trait State { fn handle(&self, ctx: &mut Context); }
struct Context { state: Box<dyn State> }
impl Context {
    fn request(&mut self) { self.state.handle(self); }
}
struct ConcreteState;
impl State for ConcreteState {
    fn handle(&self, ctx: &mut Context) { /* 状态切换逻辑 */ }
}
```

**简要说明**：
状态模式适合对象行为依赖于状态的场景。

### 3.3 策略模式的数学基础

**理论定义**：
策略模式将算法封装为独立策略，使其可互换。

**结构符号**：
`Strategy` = `{ execute() }`
`Context` = `{ strategy: Box<Strategy> }`

**Rust 伪代码**：

```rust
trait Strategy { fn execute(&self) -> i32; }
struct Add;
impl Strategy for Add { fn execute(&self) -> i32 { 1+2 } }
struct Context { strategy: Box<dyn Strategy> }
impl Context {
    fn set_strategy(&mut self, s: Box<dyn Strategy>) { self.strategy = s; }
    fn run(&self) -> i32 { self.strategy.execute() }
}
```

**简要说明**：
策略模式适合算法可切换的场景。

## 4. 函数式与并发模式

- 4.1 函数组合与高阶模式  [TODO]
- 4.2 并发模式的理论分析  [TODO]

## 5. Rust 设计模式工程案例

- 5.1 典型模式的 Rust 实现  [TODO]
- 5.2 框架与库中的模式应用  [TODO]

## 6. 理论贡献与方法论总结  [TODO]

---

### 推进计划与断点快照

- [x] 目录骨架搭建
- [ ] 创建型模式小节补全
- [ ] 结构型模式小节补全
- [ ] 行为型模式小节补全
- [ ] 工程案例与代码补全
- [ ] 理论贡献总结
