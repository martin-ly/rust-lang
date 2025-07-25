# 创建型模式集

## 1. 工厂模式

- trait抽象工厂、泛型工厂、宏自动生成

### 1.1 简单工厂

```rust
trait Product { fn do_work(&self); }
struct ConcreteA; struct ConcreteB;
impl Product for ConcreteA { fn do_work(&self) { /* ... */ } }
impl Product for ConcreteB { fn do_work(&self) { /* ... */ } }
fn factory(kind: &str) -> Box<dyn Product> { match kind { "A" => Box::new(ConcreteA), "B" => Box::new(ConcreteB), _ => panic!() } }
```

## 2. 构建器模式

- 逐步构建、链式调用、宏自动生成

### 2.1 Builder实现

```rust
struct Config { a: i32, b: String }
struct ConfigBuilder { a: i32, b: String }
impl ConfigBuilder { fn new() -> Self { /* ... */ } fn a(mut self, a: i32) -> Self { self.a = a; self } fn b(mut self, b: String) -> Self { self.b = b; self } fn build(self) -> Config { Config { a: self.a, b: self.b } } }
```

## 3. 单例与对象池

- 静态变量、OnceCell、lazy_static、对象池复用

### 3.1 单例实现

```rust
use once_cell::sync::Lazy;
static INSTANCE: Lazy<MySingleton> = Lazy::new(|| MySingleton::new());
```

## 4. 原型与类型状态

- Clone trait实现原型复制，PhantomData编码类型状态

## 5. 批判性分析与未来展望

- Rust创建型模式强调类型安全与资源管理，宏与trait提升灵活性，但部分OO模式表达不如C++/Java灵活
- 未来可探索自动化工厂/构建器生成与类型状态API安全
