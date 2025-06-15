# 01. 创建型设计模式

## 目录

1. [引言](#1-引言)
2. [单例模式](#2-单例模式)
3. [工厂模式](#3-工厂模式)
4. [抽象工厂模式](#4-抽象工厂模式)
5. [建造者模式](#5-建造者模式)
6. [原型模式](#6-原型模式)
7. [对象池模式](#7-对象池模式)
8. [总结与展望](#8-总结与展望)

## 1. 引言

### 1.1 创建型模式在Rust中的重要性

创建型设计模式关注对象的创建过程，在Rust中具有特殊的意义：

**形式化定义**：

```
Creational_Patterns(Rust) = {
    Singleton_Pattern,
    Factory_Pattern,
    Abstract_Factory_Pattern,
    Builder_Pattern,
    Prototype_Pattern,
    Object_Pool_Pattern
}
```

### 1.2 核心创建型概念

Rust中的创建型模式包含以下核心概念：

1. **对象创建控制**：控制对象的创建过程
2. **内存管理**：利用Rust的所有权系统
3. **类型安全**：编译时保证类型安全
4. **性能优化**：零成本抽象的实现

## 2. 单例模式

### 2.1 单例模式定义

****定义 2**.1.1** (单例)

```
Singleton = {instance | ∃!instance ∈ Type}
```

****定义 2**.1.2** (单例保证)

```
Singleton_Guarantee = {
    Uniqueness: ∀i1, i2 ∈ Instance, i1 = i2,
    Global_Access: ∀p ∈ Program, Access(p, instance),
    Lazy_Initialization: Initialize(instance) ↔ First_Access(instance)
}
```

### 2.2 Rust中的单例实现

**示例 2.2.1** (使用OnceCell的单例)

```rust
use std::sync::OnceCell;

struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        Singleton {
            data: "singleton data".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static INSTANCE: OnceCell<Singleton> = OnceCell::new();

fn get_instance() -> &'static Singleton {
    INSTANCE.get_or_init(|| Singleton::new())
}
```

### 2.3 线程安全单例

****定义 2**.3.1** (线程安全单例)

```
Thread_Safe_Singleton = {
    Mutex<Singleton>,
    Lazy<Mutex<Singleton>>,
    OnceCell<Singleton>
}
```

**示例 2.3.1** (线程安全单例)

```rust
use std::sync::{Mutex, Once};
use std::sync::LazyLock;

static INIT: Once = Once::new();
static mut INSTANCE: *mut Singleton = std::ptr::null_mut();

struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        Singleton {
            data: "thread safe singleton".to_string(),
        }
    }
}

fn get_instance() -> &'static Singleton {
    unsafe {
        INIT.call_once(|| {
            INSTANCE = Box::into_raw(Box::new(Singleton::new()));
        });
        &*INSTANCE
    }
}
```

## 3. 工厂模式

### 3.1 工厂模式定义

****定义 3**.1.1** (工厂)

```
Factory = {f | f: Parameters → Product}
```

****定义 3**.1.2** (工厂方法)

```
Factory_Method = {
    create: Parameters → Product,
    validate: Parameters → Bool,
    configure: Product → Product
}
```

### 3.2 简单工厂模式

**示例 3.2.1** (简单工厂)

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
struct ConcreteProductB;

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Product A".to_string()
    }
}

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Product B".to_string()
    }
}

enum ProductType {
    A,
    B,
}

struct SimpleFactory;

impl SimpleFactory {
    fn create_product(product_type: ProductType) -> Box<dyn Product> {
        match product_type {
            ProductType::A => Box::new(ConcreteProductA),
            ProductType::B => Box::new(ConcreteProductB),
        }
    }
}
```

### 3.3 工厂方法模式

****定义 3**.3.1** (工厂方法)

```
Factory_Method_Pattern = {
    Creator: {create_product: () → Product},
    Concrete_Creator: {create_product: () → Concrete_Product}
}
```

**示例 3.3.1** (工厂方法)

```rust
trait Product {
    fn operation(&self) -> String;
}

trait Creator {
    fn create_product(&self) -> Box<dyn Product>;
    fn some_operation(&self) -> String {
        let product = self.create_product();
        format!("Creator: {}", product.operation())
    }
}

struct ConcreteCreatorA;
struct ConcreteCreatorB;

impl Creator for ConcreteCreatorA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

impl Creator for ConcreteCreatorB {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}
```

## 4. 抽象工厂模式

### 4.1 抽象工厂定义

****定义 4**.1.1** (抽象工厂)

```
Abstract_Factory = {
    create_product_a: () → ProductA,
    create_product_b: () → ProductB,
    create_product_c: () → ProductC
}
```

****定义 4**.1.2** (产品族)

```
Product_Family = {ProductA, ProductB, ProductC}
```

### 4.2 Rust中的抽象工厂

**示例 4.2.1** (抽象工厂)

```rust
trait AbstractProductA {
    fn operation_a(&self) -> String;
}

trait AbstractProductB {
    fn operation_b(&self) -> String;
}

trait AbstractFactory {
    fn create_product_a(&self) -> Box<dyn AbstractProductA>;
    fn create_product_b(&self) -> Box<dyn AbstractProductB>;
}

struct ConcreteProductA1;
struct ConcreteProductB1;
struct ConcreteProductA2;
struct ConcreteProductB2;

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        "Product A1".to_string()
    }
}

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        "Product B1".to_string()
    }
}

struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA1)
    }
    
    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB1)
    }
}
```

## 5. 建造者模式

### 5.1 建造者模式定义

****定义 5**.1.1** (建造者)

```
Builder = {
    build_part_a: () → Builder,
    build_part_b: () → Builder,
    build_part_c: () → Builder,
    get_result: () → Product
}
```

****定义 5**.1.2** (建造过程)

```
Build_Process = {
    step1: Builder → Builder,
    step2: Builder → Builder,
    step3: Builder → Product
}
```

### 5.2 Rust中的建造者模式

**示例 5.2.1** (建造者模式)

```rust
struct Product {
    part_a: String,
    part_b: String,
    part_c: String,
}

struct Builder {
    product: Product,
}

impl Builder {
    fn new() -> Self {
        Builder {
            product: Product {
                part_a: String::new(),
                part_b: String::new(),
                part_c: String::new(),
            },
        }
    }
    
    fn build_part_a(mut self, part_a: String) -> Self {
        self.product.part_a = part_a;
        self
    }
    
    fn build_part_b(mut self, part_b: String) -> Self {
        self.product.part_b = part_b;
        self
    }
    
    fn build_part_c(mut self, part_c: String) -> Self {
        self.product.part_c = part_c;
        self
    }
    
    fn build(self) -> Product {
        self.product
    }
}
```

### 5.3 流式建造者

**示例 5.3.1** (流式建造者)

```rust
#[derive(Default)]
struct Product {
    part_a: Option<String>,
    part_b: Option<String>,
    part_c: Option<String>,
}

impl Product {
    fn is_complete(&self) -> bool {
        self.part_a.is_some() && self.part_b.is_some() && self.part_c.is_some()
    }
}

struct Builder {
    product: Product,
}

impl Builder {
    fn new() -> Self {
        Builder {
            product: Product::default(),
        }
    }
    
    fn part_a(mut self, part_a: String) -> Self {
        self.product.part_a = Some(part_a);
        self
    }
    
    fn part_b(mut self, part_b: String) -> Self {
        self.product.part_b = Some(part_b);
        self
    }
    
    fn part_c(mut self, part_c: String) -> Self {
        self.product.part_c = Some(part_c);
        self
    }
    
    fn build(self) -> Result<Product, String> {
        if self.product.is_complete() {
            Ok(self.product)
        } else {
            Err("Product is not complete".to_string())
        }
    }
}
```

## 6. 原型模式

### 6.1 原型模式定义

****定义 6**.1.1** (原型)

```
Prototype = {clone: () → Self}
```

****定义 6**.1.2** (克隆操作)

```
Clone_Operation = {
    shallow_clone: Object → Object,
    deep_clone: Object → Object
}
```

### 6.2 Rust中的原型模式

**示例 6.2.1** (原型模式)

```rust
use std::clone::Clone;

#[derive(Clone)]
struct Prototype {
    data: String,
    configuration: Vec<String>,
}

impl Prototype {
    fn new(data: String) -> Self {
        Prototype {
            data,
            configuration: Vec::new(),
        }
    }
    
    fn add_configuration(&mut self, config: String) {
        self.configuration.push(config);
    }
    
    fn clone(&self) -> Self {
        self.clone()
    }
}

struct PrototypeRegistry {
    prototypes: std::collections::HashMap<String, Prototype>,
}

impl PrototypeRegistry {
    fn new() -> Self {
        PrototypeRegistry {
            prototypes: std::collections::HashMap::new(),
        }
    }
    
    fn add_prototype(&mut self, name: String, prototype: Prototype) {
        self.prototypes.insert(name, prototype);
    }
    
    fn get_prototype(&self, name: &str) -> Option<Prototype> {
        self.prototypes.get(name).cloned()
    }
}
```

## 7. 对象池模式

### 7.1 对象池模式定义

****定义 7**.1.1** (对象池)

```
Object_Pool = {
    acquire: () → Object,
    release: Object → (),
    size: () → usize
}
```

****定义 7**.1.2** (池化对象)

```
Pooled_Object = {
    object: Object,
    in_use: bool,
    last_used: Time
}
```

### 7.2 Rust中的对象池

**示例 7.2.1** (对象池)

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

struct PooledObject {
    id: u32,
    data: String,
}

impl PooledObject {
    fn new(id: u32) -> Self {
        PooledObject {
            id,
            data: format!("Object {}", id),
        }
    }
    
    fn reset(&mut self) {
        self.data = format!("Object {} (reset)", self.id);
    }
}

struct ObjectPool {
    objects: Arc<Mutex<VecDeque<PooledObject>>>,
    max_size: usize,
    counter: Arc<Mutex<u32>>,
}

impl ObjectPool {
    fn new(max_size: usize) -> Self {
        ObjectPool {
            objects: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
            counter: Arc::new(Mutex::new(0)),
        }
    }
    
    fn acquire(&self) -> Option<PooledObject> {
        let mut objects = self.objects.lock().unwrap();
        if let Some(mut obj) = objects.pop_front() {
            obj.reset();
            Some(obj)
        } else {
            let mut counter = self.counter.lock().unwrap();
            if objects.len() < self.max_size {
                *counter += 1;
                Some(PooledObject::new(*counter))
            } else {
                None
            }
        }
    }
    
    fn release(&self, obj: PooledObject) {
        let mut objects = self.objects.lock().unwrap();
        if objects.len() < self.max_size {
            objects.push_back(obj);
        }
    }
}
```

## 8. 总结与展望

### 8.1 创建型模式成就

Rust中创建型模式的成就：

1. **类型安全**：编译时保证对象创建的类型安全
2. **内存安全**：利用所有权系统保证内存安全
3. **性能优化**：零成本抽象的实现
4. **表达力**：丰富的模式组合能力

### 8.2 未来发展方向

创建型模式在Rust中的发展方向：

1. **模式组合**：更复杂的模式组合
2. **性能优化**：更高效的实现方式
3. **工具支持**：更好的模式实现工具

### 8.3 创建型价值

创建型模式在Rust中的价值：

**形式化总结**：

```
Creational_Value = {
    Type_Safety: Strong,
    Memory_Safety: Guaranteed,
    Performance: Zero_Cost,
    Expressiveness: Rich
}
```

---

## 参考文献

1. Gamma, E. et al. (1994). "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Rust Team (2021). "The Rust Programming Language"
3. Freeman, A. (2009). "Pro Design Patterns in C#"
4. Nystrom, R. (2014). "Game Programming Patterns"

## 相关文档

- [02_structural_patterns.md](./02_structural_patterns.md) - 结构型设计模式
- [03_behavioral_patterns.md](./03_behavioral_patterns.md) - 行为型设计模式
- [04_concurrent_patterns.md](./04_concurrent_patterns.md) - 并发设计模式
- [05_functional_patterns.md](./05_functional_patterns.md) - 函数式设计模式

