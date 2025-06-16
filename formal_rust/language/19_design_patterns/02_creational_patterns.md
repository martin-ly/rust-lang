# 创建型设计模式

**日期**: 2025-01-27  
**版本**: 1.0.0  
**状态**: 完成

## 📋 目录

1. [创建型模式概述](#1-创建型模式概述)
2. [工厂模式 (Factory Pattern)](#2-工厂模式-factory-pattern)
3. [抽象工厂模式 (Abstract Factory Pattern)](#3-抽象工厂模式-abstract-factory-pattern)
4. [建造者模式 (Builder Pattern)](#4-建造者模式-builder-pattern)
5. [单例模式 (Singleton Pattern)](#5-单例模式-singleton-pattern)
6. [原型模式 (Prototype Pattern)](#6-原型模式-prototype-pattern)
7. [模式比较与选择](#7-模式比较与选择)

## 1. 创建型模式概述

### 1.1 形式化定义

创建型模式处理对象创建机制，形式化定义为：

$$\text{Creational}(T) = \{\text{Factory}, \text{Builder}, \text{Singleton}, \text{Prototype}, \text{AbstractFactory}\}$$

其中每个模式 $p \in \text{Creational}(T)$ 满足：

$$\forall p: \exists f: \text{Context} \rightarrow T \text{ s.t. } f \text{ is injective}$$

### 1.2 核心原则

1. **封装创建逻辑**: 将对象创建逻辑封装在专门的组件中
2. **解耦创建与使用**: 客户端代码不需要知道具体的创建细节
3. **支持扩展**: 易于添加新的产品类型或创建方式
4. **保证一致性**: 确保创建的对象满足特定约束

### 1.3 分类体系

```rust
enum CreationalPattern {
    Factory(FactoryPattern),
    AbstractFactory(AbstractFactoryPattern),
    Builder(BuilderPattern),
    Singleton(SingletonPattern),
    Prototype(PrototypePattern),
}
```

## 2. 工厂模式 (Factory Pattern)

### 2.1 形式化定义

工厂模式定义了一个创建对象的接口，但由子类决定要实例化的类是哪一个。

$$\text{Factory}(T) = \{(create, context) \mid create: \text{Context} \rightarrow T\}$$

### 2.2 结构分析

```rust
// 产品接口
trait Product {
    fn operation(&self) -> String;
}

// 具体产品
struct ConcreteProductA;
struct ConcreteProductB;

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "ConcreteProductA operation".to_string()
    }
}

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "ConcreteProductB operation".to_string()
    }
}

// 工厂接口
trait Factory {
    type Product: Product;
    
    fn create_product(&self) -> Self::Product;
}

// 具体工厂
struct ConcreteFactoryA;
struct ConcreteFactoryB;

impl Factory for ConcreteFactoryA {
    type Product = ConcreteProductA;
    
    fn create_product(&self) -> Self::Product {
        ConcreteProductA
    }
}

impl Factory for ConcreteFactoryB {
    type Product = ConcreteProductB;
    
    fn create_product(&self) -> Self::Product {
        ConcreteProductB
    }
}
```

### 2.3 参数化工厂

```rust
// 参数化工厂模式
struct ParameterizedFactory;

impl ParameterizedFactory {
    fn create_product<T: Product + Default>() -> T {
        T::default()
    }
    
    fn create_product_with_config<T: Product>(
        config: ProductConfig,
    ) -> Result<T, FactoryError>
    where
        T: From<ProductConfig>,
    {
        T::try_from(config)
    }
}

// 产品配置
#[derive(Clone, Debug)]
struct ProductConfig {
    product_type: ProductType,
    parameters: HashMap<String, String>,
}

#[derive(Clone, Debug)]
enum ProductType {
    TypeA,
    TypeB,
    TypeC,
}
```

### 2.4 性能分析

**时间复杂度**: $O(1)$ - 工厂创建产品的时间复杂度为常数
**空间复杂度**: $O(1)$ - 不需要额外的存储空间
**内存安全**: ✅ 保证内存安全
**线程安全**: ✅ 可以设计为线程安全

### 2.5 正确性证明

**不变式**: 
$$\forall f \in \text{Factory}: \forall c \in \text{Context}: f.create(c) \in \text{ValidProducts}$$

**终止性**: 工厂方法总是终止并返回有效产品

## 3. 抽象工厂模式 (Abstract Factory Pattern)

### 3.1 形式化定义

抽象工厂模式提供一个创建一系列相关或相互依赖对象的接口，而无需指定它们的具体类。

$$\text{AbstractFactory}(T_1, T_2, \ldots, T_n) = \{(create_1, create_2, \ldots, create_n) \mid create_i: \text{Context} \rightarrow T_i\}$$

### 3.2 结构分析

```rust
// 抽象产品族
trait AbstractProductA {
    fn operation_a(&self) -> String;
}

trait AbstractProductB {
    fn operation_b(&self) -> String;
}

// 具体产品族1
struct ConcreteProductA1;
struct ConcreteProductB1;

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        "ConcreteProductA1 operation".to_string()
    }
}

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        "ConcreteProductB1 operation".to_string()
    }
}

// 具体产品族2
struct ConcreteProductA2;
struct ConcreteProductB2;

impl AbstractProductA for ConcreteProductA2 {
    fn operation_a(&self) -> String {
        "ConcreteProductA2 operation".to_string()
    }
}

impl AbstractProductB for ConcreteProductB2 {
    fn operation_b(&self) -> String {
        "ConcreteProductB2 operation".to_string()
    }
}

// 抽象工厂
trait AbstractFactory {
    type ProductA: AbstractProductA;
    type ProductB: AbstractProductB;
    
    fn create_product_a(&self) -> Self::ProductA;
    fn create_product_b(&self) -> Self::ProductB;
}

// 具体工厂1
struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    type ProductA = ConcreteProductA1;
    type ProductB = ConcreteProductB1;
    
    fn create_product_a(&self) -> Self::ProductA {
        ConcreteProductA1
    }
    
    fn create_product_b(&self) -> Self::ProductB {
        ConcreteProductB1
    }
}

// 具体工厂2
struct ConcreteFactory2;

impl AbstractFactory for ConcreteFactory2 {
    type ProductA = ConcreteProductA2;
    type ProductB = ConcreteProductB2;
    
    fn create_product_a(&self) -> Self::ProductA {
        ConcreteProductA2
    }
    
    fn create_product_b(&self) -> Self::ProductB {
        ConcreteProductB2
    }
}
```

### 3.3 产品族一致性

```rust
// 产品族一致性检查
trait ProductFamily {
    type ProductA: AbstractProductA;
    type ProductB: AbstractProductB;
    
    fn create_family(&self) -> (Self::ProductA, Self::ProductB);
    fn validate_family(&self, product_a: &Self::ProductA, product_b: &Self::ProductB) -> bool;
}

impl ProductFamily for ConcreteFactory1 {
    type ProductA = ConcreteProductA1;
    type ProductB = ConcreteProductB1;
    
    fn create_family(&self) -> (Self::ProductA, Self::ProductB) {
        (self.create_product_a(), self.create_product_b())
    }
    
    fn validate_family(&self, _product_a: &Self::ProductA, _product_b: &Self::ProductB) -> bool {
        // 验证产品族的一致性
        true
    }
}
```

### 3.4 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是产品族中产品的数量
**空间复杂度**: $O(n)$ - 需要存储所有产品
**一致性保证**: ✅ 保证产品族的一致性
**扩展性**: ✅ 易于添加新的产品族

## 4. 建造者模式 (Builder Pattern)

### 4.1 形式化定义

建造者模式将一个复杂对象的构建与它的表示分离，使得同样的构建过程可以创建不同的表示。

$$\text{Builder}(T) = \{(build, reset, set_attr_1, \ldots, set_attr_n) \mid build: () \rightarrow T\}$$

### 4.2 结构分析

```rust
// 复杂产品
#[derive(Clone, Debug)]
struct ComplexProduct {
    part_a: String,
    part_b: String,
    part_c: String,
    optional_part_d: Option<String>,
}

// 建造者接口
trait Builder {
    type Product;
    
    fn reset(&mut self);
    fn set_part_a(&mut self, part_a: String) -> &mut Self;
    fn set_part_b(&mut self, part_b: String) -> &mut Self;
    fn set_part_c(&mut self, part_c: String) -> &mut Self;
    fn set_optional_part_d(&mut self, part_d: String) -> &mut Self;
    fn build(&self) -> Self::Product;
}

// 具体建造者
struct ConcreteBuilder {
    product: ComplexProduct,
}

impl ConcreteBuilder {
    fn new() -> Self {
        Self {
            product: ComplexProduct {
                part_a: String::new(),
                part_b: String::new(),
                part_c: String::new(),
                optional_part_d: None,
            },
        }
    }
}

impl Builder for ConcreteBuilder {
    type Product = ComplexProduct;
    
    fn reset(&mut self) {
        self.product = ComplexProduct {
            part_a: String::new(),
            part_b: String::new(),
            part_c: String::new(),
            optional_part_d: None,
        };
    }
    
    fn set_part_a(&mut self, part_a: String) -> &mut Self {
        self.product.part_a = part_a;
        self
    }
    
    fn set_part_b(&mut self, part_b: String) -> &mut Self {
        self.product.part_b = part_b;
        self
    }
    
    fn set_part_c(&mut self, part_c: String) -> &mut Self {
        self.product.part_c = part_c;
        self
    }
    
    fn set_optional_part_d(&mut self, part_d: String) -> &mut Self {
        self.product.optional_part_d = Some(part_d);
        self
    }
    
    fn build(&self) -> Self::Product {
        self.product.clone()
    }
}
```

### 4.3 流式接口

```rust
// 流式建造者
trait FluentBuilder {
    type Product;
    
    fn new() -> Self;
    fn with_part_a(self, part_a: String) -> Self;
    fn with_part_b(self, part_b: String) -> Self;
    fn with_part_c(self, part_c: String) -> Self;
    fn with_optional_part_d(self, part_d: String) -> Self;
    fn build(self) -> Self::Product;
}

struct FluentConcreteBuilder {
    product: ComplexProduct,
}

impl FluentBuilder for FluentConcreteBuilder {
    type Product = ComplexProduct;
    
    fn new() -> Self {
        Self {
            product: ComplexProduct {
                part_a: String::new(),
                part_b: String::new(),
                part_c: String::new(),
                optional_part_d: None,
            },
        }
    }
    
    fn with_part_a(mut self, part_a: String) -> Self {
        self.product.part_a = part_a;
        self
    }
    
    fn with_part_b(mut self, part_b: String) -> Self {
        self.product.part_b = part_b;
        self
    }
    
    fn with_part_c(mut self, part_c: String) -> Self {
        self.product.part_c = part_c;
        self
    }
    
    fn with_optional_part_d(mut self, part_d: String) -> Self {
        self.product.optional_part_d = Some(part_d);
        self
    }
    
    fn build(self) -> Self::Product {
        self.product
    }
}
```

### 4.4 验证建造者

```rust
// 验证建造者
trait ValidatingBuilder {
    type Product;
    type Error;
    
    fn build(&self) -> Result<Self::Product, Self::Error>;
    fn validate(&self) -> Result<(), Self::Error>;
}

struct ValidatingConcreteBuilder {
    product: ComplexProduct,
}

#[derive(Debug, thiserror::Error)]
enum BuilderError {
    #[error("Missing required part: {0}")]
    MissingPart(String),
    #[error("Invalid part value: {0}")]
    InvalidPart(String),
}

impl ValidatingBuilder for ValidatingConcreteBuilder {
    type Product = ComplexProduct;
    type Error = BuilderError;
    
    fn validate(&self) -> Result<(), Self::Error> {
        if self.product.part_a.is_empty() {
            return Err(BuilderError::MissingPart("part_a".to_string()));
        }
        if self.product.part_b.is_empty() {
            return Err(BuilderError::MissingPart("part_b".to_string()));
        }
        if self.product.part_c.is_empty() {
            return Err(BuilderError::MissingPart("part_c".to_string()));
        }
        Ok(())
    }
    
    fn build(&self) -> Result<Self::Product, Self::Error> {
        self.validate()?;
        Ok(self.product.clone())
    }
}
```

### 4.5 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是产品部件的数量
**空间复杂度**: $O(n)$ - 需要存储所有部件
**验证开销**: $O(n)$ - 验证所有必需部件
**内存效率**: ✅ 支持零拷贝构建

## 5. 单例模式 (Singleton Pattern)

### 5.1 形式化定义

单例模式确保一个类只有一个实例，并提供一个全局访问点。

$$\text{Singleton}(T) = \{(get_instance, instance) \mid \forall t_1, t_2: \text{getInstance}(t_1) = \text{getInstance}(t_2)\}$$

### 5.2 基本实现

```rust
use std::sync::{Arc, Mutex, Once};

// 线程安全的单例
struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        Self {
            data: "Singleton instance".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 全局单例实例
static mut INSTANCE: Option<Arc<Mutex<Singleton>>> = None;
static INIT: Once = Once::new();

// 获取单例实例
fn get_instance() -> Arc<Mutex<Singleton>> {
    unsafe {
        INIT.call_once(|| {
            INSTANCE = Some(Arc::new(Mutex::new(Singleton::new())));
        });
        INSTANCE.as_ref().unwrap().clone()
    }
}
```

### 5.3 延迟初始化

```rust
use std::sync::OnceLock;

// 使用OnceLock的延迟初始化单例
struct LazySingleton {
    data: String,
}

impl LazySingleton {
    fn new() -> Self {
        Self {
            data: "Lazy singleton instance".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 全局单例
static INSTANCE: OnceLock<LazySingleton> = OnceLock::new();

// 获取单例实例
fn get_lazy_instance() -> &'static LazySingleton {
    INSTANCE.get_or_init(|| LazySingleton::new())
}
```

### 5.4 泛型单例

```rust
// 泛型单例模式
struct GenericSingleton<T> {
    data: T,
}

impl<T> GenericSingleton<T> {
    fn new(data: T) -> Self {
        Self { data }
    }
    
    fn get_data(&self) -> &T {
        &self.data
    }
}

// 全局泛型单例
static mut GENERIC_INSTANCE: Option<Arc<Mutex<GenericSingleton<String>>>> = None;
static GENERIC_INIT: Once = Once::new();

fn get_generic_instance() -> Arc<Mutex<GenericSingleton<String>>> {
    unsafe {
        GENERIC_INIT.call_once(|| {
            GENERIC_INSTANCE = Some(Arc::new(Mutex::new(
                GenericSingleton::new("Generic singleton".to_string())
            )));
        });
        GENERIC_INSTANCE.as_ref().unwrap().clone()
    }
}
```

### 5.5 性能分析

**时间复杂度**: $O(1)$ - 获取实例的时间复杂度为常数
**空间复杂度**: $O(1)$ - 只存储一个实例
**线程安全**: ✅ 保证线程安全
**内存效率**: ✅ 避免重复分配

### 5.6 正确性证明

**唯一性不变式**:
$$\forall t_1, t_2: \text{getInstance}(t_1) = \text{getInstance}(t_2)$$

**线程安全不变式**:
$$\forall t_1, t_2: \text{ThreadSafe}(\text{getInstance}(t_1), \text{getInstance}(t_2))$$

## 6. 原型模式 (Prototype Pattern)

### 6.1 形式化定义

原型模式用原型实例指定创建对象的种类，并且通过拷贝这些原型创建新的对象。

$$\text{Prototype}(T) = \{(clone, prototype) \mid clone: T \rightarrow T \text{ s.t. } clone(t) \neq t\}$$

### 6.2 基本实现

```rust
use std::fmt::Debug;

// 原型接口
trait Prototype: Clone + Debug {
    fn clone_prototype(&self) -> Self;
    fn clone_with_modifications(&self, modifications: Vec<Modification>) -> Self;
}

// 修改类型
#[derive(Clone, Debug)]
enum Modification {
    ChangeName(String),
    ChangeValue(i32),
    AddAttribute(String, String),
}

// 具体原型
#[derive(Clone, Debug)]
struct ConcretePrototype {
    name: String,
    value: i32,
    attributes: HashMap<String, String>,
}

impl ConcretePrototype {
    fn new(name: String, value: i32) -> Self {
        Self {
            name,
            value,
            attributes: HashMap::new(),
        }
    }
}

impl Prototype for ConcretePrototype {
    fn clone_prototype(&self) -> Self {
        self.clone()
    }
    
    fn clone_with_modifications(&self, modifications: Vec<Modification>) -> Self {
        let mut clone = self.clone();
        
        for modification in modifications {
            match modification {
                Modification::ChangeName(name) => {
                    clone.name = name;
                }
                Modification::ChangeValue(value) => {
                    clone.value = value;
                }
                Modification::AddAttribute(key, value) => {
                    clone.attributes.insert(key, value);
                }
            }
        }
        
        clone
    }
}
```

### 6.3 原型注册表

```rust
use std::collections::HashMap;

// 原型注册表
struct PrototypeRegistry {
    prototypes: HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeRegistry {
    fn new() -> Self {
        Self {
            prototypes: HashMap::new(),
        }
    }
    
    fn register<P: Prototype + 'static>(&mut self, name: String, prototype: P) {
        self.prototypes.insert(name, Box::new(prototype));
    }
    
    fn clone_prototype(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(name).map(|p| p.clone_prototype())
    }
    
    fn clone_with_modifications(
        &self,
        name: &str,
        modifications: Vec<Modification>,
    ) -> Option<Box<dyn Prototype>> {
        self.prototypes
            .get(name)
            .map(|p| p.clone_with_modifications(modifications))
    }
}

// 为Box<dyn Prototype>实现Clone
impl Clone for Box<dyn Prototype> {
    fn clone(&self) -> Self {
        self.clone_prototype()
    }
}
```

### 6.4 深度克隆

```rust
// 深度克隆原型
trait DeepClone {
    fn deep_clone(&self) -> Self;
}

#[derive(Clone, Debug)]
struct DeepPrototype {
    data: Vec<String>,
    nested: Box<DeepPrototype>,
}

impl DeepClone for DeepPrototype {
    fn deep_clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            nested: Box::new(self.nested.deep_clone()),
        }
    }
}

impl Prototype for DeepPrototype {
    fn clone_prototype(&self) -> Self {
        self.deep_clone()
    }
    
    fn clone_with_modifications(&self, _modifications: Vec<Modification>) -> Self {
        self.deep_clone()
    }
}
```

### 6.5 性能分析

**时间复杂度**: $O(n)$ - 其中 $n$ 是原型对象的复杂度
**空间复杂度**: $O(n)$ - 需要复制整个对象
**内存效率**: ⚠️ 可能产生大量内存分配
**缓存友好**: ✅ 支持对象池和缓存

## 7. 模式比较与选择

### 7.1 模式对比表

| 模式 | 复杂度 | 性能 | 内存安全 | 线程安全 | 适用场景 |
|------|--------|------|----------|----------|----------|
| Factory | 低 | 高 | ✅ | ✅ | 简单对象创建 |
| AbstractFactory | 中 | 中 | ✅ | ✅ | 产品族创建 |
| Builder | 中 | 中 | ✅ | ✅ | 复杂对象构建 |
| Singleton | 低 | 高 | ✅ | ✅ | 全局状态管理 |
| Prototype | 中 | 中 | ✅ | ✅ | 对象克隆 |

### 7.2 选择指南

#### 7.2.1 何时使用工厂模式

- 需要创建不同类型的对象
- 创建逻辑相对简单
- 不需要维护对象状态

#### 7.2.2 何时使用抽象工厂模式

- 需要创建相关的产品族
- 产品族需要保持一致
- 系统需要支持多种产品族

#### 7.2.3 何时使用建造者模式

- 对象构建过程复杂
- 需要支持不同的构建配置
- 需要验证构建结果

#### 7.2.4 何时使用单例模式

- 需要全局状态管理
- 资源需要共享
- 需要控制实例数量

#### 7.2.5 何时使用原型模式

- 对象创建成本高
- 需要基于现有对象创建新对象
- 需要支持对象配置

### 7.3 组合使用

```rust
// 工厂 + 建造者组合
struct FactoryBuilder<T> {
    factory: Box<dyn Factory<Product = T>>,
    builder: Box<dyn Builder<Product = T>>,
}

impl<T> FactoryBuilder<T> {
    fn create_with_builder(&self, config: ProductConfig) -> T {
        let mut builder = self.builder.reset();
        // 根据配置设置建造者参数
        self.builder.build()
    }
}
```

---

**维护者**: Rust语言形式化理论团队  
**最后更新**: 2025-01-27 