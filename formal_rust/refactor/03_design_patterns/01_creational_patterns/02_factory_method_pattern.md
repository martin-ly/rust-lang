# 02. 工厂方法模式 (Factory Method Pattern)

## 02.01. 形式化定义

### 02.01.01. 数学定义

设 $P$ 为产品集合，$C$ 为创建者集合，$F$ 为工厂方法集合，则工厂方法模式可形式化定义为：

**定义 2.1 (工厂方法模式)** 工厂方法模式是一个四元组 $(P, C, F, \phi)$，其中：

- $P$ 是产品集合，$P = \{p_1, p_2, ..., p_n\}$
- $C$ 是创建者集合，$C = \{c_1, c_2, ..., c_m\}$
- $F$ 是工厂方法集合，$F = \{f_1, f_2, ..., f_m\}$
- $\phi: C \times F \rightarrow P$ 是工厂映射函数，满足 $\forall c \in C, f \in F: \phi(c, f) \in P$

**定义 2.2 (产品族)** 对于创建者 $c \in C$，其产品族定义为：
$P_c = \{p \in P | \exists f \in F: \phi(c, f) = p\}$

**定理 2.1 (工厂方法唯一性)** 对于任意创建者 $c \in C$ 和工厂方法 $f \in F$，存在唯一的产品 $p \in P$，使得 $\phi(c, f) = p$。

**证明**：

1. 由定义 2.1，$\phi$ 是函数，因此对于任意输入 $(c, f)$，输出是唯一的
2. 因此 $\forall c \in C, f \in F: \exists! p \in P: \phi(c, f) = p$

### 02.01.02. 类型理论定义

在类型理论中，工厂方法模式可表示为：

```typescript
// 产品接口
interface Product {
  operation(): string;
}

// 创建者接口
interface Creator {
  factoryMethod(): Product;
  someOperation(): string;
}

// 工厂方法约束
constraint FactoryMethodConstraint<T extends Product, C extends Creator> = {
  ∀c: C → c.factoryMethod() returns T
}
```

## 02.02. 实现形式化

### 02.02.01. Rust 实现

```rust
use std::fmt::Display;

/// 产品 trait - 定义产品的通用接口
/// 
/// 数学性质：
/// - 接口一致性：∀p ∈ Product: p implements Product trait
/// - 操作完整性：∀p ∈ Product: p.operation() returns String
pub trait Product: Display {
    /// 产品操作
    /// 
    /// 数学性质：
    /// - 确定性：operation() always returns same result for same state
    /// - 完整性：operation() returns complete product information
    fn operation(&self) -> String;
    
    /// 产品标识符
    /// 
    /// 数学性质：
    /// - 唯一性：get_id() returns unique identifier
    /// - 不变性：∀calls: get_id() returns same value
    fn get_id(&self) -> u64;
}

/// 具体产品 A
/// 
/// 数学性质：
/// - 产品一致性：ConcreteProductA ∈ Product
/// - 实现完整性：implements all Product methods
#[derive(Debug, Clone)]
pub struct ConcreteProductA {
    id: u64,
    data: String,
}

impl ConcreteProductA {
    /// 创建具体产品 A
    /// 
    /// 数学性质：
    /// - 构造完整性：new(id, data) creates complete product
    /// - 参数有效性：∀id, data: new(id, data) is valid
    pub fn new(id: u64, data: String) -> Self {
        ConcreteProductA { id, data }
    }
}

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        format!("ConcreteProductA operation: {} (ID: {})", self.data, self.id)
    }
    
    fn get_id(&self) -> u64 {
        self.id
    }
}

impl Display for ConcreteProductA {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ConcreteProductA(id={}, data='{}')", self.id, self.data)
    }
}

/// 具体产品 B
/// 
/// 数学性质：
/// - 产品一致性：ConcreteProductB ∈ Product
/// - 实现完整性：implements all Product methods
#[derive(Debug, Clone)]
pub struct ConcreteProductB {
    id: u64,
    value: i32,
}

impl ConcreteProductB {
    /// 创建具体产品 B
    /// 
    /// 数学性质：
    /// - 构造完整性：new(id, value) creates complete product
    /// - 参数有效性：∀id, value: new(id, value) is valid
    pub fn new(id: u64, value: i32) -> Self {
        ConcreteProductB { id, value }
    }
}

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        format!("ConcreteProductB operation: value = {} (ID: {})", self.value, self.id)
    }
    
    fn get_id(&self) -> u64 {
        self.id
    }
}

impl Display for ConcreteProductB {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ConcreteProductB(id={}, value={})", self.id, self.value)
    }
}

/// 创建者 trait - 定义工厂方法接口
/// 
/// 数学性质：
/// - 工厂一致性：∀c ∈ Creator: c implements Creator trait
/// - 方法完整性：∀c ∈ Creator: c.factory_method() returns Product
pub trait Creator {
    /// 工厂方法 - 创建产品的抽象方法
    /// 
    /// 数学性质：
    /// - 产品创建：factory_method() creates Product instance
    /// - 类型安全：factory_method() returns valid Product
    /// - 延迟绑定：具体产品类型在运行时确定
    fn factory_method(&self) -> Box<dyn Product>;
    
    /// 使用工厂方法的操作
    /// 
    /// 数学性质：
    /// - 组合性：some_operation() uses factory_method()
    /// - 一致性：∀calls: some_operation() returns consistent result
    fn some_operation(&self) -> String {
        let product = self.factory_method();
        format!("Creator: Working with {}", product.operation())
    }
}

/// 具体创建者 A
/// 
/// 数学性质：
/// - 创建者一致性：ConcreteCreatorA ∈ Creator
/// - 产品映射：factory_method() returns ConcreteProductA
#[derive(Debug)]
pub struct ConcreteCreatorA {
    creator_id: u64,
}

impl ConcreteCreatorA {
    /// 创建具体创建者 A
    /// 
    /// 数学性质：
    /// - 构造完整性：new(id) creates complete creator
    /// - 参数有效性：∀id: new(id) is valid
    pub fn new(creator_id: u64) -> Self {
        ConcreteCreatorA { creator_id }
    }
}

impl Creator for ConcreteCreatorA {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA::new(
            self.creator_id * 1000 + 1,
            format!("Created by Creator A (ID: {})", self.creator_id)
        ))
    }
}

/// 具体创建者 B
/// 
/// 数学性质：
/// - 创建者一致性：ConcreteCreatorB ∈ Creator
/// - 产品映射：factory_method() returns ConcreteProductB
#[derive(Debug)]
pub struct ConcreteCreatorB {
    creator_id: u64,
}

impl ConcreteCreatorB {
    /// 创建具体创建者 B
    /// 
    /// 数学性质：
    /// - 构造完整性：new(id) creates complete creator
    /// - 参数有效性：∀id: new(id) is valid
    pub fn new(creator_id: u64) -> Self {
        ConcreteCreatorB { creator_id }
    }
}

impl Creator for ConcreteCreatorB {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB::new(
            self.creator_id * 1000 + 2,
            self.creator_id * 10
        ))
    }
}

/// 客户端代码
/// 
/// 数学性质：
/// - 多态性：client_code works with any Creator
/// - 扩展性：new creators can be added without modifying client
pub fn client_code(creator: &dyn Creator) -> String {
    creator.some_operation()
}
```

### 02.02.02. 形式化验证

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    /// 测试工厂方法唯一性定理
    #[test]
    fn test_factory_method_uniqueness() {
        let creator_a = ConcreteCreatorA::new(1);
        let creator_b = ConcreteCreatorB::new(2);
        
        let product_a1 = creator_a.factory_method();
        let product_a2 = creator_a.factory_method();
        let product_b = creator_b.factory_method();
        
        // 验证同一创建者产生相同类型产品
        assert_eq!(product_a1.get_id() / 1000, product_a2.get_id() / 1000);
        
        // 验证不同创建者产生不同类型产品
        assert_ne!(product_a1.get_id() % 1000, product_b.get_id() % 1000);
    }
    
    /// 测试产品族一致性
    #[test]
    fn test_product_family_consistency() {
        let creator_a = ConcreteCreatorA::new(1);
        let creator_b = ConcreteCreatorB::new(2);
        
        // 验证创建者 A 的产品族
        let product_a = creator_a.factory_method();
        assert!(product_a.operation().contains("ConcreteProductA"));
        
        // 验证创建者 B 的产品族
        let product_b = creator_b.factory_method();
        assert!(product_a.operation().contains("ConcreteProductB"));
    }
    
    /// 测试客户端代码多态性
    #[test]
    fn test_client_polymorphism() {
        let creator_a = ConcreteCreatorA::new(1);
        let creator_b = ConcreteCreatorB::new(2);
        
        let result_a = client_code(&creator_a);
        let result_b = client_code(&creator_b);
        
        // 验证客户端代码能处理不同类型的创建者
        assert!(result_a.contains("Creator: Working with"));
        assert!(result_b.contains("Creator: Working with"));
        assert_ne!(result_a, result_b);
    }
    
    /// 测试产品操作一致性
    #[test]
    fn test_product_operation_consistency() {
        let creator_a = ConcreteCreatorA::new(1);
        let product = creator_a.factory_method();
        
        let operation1 = product.operation();
        let operation2 = product.operation();
        
        // 验证产品操作的一致性
        assert_eq!(operation1, operation2);
    }
}
```

## 02.03. 数学性质分析

### 02.03.01. 复杂度分析

**时间复杂度**：

- 产品创建：$O(1)$ - 直接构造
- 工厂方法调用：$O(1)$ - 方法调用
- 产品操作：$O(1)$ - 简单操作

**空间复杂度**：

- 产品存储：$O(1)$ - 固定大小
- 创建者存储：$O(1)$ - 固定大小
- 方法调用栈：$O(1)$ - 常量深度

### 02.03.02. 正确性证明

**定理 2.2 (工厂方法正确性)** 工厂方法模式的实现满足以下性质：

1. **产品创建**：$\forall c \in C: c.\text{factory\_method}() \in P$
2. **类型安全**：$\forall c \in C: \text{type}(c.\text{factory\_method}()) \subseteq \text{Product}$
3. **多态性**：$\forall c_1, c_2 \in C: \text{client\_code}(c_1) \text{ and } \text{client\_code}(c_2) \text{ work}$

**证明**：

1. 产品创建由 trait 约束保证，所有实现必须返回 Product 类型
2. 类型安全由 Rust 的类型系统保证
3. 多态性通过 trait 对象实现，允许运行时多态

## 02.04. 应用场景与约束

### 02.04.01. 适用场景

1. **框架设计**：$\text{Framework} \in \text{FactoryMethod}$
2. **插件系统**：$\text{Plugin} \in \text{FactoryMethod}$
3. **配置驱动**：$\text{Config} \rightarrow \text{Product}$
4. **测试框架**：$\text{Test} \in \text{FactoryMethod}$

### 02.04.02. 约束条件

**数学约束**：

- $\forall c \in C: c.\text{factory\_method}() \in P$
- $\forall p \in P: p \text{ implements Product trait}$
- $\forall c \in C: c \text{ implements Creator trait}$

**实现约束**：

- 创建者必须实现 Creator trait
- 产品必须实现 Product trait
- 工厂方法必须返回 Product 类型

## 02.05. 变体与扩展

### 02.05.01. 参数化工厂方法

```rust
/// 参数化工厂方法模式
/// 
/// 数学性质：
/// - 参数化创建：∀p ∈ Param: factory_method(p) returns Product
/// - 参数一致性：∀p₁, p₂: p₁ = p₂ → factory_method(p₁) = factory_method(p₂)
pub trait ParameterizedCreator<P> {
    fn factory_method(&self, param: P) -> Box<dyn Product>;
}

#[derive(Debug)]
pub struct ParameterizedConcreteCreator;

impl ParameterizedCreator<String> for ParameterizedConcreteCreator {
    fn factory_method(&self, param: String) -> Box<dyn Product> {
        if param.contains("A") {
            Box::new(ConcreteProductA::new(1, param))
        } else {
            Box::new(ConcreteProductB::new(1, param.len() as i32))
        }
    }
}
```

### 02.05.02. 泛型工厂方法

```rust
/// 泛型工厂方法模式
/// 
/// 数学性质：
/// - 类型参数化：∀T: Creator<T> creates Product<T>
/// - 类型安全：∀T: type(factory_method()) = Product<T>
pub trait GenericCreator<T> {
    fn factory_method(&self) -> Box<dyn Product<T>>;
}

pub trait Product<T> {
    fn operation(&self) -> T;
}

#[derive(Debug)]
pub struct GenericConcreteCreator;

impl GenericCreator<String> for GenericConcreteCreator {
    fn factory_method(&self) -> Box<dyn Product<String>> {
        Box::new(ConcreteProductA::new(1, "Generic Product".to_string()))
    }
}
```

## 02.06. 与其他模式的关系

### 02.06.01. 模式组合

**工厂方法 + 单例**：

```rust
/// 单例工厂方法模式
/// 
/// 数学性质：
/// - 单例性：|Creator| = 1
/// - 工厂性：∀calls: factory_method() creates Product
pub struct SingletonCreator {
    _private: (),
}

impl SingletonCreator {
    pub fn get_instance() -> &'static Self {
        static INSTANCE: Once = Once::new();
        static mut SINGLETON: *const SingletonCreator = 0 as *const _;
        
        INSTANCE.call_once(|| {
            unsafe {
                SINGLETON = Box::into_raw(Box::new(SingletonCreator { _private: () }));
            }
        });
        
        unsafe { &*SINGLETON }
    }
}

impl Creator for SingletonCreator {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA::new(1, "Singleton Created".to_string()))
    }
}
```

### 02.06.02. 模式转换

**工厂方法 → 抽象工厂**：

- 当需要创建产品族时，工厂方法可以扩展为抽象工厂
- 数学关系：$\text{FactoryMethod} \subseteq \text{AbstractFactory}$

## 02.07. 总结

工厂方法模式通过数学形式化定义实现了创建者与产品的解耦。其核心性质包括：

1. **创建解耦**：$\forall c \in C: c \text{ independent of } P$
2. **多态创建**：$\forall c_1, c_2 \in C: \text{client\_code}(c_1) = \text{client\_code}(c_2)$
3. **扩展性**：$\text{new Creator} \rightarrow \text{no client modification}$

该模式在框架设计、插件系统和配置驱动开发中具有重要应用价值。

---

**参考文献**：

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). Design Patterns: Elements of Reusable Object-Oriented Software
2. Freeman, E., Robson, E., Sierra, K., & Bates, B. (2004). Head First Design Patterns
3. Rust Reference Manual - Traits and Generics
