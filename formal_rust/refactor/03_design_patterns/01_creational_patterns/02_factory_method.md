# 工厂方法模式 (Factory Method Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [形式化定义 (Formal Definition)](#1-形式化定义-formal-definition)
2. [数学理论基础 (Mathematical Foundation)](#2-数学理论基础-mathematical-foundation)
3. [定理与证明 (Theorems and Proofs)](#3-定理与证明-theorems-and-proofs)
4. [Rust实现 (Rust Implementation)](#4-rust实现-rust-implementation)
5. [性能分析 (Performance Analysis)](#5-性能分析-performance-analysis)
6. [应用场景 (Application Scenarios)](#6-应用场景-application-scenarios)
7. [变体模式 (Variant Patterns)](#7-变体模式-variant-patterns)

---

## 1. 形式化定义 (Formal Definition)

### 1.1 工厂方法模式五元组 (Factory Method Pattern Quintuple)

-****定义 1**.1.1 (工厂方法模式)**

设 $F = (N, I, S, R, C)$ 为工厂方法模式，其中：

- $N = \{\text{"Factory Method"}\}$ (模式名称)
- $I = \{\text{"定义创建对象的接口"}, \text{"让子类决定实例化哪个类"}\}$ (意图描述)
- $S = \{\text{Creator}, \text{ConcreteCreator}, \text{Product}, \text{ConcreteProduct}, \text{factory\_method}\}$ (结构定义)
- $R = \{(\text{Creator}, \text{factory\_method}), (\text{ConcreteCreator}, \text{Product}), (\text{Product}, \text{ConcreteProduct})\}$ (关系映射)
- $C = \{\text{抽象约束}, \text{多态约束}, \text{扩展性约束}\}$ (约束条件)

### 1.2 工厂方法结构定义 (Factory Method Structure Definition)

-****定义 1**.2.1 (创建者抽象)**

设 $\text{Creator}$ 为创建者抽象，满足：

$$\text{Creator} = \{\text{interface}, \text{factory\_method}, \text{other\_methods}\}$$

其中：

- $\text{interface}$ 是接口定义
- $\text{factory\_method}$ 是工厂方法
- $\text{other\_methods}$ 是其他方法

-****定义 1**.2.2 (具体创建者)**

设 $\text{ConcreteCreator}$ 为具体创建者，满足：

$$\text{ConcreteCreator} \subseteq \text{Creator} \land \text{ConcreteCreator} \rightarrow \text{ConcreteProduct}$$

-****定义 1**.2.3 (产品抽象)**

设 $\text{Product}$ 为产品抽象，满足：

$$\text{Product} = \{\text{interface}, \text{methods}\}$$

-****定义 1**.2.4 (具体产品)**

设 $\text{ConcreteProduct}$ 为具体产品，满足：

$$\text{ConcreteProduct} \subseteq \text{Product}$$

### 1.3 工厂方法操作定义 (Factory Method Operation Definition)

-****定义 1**.3.1 (工厂方法)**

设 $\text{factory\_method}: \text{Creator} \rightarrow \text{Product}$ 为工厂方法，满足：

$$\text{factory\_method}(creator) = \text{ConcreteProduct}$$

-****定义 1**.3.2 (创建操作)**

设 $\text{create}: \text{ConcreteCreator} \rightarrow \text{ConcreteProduct}$ 为创建操作，满足：

$$\text{create}(creator) = \text{new ConcreteProduct}()$$

---

## 2. 数学理论基础 (Mathematical Foundation)

### 2.1 多态理论 (Polymorphism Theory)

-****定义 2**.1.1 (多态性)**

工厂方法模式满足多态性，当且仅当：

$$\forall c \in \text{ConcreteCreator}, \exists p \in \text{ConcreteProduct}, \text{factory\_method}(c) = p$$

-****定义 2**.1.2 (类型安全)**

工厂方法模式是类型安全的，当且仅当：

$$\forall c \in \text{ConcreteCreator}, \text{TypeOf}(\text{factory\_method}(c)) \subseteq \text{Product}$$

### 2.2 扩展性理论 (Extensibility Theory)

-****定义 2**.2.1 (扩展性)**

工厂方法模式是可扩展的，当且仅当：

$$\forall \text{NewProduct} \subseteq \text{Product}, \exists \text{NewCreator} \subseteq \text{Creator}, \text{factory\_method}(\text{NewCreator}) = \text{NewProduct}$$

-****定义 2**.2.2 (开闭原则)**

工厂方法模式满足开闭原则，当且仅当：

$$\text{OpenForExtension}(\text{Creator}) \land \text{ClosedForModification}(\text{Creator})$$

### 2.3 依赖倒置理论 (Dependency Inversion Theory)

-****定义 2**.3.1 (依赖倒置)**

工厂方法模式满足依赖倒置原则，当且仅当：

$$\text{HighLevelModule} \not\hookrightarrow \text{LowLevelModule} \land \text{HighLevelModule} \hookrightarrow \text{Abstraction}$$

其中 $\hookrightarrow$ 表示依赖关系。

---

## 3. 定理与证明 (Theorems and Proofs)

### 3.1 多态性定理 (Polymorphism Theorem)

-****定理 3**.1.1 (工厂方法多态性)**

对于任意工厂方法模式 $F$，工厂方法支持多态调用。

**证明**:
设 $c_1, c_2 \in \text{ConcreteCreator}$ 是不同的具体创建者。

根据**定义 1**.3.1，$\text{factory\_method}(c_1)$ 和 $\text{factory\_method}(c_2)$ 都返回 $\text{Product}$ 类型。

但具体返回的是不同的 $\text{ConcreteProduct}$ 实例。

因此，工厂方法支持多态调用。

-****定理 3**.1.2 (类型安全保证)**

工厂方法模式保证类型安全。

**证明**:
根据**定义 2**.1.2，对于任意具体创建者 $c$，$\text{factory\_method}(c)$ 返回的类型都是 $\text{Product}$ 的子类型。

由于 $\text{ConcreteProduct} \subseteq \text{Product}$，返回的对象可以安全地用作 $\text{Product}$ 类型。

因此，工厂方法模式保证类型安全。

### 3.2 扩展性定理 (Extensibility Theorem)

-****定理 3**.2.1 (扩展性保证)**

工厂方法模式支持无修改扩展。

**证明**:
要添加新的产品类型，只需要：

1. 创建新的 $\text{ConcreteProduct}$ 类
2. 创建对应的 $\text{ConcreteCreator}$ 类
3. 实现 $\text{factory\_method}$

不需要修改现有的 $\text{Creator}$ 或 $\text{Product}$ 抽象。

因此，工厂方法模式支持无修改扩展。

-****定理 3**.2.2 (开闭原则满足)**

工厂方法模式满足开闭原则。

**证明**:

1. **对扩展开放**: 可以添加新的具体创建者和产品
2. **对修改封闭**: 不需要修改抽象类

因此，工厂方法模式满足开闭原则。

### 3.3 依赖倒置定理 (Dependency Inversion Theorem)

-****定理 3**.3.1 (依赖倒置满足)**

工厂方法模式满足依赖倒置原则。

**证明**:
在工厂方法模式中：

- 高层模块依赖于 $\text{Creator}$ 抽象
- 低层模块（具体创建者）也依赖于 $\text{Creator}$ 抽象
- 两者都依赖于抽象，而不是具体实现

因此，工厂方法模式满足依赖倒置原则。

### 3.4 性能定理 (Performance Theorem)

-****定理 3**.4.1 (创建复杂度)**

工厂方法模式的创建时间复杂度为 $O(1)$。

**证明**:
工厂方法只包含：

1. 方法调用：$O(1)$
2. 对象创建：$O(1)$
3. 返回对象：$O(1)$

因此，总时间复杂度为 $O(1)$。

-****定理 3**.4.2 (内存复杂度)**

工厂方法模式的内存复杂度为 $O(1)$。

**证明**:
每次调用工厂方法只创建一个对象，内存使用是常数。

因此，内存复杂度为 $O(1)$。

---

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现 (Basic Implementation)

```rust
/// 产品抽象
pub trait Product {
    fn operation(&self) -> String;
    fn get_name(&self) -> &str;
}

/// 具体产品 A
pub struct ConcreteProductA {
    name: String,
}

impl ConcreteProductA {
    pub fn new() -> Self {
        ConcreteProductA {
            name: "Product A".to_string(),
        }
    }
}

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        format!("{}: Performing operation A", self.name)
    }

    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 具体产品 B
pub struct ConcreteProductB {
    name: String,
}

impl ConcreteProductB {
    pub fn new() -> Self {
        ConcreteProductB {
            name: "Product B".to_string(),
        }
    }
}

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        format!("{}: Performing operation B", self.name)
    }

    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 创建者抽象
pub trait Creator {
    fn factory_method(&self) -> Box<dyn Product>;
    
    fn some_operation(&self) -> String {
        let product = self.factory_method();
        format!("Creator: {}", product.operation())
    }
}

/// 具体创建者 A
pub struct ConcreteCreatorA;

impl Creator for ConcreteCreatorA {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA::new())
    }
}

/// 具体创建者 B
pub struct ConcreteCreatorB;

impl Creator for ConcreteCreatorB {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB::new())
    }
}
```

### 4.2 泛型工厂方法实现 (Generic Factory Method Implementation)

```rust
use std::fmt::Display;

/// 泛型产品特征
pub trait GenericProduct: Display {
    fn operation(&self) -> String;
    fn get_id(&self) -> u32;
}

/// 泛型创建者特征
pub trait GenericCreator<P: GenericProduct> {
    fn create_product(&self) -> P;
    fn get_creator_info(&self) -> String;
}

/// 具体产品实现
#[derive(Debug)]
pub struct GenericConcreteProduct {
    id: u32,
    name: String,
}

impl GenericConcreteProduct {
    pub fn new(id: u32, name: String) -> Self {
        GenericConcreteProduct { id, name }
    }
}

impl Display for GenericConcreteProduct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Product(id={}, name={})", self.id, self.name)
    }
}

impl GenericProduct for GenericConcreteProduct {
    fn operation(&self) -> String {
        format!("{} performing generic operation", self.name)
    }

    fn get_id(&self) -> u32 {
        self.id
    }
}

/// 具体创建者实现
pub struct GenericConcreteCreator {
    creator_id: u32,
}

impl GenericConcreteCreator {
    pub fn new(creator_id: u32) -> Self {
        GenericConcreteCreator { creator_id }
    }
}

impl GenericCreator<GenericConcreteProduct> for GenericConcreteCreator {
    fn create_product(&self) -> GenericConcreteProduct {
        GenericConcreteProduct::new(
            self.creator_id * 100,
            format!("Product from Creator {}", self.creator_id),
        )
    }

    fn get_creator_info(&self) -> String {
        format!("Generic Creator {}", self.creator_id)
    }
}
```

### 4.3 参数化工厂方法实现 (Parameterized Factory Method Implementation)

```rust
use std::collections::HashMap;

/// 产品类型枚举
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ProductType {
    TypeA,
    TypeB,
    TypeC,
}

/// 参数化产品特征
pub trait ParameterizedProduct {
    fn get_type(&self) -> ProductType;
    fn get_config(&self) -> HashMap<String, String>;
    fn execute(&self) -> Result<String, String>;
}

/// 参数化创建者特征
pub trait ParameterizedCreator {
    fn create_product(&self, product_type: ProductType, config: HashMap<String, String>) -> Box<dyn ParameterizedProduct>;
}

/// 具体参数化产品
pub struct ParameterizedConcreteProduct {
    product_type: ProductType,
    config: HashMap<String, String>,
}

impl ParameterizedConcreteProduct {
    pub fn new(product_type: ProductType, config: HashMap<String, String>) -> Self {
        ParameterizedConcreteProduct {
            product_type,
            config,
        }
    }
}

impl ParameterizedProduct for ParameterizedConcreteProduct {
    fn get_type(&self) -> ProductType {
        self.product_type
    }

    fn get_config(&self) -> HashMap<String, String> {
        self.config.clone()
    }

    fn execute(&self) -> Result<String, String> {
        match self.product_type {
            ProductType::TypeA => Ok(format!("Executing Type A with config: {:?}", self.config)),
            ProductType::TypeB => Ok(format!("Executing Type B with config: {:?}", self.config)),
            ProductType::TypeC => Ok(format!("Executing Type C with config: {:?}", self.config)),
        }
    }
}

/// 参数化创建者实现
pub struct ParameterizedConcreteCreator;

impl ParameterizedCreator for ParameterizedConcreteCreator {
    fn create_product(&self, product_type: ProductType, config: HashMap<String, String>) -> Box<dyn ParameterizedProduct> {
        Box::new(ParameterizedConcreteProduct::new(product_type, config))
    }
}
```

### 4.4 异步工厂方法实现 (Async Factory Method Implementation)

```rust
use std::future::Future;
use std::pin::Pin;
use tokio::time::{sleep, Duration};

/// 异步产品特征
pub trait AsyncProduct {
    fn get_name(&self) -> &str;
    fn get_async_operation(&self) -> Pin<Box<dyn Future<Output = String> + Send>>;
}

/// 异步创建者特征
pub trait AsyncCreator {
    fn create_product_async(&self) -> Pin<Box<dyn Future<Output = Box<dyn AsyncProduct + Send>> + Send>>;
}

/// 具体异步产品
pub struct AsyncConcreteProduct {
    name: String,
    delay_ms: u64,
}

impl AsyncConcreteProduct {
    pub fn new(name: String, delay_ms: u64) -> Self {
        AsyncConcreteProduct { name, delay_ms }
    }
}

impl AsyncProduct for AsyncConcreteProduct {
    fn get_name(&self) -> &str {
        &self.name
    }

    fn get_async_operation(&self) -> Pin<Box<dyn Future<Output = String> + Send>> {
        let delay_ms = self.delay_ms;
        let name = self.name.clone();
        
        Box::pin(async move {
            sleep(Duration::from_millis(delay_ms)).await;
            format!("Async operation completed for {}", name)
        })
    }
}

/// 具体异步创建者
pub struct AsyncConcreteCreator {
    creator_name: String,
}

impl AsyncConcreteCreator {
    pub fn new(creator_name: String) -> Self {
        AsyncConcreteCreator { creator_name }
    }
}

impl AsyncCreator for AsyncConcreteCreator {
    fn create_product_async(&self) -> Pin<Box<dyn Future<Output = Box<dyn AsyncProduct + Send>> + Send>> {
        let creator_name = self.creator_name.clone();
        
        Box::pin(async move {
            // 模拟异步创建过程
            sleep(Duration::from_millis(100)).await;
            
            Box::new(AsyncConcreteProduct::new(
                format!("Product from {}", creator_name),
                200,
            )) as Box<dyn AsyncProduct + Send>
        })
    }
}
```

### 4.5 测试实现 (Test Implementation)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio;

    #[test]
    fn test_basic_factory_method() {
        let creator_a = ConcreteCreatorA;
        let creator_b = ConcreteCreatorB;

        let product_a = creator_a.factory_method();
        let product_b = creator_b.factory_method();

        assert_eq!(product_a.get_name(), "Product A");
        assert_eq!(product_b.get_name(), "Product B");

        assert!(product_a.operation().contains("operation A"));
        assert!(product_b.operation().contains("operation B"));
    }

    #[test]
    fn test_generic_factory_method() {
        let creator = GenericConcreteCreator::new(1);
        let product = creator.create_product();

        assert_eq!(product.get_id(), 100);
        assert!(product.get_creator_info().contains("Generic Creator 1"));
        assert!(product.operation().contains("Product from Creator 1"));
    }

    #[test]
    fn test_parameterized_factory_method() {
        let creator = ParameterizedConcreteCreator;
        let mut config = HashMap::new();
        config.insert("key1".to_string(), "value1".to_string());
        config.insert("key2".to_string(), "value2".to_string());

        let product = creator.create_product(ProductType::TypeA, config.clone());
        
        assert_eq!(product.get_type(), ProductType::TypeA);
        assert_eq!(product.get_config(), config);
        
        let result = product.execute().unwrap();
        assert!(result.contains("Type A"));
    }

    #[tokio::test]
    async fn test_async_factory_method() {
        let creator = AsyncConcreteCreator::new("TestCreator".to_string());
        let product = creator.create_product_async().await;

        assert_eq!(product.get_name(), "Product from TestCreator");
        
        let operation_result = product.get_async_operation().await;
        assert!(operation_result.contains("Async operation completed"));
    }

    #[test]
    fn test_factory_method_polymorphism() {
        let creators: Vec<Box<dyn Creator>> = vec![
            Box::new(ConcreteCreatorA),
            Box::new(ConcreteCreatorB),
        ];

        let mut products = Vec::new();
        for creator in creators {
            products.push(creator.factory_method());
        }

        assert_eq!(products.len(), 2);
        assert_eq!(products[0].get_name(), "Product A");
        assert_eq!(products[1].get_name(), "Product B");
    }

    #[test]
    fn test_factory_method_extension() {
        // 测试扩展性：添加新的产品类型
        struct ConcreteProductC {
            name: String,
        }

        impl ConcreteProductC {
            pub fn new() -> Self {
                ConcreteProductC {
                    name: "Product C".to_string(),
                }
            }
        }

        impl Product for ConcreteProductC {
            fn operation(&self) -> String {
                format!("{}: Performing operation C", self.name)
            }

            fn get_name(&self) -> &str {
                &self.name
            }
        }

        struct ConcreteCreatorC;

        impl Creator for ConcreteCreatorC {
            fn factory_method(&self) -> Box<dyn Product> {
                Box::new(ConcreteProductC::new())
            }
        }

        let creator_c = ConcreteCreatorC;
        let product_c = creator_c.factory_method();

        assert_eq!(product_c.get_name(), "Product C");
        assert!(product_c.operation().contains("operation C"));
    }
}
```

---

## 5. 性能分析 (Performance Analysis)

### 5.1 时间复杂度分析 (Time Complexity Analysis)

-****定理 5**.1.1 (创建时间复杂度)**

工厂方法模式的创建时间复杂度为 $O(1)$。

**证明**:

- 方法调用：$O(1)$
- 对象创建：$O(1)$
- 返回对象：$O(1)$

因此，总时间复杂度为 $O(1)$。

### 5.2 空间复杂度分析 (Space Complexity Analysis)

-****定理 5**.2.1 (空间复杂度)**

工厂方法模式的空间复杂度为 $O(1)$。

**证明**:

- 对象存储：$O(1)$
- 方法调用栈：$O(1)$
- 临时变量：$O(1)$

因此，总空间复杂度为 $O(1)$。

### 5.3 内存安全分析 (Memory Safety Analysis)

-****定理 5**.3.1 (内存安全)**

Rust实现的工厂方法模式是内存安全的。

**证明**:

1. **所有权安全**: 使用 `Box<dyn Trait>` 确保所有权管理
2. **生命周期安全**: 编译时生命周期检查
3. **类型安全**: 特征对象提供类型安全
4. **线程安全**: 使用 `Send` 特征确保线程安全

### 5.4 性能基准测试 (Performance Benchmark)

```rust
use std::time::Instant;

pub fn benchmark_factory_method() {
    let iterations = 1_000_000;
    
    // 测试基础工厂方法
    let start = Instant::now();
    let creator_a = ConcreteCreatorA;
    for _ in 0..iterations {
        let _product = creator_a.factory_method();
    }
    let duration = start.elapsed();
    println!("Basic Factory Method: {:?} for {} iterations", duration, iterations);
    
    // 测试泛型工厂方法
    let start = Instant::now();
    let creator = GenericConcreteCreator::new(1);
    for _ in 0..iterations {
        let _product = creator.create_product();
    }
    let duration = start.elapsed();
    println!("Generic Factory Method: {:?} for {} iterations", duration, iterations);
}
```

---

## 6. 应用场景 (Application Scenarios)

### 6.1 文档编辑器 (Document Editor)

```rust
/// 文档抽象
pub trait Document {
    fn open(&self) -> String;
    fn save(&self) -> String;
    fn close(&self) -> String;
}

/// 具体文档类型
pub struct TextDocument;
pub struct PDFDocument;
pub struct WordDocument;

impl Document for TextDocument {
    fn open(&self) -> String { "Opening text document".to_string() }
    fn save(&self) -> String { "Saving text document".to_string() }
    fn close(&self) -> String { "Closing text document".to_string() }
}

impl Document for PDFDocument {
    fn open(&self) -> String { "Opening PDF document".to_string() }
    fn save(&self) -> String { "Saving PDF document".to_string() }
    fn close(&self) -> String { "Closing PDF document".to_string() }
}

impl Document for WordDocument {
    fn open(&self) -> String { "Opening Word document".to_string() }
    fn save(&self) -> String { "Saving Word document".to_string() }
    fn close(&self) -> String { "Closing Word document".to_string() }
}

/// 应用程序抽象
pub trait Application {
    fn create_document(&self) -> Box<dyn Document>;
    fn run(&self) -> String {
        let doc = self.create_document();
        format!("{} -> {} -> {}", doc.open(), doc.save(), doc.close())
    }
}

/// 具体应用程序
pub struct TextEditor;
pub struct PDFViewer;
pub struct WordProcessor;

impl Application for TextEditor {
    fn create_document(&self) -> Box<dyn Document> {
        Box::new(TextDocument)
    }
}

impl Application for PDFViewer {
    fn create_document(&self) -> Box<dyn Document> {
        Box::new(PDFDocument)
    }
}

impl Application for WordProcessor {
    fn create_document(&self) -> Box<dyn Document> {
        Box::new(WordDocument)
    }
}
```

### 6.2 数据库连接工厂 (Database Connection Factory)

```rust
use std::collections::HashMap;

/// 数据库连接抽象
pub trait DatabaseConnection {
    fn connect(&self) -> Result<String, String>;
    fn execute_query(&self, query: &str) -> Result<String, String>;
    fn disconnect(&self) -> Result<String, String>;
}

/// 具体数据库连接
pub struct MySQLConnection {
    host: String,
    port: u16,
    database: String,
}

impl MySQLConnection {
    pub fn new(host: String, port: u16, database: String) -> Self {
        MySQLConnection { host, port, database }
    }
}

impl DatabaseConnection for MySQLConnection {
    fn connect(&self) -> Result<String, String> {
        Ok(format!("Connected to MySQL at {}:{}", self.host, self.port))
    }

    fn execute_query(&self, query: &str) -> Result<String, String> {
        Ok(format!("MySQL executed: {}", query))
    }

    fn disconnect(&self) -> Result<String, String> {
        Ok("Disconnected from MySQL".to_string())
    }
}

pub struct PostgreSQLConnection {
    host: String,
    port: u16,
    database: String,
}

impl PostgreSQLConnection {
    pub fn new(host: String, port: u16, database: String) -> Self {
        PostgreSQLConnection { host, port, database }
    }
}

impl DatabaseConnection for PostgreSQLConnection {
    fn connect(&self) -> Result<String, String> {
        Ok(format!("Connected to PostgreSQL at {}:{}", self.host, self.port))
    }

    fn execute_query(&self, query: &str) -> Result<String, String> {
        Ok(format!("PostgreSQL executed: {}", query))
    }

    fn disconnect(&self) -> Result<String, String> {
        Ok("Disconnected from PostgreSQL".to_string())
    }
}

/// 数据库连接工厂
pub trait DatabaseConnectionFactory {
    fn create_connection(&self, config: HashMap<String, String>) -> Box<dyn DatabaseConnection>;
}

/// 具体工厂实现
pub struct MySQLConnectionFactory;

impl DatabaseConnectionFactory for MySQLConnectionFactory {
    fn create_connection(&self, config: HashMap<String, String>) -> Box<dyn DatabaseConnection> {
        let host = config.get("host").unwrap_or(&"localhost".to_string()).clone();
        let port = config.get("port").unwrap_or(&"3306".to_string()).parse().unwrap_or(3306);
        let database = config.get("database").unwrap_or(&"test".to_string()).clone();
        
        Box::new(MySQLConnection::new(host, port, database))
    }
}

pub struct PostgreSQLConnectionFactory;

impl DatabaseConnectionFactory for PostgreSQLConnectionFactory {
    fn create_connection(&self, config: HashMap<String, String>) -> Box<dyn DatabaseConnection> {
        let host = config.get("host").unwrap_or(&"localhost".to_string()).clone();
        let port = config.get("port").unwrap_or(&"5432".to_string()).parse().unwrap_or(5432);
        let database = config.get("database").unwrap_or(&"test".to_string()).clone();
        
        Box::new(PostgreSQLConnection::new(host, port, database))
    }
}
```

### 6.3 日志记录器工厂 (Logger Factory)

```rust
use std::io::{self, Write};

/// 日志记录器抽象
pub trait Logger {
    fn log(&mut self, level: &str, message: &str) -> Result<(), String>;
    fn set_level(&mut self, level: &str) -> Result<(), String>;
    fn get_level(&self) -> &str;
}

/// 控制台日志记录器
pub struct ConsoleLogger {
    level: String,
}

impl ConsoleLogger {
    pub fn new() -> Self {
        ConsoleLogger {
            level: "INFO".to_string(),
        }
    }
}

impl Logger for ConsoleLogger {
    fn log(&mut self, level: &str, message: &str) -> Result<(), String> {
        println!("[{}] {}: {}", level, self.level, message);
        Ok(())
    }

    fn set_level(&mut self, level: &str) -> Result<(), String> {
        self.level = level.to_string();
        Ok(())
    }

    fn get_level(&self) -> &str {
        &self.level
    }
}

/// 文件日志记录器
pub struct FileLogger {
    level: String,
    file_path: String,
}

impl FileLogger {
    pub fn new(file_path: String) -> Self {
        FileLogger {
            level: "INFO".to_string(),
            file_path,
        }
    }
}

impl Logger for FileLogger {
    fn log(&mut self, level: &str, message: &str) -> Result<(), String> {
        // 模拟文件写入
        println!("Writing to file {}: [{}] {}: {}", self.file_path, level, self.level, message);
        Ok(())
    }

    fn set_level(&mut self, level: &str) -> Result<(), String> {
        self.level = level.to_string();
        Ok(())
    }

    fn get_level(&self) -> &str {
        &self.level
    }
}

/// 日志记录器工厂
pub trait LoggerFactory {
    fn create_logger(&self, config: HashMap<String, String>) -> Box<dyn Logger>;
}

/// 控制台日志记录器工厂
pub struct ConsoleLoggerFactory;

impl LoggerFactory for ConsoleLoggerFactory {
    fn create_logger(&self, _config: HashMap<String, String>) -> Box<dyn Logger> {
        Box::new(ConsoleLogger::new())
    }
}

/// 文件日志记录器工厂
pub struct FileLoggerFactory;

impl LoggerFactory for FileLoggerFactory {
    fn create_logger(&self, config: HashMap<String, String>) -> Box<dyn Logger> {
        let file_path = config.get("file_path").unwrap_or(&"app.log".to_string()).clone();
        Box::new(FileLogger::new(file_path))
    }
}
```

---

## 7. 变体模式 (Variant Patterns)

### 7.1 简单工厂 (Simple Factory)

```rust
/// 简单工厂模式
pub struct SimpleFactory;

impl SimpleFactory {
    pub fn create_product(product_type: &str) -> Option<Box<dyn Product>> {
        match product_type {
            "A" => Some(Box::new(ConcreteProductA::new())),
            "B" => Some(Box::new(ConcreteProductB::new())),
            _ => None,
        }
    }
}
```

### 7.2 静态工厂方法 (Static Factory Method)

```rust
/// 静态工厂方法
pub struct StaticFactory;

impl StaticFactory {
    pub fn create_product_a() -> Box<dyn Product> {
        Box::new(ConcreteProductA::new())
    }

    pub fn create_product_b() -> Box<dyn Product> {
        Box::new(ConcreteProductB::new())
    }

    pub fn create_product_by_type(product_type: &str) -> Option<Box<dyn Product>> {
        match product_type {
            "A" => Some(Self::create_product_a()),
            "B" => Some(Self::create_product_b()),
            _ => None,
        }
    }
}
```

### 7.3 工厂方法链 (Factory Method Chain)

```rust
/// 工厂方法链
pub trait ChainedCreator {
    fn create_product(&self) -> Box<dyn Product>;
    fn create_enhanced_product(&self) -> Box<dyn Product> {
        let base_product = self.create_product();
        // 在这里可以添加增强逻辑
        base_product
    }
}

impl ChainedCreator for ConcreteCreatorA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA::new())
    }
}
```

---

## 8. 总结 (Summary)

### 8.1 设计模式特性 (Pattern Characteristics)

1. **抽象性**: 定义创建对象的接口
2. **多态性**: 支持多态创建
3. **扩展性**: 易于添加新产品类型
4. **封装性**: 封装对象创建逻辑

### 8.2 实现要点 (Implementation Points)

1. **抽象产品**: 定义产品接口
2. **具体产品**: 实现具体产品类
3. **抽象创建者**: 定义工厂方法接口
4. **具体创建者**: 实现具体工厂方法

### 8.3 使用建议 (Usage Recommendations)

1. **适用场景**: 对象创建复杂、需要扩展、支持多态
2. **注意事项**: 避免过度设计简单对象创建
3. **性能考虑**: 创建开销小，但增加了抽象层
4. **测试策略**: 易于进行单元测试和模拟

---

**文档版本**: 1.0
**最后更新**: 2024-12-19
**状态**: 完成

