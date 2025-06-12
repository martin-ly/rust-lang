# 建造者模式 (Builder Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [形式化定义 (Formal Definition)](#1-形式化定义-formal-definition)
2. [数学理论基础 (Mathematical Foundation)](#2-数学理论基础-mathematical-foundation)
3. [定理与证明 (Theorems and Proofs)](#3-定理与证明-theorems-and-proofs)
4. [Rust实现 (Rust Implementation)](#4-rust实现-rust-implementation)
5. [应用场景 (Application Scenarios)](#5-应用场景-application-scenarios)
6. [性能分析 (Performance Analysis)](#6-性能分析-performance-analysis)

---

## 1. 形式化定义 (Formal Definition)

### 1.1 建造者模式六元组 (Builder Pattern Sextuple)

-**定义 1.1.1 (建造者模式)**

设 $B = (N, I, S, R, C, O)$ 为建造者模式，其中：

- $N = \{\text{"Builder"}\}$ (模式名称)
- $I = \{\text{"分步构建复杂对象"}, \text{"控制构建过程"}\}$ (意图描述)
- $S = \{\text{Product}, \text{Builder}, \text{ConcreteBuilder}, \text{Director}, \text{Step}, \text{Result}\}$ (结构定义)
- $R = \{(\text{Builder}, \text{build\_step}), (\text{Director}, \text{Builder}), (\text{ConcreteBuilder}, \text{Product})\}$ (关系映射)
- $C = \{\text{构建顺序约束}, \text{步骤完整性约束}, \text{结果一致性约束}\}$ (约束条件)
- $O = \{\text{构建顺序}, \text{步骤依赖}\}$ (操作定义)

### 1.2 构建过程定义 (Construction Process Definition)

-**定义 1.2.1 (构建步骤序列)**

设 $\mathcal{S} = \langle s_1, s_2, \ldots, s_n \rangle$ 为构建步骤序列，满足：

$$\forall i < j, \text{Step}(s_i) \prec \text{Step}(s_j)$$

-**定义 1.2.2 (构建结果)**

设 $P$ 为最终产品，满足：

$$P = \text{Result}(\text{Execute}(\mathcal{S}))$$

---

## 2. 数学理论基础 (Mathematical Foundation)

### 2.1 构建顺序理论 (Construction Order Theory)

-**定义 2.1.1 (步骤依赖关系)**

步骤 $s_i$ 依赖于步骤 $s_j$，记作 $s_i \prec s_j$，当且仅当：

$$\text{Input}(s_i) \cap \text{Output}(s_j) \neq \emptyset$$

-**定义 2.1.2 (构建完整性)**

构建过程是完整的，当且仅当：

$$\forall \text{required\_part} \in \text{Product}, \exists s \in \mathcal{S} : \text{creates}(s, \text{required\_part})$$

### 2.2 构建一致性理论 (Construction Consistency Theory)

-**定义 2.2.1 (步骤一致性)**

构建步骤是一致的，当且仅当：

$$\forall s_i, s_j \in \mathcal{S}, \text{Compatible}(\text{Output}(s_i), \text{Input}(s_j))$$

---

## 3. 定理与证明 (Theorems and Proofs)

### 3.1 构建顺序定理 (Construction Order Theorem)

-**定理 3.1.1 (构建顺序正确性)**

对于任意建造者模式 $B$，构建步骤的执行顺序是正确的。

**证明**:
设 $\mathcal{S} = \langle s_1, s_2, \ldots, s_n \rangle$ 为构建步骤序列。

根据定义 1.2.1，$\forall i < j, \text{Step}(s_i) \prec \text{Step}(s_j)$。

因此，构建顺序满足依赖关系约束。

-**定理 3.1.2 (构建完整性)**

建造者模式保证构建过程的完整性。

**证明**:
根据定义 2.1.2，构建过程是完整的当且仅当所有必需的部分都被创建。

在建造者模式中，Director 控制构建过程，确保所有必需步骤都被执行。

因此，构建过程是完整的。

-**定理 3.1.3 (构建一致性)**

建造者模式保证构建步骤的一致性。

**证明**:
根据定义 2.2.1，构建步骤是一致的当且仅当所有步骤的输入输出兼容。

在建造者模式中，Builder 接口定义了统一的构建方法，确保步骤兼容性。

因此，构建步骤是一致的。

### 3.2 复杂度分析定理 (Complexity Analysis Theorem)

-**定理 3.2.1 (构建时间复杂度)**

建造者模式的构建时间复杂度为 $O(n)$，其中 $n$ 是构建步骤的数量。

**证明**:
设 $\mathcal{S} = \langle s_1, s_2, \ldots, s_n \rangle$ 为构建步骤序列。

每个步骤的执行时间为常数时间 $O(1)$。

因此，总构建时间为 $O(n)$。

-**定理 3.2.2 (空间复杂度)**

建造者模式的空间复杂度为 $O(1)$。

**证明**:
建造者模式使用固定的内存空间来存储中间状态。

不随构建步骤数量增加而增加额外空间。

因此，空间复杂度为 $O(1)$。

---

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现 (Basic Implementation)

```rust
/// 产品
#[derive(Debug, Clone)]
pub struct Product {
    pub part_a: String,
    pub part_b: String,
    pub part_c: String,
}

impl Product {
    pub fn new() -> Self {
        Product {
            part_a: String::new(),
            part_b: String::new(),
            part_c: String::new(),
        }
    }

    pub fn display(&self) {
        println!("Product parts:");
        println!("  Part A: {}", self.part_a);
        println!("  Part B: {}", self.part_b);
        println!("  Part C: {}", self.part_c);
    }
}

/// 抽象建造者
pub trait Builder {
    fn build_part_a(&mut self, part: String);
    fn build_part_b(&mut self, part: String);
    fn build_part_c(&mut self, part: String);
    fn get_result(&self) -> Product;
}

/// 具体建造者
pub struct ConcreteBuilder {
    product: Product,
}

impl ConcreteBuilder {
    pub fn new() -> Self {
        ConcreteBuilder {
            product: Product::new(),
        }
    }
}

impl Builder for ConcreteBuilder {
    fn build_part_a(&mut self, part: String) {
        self.product.part_a = part;
    }

    fn build_part_b(&mut self, part: String) {
        self.product.part_b = part;
    }

    fn build_part_c(&mut self, part: String) {
        self.product.part_c = part;
    }

    fn get_result(&self) -> Product {
        self.product.clone()
    }
}

/// 指导者
pub struct Director;

impl Director {
    pub fn construct(&self, builder: &mut impl Builder) -> Product {
        builder.build_part_a("Part A".to_string());
        builder.build_part_b("Part B".to_string());
        builder.build_part_c("Part C".to_string());
        builder.get_result()
    }

    pub fn construct_custom(&self, builder: &mut impl Builder, parts: Vec<String>) -> Product {
        if parts.len() >= 1 {
            builder.build_part_a(parts[0].clone());
        }
        if parts.len() >= 2 {
            builder.build_part_b(parts[1].clone());
        }
        if parts.len() >= 3 {
            builder.build_part_c(parts[2].clone());
        }
        builder.get_result()
    }
}
```

### 4.2 泛型建造者实现 (Generic Builder Implementation)

```rust
use std::collections::HashMap;

/// 泛型产品
#[derive(Debug, Clone)]
pub struct GenericProduct<T> {
    parts: HashMap<String, T>,
}

impl<T: Clone> GenericProduct<T> {
    pub fn new() -> Self {
        GenericProduct {
            parts: HashMap::new(),
        }
    }

    pub fn add_part(&mut self, name: String, part: T) {
        self.parts.insert(name, part);
    }

    pub fn get_part(&self, name: &str) -> Option<&T> {
        self.parts.get(name)
    }

    pub fn get_all_parts(&self) -> &HashMap<String, T> {
        &self.parts
    }
}

/// 泛型建造者
pub trait GenericBuilder<T> {
    fn build_part(&mut self, name: String, part: T);
    fn get_result(&self) -> GenericProduct<T>;
    fn reset(&mut self);
}

/// 泛型具体建造者
pub struct GenericConcreteBuilder<T> {
    product: GenericProduct<T>,
}

impl<T: Clone> GenericConcreteBuilder<T> {
    pub fn new() -> Self {
        GenericConcreteBuilder {
            product: GenericProduct::new(),
        }
    }
}

impl<T: Clone> GenericBuilder<T> for GenericConcreteBuilder<T> {
    fn build_part(&mut self, name: String, part: T) {
        self.product.add_part(name, part);
    }

    fn get_result(&self) -> GenericProduct<T> {
        self.product.clone()
    }

    fn reset(&mut self) {
        self.product = GenericProduct::new();
    }
}

/// 泛型指导者
pub struct GenericDirector;

impl GenericDirector {
    pub fn construct<T: Clone>(
        &self,
        builder: &mut impl GenericBuilder<T>,
        parts: HashMap<String, T>,
    ) -> GenericProduct<T> {
        for (name, part) in parts {
            builder.build_part(name, part);
        }
        builder.get_result()
    }
}
```

### 4.3 链式建造者实现 (Fluent Builder Implementation)

```rust
/// 链式建造者
pub struct FluentBuilder {
    product: Product,
}

impl FluentBuilder {
    pub fn new() -> Self {
        FluentBuilder {
            product: Product::new(),
        }
    }

    pub fn part_a(mut self, part: String) -> Self {
        self.product.part_a = part;
        self
    }

    pub fn part_b(mut self, part: String) -> Self {
        self.product.part_b = part;
        self
    }

    pub fn part_c(mut self, part: String) -> Self {
        self.product.part_c = part;
        self
    }

    pub fn build(self) -> Product {
        self.product
    }
}

/// 带验证的链式建造者
pub struct ValidatedBuilder {
    product: Product,
    validation_errors: Vec<String>,
}

impl ValidatedBuilder {
    pub fn new() -> Self {
        ValidatedBuilder {
            product: Product::new(),
            validation_errors: Vec::new(),
        }
    }

    pub fn part_a(mut self, part: String) -> Self {
        if part.is_empty() {
            self.validation_errors.push("Part A cannot be empty".to_string());
        } else {
            self.product.part_a = part;
        }
        self
    }

    pub fn part_b(mut self, part: String) -> Self {
        if part.is_empty() {
            self.validation_errors.push("Part B cannot be empty".to_string());
        } else {
            self.product.part_b = part;
        }
        self
    }

    pub fn part_c(mut self, part: String) -> Self {
        if part.is_empty() {
            self.validation_errors.push("Part C cannot be empty".to_string());
        } else {
            self.product.part_c = part;
        }
        self
    }

    pub fn build(self) -> Result<Product, Vec<String>> {
        if self.validation_errors.is_empty() {
            Ok(self.product)
        } else {
            Err(self.validation_errors)
        }
    }
}
```

### 4.4 异步建造者实现 (Async Builder Implementation)

```rust
use std::future::Future;
use tokio::time::{sleep, Duration};

/// 异步产品
#[derive(Debug, Clone)]
pub struct AsyncProduct {
    pub part_a: String,
    pub part_b: String,
    pub part_c: String,
    pub metadata: HashMap<String, String>,
}

impl AsyncProduct {
    pub fn new() -> Self {
        AsyncProduct {
            part_a: String::new(),
            part_b: String::new(),
            part_c: String::new(),
            metadata: HashMap::new(),
        }
    }
}

/// 异步建造者
pub trait AsyncBuilder {
    fn build_part_a(&mut self, part: String) -> impl Future<Output = ()> + Send;
    fn build_part_b(&mut self, part: String) -> impl Future<Output = ()> + Send;
    fn build_part_c(&mut self, part: String) -> impl Future<Output = ()> + Send;
    fn get_result(&self) -> AsyncProduct;
}

/// 异步具体建造者
pub struct AsyncConcreteBuilder {
    product: AsyncProduct,
}

impl AsyncConcreteBuilder {
    pub fn new() -> Self {
        AsyncConcreteBuilder {
            product: AsyncProduct::new(),
        }
    }
}

impl AsyncBuilder for AsyncConcreteBuilder {
    async fn build_part_a(&mut self, part: String) {
        // 模拟异步操作
        sleep(Duration::from_millis(100)).await;
        self.product.part_a = part;
        self.product.metadata.insert("part_a_built".to_string(), "true".to_string());
    }

    async fn build_part_b(&mut self, part: String) {
        // 模拟异步操作
        sleep(Duration::from_millis(150)).await;
        self.product.part_b = part;
        self.product.metadata.insert("part_b_built".to_string(), "true".to_string());
    }

    async fn build_part_c(&mut self, part: String) {
        // 模拟异步操作
        sleep(Duration::from_millis(200)).await;
        self.product.part_c = part;
        self.product.metadata.insert("part_c_built".to_string(), "true".to_string());
    }

    fn get_result(&self) -> AsyncProduct {
        self.product.clone()
    }
}

/// 异步指导者
pub struct AsyncDirector;

impl AsyncDirector {
    pub async fn construct(&self, builder: &mut impl AsyncBuilder) -> AsyncProduct {
        builder.build_part_a("Async Part A".to_string()).await;
        builder.build_part_b("Async Part B".to_string()).await;
        builder.build_part_c("Async Part C".to_string()).await;
        builder.get_result()
    }
}
```

---

## 5. 应用场景 (Application Scenarios)

### 5.1 数据库查询构建器 (Database Query Builder)

```rust
/// SQL查询构建器
pub struct SqlQueryBuilder {
    select: Vec<String>,
    from: String,
    where_conditions: Vec<String>,
    order_by: Vec<String>,
    limit: Option<usize>,
}

impl SqlQueryBuilder {
    pub fn new() -> Self {
        SqlQueryBuilder {
            select: Vec::new(),
            from: String::new(),
            where_conditions: Vec::new(),
            order_by: Vec::new(),
            limit: None,
        }
    }

    pub fn select(mut self, columns: Vec<String>) -> Self {
        self.select = columns;
        self
    }

    pub fn from(mut self, table: String) -> Self {
        self.from = table;
        self
    }

    pub fn where_condition(mut self, condition: String) -> Self {
        self.where_conditions.push(condition);
        self
    }

    pub fn order_by(mut self, columns: Vec<String>) -> Self {
        self.order_by = columns;
        self
    }

    pub fn limit(mut self, limit: usize) -> Self {
        self.limit = Some(limit);
        self
    }

    pub fn build(self) -> String {
        let mut query = format!("SELECT {}", self.select.join(", "));
        query.push_str(&format!(" FROM {}", self.from));
        
        if !self.where_conditions.is_empty() {
            query.push_str(&format!(" WHERE {}", self.where_conditions.join(" AND ")));
        }
        
        if !self.order_by.is_empty() {
            query.push_str(&format!(" ORDER BY {}", self.order_by.join(", ")));
        }
        
        if let Some(limit) = self.limit {
            query.push_str(&format!(" LIMIT {}", limit));
        }
        
        query
    }
}
```

### 5.2 HTTP请求构建器 (HTTP Request Builder)

```rust
use std::collections::HashMap;

/// HTTP请求构建器
pub struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        HttpRequestBuilder {
            method: "GET".to_string(),
            url: String::new(),
            headers: HashMap::new(),
            body: None,
        }
    }

    pub fn method(mut self, method: String) -> Self {
        self.method = method;
        self
    }

    pub fn url(mut self, url: String) -> Self {
        self.url = url;
        self
    }

    pub fn header(mut self, key: String, value: String) -> Self {
        self.headers.insert(key, value);
        self
    }

    pub fn body(mut self, body: String) -> Self {
        self.body = Some(body);
        self
    }

    pub fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
        }
    }
}

#[derive(Debug)]
pub struct HttpRequest {
    pub method: String,
    pub url: String,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}
```

### 5.3 配置对象构建器 (Configuration Object Builder)

```rust
use std::collections::HashMap;

/// 应用配置构建器
pub struct ConfigBuilder {
    database: DatabaseConfig,
    server: ServerConfig,
    logging: LoggingConfig,
    features: HashMap<String, bool>,
}

#[derive(Debug, Clone)]
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub password: String,
    pub database: String,
}

#[derive(Debug, Clone)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub timeout: u64,
}

#[derive(Debug, Clone)]
pub struct LoggingConfig {
    pub level: String,
    pub file: String,
    pub max_size: usize,
    pub rotation: String,
}

impl ConfigBuilder {
    pub fn new() -> Self {
        ConfigBuilder {
            database: DatabaseConfig {
                host: "localhost".to_string(),
                port: 5432,
                username: "user".to_string(),
                password: "password".to_string(),
                database: "app".to_string(),
            },
            server: ServerConfig {
                host: "0.0.0.0".to_string(),
                port: 8080,
                workers: 4,
                timeout: 30,
            },
            logging: LoggingConfig {
                level: "info".to_string(),
                file: "app.log".to_string(),
                max_size: 100,
                rotation: "daily".to_string(),
            },
            features: HashMap::new(),
        }
    }

    pub fn database(mut self, config: DatabaseConfig) -> Self {
        self.database = config;
        self
    }

    pub fn server(mut self, config: ServerConfig) -> Self {
        self.server = config;
        self
    }

    pub fn logging(mut self, config: LoggingConfig) -> Self {
        self.logging = config;
        self
    }

    pub fn feature(mut self, name: String, enabled: bool) -> Self {
        self.features.insert(name, enabled);
        self
    }

    pub fn build(self) -> AppConfig {
        AppConfig {
            database: self.database,
            server: self.server,
            logging: self.logging,
            features: self.features,
        }
    }
}

#[derive(Debug)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub server: ServerConfig,
    pub logging: LoggingConfig,
    pub features: HashMap<String, bool>,
}
```

---

## 6. 性能分析 (Performance Analysis)

### 6.1 时间复杂度分析

**构建步骤执行**: $O(n)$

- 每个构建步骤的执行时间为常数时间
- 总构建时间为步骤数量的线性函数

**内存分配**: $O(1)$

- 建造者模式使用固定的内存空间
- 不随构建步骤数量增加而增加额外空间

### 6.2 空间复杂度分析

**中间状态存储**: $O(1)$

- 建造者维护固定的产品状态
- 状态大小不随构建过程变化

**方法调用栈**: $O(1)$

- 方法调用深度固定
- 不产生递归调用

### 6.3 性能优化策略

-**1. 对象池模式**

```rust
pub struct BuilderPool {
    builders: Vec<ConcreteBuilder>,
}

impl BuilderPool {
    pub fn new(capacity: usize) -> Self {
        let mut builders = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            builders.push(ConcreteBuilder::new());
        }
        BuilderPool { builders }
    }

    pub fn acquire(&mut self) -> Option<ConcreteBuilder> {
        self.builders.pop()
    }

    pub fn release(&mut self, builder: ConcreteBuilder) {
        if self.builders.len() < self.builders.capacity() {
            self.builders.push(builder);
        }
    }
}
```

-**2. 缓存机制**

```rust
pub struct CachedBuilder {
    cache: HashMap<String, Product>,
    builder: ConcreteBuilder,
}

impl CachedBuilder {
    pub fn new() -> Self {
        CachedBuilder {
            cache: HashMap::new(),
            builder: ConcreteBuilder::new(),
        }
    }

    pub fn build_with_cache(&mut self, key: String, parts: Vec<String>) -> Product {
        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }

        let product = self.build_product(parts);
        self.cache.insert(key, product.clone());
        product
    }

    fn build_product(&mut self, parts: Vec<String>) -> Product {
        // 构建逻辑
        Product::new()
    }
}
```

---

## 总结

建造者模式通过分步构建复杂对象，提供了灵活的对象创建机制。其形式化模型确保了构建过程的正确性、完整性和一致性，而Rust实现展示了模式在实际应用中的强大能力。

该模式特别适用于：

- 复杂对象的创建过程
- 需要控制构建步骤的场景
- 支持不同构建配置的应用
- 需要验证构建过程的系统

通过形式化分析和Rust实现，建造者模式展现了其在软件架构中的重要价值。
