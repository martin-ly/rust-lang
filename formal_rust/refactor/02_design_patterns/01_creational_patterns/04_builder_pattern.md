# 建造者模式形式化重构 (Builder Pattern Formal Refactoring)

## 目录

1. [形式化定义](#1-形式化定义)
2. [数学理论基础](#2-数学理论基础)
3. [核心定理与证明](#3-核心定理与证明)
4. [Rust实现](#4-rust实现)
5. [应用场景](#6-应用场景)
6. [变体模式](#6-变体模式)
7. [质量属性分析](#7-质量属性分析)
8. [总结](#8-总结)

---

## 1. 形式化定义

### 1.1 建造者模式五元组

**定义1.1 (建造者模式五元组)**
设 $B = (N, I, S, R, C)$ 为建造者模式，其中：

- $N = \{\text{Builder}, \text{ConcreteBuilder}_1, \ldots, \text{ConcreteBuilder}_n, \text{Director}, \text{Product}\}$ 是类集合
- $I = \{\text{分步构建}, \text{复杂对象创建}, \text{构建过程控制}, \text{表示分离}\}$ 是意图集合
- $S = \{\text{Builder}, \text{ConcreteBuilder}, \text{Director}, \text{Product}, \text{构建步骤}\}$ 是结构集合
- $R = \{(b, p) | b \in \text{Builder}, p \in \text{Product}\} \cup \{(d, b) | d \in \text{Director}, b \in \text{Builder}\}$ 是关系集合
- $C = \{\text{构建步骤有序}, \text{产品完整性}, \text{构建过程可控制}\}$ 是约束集合

### 1.2 构建过程形式化定义

**定义1.2 (构建过程四元组)**
设 $BP = (S, O, V, T)$ 为构建过程，其中：

- $S = \{s_1, s_2, \ldots, s_n\}$ 是构建步骤集合
- $O = \{o_1, o_2, \ldots, o_m\}$ 是操作集合
- $V = \{v_1, v_2, \ldots, v_k\}$ 是验证规则集合
- $T: S \times O \rightarrow V$ 是转换函数

### 1.3 产品状态定义

**定义1.3 (产品状态)**
产品 $P$ 在构建过程中的状态定义为：

$$\text{State}(P) = \{(a_1, v_1), (a_2, v_2), \ldots, (a_n, v_n)\}$$

其中 $a_i$ 是属性，$v_i$ 是值。

**定义1.4 (构建完整性)**
产品 $P$ 是完整的，当且仅当：

$$\forall a \in \text{RequiredAttributes}(P): \exists v: (a, v) \in \text{State}(P)$$

---

## 2. 数学理论基础

### 2.1 构建序列理论

**定义2.1 (构建序列)**
构建序列是一个有序的操作序列：

$$\text{BuildSequence} = [o_1, o_2, \ldots, o_n]$$

其中 $o_i$ 是构建操作。

**定义2.2 (构建序列有效性)**
构建序列是有效的，当且仅当：

$$\forall i < j: \text{dependency}(o_i, o_j) \Rightarrow \text{executed}(o_i) \text{ before } \text{executed}(o_j)$$

### 2.2 分步构建理论

**定义2.3 (分步构建)**
分步构建是一个状态转换序列：

$$\text{State}_0 \xrightarrow{o_1} \text{State}_1 \xrightarrow{o_2} \cdots \xrightarrow{o_n} \text{State}_n$$

**定义2.4 (构建不变性)**
构建过程中的不变性定义为：

$$\forall \text{State}_i: \text{Invariant}(\text{State}_i) = \text{true}$$

### 2.3 表示分离理论

**定义2.5 (表示分离)**
构建过程与产品表示分离：

$$\text{BuildProcess} \perp \text{ProductRepresentation}$$

---

## 3. 核心定理与证明

### 3.1 构建完整性定理

**定理3.1.1 (构建完整性保证)**
如果构建序列是有效的且所有必需属性都被设置，则构建的产品是完整的。

**证明：**
设 $B = (N, I, S, R, C)$ 为建造者模式，$BP$ 为构建过程。

1. 根据定义1.4，产品完整性要求所有必需属性都有值
2. 构建序列有效性确保依赖关系满足
3. 所有构建步骤执行后，所有必需属性都被设置
4. 因此，构建的产品是完整的。

**推论3.1.1 (构建顺序无关性)**
如果构建操作之间无依赖关系，则构建顺序可以任意调整。

### 3.2 构建过程控制定理

**定理3.2.1 (构建过程可控性)**
建造者模式允许精确控制构建过程。

**证明：**

1. 每个构建步骤都是独立的方法调用
2. 可以条件性地执行某些步骤
3. 可以重复执行某些步骤
4. 可以跳过某些可选步骤
5. 因此，构建过程完全可控

**定理3.2.2 (构建过程可验证性)**
构建过程中的每个状态都可以验证。

**证明：**

1. 每个构建步骤后，产品状态都是确定的
2. 可以定义验证规则检查状态正确性
3. 可以检测构建错误和异常
4. 因此，构建过程可验证

### 3.3 表示分离定理

**定理3.3.1 (表示分离满足)**
建造者模式实现了构建过程与产品表示的分离。

**证明：**

1. Builder接口定义了构建步骤，不涉及具体产品表示
2. ConcreteBuilder实现构建逻辑，与产品表示解耦
3. Director控制构建过程，不依赖具体产品
4. 因此，表示分离得到保证

### 3.4 性能定理

**定理3.4.1 (构建复杂度)**
建造者模式的构建复杂度为 $O(|S|)$，其中 $|S|$ 是构建步骤数量。

**证明：**

1. 每个构建步骤执行一次
2. 步骤间无复杂依赖关系
3. 时间复杂度与步骤数量成正比

**定理3.4.2 (内存复杂度)**
建造者模式的内存复杂度为 $O(|A|)$，其中 $|A|$ 是产品属性数量。

**证明：**

1. 需要存储产品的所有属性
2. 构建过程中需要临时存储中间状态
3. 内存复杂度与属性数量成正比

---

## 4. Rust实现

### 4.1 基础实现

```rust
// 产品
#[derive(Debug, Default)]
struct Product {
    part_a: Option<String>,
    part_b: Option<String>,
    part_c: Option<i32>,
    part_d: Option<bool>,
}

impl Product {
    fn builder() -> ProductBuilder {
        ProductBuilder::default()
    }
    
    fn is_complete(&self) -> bool {
        self.part_a.is_some() && self.part_b.is_some()
    }
}

// 抽象建造者
trait Builder {
    fn build_part_a(&mut self, value: String) -> &mut Self;
    fn build_part_b(&mut self, value: String) -> &mut Self;
    fn build_part_c(&mut self, value: i32) -> &mut Self;
    fn build_part_d(&mut self, value: bool) -> &mut Self;
    fn build(&self) -> Product;
}

// 具体建造者
#[derive(Default)]
struct ProductBuilder {
    part_a: Option<String>,
    part_b: Option<String>,
    part_c: Option<i32>,
    part_d: Option<bool>,
}

impl Builder for ProductBuilder {
    fn build_part_a(&mut self, value: String) -> &mut Self {
        self.part_a = Some(value);
        self
    }
    
    fn build_part_b(&mut self, value: String) -> &mut Self {
        self.part_b = Some(value);
        self
    }
    
    fn build_part_c(&mut self, value: i32) -> &mut Self {
        self.part_c = Some(value);
        self
    }
    
    fn build_part_d(&mut self, value: bool) -> &mut Self {
        self.part_d = Some(value);
        self
    }
    
    fn build(&self) -> Product {
        Product {
            part_a: self.part_a.clone(),
            part_b: self.part_b.clone(),
            part_c: self.part_c,
            part_d: self.part_d,
        }
    }
}

// 指导者
struct Director;

impl Director {
    fn construct_minimal_product(builder: &mut ProductBuilder) -> Product {
        builder
            .build_part_a("Default A".to_string())
            .build_part_b("Default B".to_string())
            .build()
    }
    
    fn construct_full_product(builder: &mut ProductBuilder) -> Product {
        builder
            .build_part_a("Full A".to_string())
            .build_part_b("Full B".to_string())
            .build_part_c(42)
            .build_part_d(true)
            .build()
    }
}
```

### 4.2 泛型实现

```rust
// 泛型产品
#[derive(Debug, Clone)]
struct GenericProduct<T, U, V> {
    field_1: Option<T>,
    field_2: Option<U>,
    field_3: Option<V>,
}

// 泛型建造者
struct GenericBuilder<T, U, V> {
    field_1: Option<T>,
    field_2: Option<U>,
    field_3: Option<V>,
}

impl<T, U, V> GenericBuilder<T, U, V> {
    fn new() -> Self {
        GenericBuilder {
            field_1: None,
            field_2: None,
            field_3: None,
        }
    }
    
    fn set_field_1(mut self, value: T) -> Self {
        self.field_1 = Some(value);
        self
    }
    
    fn set_field_2(mut self, value: U) -> Self {
        self.field_2 = Some(value);
        self
    }
    
    fn set_field_3(mut self, value: V) -> Self {
        self.field_3 = Some(value);
        self
    }
    
    fn build(self) -> GenericProduct<T, U, V> {
        GenericProduct {
            field_1: self.field_1,
            field_2: self.field_2,
            field_3: self.field_3,
        }
    }
}
```

### 4.3 验证建造者

```rust
// 验证规则
trait ValidationRule {
    fn validate(&self, product: &Product) -> Result<(), String>;
}

// 必需属性验证
struct RequiredFieldsValidation;

impl ValidationRule for RequiredFieldsValidation {
    fn validate(&self, product: &Product) -> Result<(), String> {
        if product.part_a.is_none() {
            return Err("Part A is required".to_string());
        }
        if product.part_b.is_none() {
            return Err("Part B is required".to_string());
        }
        Ok(())
    }
}

// 验证建造者
struct ValidatingBuilder {
    builder: ProductBuilder,
    validators: Vec<Box<dyn ValidationRule>>,
}

impl ValidatingBuilder {
    fn new() -> Self {
        let mut vb = ValidatingBuilder {
            builder: ProductBuilder::default(),
            validators: Vec::new(),
        };
        vb.validators.push(Box::new(RequiredFieldsValidation));
        vb
    }
    
    fn build_part_a(&mut self, value: String) -> &mut Self {
        self.builder.build_part_a(value);
        self
    }
    
    fn build_part_b(&mut self, value: String) -> &mut Self {
        self.builder.build_part_b(value);
        self
    }
    
    fn build(&self) -> Result<Product, String> {
        let product = self.builder.build();
        
        for validator in &self.validators {
            validator.validate(&product)?;
        }
        
        Ok(product)
    }
}
```

### 4.4 异步建造者

```rust
use std::future::Future;
use std::pin::Pin;

// 异步建造者
trait AsyncBuilder {
    fn build_part_a_async(&mut self, value: String) -> Pin<Box<dyn Future<Output = &mut Self> + Send>>;
    fn build_part_b_async(&mut self, value: String) -> Pin<Box<dyn Future<Output = &mut Self> + Send>>;
    fn build_async(&self) -> Pin<Box<dyn Future<Output = Product> + Send>>;
}

// 异步具体建造者
struct AsyncProductBuilder {
    builder: ProductBuilder,
}

impl AsyncBuilder for AsyncProductBuilder {
    fn build_part_a_async(&mut self, value: String) -> Pin<Box<dyn Future<Output = &mut Self> + Send>> {
        let builder = &mut self.builder;
        Box::pin(async move {
            builder.build_part_a(value);
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            self
        })
    }
    
    fn build_part_b_async(&mut self, value: String) -> Pin<Box<dyn Future<Output = &mut Self> + Send>> {
        let builder = &mut self.builder;
        Box::pin(async move {
            builder.build_part_b(value);
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            self
        })
    }
    
    fn build_async(&self) -> Pin<Box<dyn Future<Output = Product> + Send>> {
        let product = self.builder.build();
        Box::pin(async move {
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            product
        })
    }
}
```

---

## 5. 应用场景

### 5.1 配置对象构建

```rust
// 数据库配置
#[derive(Debug)]
struct DatabaseConfig {
    host: String,
    port: u16,
    username: String,
    password: String,
    database: String,
    max_connections: u32,
    timeout: u64,
}

impl DatabaseConfig {
    fn builder() -> DatabaseConfigBuilder {
        DatabaseConfigBuilder::new()
    }
}

struct DatabaseConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    username: Option<String>,
    password: Option<String>,
    database: Option<String>,
    max_connections: Option<u32>,
    timeout: Option<u64>,
}

impl DatabaseConfigBuilder {
    fn new() -> Self {
        DatabaseConfigBuilder {
            host: None,
            port: None,
            username: None,
            password: None,
            database: None,
            max_connections: None,
            timeout: None,
        }
    }
    
    fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }
    
    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    fn username(mut self, username: String) -> Self {
        self.username = Some(username);
        self
    }
    
    fn password(mut self, password: String) -> Self {
        self.password = Some(password);
        self
    }
    
    fn database(mut self, database: String) -> Self {
        self.database = Some(database);
        self
    }
    
    fn max_connections(mut self, max_connections: u32) -> Self {
        self.max_connections = Some(max_connections);
        self
    }
    
    fn timeout(mut self, timeout: u64) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    fn build(self) -> Result<DatabaseConfig, String> {
        Ok(DatabaseConfig {
            host: self.host.ok_or("Host is required")?,
            port: self.port.unwrap_or(5432),
            username: self.username.ok_or("Username is required")?,
            password: self.password.ok_or("Password is required")?,
            database: self.database.ok_or("Database is required")?,
            max_connections: self.max_connections.unwrap_or(10),
            timeout: self.timeout.unwrap_or(30),
        })
    }
}
```

### 5.2 HTTP请求构建

```rust
// HTTP请求
#[derive(Debug)]
struct HttpRequest {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<String>,
    timeout: Duration,
}

impl HttpRequest {
    fn builder() -> HttpRequestBuilder {
        HttpRequestBuilder::new()
    }
}

struct HttpRequestBuilder {
    method: Option<String>,
    url: Option<String>,
    headers: HashMap<String, String>,
    body: Option<String>,
    timeout: Option<Duration>,
}

impl HttpRequestBuilder {
    fn new() -> Self {
        HttpRequestBuilder {
            method: None,
            url: None,
            headers: HashMap::new(),
            body: None,
            timeout: None,
        }
    }
    
    fn method(mut self, method: String) -> Self {
        self.method = Some(method);
        self
    }
    
    fn url(mut self, url: String) -> Self {
        self.url = Some(url);
        self
    }
    
    fn header(mut self, key: String, value: String) -> Self {
        self.headers.insert(key, value);
        self
    }
    
    fn body(mut self, body: String) -> Self {
        self.body = Some(body);
        self
    }
    
    fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    fn build(self) -> Result<HttpRequest, String> {
        Ok(HttpRequest {
            method: self.method.ok_or("Method is required")?,
            url: self.url.ok_or("URL is required")?,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
        })
    }
}
```

### 5.3 游戏对象构建

```rust
// 游戏角色
#[derive(Debug)]
struct GameCharacter {
    name: String,
    class: CharacterClass,
    level: u32,
    attributes: Attributes,
    equipment: Equipment,
    skills: Vec<Skill>,
}

#[derive(Debug)]
enum CharacterClass {
    Warrior,
    Mage,
    Archer,
}

#[derive(Debug)]
struct Attributes {
    strength: u32,
    dexterity: u32,
    intelligence: u32,
    vitality: u32,
}

#[derive(Debug)]
struct Equipment {
    weapon: Option<Weapon>,
    armor: Option<Armor>,
    accessory: Option<Accessory>,
}

// 角色建造者
struct CharacterBuilder {
    name: Option<String>,
    class: Option<CharacterClass>,
    level: Option<u32>,
    attributes: Option<Attributes>,
    equipment: Equipment,
    skills: Vec<Skill>,
}

impl CharacterBuilder {
    fn new() -> Self {
        CharacterBuilder {
            name: None,
            class: None,
            level: Some(1),
            attributes: None,
            equipment: Equipment {
                weapon: None,
                armor: None,
                accessory: None,
            },
            skills: Vec::new(),
        }
    }
    
    fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }
    
    fn class(mut self, class: CharacterClass) -> Self {
        self.class = Some(class);
        self
    }
    
    fn level(mut self, level: u32) -> Self {
        self.level = Some(level);
        self
    }
    
    fn attributes(mut self, attributes: Attributes) -> Self {
        self.attributes = Some(attributes);
        self
    }
    
    fn weapon(mut self, weapon: Weapon) -> Self {
        self.equipment.weapon = Some(weapon);
        self
    }
    
    fn armor(mut self, armor: Armor) -> Self {
        self.equipment.armor = Some(armor);
        self
    }
    
    fn skill(mut self, skill: Skill) -> Self {
        self.skills.push(skill);
        self
    }
    
    fn build(self) -> Result<GameCharacter, String> {
        Ok(GameCharacter {
            name: self.name.ok_or("Name is required")?,
            class: self.class.ok_or("Class is required")?,
            level: self.level.unwrap_or(1),
            attributes: self.attributes.ok_or("Attributes are required")?,
            equipment: self.equipment,
            skills: self.skills,
        })
    }
}
```

---

## 6. 变体模式

### 6.1 链式建造者

```rust
// 链式建造者
struct ChainBuilder {
    product: Product,
}

impl ChainBuilder {
    fn new() -> Self {
        ChainBuilder {
            product: Product::default(),
        }
    }
    
    fn part_a(mut self, value: String) -> Self {
        self.product.part_a = Some(value);
        self
    }
    
    fn part_b(mut self, value: String) -> Self {
        self.product.part_b = Some(value);
        self
    }
    
    fn part_c(mut self, value: i32) -> Self {
        self.product.part_c = Some(value);
        self
    }
    
    fn build(self) -> Product {
        self.product
    }
}
```

### 6.2 模板建造者

```rust
// 模板建造者
trait TemplateBuilder {
    fn build_template(&mut self) -> &mut Self;
    fn customize(&mut self) -> &mut Self;
    fn finalize(&mut self) -> &mut Self;
    fn build(&self) -> Product;
}

struct TemplateProductBuilder {
    builder: ProductBuilder,
}

impl TemplateBuilder for TemplateProductBuilder {
    fn build_template(&mut self) -> &mut Self {
        self.builder
            .build_part_a("Template A".to_string())
            .build_part_b("Template B".to_string());
        self
    }
    
    fn customize(&mut self) -> &mut Self {
        // 子类可以重写此方法进行自定义
        self
    }
    
    fn finalize(&mut self) -> &mut Self {
        self.builder.build_part_c(42);
        self
    }
    
    fn build(&self) -> Product {
        self.builder.build()
    }
}
```

### 6.3 分步建造者

```rust
// 分步建造者
enum BuildStep {
    Initialize,
    BuildPartA,
    BuildPartB,
    BuildPartC,
    Finalize,
}

struct StepBuilder {
    builder: ProductBuilder,
    current_step: BuildStep,
}

impl StepBuilder {
    fn new() -> Self {
        StepBuilder {
            builder: ProductBuilder::default(),
            current_step: BuildStep::Initialize,
        }
    }
    
    fn next_step(&mut self) -> Result<&mut Self, String> {
        match self.current_step {
            BuildStep::Initialize => {
                self.current_step = BuildStep::BuildPartA;
                Ok(self)
            }
            BuildStep::BuildPartA => {
                self.current_step = BuildStep::BuildPartB;
                Ok(self)
            }
            BuildStep::BuildPartB => {
                self.current_step = BuildStep::BuildPartC;
                Ok(self)
            }
            BuildStep::BuildPartC => {
                self.current_step = BuildStep::Finalize;
                Ok(self)
            }
            BuildStep::Finalize => {
                Err("Build process already completed".to_string())
            }
        }
    }
    
    fn can_build(&self) -> bool {
        matches!(self.current_step, BuildStep::Finalize)
    }
    
    fn build(&self) -> Result<Product, String> {
        if self.can_build() {
            Ok(self.builder.build())
        } else {
            Err("Build process not completed".to_string())
        }
    }
}
```

---

## 7. 质量属性分析

### 7.1 可维护性

**定义7.1 (建造者可维护性)**
$$\text{Maintainability}(B) = \frac{|S|}{|C|} \cdot \frac{1}{\text{Complexity}(B)}$$

**分析：**

- 构建步骤清晰分离
- 职责单一，易于理解
- 复杂度适中，维护成本低

### 7.2 可扩展性

**定义7.2 (建造者可扩展性)**
$$\text{Extensibility}(B) = \frac{|R|}{|S|} \cdot \frac{1}{|C|}$$

**分析：**

- 支持新构建步骤添加
- 支持新产品类型扩展
- 支持构建过程定制

### 7.3 可重用性

**定义7.3 (建造者可重用性)**
$$\text{Reusability}(B) = \frac{|I|}{|S|} \cdot \frac{1}{\text{Complexity}(B)}$$

**分析：**

- 构建步骤可重用
- 构建过程可重用
- 验证规则可重用

### 7.4 性能分析

**时间复杂度：**

- 构建过程：$O(|S|)$
- 验证过程：$O(|V|)$
- 产品创建：$O(1)$

**空间复杂度：**

- 产品存储：$O(|A|)$
- 构建状态：$O(|S|)$
- 总空间：$O(|A| + |S|)$

---

## 8. 总结

### 8.1 核心优势

1. **分步构建**：支持复杂对象的分步构建
2. **构建控制**：精确控制构建过程和步骤
3. **表示分离**：构建过程与产品表示分离
4. **可扩展性**：支持新构建步骤和产品类型

### 8.2 适用场景

1. **复杂对象创建**：具有多个组成部分的复杂对象
2. **构建过程控制**：需要精确控制构建过程
3. **多种表示**：同一构建过程创建不同表示
4. **参数化构建**：根据参数构建不同配置

### 8.3 注意事项

1. **复杂度增加**：引入建造者增加系统复杂度
2. **构建步骤管理**：需要管理构建步骤的顺序和依赖
3. **验证复杂性**：复杂对象的验证可能很复杂
4. **性能开销**：分步构建可能带来性能开销

### 8.4 形式化验证

通过形式化定义和定理证明，我们验证了：

1. **构建完整性定理**：确保构建的产品完整
2. **构建过程控制定理**：支持精确的构建控制
3. **表示分离定理**：实现构建过程与表示分离
4. **性能定理**：构建复杂度为 $O(|S|)$

建造者模式通过严格的数学基础和形式化验证，为复杂对象构建提供了可靠的理论保证和实践指导。
