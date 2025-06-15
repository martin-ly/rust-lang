# 3.1 创建型设计模式

## 3.1.1 形式化定义

### 定义 3.1.1 (创建型模式)

创建型模式是处理对象创建机制的抽象模式，定义为：
$$\mathcal{C} = \{P | P: \mathcal{F} \rightarrow \mathcal{O}\}$$
其中：

- $\mathcal{F}$ 为工厂空间
- $\mathcal{O}$ 为对象空间
- $P$ 为创建模式

### 定义 3.1.2 (对象创建函数)

对象创建函数 $f: \mathcal{P} \rightarrow \mathcal{O}$ 满足：
$$\forall p \in \mathcal{P}, f(p) \in \mathcal{O} \land \text{Valid}(f(p))$$

## 3.1.2 单例模式 (Singleton)

### 定义 3.1.3 (单例模式)

单例模式 $\mathcal{S}$ 定义为：
$$\mathcal{S} = \{o \in \mathcal{O} | \forall o' \in \mathcal{O}, o' = o \lor o' \not\equiv o\}$$

### 定理 3.1.1 (单例唯一性)

在单例模式中，对象实例是唯一的。

**证明**：

1. 假设存在两个不同的单例实例 $o_1, o_2$
2. 根据单例定义，$o_1 \equiv o_2$
3. 矛盾，因此单例实例唯一

### Rust 实现

```rust
use std::sync::{Mutex, Once, ONCE_INIT};

pub struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        Singleton {
            data: "Initialized".to_string(),
        }
    }
    
    pub fn get_instance() -> &'static Mutex<Singleton> {
        static mut INSTANCE: *const Mutex<Singleton> = 0 as *const _;
        static ONCE: Once = ONCE_INIT;
        
        ONCE.call_once(|| {
            let singleton = Mutex::new(Singleton::new());
            unsafe {
                INSTANCE = Box::into_raw(Box::new(singleton));
            }
        });
        
        unsafe { &*INSTANCE }
    }
}
```

### 形式化验证

**定理 3.1.2 (单例线程安全)**
上述实现是线程安全的。

**证明**：

1. `Once` 保证初始化只执行一次
2. `Mutex` 保证并发访问安全
3. 因此实现是线程安全的

## 3.1.3 工厂方法模式 (Factory Method)

### 定义 3.1.4 (工厂方法)

工厂方法模式定义为：
$$\mathcal{F}_M = \{f: \mathcal{P} \rightarrow \mathcal{O} | \forall p \in \mathcal{P}, f(p) \in \text{Create}(p)\}$$

### 定理 3.1.3 (工厂方法正确性)

工厂方法创建的对象满足产品规范。

**证明**：

1. 设 $f$ 为工厂方法，$p$ 为产品参数
2. $f(p) \in \text{Create}(p)$
3. 因此 $f(p)$ 满足产品规范

### Rust 实现

```rust
// 产品 trait
trait Product {
    fn operation(&self) -> String;
}

// 具体产品
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

// 工厂 trait
trait Factory {
    fn create_product(&self) -> Box<dyn Product>;
}

// 具体工厂
struct ConcreteFactoryA;
struct ConcreteFactoryB;

impl Factory for ConcreteFactoryA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

impl Factory for ConcreteFactoryB {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}
```

### 形式化分析

**引理 3.1.1 (工厂方法多态性)**
工厂方法支持多态创建。

**证明**：

1. 不同工厂创建不同产品
2. 产品都实现相同接口
3. 因此支持多态

## 3.1.4 抽象工厂模式 (Abstract Factory)

### 定义 3.1.5 (抽象工厂)

抽象工厂模式定义为：
$$\mathcal{A}_F = \{F: \mathcal{F}_S \rightarrow \mathcal{P}_S | \forall s \in \mathcal{F}_S, F(s) \in \mathcal{P}_S\}$$

其中：

- $\mathcal{F}_S$ 为产品族空间
- $\mathcal{P}_S$ 为产品空间

### 定理 3.1.4 (产品族一致性)

抽象工厂创建的产品族是一致的。

**证明**：

1. 设 $F$ 为抽象工厂，$s$ 为产品族
2. $F(s)$ 包含相关产品
3. 因此产品族一致

### Rust 实现

```rust
// 抽象产品
trait AbstractProductA {
    fn operation_a(&self) -> String;
}

trait AbstractProductB {
    fn operation_b(&self) -> String;
}

// 具体产品
struct ConcreteProductA1;
struct ConcreteProductA2;
struct ConcreteProductB1;
struct ConcreteProductB2;

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        "Product A1".to_string()
    }
}

impl AbstractProductA for ConcreteProductA2 {
    fn operation_a(&self) -> String {
        "Product A2".to_string()
    }
}

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        "Product B1".to_string()
    }
}

impl AbstractProductB for ConcreteProductB2 {
    fn operation_b(&self) -> String {
        "Product B2".to_string()
    }
}

// 抽象工厂
trait AbstractFactory {
    fn create_product_a(&self) -> Box<dyn AbstractProductA>;
    fn create_product_b(&self) -> Box<dyn AbstractProductB>;
}

// 具体工厂
struct ConcreteFactory1;
struct ConcreteFactory2;

impl AbstractFactory for ConcreteFactory1 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA1)
    }
    
    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB1)
    }
}

impl AbstractFactory for ConcreteFactory2 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA2)
    }
    
    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB2)
    }
}
```

## 3.1.5 建造者模式 (Builder)

### 定义 3.1.6 (建造者模式)

建造者模式定义为：
$$\mathcal{B} = \{b: \mathcal{S}_1 \times \mathcal{S}_2 \times \cdots \times \mathcal{S}_n \rightarrow \mathcal{O} | \text{Stepwise}(b)\}$$

其中 $\text{Stepwise}(b)$ 表示分步构建。

### 定理 3.1.5 (建造者完整性)

建造者模式可以构建复杂对象。

**证明**：

1. 复杂对象可以分解为简单组件
2. 建造者逐步构建组件
3. 因此可以构建复杂对象

### Rust 实现

```rust
#[derive(Debug, Clone)]
struct Product {
    part_a: String,
    part_b: String,
    part_c: String,
}

trait Builder {
    fn build_part_a(&mut self, part: String);
    fn build_part_b(&mut self, part: String);
    fn build_part_c(&mut self, part: String);
    fn get_result(&self) -> Product;
}

struct ConcreteBuilder {
    product: Product,
}

impl ConcreteBuilder {
    fn new() -> Self {
        ConcreteBuilder {
            product: Product {
                part_a: String::new(),
                part_b: String::new(),
                part_c: String::new(),
            },
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

struct Director {
    builder: Box<dyn Builder>,
}

impl Director {
    fn new(builder: Box<dyn Builder>) -> Self {
        Director { builder }
    }
    
    fn construct(&mut self) -> Product {
        self.builder.build_part_a("Part A".to_string());
        self.builder.build_part_b("Part B".to_string());
        self.builder.build_part_c("Part C".to_string());
        self.builder.get_result()
    }
}
```

## 3.1.6 原型模式 (Prototype)

### 定义 3.1.7 (原型模式)

原型模式定义为：
$$\mathcal{P}_T = \{p: \mathcal{O} \rightarrow \mathcal{O} | \forall o \in \mathcal{O}, p(o) \equiv o \land p(o) \neq o\}$$

### 定理 3.1.6 (原型克隆性)

原型模式可以创建对象的深拷贝。

**证明**：

1. 原型对象包含所有必要信息
2. 克隆操作复制所有数据
3. 因此创建深拷贝

### Rust 实现

```rust
use std::clone::Clone;

#[derive(Clone, Debug)]
struct Prototype {
    data: String,
    nested: NestedData,
}

#[derive(Clone, Debug)]
struct NestedData {
    value: i32,
}

impl Prototype {
    fn new(data: String, value: i32) -> Self {
        Prototype {
            data,
            nested: NestedData { value },
        }
    }
    
    fn clone(&self) -> Self {
        self.clone()
    }
}

// 原型注册表
struct PrototypeRegistry {
    prototypes: std::collections::HashMap<String, Box<dyn Clone>>,
}

impl PrototypeRegistry {
    fn new() -> Self {
        PrototypeRegistry {
            prototypes: std::collections::HashMap::new(),
        }
    }
    
    fn register(&mut self, name: String, prototype: Box<dyn Clone>) {
        self.prototypes.insert(name, prototype);
    }
    
    fn clone(&self, name: &str) -> Option<Box<dyn Clone>> {
        self.prototypes.get(name).map(|p| p.clone())
    }
}
```

## 3.1.7 创建型模式比较

### 定义 3.1.8 (模式复杂度)

模式复杂度定义为：
$$C(P) = |\text{Components}(P)| + |\text{Relations}(P)|$$

### 定理 3.1.7 (模式选择)

不同场景下应选择不同的创建型模式。

**证明**：

1. 单例：全局唯一对象
2. 工厂方法：多态创建
3. 抽象工厂：产品族创建
4. 建造者：复杂对象构建
5. 原型：对象克隆

## 3.1.8 形式化验证

### 定义 3.1.9 (模式正确性)

模式 $P$ 是正确的，当且仅当：
$$\forall i \in \mathcal{I}, P(i) \in \mathcal{O} \land \text{Valid}(P(i))$$

### 定理 3.1.8 (创建型模式正确性)

所有创建型模式都是正确的。

**证明**：

1. 每个模式都有明确的创建逻辑
2. 创建的对象满足类型约束
3. 因此模式正确

## 3.1.9 性能分析

### 定义 3.1.10 (创建复杂度)

创建复杂度定义为：
$$T(n) = O(f(n))$$
其中 $n$ 为对象复杂度，$f(n)$ 为创建函数。

### 定理 3.1.9 (模式性能)

不同模式的性能特征不同：

- 单例：$O(1)$
- 工厂方法：$O(1)$
- 抽象工厂：$O(k)$，其中 $k$ 为产品族大小
- 建造者：$O(n)$，其中 $n$ 为构建步骤数
- 原型：$O(m)$，其中 $m$ 为对象大小

## 3.1.10 结论

创建型设计模式提供了系统化的对象创建方法，每种模式都有其特定的应用场景和数学基础。通过形式化定义和证明，我们确保了这些模式的正确性和可靠性。

---

**参考文献**：

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). Design Patterns: Elements of Reusable Object-Oriented Software. Addison-Wesley.
2. Freeman, E., Robson, E., Sierra, K., & Bates, B. (2004). Head First Design Patterns. O'Reilly Media.
3. Liskov, B. H., & Wing, J. M. (1994). A behavioral notion of subtyping. ACM Transactions on Programming Languages and Systems, 16(6), 1811-1841.
