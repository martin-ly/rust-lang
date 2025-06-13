# 创建型设计模式形式化重构

## 目录

1. [理论基础](#1-理论基础)
2. [创建型模式五元组定义](#2-创建型模式五元组定义)
3. [单例模式形式化理论](#3-单例模式形式化理论)
4. [工厂方法模式形式化理论](#4-工厂方法模式形式化理论)
5. [抽象工厂模式形式化理论](#5-抽象工厂模式形式化理论)
6. [建造者模式形式化理论](#6-建造者模式形式化理论)
7. [原型模式形式化理论](#7-原型模式形式化理论)
8. [核心定理证明](#8-核心定理证明)
9. [Rust实现](#9-rust实现)

## 1. 理论基础

### 1.1 对象创建基础

**定义1.1 (对象)**
对象 $O = (S, M, I)$ 包含：
- $S$: 状态集合
- $M$: 方法集合
- $I$: 接口集合

**定义1.2 (对象创建)**
对象创建函数 $\text{Create}: \text{Class} \times \text{Args} \rightarrow \text{Object}$ 定义为：
$$\text{Create}(C, args) = O \text{ where } O \text{ is an instance of } C$$

**定义1.3 (对象生命周期)**
对象生命周期 $\text{Lifecycle}: \text{Object} \times \text{Time} \rightarrow \text{State}$ 定义为：
$$\text{Lifecycle}(O, t) = \begin{cases}
\text{Created} & \text{if } t = t_{\text{create}} \\
\text{Active} & \text{if } t_{\text{create}} < t < t_{\text{destroy}} \\
\text{Destroyed} & \text{if } t \geq t_{\text{destroy}}
\end{cases}$$

### 1.2 创建模式基础

**定义1.4 (创建模式)**
创建模式 $CP = (F, C, I, R)$ 包含：
- $F$: 工厂函数集合
- $C$: 创建约束集合
- $I$: 初始化规则集合
- $R$: 资源管理规则集合

**定义1.5 (创建约束)**
创建约束 $\text{CreationConstraint}: \text{Class} \times \text{Context} \rightarrow \text{Boolean}$ 定义为：
$$\text{CreationConstraint}(C, ctx) = \begin{cases}
\text{true} & \text{if creation is allowed in context } ctx \\
\text{false} & \text{otherwise}
\end{cases}$$

## 2. 创建型模式五元组定义

**定义2.1 (创建型模式系统)**
创建型模式系统 $CPS = (S, F, A, B, P)$ 包含：

- **S (Singleton)**: 单例模式系统 $S = (I, A, L, T)$
  - $I$: 实例管理
  - $A$: 访问控制
  - $L$: 生命周期管理
  - $T$: 线程安全

- **F (Factory Method)**: 工厂方法系统 $F = (I, C, P, D)$
  - $I$: 工厂接口
  - $C$: 具体工厂
  - $P$: 产品定义
  - $D$: 延迟创建

- **A (Abstract Factory)**: 抽象工厂系统 $A = (F, P, C, R)$
  - $F$: 工厂族
  - $P$: 产品族
  - $C$: 创建协调
  - $R$: 关系管理

- **B (Builder)**: 建造者系统 $B = (S, P, C, F)$
  - $S$: 构建步骤
  - $P$: 产品构建
  - $C$: 构建控制
  - $F$: 最终产品

- **P (Prototype)**: 原型系统 $P = (O, C, D, R)$
  - $O$: 原型对象
  - $C$: 克隆操作
  - $D$: 深度复制
  - $R$: 复制关系

## 3. 单例模式形式化理论

### 3.1 单例代数理论

**定义3.1 (单例代数)**
单例代数 $SA = (I, A, L, T, C)$ 包含：

- **I (Instance)**: 实例管理
- **A (Access)**: 访问控制
- **L (Lifecycle)**: 生命周期管理
- **T (Threading)**: 线程安全
- **C (Constraints)**: 约束条件

**定义3.2 (单例约束)**
单例约束集合 $SC = \{SC_1, SC_2, SC_3\}$ 定义为：

1. **唯一性约束**: $\forall t \in \text{Time}, \exists! i \in \text{Instance}: \text{Active}(i, t)$
2. **全局访问约束**: $\forall p \in \text{Process}, \text{CanAccess}(p, i)$
3. **生命周期约束**: $\text{Lifecycle}(i) = [t_{\text{start}}, \infty)$

### 3.2 单例状态理论

**定义3.3 (单例状态)**
单例状态函数 $\text{SingletonState}: \text{Time} \rightarrow \text{State}$ 定义为：
$$\text{SingletonState}(t) = \begin{cases}
\text{Uninitialized} & \text{if } t < t_{\text{init}} \\
\text{Initialized} & \text{if } t \geq t_{\text{init}}
\end{cases}$$

**定义3.4 (单例访问)**
单例访问函数 $\text{SingletonAccess}: \text{Process} \times \text{Time} \rightarrow \text{Instance}$ 定义为：
$$\text{SingletonAccess}(p, t) = i \text{ where } \text{Active}(i, t) \land \text{CanAccess}(p, i)$$

## 4. 工厂方法模式形式化理论

### 4.1 工厂方法代数理论

**定义4.1 (工厂方法代数)**
工厂方法代数 $FMA = (I, C, P, D, R)$ 包含：

- **I (Interface)**: 工厂接口
- **C (Concrete)**: 具体工厂
- **P (Product)**: 产品定义
- **D (Defer)**: 延迟创建
- **R (Rules)**: 创建规则

**定义4.2 (工厂方法规则)**
工厂方法规则集合 $FMR = \{FMR_1, FMR_2, FMR_3\}$ 定义为：

1. **接口定义规则**: $\forall f \in \text{Factory}, \exists i \in \text{Interface}: \text{Implements}(f, i)$
2. **产品创建规则**: $\text{Create}(f, args) \rightarrow p \text{ where } p \in \text{Product}$
3. **延迟创建规则**: $\text{Create}(f, args) = \text{Defer}(\text{CreateProduct}, args)$

### 4.2 工厂方法类型理论

**定义4.3 (工厂类型)**
工厂类型 $FT = \text{Factory} \rightarrow \text{Product}$ 定义为：
$$FT = \{\lambda args. \text{CreateProduct}(args) \mid \text{CreateProduct} \in \text{ProductCreators}\}$$

**定义4.4 (产品类型)**
产品类型 $PT = \text{Product} \times \text{Methods}$ 定义为：
$$PT = \{(p, m) \mid p \in \text{Product}, m \in \text{Methods}(p)\}$$

## 5. 抽象工厂模式形式化理论

### 5.1 抽象工厂代数理论

**定义5.1 (抽象工厂代数)**
抽象工厂代数 $AFA = (F, P, C, R, I)$ 包含：

- **F (Factory Family)**: 工厂族
- **P (Product Family)**: 产品族
- **C (Creation)**: 创建协调
- **R (Relations)**: 关系管理
- **I (Interface)**: 接口定义

**定义5.2 (工厂族关系)**
工厂族关系 $\text{FactoryFamily}: \text{Factory} \times \text{Product} \rightarrow \text{Boolean}$ 定义为：
$$\text{FactoryFamily}(f, p) = \begin{cases}
\text{true} & \text{if } f \text{ can create } p \\
\text{false} & \text{otherwise}
\end{cases}$$

### 5.2 产品族理论

**定义5.3 (产品族)**
产品族 $PF = \{P_1, P_2, \ldots, P_n\}$ 定义为：
$$PF = \{\text{Product} \mid \text{Compatible}(\text{Product})\}$$

**定义5.4 (产品兼容性)**
产品兼容性 $\text{Compatible}: \text{Product} \times \text{Product} \rightarrow \text{Boolean}$ 定义为：
$$\text{Compatible}(p_1, p_2) = \begin{cases}
\text{true} & \text{if } p_1, p_2 \text{ can work together} \\
\text{false} & \text{otherwise}
\end{cases}$$

## 6. 建造者模式形式化理论

### 6.1 建造者代数理论

**定义6.1 (建造者代数)**
建造者代数 $BA = (S, P, C, F, R)$ 包含：

- **S (Steps)**: 构建步骤
- **P (Product)**: 产品构建
- **C (Control)**: 构建控制
- **F (Final)**: 最终产品
- **R (Rules)**: 构建规则

**定义6.2 (构建步骤)**
构建步骤序列 $\text{BuildSteps}: \text{Builder} \rightarrow [\text{Step}]$ 定义为：
$$\text{BuildSteps}(b) = [s_1, s_2, \ldots, s_n] \text{ where } s_i \in \text{Steps}$$

**定义6.3 (步骤依赖)**
步骤依赖关系 $\text{StepDependency}: \text{Step} \times \text{Step} \rightarrow \text{Boolean}$ 定义为：
$$\text{StepDependency}(s_1, s_2) = \begin{cases}
\text{true} & \text{if } s_2 \text{ depends on } s_1 \\
\text{false} & \text{otherwise}
\end{cases}$$

### 6.2 构建过程理论

**定义6.4 (构建过程)**
构建过程 $\text{BuildProcess}: \text{Builder} \times \text{Config} \rightarrow \text{Product}$ 定义为：
$$\text{BuildProcess}(b, c) = \text{ExecuteSteps}(\text{BuildSteps}(b), c)$$

**定义6.5 (构建验证)**
构建验证函数 $\text{BuildValidation}: \text{Product} \times \text{Spec} \rightarrow \text{Boolean}$ 定义为：
$$\text{BuildValidation}(p, spec) = \begin{cases}
\text{true} & \text{if } p \text{ satisfies } spec \\
\text{false} & \text{otherwise}
\end{cases}$$

## 7. 原型模式形式化理论

### 7.1 原型代数理论

**定义7.1 (原型代数)**
原型代数 $PA = (O, C, D, R, I)$ 包含：

- **O (Object)**: 原型对象
- **C (Clone)**: 克隆操作
- **D (Deep)**: 深度复制
- **R (Relations)**: 复制关系
- **I (Interface)**: 克隆接口

**定义7.2 (克隆操作)**
克隆操作 $\text{Clone}: \text{Prototype} \rightarrow \text{Object}$ 定义为：
$$\text{Clone}(p) = \text{Copy}(p)$$

**定义7.3 (深度克隆)**
深度克隆 $\text{DeepClone}: \text{Prototype} \rightarrow \text{Object}$ 定义为：
$$\text{DeepClone}(p) = \text{RecursiveCopy}(p)$$

### 7.2 复制关系理论

**定义7.4 (复制关系)**
复制关系 $\text{CopyRelation}: \text{Object} \times \text{Object} \rightarrow \text{Relation}$ 定义为：
$$\text{CopyRelation}(o_1, o_2) = \begin{cases}
\text{Shallow} & \text{if } o_2 \text{ is shallow copy of } o_1 \\
\text{Deep} & \text{if } o_2 \text{ is deep copy of } o_1 \\
\text{None} & \text{otherwise}
\end{cases}$$

## 8. 核心定理证明

### 8.1 单例唯一性定理

**定理8.1 (单例唯一性)**
在单例模式中，任意时刻最多存在一个实例。

**证明**:
设 $i_1, i_2$ 为两个不同的实例，$t$ 为任意时刻。

根据单例约束 $SC_1$ (唯一性约束):
$$\forall t \in \text{Time}, \exists! i \in \text{Instance}: \text{Active}(i, t)$$

这意味着对于任意时刻 $t$，存在唯一的活跃实例 $i$。

假设存在两个活跃实例 $i_1 \neq i_2$，则：
$$\text{Active}(i_1, t) \land \text{Active}(i_2, t)$$

这与唯一性约束矛盾，因此假设不成立。

**结论**: 任意时刻最多存在一个实例。$\square$

### 8.2 工厂方法类型安全定理

**定理8.2 (工厂方法类型安全)**
如果工厂方法通过类型检查，则创建的产品类型是安全的。

**证明**:
设 $f$ 为通过类型检查的工厂方法，即 $\text{TypeCheck}(f) = \text{true}$。

根据工厂方法规则 $FMR_2$ (产品创建规则):
$$\text{Create}(f, args) \rightarrow p \text{ where } p \in \text{Product}$$

这意味着工厂方法创建的对象 $p$ 属于预定义的产品类型集合。

因此创建的产品类型是安全的。$\square$

### 8.3 抽象工厂一致性定理

**定理8.3 (抽象工厂一致性)**
如果抽象工厂创建的产品族通过兼容性检查，则产品族是内部一致的。

**证明**:
设 $PF = \{p_1, p_2, \ldots, p_n\}$ 为通过兼容性检查的产品族。

根据产品兼容性定义：
$$\forall p_i, p_j \in PF: \text{Compatible}(p_i, p_j)$$

这意味着产品族中的所有产品都是相互兼容的。

因此产品族是内部一致的。$\square$

### 8.4 建造者完整性定理

**定理8.4 (建造者完整性)**
如果建造者按照预定义步骤构建产品，则构建过程是完整的。

**证明**:
设 $b$ 为建造者，$steps = [s_1, s_2, \ldots, s_n]$ 为预定义步骤。

根据构建过程定义：
$$\text{BuildProcess}(b, c) = \text{ExecuteSteps}(steps, c)$$

如果所有步骤都正确执行，则构建过程是完整的。

因此建造者能够完整地构建产品。$\square$

### 8.5 原型复制正确性定理

**定理8.5 (原型复制正确性)**
如果原型对象通过深度克隆复制，则复制对象与原对象在结构上等价。

**证明**:
设 $p$ 为原型对象，$p' = \text{DeepClone}(p)$ 为深度克隆结果。

根据深度克隆定义：
$$\text{DeepClone}(p) = \text{RecursiveCopy}(p)$$

这意味着 $p'$ 是 $p$ 的递归复制，包含所有嵌套对象。

因此复制对象与原对象在结构上等价。$\square$

## 9. Rust实现

### 9.1 单例模式实现

```rust
use std::sync::{Mutex, Once, ONCE_INIT};
use std::mem;

/// 单例模式核心结构
pub struct Singleton<T> {
    data: T,
}

impl<T> Singleton<T> {
    /// 获取单例实例
    pub fn get_instance() -> &'static Mutex<Singleton<T>>
    where
        T: Default + 'static,
    {
        static mut INSTANCE: *const Mutex<Singleton<T>> = 0 as *const _;
        static ONCE: Once = ONCE_INIT;

        ONCE.call_once(|| {
            let singleton = Mutex::new(Singleton {
                data: T::default(),
            });
            unsafe {
                INSTANCE = Box::into_raw(Box::new(singleton));
            }
        });

        unsafe { &*INSTANCE }
    }

    /// 获取数据引用
    pub fn get_data(&self) -> &T {
        &self.data
    }

    /// 获取数据可变引用
    pub fn get_data_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

/// 线程安全的单例管理器
pub struct SingletonManager<T> {
    instance: Mutex<Option<T>>,
}

impl<T> SingletonManager<T> {
    pub fn new() -> Self {
        SingletonManager {
            instance: Mutex::new(None),
        }
    }

    /// 获取或创建实例
    pub fn get_or_create<F>(&self, creator: F) -> Result<T, Box<dyn std::error::Error>>
    where
        F: FnOnce() -> T,
        T: Clone,
    {
        let mut instance = self.instance.lock()?;
        if instance.is_none() {
            *instance = Some(creator());
        }
        Ok(instance.as_ref().unwrap().clone())
    }
}
```

### 9.2 工厂方法模式实现

```rust
/// 产品trait
pub trait Product {
    fn operation(&self) -> String;
    fn get_name(&self) -> String;
}

/// 具体产品A
pub struct ConcreteProductA {
    name: String,
}

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        format!("ConcreteProductA operation: {}", self.name)
    }

    fn get_name(&self) -> String {
        self.name.clone()
    }
}

/// 具体产品B
pub struct ConcreteProductB {
    name: String,
}

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        format!("ConcreteProductB operation: {}", self.name)
    }

    fn get_name(&self) -> String {
        self.name.clone()
    }
}

/// 工厂trait
pub trait Factory {
    type ProductType: Product;
    
    fn create_product(&self, name: String) -> Self::ProductType;
}

/// 具体工厂A
pub struct ConcreteFactoryA;

impl Factory for ConcreteFactoryA {
    type ProductType = ConcreteProductA;
    
    fn create_product(&self, name: String) -> Self::ProductType {
        ConcreteProductA { name }
    }
}

/// 具体工厂B
pub struct ConcreteFactoryB;

impl Factory for ConcreteFactoryB {
    type ProductType = ConcreteProductB;
    
    fn create_product(&self, name: String) -> Self::ProductType {
        ConcreteProductB { name }
    }
}

/// 工厂管理器
pub struct FactoryManager {
    factories: HashMap<String, Box<dyn Factory<ProductType = Box<dyn Product>>>>,
}

impl FactoryManager {
    pub fn new() -> Self {
        let mut manager = FactoryManager {
            factories: HashMap::new(),
        };
        
        // 注册工厂
        manager.register_factory("A", Box::new(ConcreteFactoryA));
        manager.register_factory("B", Box::new(ConcreteFactoryB));
        
        manager
    }
    
    pub fn register_factory(&mut self, name: &str, factory: Box<dyn Factory<ProductType = Box<dyn Product>>>) {
        self.factories.insert(name.to_string(), factory);
    }
    
    pub fn create_product(&self, factory_name: &str, product_name: String) -> Option<Box<dyn Product>> {
        self.factories.get(factory_name)
            .map(|factory| factory.create_product(product_name))
    }
}
```

### 9.3 抽象工厂模式实现

```rust
/// 抽象产品A
pub trait AbstractProductA {
    fn operation_a(&self) -> String;
}

/// 抽象产品B
pub trait AbstractProductB {
    fn operation_b(&self) -> String;
}

/// 具体产品A1
pub struct ConcreteProductA1 {
    name: String,
}

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        format!("ConcreteProductA1: {}", self.name)
    }
}

/// 具体产品A2
pub struct ConcreteProductA2 {
    name: String,
}

impl AbstractProductA for ConcreteProductA2 {
    fn operation_a(&self) -> String {
        format!("ConcreteProductA2: {}", self.name)
    }
}

/// 具体产品B1
pub struct ConcreteProductB1 {
    name: String,
}

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        format!("ConcreteProductB1: {}", self.name)
    }
}

/// 具体产品B2
pub struct ConcreteProductB2 {
    name: String,
}

impl AbstractProductB for ConcreteProductB2 {
    fn operation_b(&self) -> String {
        format!("ConcreteProductB2: {}", self.name)
    }
}

/// 抽象工厂trait
pub trait AbstractFactory {
    type ProductA: AbstractProductA;
    type ProductB: AbstractProductB;
    
    fn create_product_a(&self, name: String) -> Self::ProductA;
    fn create_product_b(&self, name: String) -> Self::ProductB;
}

/// 具体工厂1
pub struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    type ProductA = ConcreteProductA1;
    type ProductB = ConcreteProductB1;
    
    fn create_product_a(&self, name: String) -> Self::ProductA {
        ConcreteProductA1 { name }
    }
    
    fn create_product_b(&self, name: String) -> Self::ProductB {
        ConcreteProductB1 { name }
    }
}

/// 具体工厂2
pub struct ConcreteFactory2;

impl AbstractFactory for ConcreteFactory2 {
    type ProductA = ConcreteProductA2;
    type ProductB = ConcreteProductB2;
    
    fn create_product_a(&self, name: String) -> Self::ProductA {
        ConcreteProductA2 { name }
    }
    
    fn create_product_b(&self, name: String) -> Self::ProductB {
        ConcreteProductB2 { name }
    }
}
```

### 9.4 建造者模式实现

```rust
/// 产品
pub struct Product {
    parts: Vec<String>,
}

impl Product {
    pub fn new() -> Self {
        Product { parts: Vec::new() }
    }
    
    pub fn add_part(&mut self, part: String) {
        self.parts.push(part);
    }
    
    pub fn show(&self) -> String {
        format!("Product parts: {}", self.parts.join(", "))
    }
}

/// 抽象建造者
pub trait Builder {
    fn build_part_a(&mut self);
    fn build_part_b(&mut self);
    fn build_part_c(&mut self);
    fn get_result(&self) -> Product;
}

/// 具体建造者1
pub struct ConcreteBuilder1 {
    product: Product,
}

impl ConcreteBuilder1 {
    pub fn new() -> Self {
        ConcreteBuilder1 {
            product: Product::new(),
        }
    }
}

impl Builder for ConcreteBuilder1 {
    fn build_part_a(&mut self) {
        self.product.add_part("Part A1".to_string());
    }
    
    fn build_part_b(&mut self) {
        self.product.add_part("Part B1".to_string());
    }
    
    fn build_part_c(&mut self) {
        self.product.add_part("Part C1".to_string());
    }
    
    fn get_result(&self) -> Product {
        Product {
            parts: self.product.parts.clone(),
        }
    }
}

/// 具体建造者2
pub struct ConcreteBuilder2 {
    product: Product,
}

impl ConcreteBuilder2 {
    pub fn new() -> Self {
        ConcreteBuilder2 {
            product: Product::new(),
        }
    }
}

impl Builder for ConcreteBuilder2 {
    fn build_part_a(&mut self) {
        self.product.add_part("Part A2".to_string());
    }
    
    fn build_part_b(&mut self) {
        self.product.add_part("Part B2".to_string());
    }
    
    fn build_part_c(&mut self) {
        self.product.add_part("Part C2".to_string());
    }
    
    fn get_result(&self) -> Product {
        Product {
            parts: self.product.parts.clone(),
        }
    }
}

/// 导演
pub struct Director;

impl Director {
    pub fn construct<B: Builder>(&self, builder: &mut B) -> Product {
        builder.build_part_a();
        builder.build_part_b();
        builder.build_part_c();
        builder.get_result()
    }
}
```

### 9.5 原型模式实现

```rust
use std::collections::HashMap;

/// 原型trait
pub trait Prototype {
    fn clone(&self) -> Box<dyn Prototype>;
    fn get_name(&self) -> String;
    fn set_name(&mut self, name: String);
}

/// 具体原型
pub struct ConcretePrototype {
    name: String,
    data: HashMap<String, String>,
}

impl ConcretePrototype {
    pub fn new(name: String) -> Self {
        let mut data = HashMap::new();
        data.insert("key1".to_string(), "value1".to_string());
        data.insert("key2".to_string(), "value2".to_string());
        
        ConcretePrototype { name, data }
    }
}

impl Prototype for ConcretePrototype {
    fn clone(&self) -> Box<dyn Prototype> {
        Box::new(ConcretePrototype {
            name: self.name.clone(),
            data: self.data.clone(), // 深度克隆
        })
    }
    
    fn get_name(&self) -> String {
        self.name.clone()
    }
    
    fn set_name(&mut self, name: String) {
        self.name = name;
    }
}

/// 原型管理器
pub struct PrototypeManager {
    prototypes: HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeManager {
    pub fn new() -> Self {
        PrototypeManager {
            prototypes: HashMap::new(),
        }
    }
    
    pub fn register_prototype(&mut self, name: String, prototype: Box<dyn Prototype>) {
        self.prototypes.insert(name, prototype);
    }
    
    pub fn create_prototype(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(name).map(|p| p.clone())
    }
}
```

---

**结论**: 创建型设计模式通过严格的形式化定义和实现，为对象创建提供了系统化的解决方案，确保了创建过程的可控性和一致性。 