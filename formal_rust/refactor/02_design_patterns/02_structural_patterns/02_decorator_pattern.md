# 02. 装饰器模式形式化理论

## 目录

1. [形式化定义](#1-形式化定义)
2. [数学基础](#2-数学基础)
3. [类型系统分析](#3-类型系统分析)
4. [范畴论视角](#4-范畴论视角)
5. [Rust 类型系统映射](#5-rust-类型系统映射)
6. [实现策略](#6-实现策略)
7. [形式化证明](#7-形式化证明)
8. [应用场景](#8-应用场景)
9. [总结](#9-总结)

## 1. 形式化定义

### 1.1 基本定义

装饰器模式是一种结构型设计模式，它允许向对象动态地添加新的功能，而不改变其结构。

**形式化定义**：
设 $\mathcal{O}$ 为对象集合，$\mathcal{D}$ 为装饰器集合，则装饰器模式可定义为：

$$\text{Decorator} : \mathcal{O} \times \mathcal{D} \rightarrow \mathcal{O}$$

其中：

- $\mathcal{O}$ 为基础对象集合
- $\mathcal{D}$ 为装饰器集合

### 1.2 类型签名

```haskell
class Component where
  operation :: Component -> String

class Decorator where
  operation :: Decorator -> String
  setComponent :: Decorator -> Component -> Decorator
```

### 1.3 模式结构

```text
Component
└── operation() -> String

ConcreteComponent
└── operation() -> String

Decorator
├── component: Component
├── operation() -> String
└── setComponent(component) -> void

ConcreteDecorator
├── operation() -> String
└── addedBehavior() -> String
```

## 2. 数学基础

### 2.1 装饰函数理论

**定义 2.1**：装饰函数
装饰函数 $D$ 是一个从对象和装饰器到装饰后对象的映射：
$$D : \mathcal{O} \times \mathcal{D} \rightarrow \mathcal{O}$$

**定义 2.2**：装饰组合
装饰组合 $C$ 是多个装饰器的组合：
$$C : \mathcal{D}^* \rightarrow \mathcal{D}$$

其中 $\mathcal{D}^*$ 表示装饰器的序列。

### 2.2 装饰性质

**性质 2.1**：装饰的结合性
$$\forall o \in \mathcal{O}, d_1, d_2, d_3 \in \mathcal{D} : D(D(o, d_1), d_2), d_3) = D(o, C(d_1, d_2, d_3))$$

**性质 2.2**：装饰的幂等性
$$\forall o \in \mathcal{O}, d \in \mathcal{D} : D(D(o, d), d) = D(o, d)$$

**定理 2.1**：装饰的唯一性
对于任意对象 $o$ 和装饰器序列 $\langle d_1, d_2, \ldots, d_n \rangle$，装饰结果 $D(o, C(d_1, d_2, \ldots, d_n))$ 是唯一的。

## 3. 类型系统分析

### 3.1 类型构造器

在 Rust 中，装饰器模式可以通过 trait 和结构体实现：

```rust
// 组件接口
trait Component {
    fn operation(&self) -> String;
}

// 具体组件
struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

// 装饰器基类
struct Decorator {
    component: Box<dyn Component>,
}

impl Decorator {
    fn new(component: Box<dyn Component>) -> Self {
        Decorator { component }
    }
}

impl Component for Decorator {
    fn operation(&self) -> String {
        self.component.operation()
    }
}
```

### 3.2 类型约束

**约束 1**：组件类型约束
$$\text{Component} \subseteq \text{Trait} \land \text{ConcreteComponent} \subseteq \text{Component}$$

**约束 2**：装饰器类型约束
$$\text{Decorator} \subseteq \text{Struct} \land \text{Decorator} \subseteq \text{Component}$$

### 3.3 类型推导

给定装饰器类型 $D$ 和组件类型 $C$，类型推导规则为：

$$\frac{D : \text{Decorator} \quad D \vdash \text{operation} : () \rightarrow \text{String}}{D.\text{operation}() : \text{String}}$$

## 4. 范畴论视角

### 4.1 函子映射

装饰器模式可以看作是一个函子：
$$F : \mathcal{C} \rightarrow \mathcal{C}$$

其中 $\mathcal{C}$ 是对象范畴，$F$ 是装饰函子。

### 4.2 自然变换

不同装饰器之间的转换可以表示为自然变换：
$$\eta : F \Rightarrow G$$

**定理 4.1**：装饰器转换的一致性
对于任意自然变换 $\eta$，满足：
$$\eta_{o_1 \circ o_2} = \eta_{o_1} \circ \eta_{o_2}$$

## 5. Rust 类型系统映射

### 5.1 实现架构

```rust
// 组件接口
trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

// 具体组件
struct SimpleCoffee;

impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 {
        2.0
    }
    
    fn description(&self) -> String {
        "Simple Coffee".to_string()
    }
}

// 装饰器基类
struct CoffeeDecorator {
    coffee: Box<dyn Coffee>,
}

impl CoffeeDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        CoffeeDecorator { coffee }
    }
}

impl Coffee for CoffeeDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost()
    }
    
    fn description(&self) -> String {
        self.coffee.description()
    }
}

// 具体装饰器
struct MilkDecorator {
    coffee: Box<dyn Coffee>,
}

impl MilkDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        MilkDecorator { coffee }
    }
}

impl Coffee for MilkDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost() + 0.5
    }
    
    fn description(&self) -> String {
        format!("{} with Milk", self.coffee.description())
    }
}

struct SugarDecorator {
    coffee: Box<dyn Coffee>,
}

impl SugarDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        SugarDecorator { coffee }
    }
}

impl Coffee for SugarDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost() + 0.2
    }
    
    fn description(&self) -> String {
        format!("{} with Sugar", self.coffee.description())
    }
}
```

### 5.2 类型安全保证

**定理 5.1**：类型安全
对于任意装饰器 $D$ 和组件 $C$：
$$\text{TypeOf}(D.\text{operation}()) = \text{ExpectedType}(C.\text{operation}())$$

## 6. 实现策略

### 6.1 策略选择

1. **组合策略**：使用组合关系实现装饰器
2. **继承策略**：使用 trait 继承实现装饰器
3. **混合策略**：结合组合和继承

### 6.2 性能分析

**时间复杂度**：

- 装饰调用：$O(1)$
- 装饰链调用：$O(n)$，其中 $n$ 为装饰器数量
- 装饰器创建：$O(1)$

**空间复杂度**：

- 装饰器实例：$O(1)$
- 装饰链：$O(n)$，其中 $n$ 为装饰器数量

## 7. 形式化证明

### 7.1 装饰正确性证明

**命题 7.1**：装饰正确性
对于任意组件 $c$ 和装饰器 $d$，装饰后的对象 $D(c, d)$ 满足：

1. $D(c, d)$ 实现了相同的接口
2. $D(c, d)$ 的行为是 $c$ 的行为加上 $d$ 的额外行为

**证明**：

1. 装饰器实现了与组件相同的接口
2. 装饰器在调用组件方法的基础上添加额外行为
3. 因此装饰后的对象满足接口要求并具有增强的行为。$\square$

### 7.2 装饰组合证明

**命题 7.2**：装饰组合
多个装饰器可以按任意顺序组合，结果相同。

**证明**：

1. 装饰器通过组合关系连接
2. 每个装饰器都实现相同的接口
3. 装饰器的组合满足结合律
4. 因此装饰组合是确定的。$\square$

## 8. 应用场景

### 8.1 咖啡店系统

```rust
// 应用示例
fn main() {
    // 创建基础咖啡
    let coffee = SimpleCoffee;
    
    // 添加牛奶
    let coffee_with_milk = MilkDecorator::new(Box::new(coffee));
    
    // 添加糖
    let coffee_with_milk_and_sugar = SugarDecorator::new(Box::new(coffee_with_milk));
    
    // 使用装饰后的咖啡
    println!("Description: {}", coffee_with_milk_and_sugar.description());
    println!("Cost: ${:.2}", coffee_with_milk_and_sugar.cost());
    
    // 另一种组合方式
    let coffee = SimpleCoffee;
    let coffee_with_sugar = SugarDecorator::new(Box::new(coffee));
    let coffee_with_sugar_and_milk = MilkDecorator::new(Box::new(coffee_with_sugar));
    
    println!("Description: {}", coffee_with_sugar_and_milk.description());
    println!("Cost: ${:.2}", coffee_with_sugar_and_milk.cost());
}
```

### 8.2 日志系统

```rust
trait Logger {
    fn log(&self, message: &str);
}

struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        println!("Console: {}", message);
    }
}

struct TimestampDecorator {
    logger: Box<dyn Logger>,
}

impl TimestampDecorator {
    fn new(logger: Box<dyn Logger>) -> Self {
        TimestampDecorator { logger }
    }
}

impl Logger for TimestampDecorator {
    fn log(&self, message: &str) {
        let timestamp = chrono::Utc::now().format("%Y-%m-%d %H:%M:%S");
        self.logger.log(&format!("[{}] {}", timestamp, message));
    }
}

struct LevelDecorator {
    logger: Box<dyn Logger>,
    level: String,
}

impl LevelDecorator {
    fn new(logger: Box<dyn Logger>, level: String) -> Self {
        LevelDecorator { logger, level }
    }
}

impl Logger for LevelDecorator {
    fn log(&self, message: &str) {
        self.logger.log(&format!("[{}] {}", self.level, message));
    }
}
```

## 9. 总结

装饰器模式通过以下方式提供形式化保证：

1. **动态扩展**：在运行时动态地向对象添加功能
2. **类型安全**：通过 Rust 的类型系统确保装饰的正确性
3. **组合灵活性**：支持多种装饰器的组合
4. **开闭原则**：对扩展开放，对修改封闭

该模式在 Rust 中的实现充分利用了 trait 系统和所有权系统的优势，提供了安全且灵活的功能扩展机制。

---

**参考文献**：

1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Pierce, B. C. "Types and Programming Languages"
3. Mac Lane, S. "Categories for the Working Mathematician"
