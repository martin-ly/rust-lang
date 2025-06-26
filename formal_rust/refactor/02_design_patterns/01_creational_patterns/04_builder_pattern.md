# 04. 建造者模式形式化理论

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

建造者模式是一种创建型设计模式，它将复杂对象的构建过程分解为多个步骤，允许使用相同的构建过程创建不同的表示。

**形式化定义**：
设 $\mathcal{O}$ 为对象集合，$\mathcal{S}$ 为构建步骤集合，则建造者模式可定义为：

$$\text{Builder} : \mathcal{S}^* \rightarrow \mathcal{O}$$

其中：

- $\mathcal{S}^*$ 表示构建步骤的序列
- $\mathcal{O}$ 为目标对象集合

### 1.2 类型签名

```haskell
class Builder b where
  reset :: b -> b
  setPartA :: b -> PartA -> b
  setPartB :: b -> PartB -> b
  setPartC :: b -> PartC -> b
  build :: b -> Product
```

### 1.3 模式结构

```text
Builder
├── reset() -> Builder
├── setPartA(part) -> Builder
├── setPartB(part) -> Builder
├── setPartC(part) -> Builder
└── build() -> Product

Director
└── construct(builder) -> Product
```

## 2. 数学基础

### 2.1 构建序列理论

**定义 2.1**：构建序列
构建序列是一个有序的步骤集合：
$$\sigma = \langle s_1, s_2, \ldots, s_n \rangle$$

其中 $s_i \in \mathcal{S}$ 表示构建步骤。

**定义 2.2**：构建函数
构建函数 $B$ 将构建序列映射到对象：
$$B : \mathcal{S}^* \rightarrow \mathcal{O}$$

**性质 2.1**：构建函数的单调性
$$\forall \sigma_1, \sigma_2 \in \mathcal{S}^* : \sigma_1 \subseteq \sigma_2 \Rightarrow B(\sigma_1) \subseteq B(\sigma_2)$$

### 2.2 步骤依赖关系

**定义 2.3**：步骤依赖图
步骤依赖图 $G = (V, E)$ 其中：

- $V = \mathcal{S}$ 为步骤集合
- $E = \{(s_i, s_j) | s_i \text{ 必须在 } s_j \text{ 之前执行}\}$

**定理 2.1**：构建序列的有效性
构建序列 $\sigma$ 有效当且仅当对应的依赖图 $G_\sigma$ 是无环的。

## 3. 类型系统分析

### 3.1 类型构造器

在 Rust 中，建造者模式可以通过 trait 和泛型实现：

```rust
// 产品接口
trait Product {
    fn operation(&self) -> String;
}

// 建造者接口
trait Builder {
    type Output: Product;
    
    fn reset(&mut self) -> &mut Self;
    fn set_part_a(&mut self, part: PartA) -> &mut Self;
    fn set_part_b(&mut self, part: PartB) -> &mut Self;
    fn set_part_c(&mut self, part: PartC) -> &mut Self;
    fn build(&self) -> Self::Output;
}
```

### 3.2 类型约束

**约束 1**：建造者类型约束
$$\text{Builder} \subseteq \text{Object} \land \text{ConcreteBuilder} \subseteq \text{Builder}$$

**约束 2**：产品类型约束
$$\text{Product} \subseteq \text{Object} \land \text{ConcreteProduct} \subseteq \text{Product}$$

### 3.3 类型推导

给定建造者类型 $B$ 和产品类型 $P$，类型推导规则为：

$$\frac{B : \text{Builder} \quad B \vdash \text{build} : () \rightarrow P}{B.\text{build}() : P}$$

## 4. 范畴论视角

### 4.1 函子映射

建造者模式可以看作是一个函子：
$$F : \mathcal{C} \rightarrow \mathcal{D}$$

其中：

- $\mathcal{C}$ 是构建步骤范畴
- $\mathcal{D}$ 是产品范畴

### 4.2 自然变换

不同建造者之间的转换可以表示为自然变换：
$$\eta : F \Rightarrow G$$

**定理 4.1**：建造者转换的一致性
对于任意自然变换 $\eta$，满足：
$$\eta_{P \circ Q} = \eta_P \circ \eta_Q$$

## 5. Rust 类型系统映射

### 5.1 实现架构

```rust
// 产品定义
#[derive(Debug, Clone)]
struct Car {
    engine: Option<String>,
    wheels: Option<u32>,
    color: Option<String>,
}

impl Car {
    fn new() -> Self {
        Car {
            engine: None,
            wheels: None,
            color: None,
        }
    }
}

// 建造者实现
struct CarBuilder {
    car: Car,
}

impl CarBuilder {
    fn new() -> Self {
        CarBuilder {
            car: Car::new(),
        }
    }
    
    fn reset(&mut self) -> &mut Self {
        self.car = Car::new();
        self
    }
    
    fn set_engine(&mut self, engine: String) -> &mut Self {
        self.car.engine = Some(engine);
        self
    }
    
    fn set_wheels(&mut self, wheels: u32) -> &mut Self {
        self.car.wheels = Some(wheels);
        self
    }
    
    fn set_color(&mut self, color: String) -> &mut Self {
        self.car.color = Some(color);
        self
    }
    
    fn build(&self) -> Car {
        self.car.clone()
    }
}

// 导演类
struct Director;

impl Director {
    fn construct_sports_car(builder: &mut CarBuilder) -> Car {
        builder
            .reset()
            .set_engine("V8 Engine".to_string())
            .set_wheels(4)
            .set_color("Red".to_string())
            .build()
    }
    
    fn construct_suv(builder: &mut CarBuilder) -> Car {
        builder
            .reset()
            .set_engine("V6 Engine".to_string())
            .set_wheels(4)
            .set_color("Blue".to_string())
            .build()
    }
}
```

### 5.2 类型安全保证

**定理 5.1**：类型安全
对于任意建造者 $B$ 和产品 $P$：
$$\text{TypeOf}(B.\text{build}()) = \text{ExpectedType}(P)$$

## 6. 实现策略

### 6.1 策略选择

1. **可变引用策略**：使用 `&mut self` 返回 `&mut Self`
2. **所有权策略**：使用 `self` 返回 `Self`
3. **不可变策略**：使用 `&self` 返回新实例

### 6.2 性能分析

**时间复杂度**：

- 构建步骤：$O(1)$ 每步
- 构建完成：$O(n)$，其中 $n$ 为步骤数
- 重置操作：$O(1)$

**空间复杂度**：

- 建造者实例：$O(1)$
- 产品实例：$O(m)$，其中 $m$ 为产品属性数

## 7. 形式化证明

### 7.1 构建完整性证明

**命题 7.1**：构建完整性
对于任意有效的构建序列 $\sigma$，建造者能够生成完整的产品。

**证明**：

1. 设 $\sigma = \langle s_1, s_2, \ldots, s_n \rangle$ 为有效构建序列
2. 根据定义，每个步骤 $s_i$ 都有对应的设置方法
3. 建造者按顺序执行所有步骤
4. 最终调用 `build()` 方法生成产品
5. 因此构建过程是完整的。$\square$

### 7.2 步骤顺序证明

**命题 7.2**：步骤顺序无关性
建造者模式允许灵活的步骤顺序，只要满足依赖约束。

**证明**：

1. 建造者模式使用链式调用
2. 每个步骤都是独立的操作
3. 只要满足依赖关系，步骤顺序可以调整
4. 因此步骤顺序具有灵活性。$\square$

## 8. 应用场景

### 8.1 复杂对象构建

```rust
// 应用示例
fn main() {
    let mut builder = CarBuilder::new();
    
    // 构建跑车
    let sports_car = Director::construct_sports_car(&mut builder);
    println!("Sports Car: {:?}", sports_car);
    
    // 构建SUV
    let suv = Director::construct_suv(&mut builder);
    println!("SUV: {:?}", suv);
    
    // 手动构建
    let custom_car = builder
        .reset()
        .set_engine("Electric Engine".to_string())
        .set_wheels(4)
        .set_color("Green".to_string())
        .build();
    println!("Custom Car: {:?}", custom_car);
}
```

### 8.2 配置对象构建

```rust
trait ConfigBuilder {
    fn set_database_url(&mut self, url: String) -> &mut Self;
    fn set_api_key(&mut self, key: String) -> &mut Self;
    fn set_timeout(&mut self, timeout: u64) -> &mut Self;
    fn build(&self) -> Config;
}
```

## 9. 总结

建造者模式通过以下方式提供形式化保证：

1. **构建过程分解**：将复杂对象的构建分解为多个步骤
2. **步骤灵活性**：支持不同的构建顺序和组合
3. **类型安全**：通过 Rust 的类型系统确保构建过程的正确性
4. **可重用性**：相同的构建过程可以创建不同的产品表示

该模式在 Rust 中的实现充分利用了所有权系统和类型系统的优势，提供了安全且灵活的构建机制。

---

**参考文献**：

1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Pierce, B. C. "Types and Programming Languages"
3. Mac Lane, S. "Categories for the Working Mathematician"
