# 01. 适配器模式形式化理论

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

适配器模式是一种结构型设计模式，它允许不兼容的接口能够一起工作，通过将一个类的接口转换成客户期望的另一个接口。

**形式化定义**：
设 $\mathcal{I}_1$ 为源接口集合，$\mathcal{I}_2$ 为目标接口集合，则适配器模式可定义为：

$$\text{Adapter} : \mathcal{I}_1 \rightarrow \mathcal{I}_2$$

其中：

- $\mathcal{I}_1$ 为不兼容的源接口
- $\mathcal{I}_2$ 为客户期望的目标接口

### 1.2 类型签名

```haskell
class Adaptee where
  specificRequest :: Adaptee -> String

class Target where
  request :: Target -> String

class Adapter where
  request :: Adapter -> String
```

### 1.3 模式结构

```
Target
└── request() -> String

Adaptee
└── specificRequest() -> String

Adapter
├── adaptee: Adaptee
└── request() -> String
```

## 2. 数学基础

### 2.1 接口映射理论

**定义 2.1**：接口映射
接口映射 $M$ 是一个从源接口到目标接口的函数：
$$M : \mathcal{I}_1 \rightarrow \mathcal{I}_2$$

**定义 2.2**：适配函数
适配函数 $A$ 将源接口的方法调用转换为目标接口的方法调用：
$$A : \text{Method}_1 \rightarrow \text{Method}_2$$

其中：

- $\text{Method}_1$ 为源接口的方法集合
- $\text{Method}_2$ 为目标接口的方法集合

### 2.2 适配性质

**性质 2.1**：适配的传递性
$$\forall i_1, i_2, i_3 \in \mathcal{I} : A(i_1 \rightarrow i_2) \land A(i_2 \rightarrow i_3) \Rightarrow A(i_1 \rightarrow i_3)$$

**性质 2.2**：适配的幂等性
$$\forall i \in \mathcal{I} : A(A(i)) = A(i)$$

**定理 2.1**：适配的唯一性
对于任意源接口 $i_1$ 和目标接口 $i_2$，适配器 $A$ 是唯一的。

## 3. 类型系统分析

### 3.1 类型构造器

在 Rust 中，适配器模式可以通过 trait 和结构体实现：

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 源接口（不兼容）
trait Adaptee {
    fn specific_request(&self) -> String;
}

// 适配器
struct Adapter {
    adaptee: Box<dyn Adaptee>,
}

impl Adapter {
    fn new(adaptee: Box<dyn Adaptee>) -> Self {
        Adapter { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将源接口调用适配为目标接口
        self.adaptee.specific_request()
    }
}
```

### 3.2 类型约束

**约束 1**：接口类型约束
$$\text{Target} \subseteq \text{Trait} \land \text{Adaptee} \subseteq \text{Trait}$$

**约束 2**：适配器类型约束
$$\text{Adapter} \subseteq \text{Struct} \land \text{Adapter} \subseteq \text{Target}$$

### 3.3 类型推导

给定适配器类型 $A$ 和目标类型 $T$，类型推导规则为：

$$\frac{A : \text{Adapter} \quad A \vdash \text{request} : () \rightarrow \text{String}}{A.\text{request}() : \text{String}}$$

## 4. 范畴论视角

### 4.1 函子映射

适配器模式可以看作是一个函子：
$$F : \mathcal{C}_1 \rightarrow \mathcal{C}_2$$

其中：

- $\mathcal{C}_1$ 是源接口范畴
- $\mathcal{C}_2$ 是目标接口范畴

### 4.2 自然变换

不同适配器之间的转换可以表示为自然变换：
$$\eta : F \Rightarrow G$$

**定理 4.1**：适配器转换的一致性
对于任意自然变换 $\eta$，满足：
$$\eta_{i_1 \circ i_2} = \eta_{i_1} \circ \eta_{i_2}$$

## 5. Rust 类型系统映射

### 5.1 实现架构

```rust
// 目标接口
trait PaymentProcessor {
    fn process_payment(&self, amount: f64) -> Result<String, String>;
}

// 源接口（第三方支付系统）
trait ThirdPartyPayment {
    fn pay(&self, amount: f64, currency: &str) -> bool;
    fn get_payment_status(&self) -> &str;
}

// 具体源实现
struct PayPalPayment;

impl ThirdPartyPayment for PayPalPayment {
    fn pay(&self, amount: f64, currency: &str) -> bool {
        println!("PayPal: Processing payment of {} {}", amount, currency);
        true
    }
    
    fn get_payment_status(&self) -> &str {
        "Completed"
    }
}

// 适配器
struct PaymentAdapter {
    third_party: Box<dyn ThirdPartyPayment>,
}

impl PaymentAdapter {
    fn new(third_party: Box<dyn ThirdPartyPayment>) -> Self {
        PaymentAdapter { third_party }
    }
}

impl PaymentProcessor for PaymentAdapter {
    fn process_payment(&self, amount: f64) -> Result<String, String> {
        if self.third_party.pay(amount, "USD") {
            Ok(format!("Payment processed successfully. Status: {}", 
                      self.third_party.get_payment_status()))
        } else {
            Err("Payment processing failed".to_string())
        }
    }
}

// 客户端代码
struct Client;

impl Client {
    fn process_payment(processor: &dyn PaymentProcessor, amount: f64) {
        match processor.process_payment(amount) {
            Ok(result) => println!("Success: {}", result),
            Err(error) => println!("Error: {}", error),
        }
    }
}
```

### 5.2 类型安全保证

**定理 5.1**：类型安全
对于任意适配器 $A$ 和目标接口 $T$：
$$\text{TypeOf}(A.\text{request}()) = \text{ExpectedType}(T.\text{request}())$$

## 6. 实现策略

### 6.1 策略选择

1. **对象适配器策略**：使用组合关系
2. **类适配器策略**：使用继承关系（Rust 中通过 trait 实现）
3. **接口适配器策略**：适配多个接口

### 6.2 性能分析

**时间复杂度**：

- 适配调用：$O(1)$
- 接口转换：$O(1)$
- 方法委托：$O(1)$

**空间复杂度**：

- 适配器实例：$O(1)$
- 被适配对象：$O(1)$

## 7. 形式化证明

### 7.1 适配正确性证明

**命题 7.1**：适配正确性
对于任意源接口 $i_1$ 和目标接口 $i_2$，适配器 $A$ 能够正确地将 $i_1$ 适配为 $i_2$。

**证明**：

1. 设 $m_1$ 为源接口的方法，$m_2$ 为目标接口的方法
2. 适配器 $A$ 实现了目标接口 $i_2$
3. 在适配器的实现中，调用源接口的方法 $m_1$
4. 将源接口的结果转换为目标接口期望的格式
5. 因此适配是正确的。$\square$

### 7.2 接口兼容性证明

**命题 7.2**：接口兼容性
适配器模式确保客户端代码无需修改即可使用不兼容的接口。

**证明**：

1. 适配器实现了客户端期望的目标接口
2. 客户端代码只依赖目标接口
3. 适配器内部处理与源接口的交互
4. 因此客户端代码无需修改。$\square$

## 8. 应用场景

### 8.1 支付系统集成

```rust
// 应用示例
fn main() {
    // 创建第三方支付系统
    let paypal = PayPalPayment;
    
    // 创建适配器
    let adapter = PaymentAdapter::new(Box::new(paypal));
    
    // 客户端使用统一的接口
    Client::process_payment(&adapter, 100.0);
    Client::process_payment(&adapter, 50.0);
}
```

### 8.2 数据格式转换

```rust
trait DataFormat {
    fn serialize(&self, data: &str) -> Vec<u8>;
    fn deserialize(&self, data: &[u8]) -> String;
}

trait LegacyFormat {
    fn encode(&self, data: &str) -> String;
    fn decode(&self, data: &str) -> String;
}

struct FormatAdapter {
    legacy: Box<dyn LegacyFormat>,
}

impl DataFormat for FormatAdapter {
    fn serialize(&self, data: &str) -> Vec<u8> {
        let encoded = self.legacy.encode(data);
        encoded.into_bytes()
    }
    
    fn deserialize(&self, data: &[u8]) -> String {
        let decoded = String::from_utf8_lossy(data);
        self.legacy.decode(&decoded)
    }
}
```

## 9. 总结

适配器模式通过以下方式提供形式化保证：

1. **接口兼容性**：将不兼容的接口转换为兼容的接口
2. **类型安全**：通过 Rust 的类型系统确保适配的正确性
3. **代码复用**：允许现有代码与新的接口一起工作
4. **解耦合**：客户端代码与具体实现解耦

该模式在 Rust 中的实现充分利用了 trait 系统和所有权系统的优势，提供了安全且灵活的接口适配机制。

---

**参考文献**：

1. Gamma, E., et al. "Design Patterns: Elements of Reusable Object-Oriented Software"
2. Pierce, B. C. "Types and Programming Languages"
3. Mac Lane, S. "Categories for the Working Mathematician"
