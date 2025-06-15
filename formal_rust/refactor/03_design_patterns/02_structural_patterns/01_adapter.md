# 适配器模式 (Adapter Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [形式化定义 (Formal Definition)](#1-形式化定义-formal-definition)
2. [数学理论基础 (Mathematical Foundation)](#2-数学理论基础-mathematical-foundation)
3. [定理与证明 (Theorems and Proofs)](#3-定理与证明-theorems-and-proofs)
4. [Rust实现 (Rust Implementation)](#4-rust实现-rust-implementation)
5. [应用场景 (Application Scenarios)](#5-应用场景-application-scenarios)
6. [性能分析 (Performance Analysis)](#6-性能分析-performance-analysis)

---

## 1. 形式化定义 (Formal Definition)

### 1.1 适配器模式五元组 (Adapter Pattern Quintuple)

-**定义 1.1.1 (适配器模式)**

设 $A = (N, I, S, R, C)$ 为适配器模式，其中：

- $N = \{\text{"Adapter"}\}$ (模式名称)
- $I = \{\text{"使不兼容接口能够协同工作"}, \text{"提供统一接口"}\}$ (意图描述)
- $S = \{\text{Target}, \text{Adapter}, \text{Adaptee}, \text{Client}, \text{Interface}\}$ (结构定义)
- $R = \{(\text{Client}, \text{Target}), (\text{Adapter}, \text{Target}), (\text{Adapter}, \text{Adaptee})\}$ (关系映射)
- $C = \{\text{接口兼容性约束}, \text{功能等价性约束}, \text{性能约束}\}$ (约束条件)

### 1.2 接口适配定义 (Interface Adaptation Definition)

-**定义 1.2.1 (接口映射)**

设 $\mathcal{M}$ 为接口映射函数，满足：

$$\mathcal{M}: \text{TargetInterface} \rightarrow \text{AdapteeInterface}$$

-**定义 1.2.2 (功能等价性)**

适配器 $A$ 满足功能等价性，当且仅当：

$$\forall f \in \text{TargetInterface}, \text{Behavior}(f) = \text{Behavior}(\mathcal{M}(f))$$

---

## 2. 数学理论基础 (Mathematical Foundation)

### 2.1 接口兼容性理论 (Interface Compatibility Theory)

-**定义 2.1.1 (接口兼容性)**

两个接口 $I_1, I_2$ 是兼容的，当且仅当存在适配器 $A$ 使得：

$$\text{Client}(I_1) \equiv \text{Client}(A(I_2))$$

-**定义 2.1.2 (适配器正确性)**

适配器 $A$ 是正确的，当且仅当：

$$\forall \text{input}, \text{output} = A(\text{input}) \Rightarrow \text{ExpectedOutput}(\text{input}) = \text{output}$$

### 2.2 功能保持理论 (Function Preservation Theory)

-**定义 2.2.1 (功能保持)**

适配器保持功能，当且仅当：

$$\forall \text{operation}, \text{Result}(\text{operation}) = \text{Result}(A(\text{operation}))$$

---

## 3. 定理与证明 (Theorems and Proofs)

### 3.1 适配器正确性定理 (Adapter Correctness Theorem)

-**定理 3.1.1 (接口适配正确性)**

对于任意适配器模式 $A$，适配器正确地将目标接口适配到被适配者接口。

**证明**:
根据定义 1.2.1，接口映射函数 $\mathcal{M}$ 建立了目标接口到被适配者接口的映射。

根据定义 1.2.2，功能等价性确保了行为的一致性。

因此，适配器正确地将接口进行适配。

-**定理 3.1.2 (功能保持性)**

适配器模式保持原有功能的完整性。

**证明**:
根据定义 2.2.1，功能保持要求适配后的操作结果与原操作结果一致。

适配器的设计目标就是保持功能不变，只改变接口形式。

因此，适配器保持功能的完整性。

-**定理 3.1.3 (客户端透明性)**

适配器模式对客户端是透明的。

**证明**:
客户端只需要知道目标接口，不需要了解适配器的内部实现。

适配器封装了适配逻辑，客户端无需修改。

因此，适配器对客户端是透明的。

### 3.2 性能分析定理 (Performance Analysis Theorem)

-**定理 3.2.1 (适配器时间复杂度)**

适配器的时间复杂度为 $O(1)$，其中包含接口转换的开销。

**证明**:
适配器主要进行接口转换，不涉及复杂的算法。

转换操作通常是常数时间操作。

因此，时间复杂度为 $O(1)$。

-**定理 3.2.2 (适配器空间复杂度)**

适配器的空间复杂度为 $O(1)$。

**证明**:
适配器只需要存储被适配者的引用和转换逻辑。

不需要额外的数据结构。

因此，空间复杂度为 $O(1)$。

---

## 4. Rust实现 (Rust Implementation)

### 4.1 对象适配器实现 (Object Adapter Implementation)

```rust
/// 目标接口
pub trait Target {
    fn request(&self) -> String;
}

/// 被适配者
pub struct Adaptee {
    specific_data: String,
}

impl Adaptee {
    pub fn new(data: String) -> Self {
        Adaptee {
            specific_data: data,
        }
    }

    pub fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.specific_data)
    }
}

/// 适配器
pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Adapter { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将目标接口调用转换为被适配者接口调用
        self.adaptee.specific_request()
    }
}

/// 客户端
pub struct Client;

impl Client {
    pub fn use_target(&self, target: &dyn Target) -> String {
        target.request()
    }
}
```

### 4.2 类适配器实现 (Class Adapter Implementation)

```rust
/// 目标接口
pub trait Target {
    fn request(&self) -> String;
}

/// 被适配者
pub struct Adaptee {
    specific_data: String,
}

impl Adaptee {
    pub fn new(data: String) -> Self {
        Adaptee {
            specific_data: data,
        }
    }

    pub fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.specific_data)
    }
}

/// 类适配器（通过继承实现）
pub struct ClassAdapter {
    adaptee: Adaptee,
}

impl ClassAdapter {
    pub fn new(data: String) -> Self {
        ClassAdapter {
            adaptee: Adaptee::new(data),
        }
    }
}

impl Target for ClassAdapter {
    fn request(&self) -> String {
        // 直接调用被适配者的方法
        self.adaptee.specific_request()
    }
}
```

### 4.3 泛型适配器实现 (Generic Adapter Implementation)

```rust
use std::collections::HashMap;

/// 泛型目标接口
pub trait GenericTarget<T> {
    fn process(&self, data: T) -> T;
    fn get_info(&self) -> String;
}

/// 泛型被适配者
pub struct GenericAdaptee<T> {
    data: T,
    metadata: HashMap<String, String>,
}

impl<T> GenericAdaptee<T> {
    pub fn new(data: T) -> Self {
        GenericAdaptee {
            data,
            metadata: HashMap::new(),
        }
    }

    pub fn specific_process(&self, input: T) -> T {
        // 具体的处理逻辑
        input
    }

    pub fn get_specific_info(&self) -> String {
        format!("GenericAdaptee with {} metadata items", self.metadata.len())
    }

    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
}

/// 泛型适配器
pub struct GenericAdapter<T> {
    adaptee: GenericAdaptee<T>,
}

impl<T> GenericAdapter<T> {
    pub fn new(adaptee: GenericAdaptee<T>) -> Self {
        GenericAdapter { adaptee }
    }
}

impl<T> GenericTarget<T> for GenericAdapter<T> {
    fn process(&self, data: T) -> T {
        self.adaptee.specific_process(data)
    }

    fn get_info(&self) -> String {
        self.adaptee.get_specific_info()
    }
}
```

### 4.4 多接口适配器实现 (Multi-Interface Adapter Implementation)

```rust
/// 第一个目标接口
pub trait TargetA {
    fn operation_a(&self) -> String;
}

/// 第二个目标接口
pub trait TargetB {
    fn operation_b(&self) -> String;
}

/// 被适配者
pub struct MultiAdaptee {
    data: String,
}

impl MultiAdaptee {
    pub fn new(data: String) -> Self {
        MultiAdaptee { data }
    }

    pub fn specific_operation_a(&self) -> String {
        format!("Adaptee A: {}", self.data)
    }

    pub fn specific_operation_b(&self) -> String {
        format!("Adaptee B: {}", self.data)
    }
}

/// 多接口适配器
pub struct MultiAdapter {
    adaptee: MultiAdaptee,
}

impl MultiAdapter {
    pub fn new(adaptee: MultiAdaptee) -> Self {
        MultiAdapter { adaptee }
    }
}

impl TargetA for MultiAdapter {
    fn operation_a(&self) -> String {
        self.adaptee.specific_operation_a()
    }
}

impl TargetB for MultiAdapter {
    fn operation_b(&self) -> String {
        self.adaptee.specific_operation_b()
    }
}
```

### 4.5 异步适配器实现 (Async Adapter Implementation)

```rust
use std::future::Future;
use tokio::time::{sleep, Duration};

/// 异步目标接口
pub trait AsyncTarget {
    fn async_request(&self) -> impl Future<Output = String> + Send;
}

/// 同步被适配者
pub struct SyncAdaptee {
    data: String,
}

impl SyncAdaptee {
    pub fn new(data: String) -> Self {
        SyncAdaptee { data }
    }

    pub fn sync_request(&self) -> String {
        format!("SyncAdaptee: {}", self.data)
    }
}

/// 异步适配器
pub struct AsyncAdapter {
    adaptee: SyncAdaptee,
}

impl AsyncAdapter {
    pub fn new(adaptee: SyncAdaptee) -> Self {
        AsyncAdapter { adaptee }
    }
}

impl AsyncTarget for AsyncAdapter {
    async fn async_request(&self) -> String {
        // 模拟异步处理
        sleep(Duration::from_millis(100)).await;
        
        // 调用同步方法
        self.adaptee.sync_request()
    }
}
```

---

## 5. 应用场景 (Application Scenarios)

### 5.1 第三方库适配 (Third-Party Library Adapter)

```rust
use std::collections::HashMap;

/// 应用内部接口
pub trait PaymentProcessor {
    fn process_payment(&self, amount: f64, currency: &str) -> Result<String, String>;
    fn get_balance(&self) -> f64;
}

/// 第三方支付库接口
pub struct ThirdPartyPayment {
    api_key: String,
    balance: f64,
}

impl ThirdPartyPayment {
    pub fn new(api_key: String) -> Self {
        ThirdPartyPayment {
            api_key,
            balance: 1000.0,
        }
    }

    pub fn make_payment(&mut self, amount: f64, currency_code: &str) -> Result<String, String> {
        if amount > self.balance {
            return Err("Insufficient funds".to_string());
        }
        
        self.balance -= amount;
        Ok(format!("Payment of {} {} processed", amount, currency_code))
    }

    pub fn get_current_balance(&self) -> f64 {
        self.balance
    }
}

/// 支付适配器
pub struct PaymentAdapter {
    third_party: ThirdPartyPayment,
}

impl PaymentAdapter {
    pub fn new(api_key: String) -> Self {
        PaymentAdapter {
            third_party: ThirdPartyPayment::new(api_key),
        }
    }
}

impl PaymentProcessor for PaymentAdapter {
    fn process_payment(&self, amount: f64, currency: &str) -> Result<String, String> {
        // 适配第三方库的接口
        let mut third_party = ThirdPartyPayment::new(self.third_party.api_key.clone());
        third_party.balance = self.third_party.balance;
        
        third_party.make_payment(amount, currency)
    }

    fn get_balance(&self) -> f64 {
        self.third_party.get_current_balance()
    }
}
```

### 5.2 数据格式适配 (Data Format Adapter)

```rust
use serde::{Deserialize, Serialize};

/// 内部数据格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InternalData {
    pub id: u32,
    pub name: String,
    pub value: f64,
    pub timestamp: u64,
}

/// 外部数据格式
#[derive(Debug, Clone)]
pub struct ExternalData {
    pub identifier: String,
    pub title: String,
    pub amount: String,
    pub date: String,
}

/// 数据适配器
pub struct DataAdapter;

impl DataAdapter {
    pub fn external_to_internal(external: &ExternalData) -> InternalData {
        InternalData {
            id: external.identifier.parse().unwrap_or(0),
            name: external.title.clone(),
            value: external.amount.parse().unwrap_or(0.0),
            timestamp: Self::parse_timestamp(&external.date),
        }
    }

    pub fn internal_to_external(internal: &InternalData) -> ExternalData {
        ExternalData {
            identifier: internal.id.to_string(),
            title: internal.name.clone(),
            amount: internal.value.to_string(),
            date: Self::format_timestamp(internal.timestamp),
        }
    }

    fn parse_timestamp(date_str: &str) -> u64 {
        // 简化的时间戳解析
        date_str.len() as u64
    }

    fn format_timestamp(timestamp: u64) -> String {
        format!("{}", timestamp)
    }
}
```

### 5.3 协议适配器 (Protocol Adapter)

```rust
use std::collections::HashMap;

/// HTTP协议接口
pub trait HttpProtocol {
    fn send_request(&self, url: &str, method: &str, headers: HashMap<String, String>) -> Result<String, String>;
    fn receive_response(&self) -> Result<String, String>;
}

/// WebSocket协议接口
pub trait WebSocketProtocol {
    fn connect(&self, url: &str) -> Result<(), String>;
    fn send_message(&self, message: &str) -> Result<(), String>;
    fn receive_message(&self) -> Result<String, String>;
    fn disconnect(&self) -> Result<(), String>;
}

/// WebSocket实现
pub struct WebSocketClient {
    connected: bool,
    url: String,
}

impl WebSocketClient {
    pub fn new() -> Self {
        WebSocketClient {
            connected: false,
            url: String::new(),
        }
    }
}

impl WebSocketProtocol for WebSocketClient {
    fn connect(&self, url: &str) -> Result<(), String> {
        // WebSocket连接逻辑
        Ok(())
    }

    fn send_message(&self, message: &str) -> Result<(), String> {
        if !self.connected {
            return Err("Not connected".to_string());
        }
        Ok(())
    }

    fn receive_message(&self) -> Result<String, String> {
        if !self.connected {
            return Err("Not connected".to_string());
        }
        Ok("WebSocket message".to_string())
    }

    fn disconnect(&self) -> Result<(), String> {
        Ok(())
    }
}

/// HTTP到WebSocket适配器
pub struct HttpToWebSocketAdapter {
    websocket: WebSocketClient,
}

impl HttpToWebSocketAdapter {
    pub fn new() -> Self {
        HttpToWebSocketAdapter {
            websocket: WebSocketClient::new(),
        }
    }
}

impl HttpProtocol for HttpToWebSocketAdapter {
    fn send_request(&self, url: &str, method: &str, headers: HashMap<String, String>) -> Result<String, String> {
        // 将HTTP请求转换为WebSocket消息
        let message = format!("{} {} {:?}", method, url, headers);
        self.websocket.send_message(&message)?;
        self.websocket.receive_message()
    }

    fn receive_response(&self) -> Result<String, String> {
        self.websocket.receive_message()
    }
}
```

---

## 6. 性能分析 (Performance Analysis)

### 6.1 时间复杂度分析

**接口转换**: $O(1)$

- 适配器主要进行接口转换，时间为常数

**数据转换**: $O(n)$

- 数据格式转换可能需要遍历数据结构

**协议转换**: $O(1)$

- 协议适配通常是常数时间操作

### 6.2 空间复杂度分析

**对象适配器**: $O(1)$

- 只需要存储被适配者的引用

**类适配器**: $O(1)$

- 通过继承实现，空间开销最小

**数据适配器**: $O(n)$

- 可能需要额外的数据结构来存储转换后的数据

### 6.3 性能优化策略

**1. 缓存适配结果**

```rust
use std::collections::HashMap;

pub struct CachedAdapter {
    adaptee: Box<dyn Target>,
    cache: HashMap<String, String>,
}

impl CachedAdapter {
    pub fn new(adaptee: Box<dyn Target>) -> Self {
        CachedAdapter {
            adaptee,
            cache: HashMap::new(),
        }
    }

    pub fn request(&mut self, input: &str) -> String {
        if let Some(cached) = self.cache.get(input) {
            return cached.clone();
        }

        let result = self.adaptee.request();
        self.cache.insert(input.to_string(), result.clone());
        result
    }
}
```

**2. 延迟适配**

```rust
pub struct LazyAdapter {
    adaptee: Option<Box<dyn Target>>,
    factory: Box<dyn Fn() -> Box<dyn Target>>,
}

impl LazyAdapter {
    pub fn new<F>(factory: F) -> Self 
    where 
        F: Fn() -> Box<dyn Target> + 'static,
    {
        LazyAdapter {
            adaptee: None,
            factory: Box::new(factory),
        }
    }

    pub fn get_adaptee(&mut self) -> &mut Box<dyn Target> {
        if self.adaptee.is_none() {
            self.adaptee = Some((self.factory)());
        }
        self.adaptee.as_mut().unwrap()
    }
}
```

---

## 总结

适配器模式通过提供统一的接口，使不兼容的组件能够协同工作。其形式化模型确保了接口适配的正确性和功能保持性，而Rust实现展示了模式在实际应用中的灵活性和实用性。

该模式特别适用于：

- 集成第三方库和组件
- 处理不同数据格式的转换
- 协议适配和通信接口统一
- 遗留系统的现代化改造

通过形式化分析和Rust实现，适配器模式展现了其在软件架构中的重要价值，特别是在系统集成和接口统一方面。
