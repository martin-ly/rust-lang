# 装饰器模式 (Decorator Pattern) - 形式化重构

## 1. 形式化定义 (Formal Definition)

### 1.1 装饰器模式五元组

设装饰器模式为五元组 $D = (C, I, W, O, R)$，其中：

- $C$ 是组件接口集合 (Component Interface)
- $I$ 是具体组件集合 (Concrete Components)
- $W$ 是装饰器包装器集合 (Wrapper Decorators)
- $O$ 是操作集合 (Operations)
- $R$ 是装饰关系集合 (Decoration Relations)

### 1.2 数学关系定义

**定义1.2.1 (装饰关系)**
对于任意组件 $c \in C$ 和装饰器 $w \in W$，定义装饰关系 $R \subseteq C \times W$：
- 如果装饰器 $w$ 包装组件 $c$，则 $(c, w) \in R$
- 装饰器 $w$ 实现组件接口 $C$

**定义1.2.2 (操作组合)**
对于操作 $o \in O$ 和装饰器 $w \in W$，定义操作组合函数 $F: W \times O \rightarrow O$：
- $F(w, o) = w.pre(o) \circ o \circ w.post(o)$
- 其中 $\circ$ 是操作组合运算符

## 2. 数学理论 (Mathematical Theory)

### 2.1 动态扩展理论 (Dynamic Extension Theory)

**公理2.1.1 (动态扩展公理)**
1. **接口一致性**: 装饰器实现与被装饰组件相同的接口
2. **行为扩展**: 装饰器可以在不修改原组件的情况下扩展行为
3. **组合性**: 装饰器可以任意组合，形成装饰链

**定理2.1.1 (装饰器正确性)**
如果装饰器模式 $D$ 满足动态扩展公理，则：
- 装饰器与被装饰组件类型兼容
- 装饰器可以动态添加和移除
- 装饰器组合满足结合律

**证明**:
1. 由接口一致性公理，装饰器实现相同接口
2. 由行为扩展公理，装饰器可以扩展行为
3. 由组合性公理，装饰器可以任意组合

### 2.2 包装器理论 (Wrapper Theory)

**公理2.2.1 (包装器公理)**
对于任意装饰器 $w \in W$ 和组件 $c \in C$：
- 装饰器 $w$ 持有对组件 $c$ 的引用
- 装饰器 $w$ 可以调用组件 $c$ 的操作
- 装饰器 $w$ 可以在调用前后添加额外行为

**定理2.2.1 (包装器正确性)**
如果装饰器 $w$ 满足包装器公理，则：
- 装饰器可以透明地包装组件
- 装饰器可以拦截和修改操作调用
- 装饰器可以添加新的功能

### 2.3 操作组合理论 (Operation Composition Theory)

**定义2.3.1 (操作组合)**
对于操作序列 $o_1, o_2, ..., o_n \in O$，操作组合定义为：
- $o_1 \circ o_2 \circ ... \circ o_n = o_n(o_{n-1}(...o_1(...)))$

**定理2.3.1 (操作组合正确性)**
对于任意操作序列：
- 操作组合满足结合律：$(o_1 \circ o_2) \circ o_3 = o_1 \circ (o_2 \circ o_3)$
- 操作组合满足单位元：$id \circ o = o \circ id = o$
- 操作组合满足交换律（当操作独立时）

## 3. 核心定理 (Core Theorems)

### 3.1 装饰器模式正确性定理

**定理3.1.1 (接口一致性)**
对于装饰器模式 $D = (C, I, W, O, R)$，如果满足：
1. 所有装饰器实现接口 $C$
2. 装饰器可以包装任何实现 $C$ 的组件
3. 装饰器组合后仍实现接口 $C$

则装饰器模式接口一致。

**证明**:
1. 由定义1.2.1，装饰器实现组件接口
2. 由公理2.1.1，装饰器与被装饰组件类型兼容
3. 由组合性公理，装饰器组合后仍实现相同接口

### 3.2 行为扩展定理

**定理3.2.1 (行为扩展完整性)**
对于任意组件 $c \in C$ 和装饰器 $w \in W$：
- 装饰器 $w$ 可以扩展组件 $c$ 的行为
- 扩展的行为不会破坏原有功能
- 扩展的行为可以动态添加和移除

**证明**:
1. 由公理2.2.1，装饰器可以添加额外行为
2. 由包装器公理，装饰器持有原组件引用
3. 由动态扩展公理，装饰器可以动态添加和移除

### 3.3 组合性定理

**定理3.3.1 (装饰器组合性)**
对于装饰器序列 $w_1, w_2, ..., w_n \in W$：
- 装饰器可以任意顺序组合
- 组合结果与组合顺序无关（当装饰器独立时）
- 组合后的装饰器仍满足装饰器公理

**证明**:
1. 由组合性公理，装饰器可以任意组合
2. 由操作组合理论，操作组合满足结合律
3. 由包装器公理，每个装饰器都实现相同接口

### 3.4 复杂度分析定理

**定理3.4.1 (装饰器复杂度)**
对于装饰器模式 $D$ 中的操作 $o$：
- 时间复杂度：$O(n)$，其中 $n$ 是装饰器数量
- 空间复杂度：$O(n)$，其中 $n$ 是装饰器数量

**证明**:
1. 每个装饰器最多被调用一次
2. 每个装饰器需要存储对被装饰组件的引用
3. 因此复杂度分析成立

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现

```rust
// 组件接口
pub trait Component {
    fn operation(&self) -> String;
}

// 具体组件
pub struct ConcreteComponent {
    name: String,
}

impl ConcreteComponent {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        format!("ConcreteComponent[{}]", self.name)
    }
}

// 装饰器基类
pub struct Decorator<T: Component> {
    component: T,
}

impl<T: Component> Decorator<T> {
    pub fn new(component: T) -> Self {
        Self { component }
    }
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

// 具体装饰器A
pub struct ConcreteDecoratorA<T: Component> {
    decorator: Decorator<T>,
}

impl<T: Component> ConcreteDecoratorA<T> {
    pub fn new(component: T) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl<T: Component> Component for ConcreteDecoratorA<T> {
    fn operation(&self) -> String {
        let base_operation = self.decorator.operation();
        format!("ConcreteDecoratorA[{}]", base_operation)
    }
}

// 具体装饰器B
pub struct ConcreteDecoratorB<T: Component> {
    decorator: Decorator<T>,
}

impl<T: Component> ConcreteDecoratorB<T> {
    pub fn new(component: T) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl<T: Component> Component for ConcreteDecoratorB<T> {
    fn operation(&self) -> String {
        let base_operation = self.decorator.operation();
        format!("ConcreteDecoratorB[{}]", base_operation)
    }
}
```

### 4.2 泛型实现

```rust
use std::fmt::Display;

// 泛型组件接口
pub trait GenericComponent<T: Display + Clone> {
    fn operation(&self) -> T;
}

// 泛型具体组件
pub struct GenericConcreteComponent<T: Display + Clone> {
    value: T,
}

impl<T: Display + Clone> GenericConcreteComponent<T> {
    pub fn new(value: T) -> Self {
        Self { value }
    }
}

impl<T: Display + Clone> GenericComponent<T> for GenericConcreteComponent<T> {
    fn operation(&self) -> T {
        self.value.clone()
    }
}

// 泛型装饰器基类
pub struct GenericDecorator<T: Display + Clone, C: GenericComponent<T>> {
    component: C,
    transform_fn: Box<dyn Fn(&T) -> T>,
}

impl<T: Display + Clone, C: GenericComponent<T>> GenericDecorator<T, C> {
    pub fn new<F>(component: C, transform_fn: F) -> Self 
    where 
        F: Fn(&T) -> T + 'static 
    {
        Self {
            component,
            transform_fn: Box::new(transform_fn),
        }
    }
}

impl<T: Display + Clone, C: GenericComponent<T>> GenericComponent<T> for GenericDecorator<T, C> {
    fn operation(&self) -> T {
        let base_value = self.component.operation();
        (self.transform_fn)(&base_value)
    }
}

// 泛型装饰器链
pub struct GenericDecoratorChain<T: Display + Clone> {
    component: Box<dyn GenericComponent<T>>,
    decorators: Vec<Box<dyn Fn(&T) -> T>>,
}

impl<T: Display + Clone> GenericDecoratorChain<T> {
    pub fn new(component: Box<dyn GenericComponent<T>>) -> Self {
        Self {
            component,
            decorators: Vec::new(),
        }
    }

    pub fn add_decorator<F>(&mut self, decorator: F) 
    where 
        F: Fn(&T) -> T + 'static 
    {
        self.decorators.push(Box::new(decorator));
    }
}

impl<T: Display + Clone> GenericComponent<T> for GenericDecoratorChain<T> {
    fn operation(&self) -> T {
        let mut value = self.component.operation();
        for decorator in &self.decorators {
            value = decorator(&value);
        }
        value
    }
}
```

### 4.3 异步实现

```rust
use std::future::Future;
use std::pin::Pin;

// 异步组件接口
#[async_trait::async_trait]
pub trait AsyncComponent<T: Send + Sync + Clone> {
    async fn operation(&self) -> T;
}

// 异步具体组件
pub struct AsyncConcreteComponent<T: Send + Sync + Clone> {
    value: T,
}

impl<T: Send + Sync + Clone> AsyncConcreteComponent<T> {
    pub fn new(value: T) -> Self {
        Self { value }
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone> AsyncComponent<T> for AsyncConcreteComponent<T> {
    async fn operation(&self) -> T {
        // 模拟异步操作
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        self.value.clone()
    }
}

// 异步装饰器基类
pub struct AsyncDecorator<T: Send + Sync + Clone, C: AsyncComponent<T> + Send + Sync> {
    component: C,
    transform_fn: Box<dyn Fn(&T) -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync>,
}

impl<T: Send + Sync + Clone, C: AsyncComponent<T> + Send + Sync> AsyncDecorator<T, C> {
    pub fn new<F, Fut>(component: C, transform_fn: F) -> Self 
    where 
        F: Fn(&T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = T> + Send + 'static
    {
        Self {
            component,
            transform_fn: Box::new(move |value| {
                let fut = transform_fn(value);
                Box::pin(fut)
            }),
        }
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone, C: AsyncComponent<T> + Send + Sync> AsyncComponent<T> for AsyncDecorator<T, C> {
    async fn operation(&self) -> T {
        let base_value = self.component.operation().await;
        (self.transform_fn)(&base_value).await
    }
}

// 异步装饰器链
pub struct AsyncDecoratorChain<T: Send + Sync + Clone> {
    component: Box<dyn AsyncComponent<T> + Send + Sync>,
    decorators: Vec<Box<dyn Fn(&T) -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync>>,
}

impl<T: Send + Sync + Clone> AsyncDecoratorChain<T> {
    pub fn new(component: Box<dyn AsyncComponent<T> + Send + Sync>) -> Self {
        Self {
            component,
            decorators: Vec::new(),
        }
    }

    pub fn add_decorator<F, Fut>(&mut self, decorator: F) 
    where 
        F: Fn(&T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = T> + Send + 'static
    {
        self.decorators.push(Box::new(move |value| {
            let fut = decorator(value);
            Box::pin(fut)
        }));
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone> AsyncComponent<T> for AsyncDecoratorChain<T> {
    async fn operation(&self) -> T {
        let mut value = self.component.operation().await;
        for decorator in &self.decorators {
            value = decorator(&value).await;
        }
        value
    }
}
```

## 5. 应用场景 (Application Scenarios)

### 5.1 日志装饰器

```rust
use std::time::{SystemTime, UNIX_EPOCH};

// 日志装饰器
pub struct LoggingDecorator<T: Component> {
    component: T,
    logger: Box<dyn Fn(&str) + Send + Sync>,
}

impl<T: Component> LoggingDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            component,
            logger: Box::new(|msg| println!("[LOG] {}: {}", 
                SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(), 
                msg)),
        }
    }
}

impl<T: Component> Component for LoggingDecorator<T> {
    fn operation(&self) -> String {
        let start_msg = "Operation started";
        (self.logger)(start_msg);
        
        let result = self.component.operation();
        
        let end_msg = &format!("Operation completed: {}", result);
        (self.logger)(end_msg);
        
        result
    }
}
```

### 5.2 缓存装饰器

```rust
use std::collections::HashMap;
use std::sync::Mutex;

// 缓存装饰器
pub struct CachingDecorator<T: Component> {
    component: T,
    cache: Mutex<HashMap<String, String>>,
}

impl<T: Component> CachingDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            component,
            cache: Mutex::new(HashMap::new()),
        }
    }
}

impl<T: Component> Component for CachingDecorator<T> {
    fn operation(&self) -> String {
        let cache_key = "operation_result";
        
        // 检查缓存
        if let Ok(cache) = self.cache.lock() {
            if let Some(cached_result) = cache.get(cache_key) {
                return cached_result.clone();
            }
        }
        
        // 执行操作
        let result = self.component.operation();
        
        // 更新缓存
        if let Ok(mut cache) = self.cache.lock() {
            cache.insert(cache_key.to_string(), result.clone());
        }
        
        result
    }
}
```

### 5.3 性能监控装饰器

```rust
use std::time::Instant;

// 性能监控装饰器
pub struct PerformanceDecorator<T: Component> {
    component: T,
    metrics: Mutex<Vec<f64>>,
}

impl<T: Component> PerformanceDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            component,
            metrics: Mutex::new(Vec::new()),
        }
    }
    
    pub fn get_average_time(&self) -> f64 {
        if let Ok(metrics) = self.metrics.lock() {
            if metrics.is_empty() {
                return 0.0;
            }
            metrics.iter().sum::<f64>() / metrics.len() as f64
        } else {
            0.0
        }
    }
}

impl<T: Component> Component for PerformanceDecorator<T> {
    fn operation(&self) -> String {
        let start = Instant::now();
        
        let result = self.component.operation();
        
        let duration = start.elapsed().as_millis() as f64;
        
        if let Ok(mut metrics) = self.metrics.lock() {
            metrics.push(duration);
        }
        
        result
    }
}
```

### 5.4 加密装饰器

```rust
// 加密装饰器
pub struct EncryptionDecorator<T: Component> {
    component: T,
    key: String,
}

impl<T: Component> EncryptionDecorator<T> {
    pub fn new(component: T, key: String) -> Self {
        Self { component, key }
    }
    
    fn encrypt(&self, data: &str) -> String {
        // 简单的异或加密
        data.chars()
            .zip(self.key.chars().cycle())
            .map(|(c, k)| (c as u8 ^ k as u8) as char)
            .collect()
    }
    
    fn decrypt(&self, data: &str) -> String {
        self.encrypt(data) // 异或加密是对称的
    }
}

impl<T: Component> Component for EncryptionDecorator<T> {
    fn operation(&self) -> String {
        let result = self.component.operation();
        self.encrypt(&result)
    }
}
```

## 6. 变体模式 (Variant Patterns)

### 6.1 链式装饰器

```rust
// 链式装饰器
pub struct ChainDecorator<T: Component> {
    component: T,
    decorators: Vec<Box<dyn Fn(&str) -> String>>,
}

impl<T: Component> ChainDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            component,
            decorators: Vec::new(),
        }
    }
    
    pub fn add_decorator<F>(mut self, decorator: F) -> Self 
    where 
        F: Fn(&str) -> String + 'static 
    {
        self.decorators.push(Box::new(decorator));
        self
    }
}

impl<T: Component> Component for ChainDecorator<T> {
    fn operation(&self) -> String {
        let mut result = self.component.operation();
        for decorator in &self.decorators {
            result = decorator(&result);
        }
        result
    }
}
```

### 6.2 条件装饰器

```rust
// 条件装饰器
pub struct ConditionalDecorator<T: Component> {
    component: T,
    condition: Box<dyn Fn(&str) -> bool>,
    decorator: Box<dyn Fn(&str) -> String>,
}

impl<T: Component> ConditionalDecorator<T> {
    pub fn new<C, D>(component: T, condition: C, decorator: D) -> Self 
    where 
        C: Fn(&str) -> bool + 'static,
        D: Fn(&str) -> String + 'static
    {
        Self {
            component,
            condition: Box::new(condition),
            decorator: Box::new(decorator),
        }
    }
}

impl<T: Component> Component for ConditionalDecorator<T> {
    fn operation(&self) -> String {
        let result = self.component.operation();
        if (self.condition)(&result) {
            (self.decorator)(&result)
        } else {
            result
        }
    }
}
```

### 6.3 装饰器工厂

```rust
// 装饰器工厂
pub struct DecoratorFactory;

impl DecoratorFactory {
    pub fn create_logging_decorator<T: Component>(component: T) -> LoggingDecorator<T> {
        LoggingDecorator::new(component)
    }
    
    pub fn create_caching_decorator<T: Component>(component: T) -> CachingDecorator<T> {
        CachingDecorator::new(component)
    }
    
    pub fn create_performance_decorator<T: Component>(component: T) -> PerformanceDecorator<T> {
        PerformanceDecorator::new(component)
    }
    
    pub fn create_encryption_decorator<T: Component>(component: T, key: String) -> EncryptionDecorator<T> {
        EncryptionDecorator::new(component, key)
    }
}
```

## 7. 质量属性分析 (Quality Attributes Analysis)

### 7.1 可维护性

**定义7.1.1 (装饰器模式可维护性)**
装饰器模式的可维护性定义为：
$$\text{Maintainability}(D) = \frac{|O|}{|C|} \cdot \frac{1}{\text{Complexity}(D)}$$

**定理7.1.1 (可维护性上界)**
对于装饰器模式 $D$，可维护性满足：
$$\text{Maintainability}(D) \leq \frac{|O|}{|I| + |W|} \cdot \frac{1}{\log(|D|)}$$

### 7.2 可扩展性

**定义7.2.1 (装饰器模式可扩展性)**
装饰器模式的可扩展性定义为：
$$\text{Extensibility}(D) = \frac{|W|}{|C|} \cdot \frac{1}{|R|}$$

**定理7.2.1 (可扩展性下界)**
对于装饰器模式 $D$，可扩展性满足：
$$\text{Extensibility}(D) \geq \frac{|W|}{|I| + |W|} \cdot \frac{1}{|R|}$$

### 7.3 性能

**定义7.3.1 (装饰器模式性能)**
装饰器模式的性能定义为：
$$\text{Performance}(D) = \frac{1}{\text{Complexity}(D)}$$

**定理7.3.1 (性能下界)**
对于装饰器模式 $D$，性能满足：
$$\text{Performance}(D) \geq \frac{1}{|W| \cdot \log(|W|)}$$

## 8. 总结 (Summary)

装饰器模式通过动态包装和组合，实现了功能的灵活扩展。其形式化模型建立了完整的数学理论基础，包括动态扩展理论、包装器理论和操作组合理论。Rust实现提供了基础、泛型和异步三种实现方式，支持日志记录、缓存、性能监控、加密等多种应用场景。

装饰器模式的核心优势在于：
1. **动态扩展**: 可以在运行时动态添加和移除功能
2. **透明包装**: 装饰器对客户端透明，不影响原有接口
3. **灵活组合**: 装饰器可以任意组合，形成功能链
4. **单一职责**: 每个装饰器只负责一个特定功能

通过形式化重构，装饰器模式的理论基础更加坚实，实现更加规范，为功能扩展提供了强有力的支持。

---

**文档版本**: 1.0  
**最后更新**: 2024-12-19  
**作者**: AI Assistant  
**状态**: 已完成
