# 享元模式 (Flyweight Pattern) - 形式化重构

## 1. 形式化定义 (Formal Definition)

### 1.1 享元模式五元组

设享元模式为五元组 $F = (I, E, S, C, P)$，其中：

- $I$ 是内部状态集合 (Intrinsic State)
- $E$ 是外部状态集合 (Extrinsic State)
- $S$ 是共享对象集合 (Shared Objects)
- $C$ 是上下文集合 (Context)
- $P$ 是池化管理集合 (Pool Management)

### 1.2 数学关系定义

**定义1.2.1 (状态分离)**
对于享元对象 $f \in S$，定义状态分离函数：

- 内部状态：$I_f \subseteq I$，对象固有的、不可变的状态
- 外部状态：$E_f \subseteq E$，对象运行时的、可变的状态

**定义1.2.2 (共享关系)**
对于享元对象 $f_1, f_2 \in S$，定义共享关系 $R \subseteq S \times S$：

- $(f_1, f_2) \in R$ 当且仅当 $I_{f_1} = I_{f_2}$

**定义1.2.3 (池化映射)**
对于内部状态 $i \in I$，定义池化映射 $P: I \rightarrow S$：

- $P(i) = f$ 表示内部状态 $i$ 对应的享元对象 $f$

## 2. 数学理论 (Mathematical Theory)

### 2.1 状态分离理论 (State Separation Theory)

**公理2.1.1 (状态分离公理)**

1. **内部状态不变性**: 内部状态在对象生命周期内不变
2. **外部状态可变性**: 外部状态可以在运行时改变
3. **状态独立性**: 内部状态与外部状态相互独立

**定理2.1.1 (状态分离正确性)**
如果享元模式 $F$ 满足状态分离公理，则：

- 内部状态可以被多个对象共享
- 外部状态为每个对象独有
- 状态分离降低内存使用

**证明**:

1. 由内部状态不变性公理，内部状态可以共享
2. 由外部状态可变性公理，外部状态需要独有
3. 由状态独立性公理，状态分离是合理的

### 2.2 对象共享理论 (Object Sharing Theory)

**公理2.2.1 (对象共享公理)**
对于享元对象集合 $S$：

- 相同内部状态的对象可以共享
- 共享对象通过池化管理
- 共享对象支持并发访问

**定理2.2.1 (共享正确性)**
如果享元模式 $F$ 满足对象共享公理，则：

- 共享对象的内存使用最小化
- 共享对象的访问是线程安全的
- 共享对象的生命周期被正确管理

### 2.3 池化管理理论 (Pool Management Theory)

**定义2.3.1 (池化函数)**
对于内部状态集合 $I$，池化函数 $P: I \rightarrow S$ 定义为：

- $P(i) = \text{get_or_create}(i)$，获取或创建内部状态为 $i$ 的享元对象

**定理2.3.1 (池化正确性)**
对于任意内部状态 $i \in I$：

- 池化函数是确定性的
- 池化函数在有限时间内返回结果
- 池化函数保证对象唯一性

## 3. 核心定理 (Core Theorems)

### 3.1 享元模式正确性定理

**定理3.1.1 (状态分离完整性)**
对于享元模式 $F = (I, E, S, C, P)$，如果满足：

1. 内部状态与外部状态完全分离
2. 相同内部状态的对象可以共享
3. 外部状态通过上下文传递

则享元模式状态分离完整。

**证明**:

1. 由定义1.2.1，状态分离函数定义正确
2. 由公理2.1.1，状态分离公理成立
3. 由定义1.2.2，共享关系定义正确

### 3.2 内存优化定理

**定理3.2.1 (内存使用优化)**
对于享元模式 $F$：

- 内存使用：$O(|I| + |E| \cdot |C|)$ 而不是 $O(|S| \cdot (|I| + |E|))$
- 其中 $|I|$ 是不同内部状态数量，$|C|$ 是上下文数量

**证明**:

1. 内部状态被共享，只需要存储一次
2. 外部状态为每个上下文独有
3. 因此内存使用优化

### 3.3 性能分析定理

**定理3.3.1 (享元性能)**
对于享元模式 $F$ 中的操作：

- 对象创建：$O(\log(|I|))$ 查找时间
- 对象访问：$O(1)$ 访问时间
- 内存使用：$O(|I| + |E| \cdot |C|)$

**证明**:

1. 对象创建需要查找池中是否已存在
2. 对象访问是直接引用访问
3. 内存使用由状态分离决定

### 3.4 并发安全定理

**定理3.4.1 (并发安全性)**
对于享元模式 $F$：

- 内部状态是只读的，天然线程安全
- 外部状态通过上下文管理，支持并发访问
- 池化管理需要同步机制

**证明**:

1. 内部状态不变性保证只读访问
2. 外部状态独立性保证并发安全
3. 池化管理需要线程安全实现

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 享元接口
pub trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
}

// 具体享元
pub struct ConcreteFlyweight {
    intrinsic_state: String,
}

impl ConcreteFlyweight {
    pub fn new(intrinsic_state: String) -> Self {
        Self { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!("ConcreteFlyweight[{}] with extrinsic state: {}", 
                self.intrinsic_state, extrinsic_state)
    }
}

// 享元工厂
pub struct FlyweightFactory {
    flyweights: Arc<Mutex<HashMap<String, Arc<ConcreteFlyweight>>>>,
}

impl FlyweightFactory {
    pub fn new() -> Self {
        Self {
            flyweights: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_flyweight(&self, intrinsic_state: String) -> Arc<ConcreteFlyweight> {
        let mut flyweights = self.flyweights.lock().unwrap();
        
        if let Some(flyweight) = flyweights.get(&intrinsic_state) {
            flyweight.clone()
        } else {
            let flyweight = Arc::new(ConcreteFlyweight::new(intrinsic_state.clone()));
            flyweights.insert(intrinsic_state, flyweight.clone());
            flyweight
        }
    }
    
    pub fn get_flyweight_count(&self) -> usize {
        self.flyweights.lock().unwrap().len()
    }
}

// 上下文
pub struct Context {
    flyweight: Arc<dyn Flyweight>,
    extrinsic_state: String,
}

impl Context {
    pub fn new(flyweight: Arc<dyn Flyweight>, extrinsic_state: String) -> Self {
        Self {
            flyweight,
            extrinsic_state,
        }
    }
    
    pub fn operation(&self) -> String {
        self.flyweight.operation(&self.extrinsic_state)
    }
}
```

### 4.2 泛型实现

```rust
use std::collections::HashMap;
use std::fmt::Display;
use std::sync::{Arc, Mutex};

// 泛型享元接口
pub trait GenericFlyweight<T: Display + Clone> {
    fn operation(&self, extrinsic_state: T) -> String;
}

// 泛型具体享元
pub struct GenericConcreteFlyweight<T: Display + Clone> {
    intrinsic_state: T,
}

impl<T: Display + Clone> GenericConcreteFlyweight<T> {
    pub fn new(intrinsic_state: T) -> Self {
        Self { intrinsic_state }
    }
}

impl<T: Display + Clone> GenericFlyweight<T> for GenericConcreteFlyweight<T> {
    fn operation(&self, extrinsic_state: T) -> String {
        format!("GenericFlyweight[{}] with extrinsic state: {}", 
                self.intrinsic_state, extrinsic_state)
    }
}

// 泛型享元工厂
pub struct GenericFlyweightFactory<T: Display + Clone + Eq + std::hash::Hash> {
    flyweights: Arc<Mutex<HashMap<T, Arc<GenericConcreteFlyweight<T>>>>>,
}

impl<T: Display + Clone + Eq + std::hash::Hash> GenericFlyweightFactory<T> {
    pub fn new() -> Self {
        Self {
            flyweights: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_flyweight(&self, intrinsic_state: T) -> Arc<GenericConcreteFlyweight<T>> {
        let mut flyweights = self.flyweights.lock().unwrap();
        
        if let Some(flyweight) = flyweights.get(&intrinsic_state) {
            flyweight.clone()
        } else {
            let flyweight = Arc::new(GenericConcreteFlyweight::new(intrinsic_state.clone()));
            flyweights.insert(intrinsic_state, flyweight.clone());
            flyweight
        }
    }
    
    pub fn get_flyweight_count(&self) -> usize {
        self.flyweights.lock().unwrap().len()
    }
}

// 泛型上下文
pub struct GenericContext<T: Display + Clone> {
    flyweight: Arc<dyn GenericFlyweight<T>>,
    extrinsic_state: T,
}

impl<T: Display + Clone> GenericContext<T> {
    pub fn new(flyweight: Arc<dyn GenericFlyweight<T>>, extrinsic_state: T) -> Self {
        Self {
            flyweight,
            extrinsic_state,
        }
    }
    
    pub fn operation(&self) -> String {
        self.flyweight.operation(self.extrinsic_state.clone())
    }
}
```

### 4.3 异步实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use tokio::sync::Mutex;

// 异步享元接口
#[async_trait::async_trait]
pub trait AsyncFlyweight<T: Send + Sync + Clone> {
    async fn operation(&self, extrinsic_state: T) -> String;
}

// 异步具体享元
pub struct AsyncConcreteFlyweight<T: Send + Sync + Clone> {
    intrinsic_state: T,
}

impl<T: Send + Sync + Clone> AsyncConcreteFlyweight<T> {
    pub fn new(intrinsic_state: T) -> Self {
        Self { intrinsic_state }
    }
}

#[async_trait::async_trait]
impl<T: Send + Sync + Clone> AsyncFlyweight<T> for AsyncConcreteFlyweight<T> {
    async fn operation(&self, extrinsic_state: T) -> String {
        // 模拟异步操作
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        
        format!("AsyncFlyweight[{}] with extrinsic state: {}", 
                self.intrinsic_state, extrinsic_state)
    }
}

// 异步享元工厂
pub struct AsyncFlyweightFactory<T: Send + Sync + Clone + Eq + std::hash::Hash> {
    flyweights: Arc<RwLock<HashMap<T, Arc<AsyncConcreteFlyweight<T>>>>>,
}

impl<T: Send + Sync + Clone + Eq + std::hash::Hash> AsyncFlyweightFactory<T> {
    pub fn new() -> Self {
        Self {
            flyweights: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn get_flyweight(&self, intrinsic_state: T) -> Arc<AsyncConcreteFlyweight<T>> {
        // 先尝试读取
        {
            let flyweights = self.flyweights.read().await;
            if let Some(flyweight) = flyweights.get(&intrinsic_state) {
                return flyweight.clone();
            }
        }
        
        // 如果不存在，创建新的
        let mut flyweights = self.flyweights.write().await;
        
        // 双重检查
        if let Some(flyweight) = flyweights.get(&intrinsic_state) {
            flyweight.clone()
        } else {
            let flyweight = Arc::new(AsyncConcreteFlyweight::new(intrinsic_state.clone()));
            flyweights.insert(intrinsic_state, flyweight.clone());
            flyweight
        }
    }
    
    pub async fn get_flyweight_count(&self) -> usize {
        self.flyweights.read().await.len()
    }
}

// 异步上下文
pub struct AsyncContext<T: Send + Sync + Clone> {
    flyweight: Arc<dyn AsyncFlyweight<T> + Send + Sync>,
    extrinsic_state: T,
}

impl<T: Send + Sync + Clone> AsyncContext<T> {
    pub fn new(flyweight: Arc<dyn AsyncFlyweight<T> + Send + Sync>, extrinsic_state: T) -> Self {
        Self {
            flyweight,
            extrinsic_state,
        }
    }
    
    pub async fn operation(&self) -> String {
        self.flyweight.operation(self.extrinsic_state.clone()).await
    }
}
```

## 5. 应用场景 (Application Scenarios)

### 5.1 字符渲染系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 字符享元
pub struct Character {
    char: char,
    font: String,
    size: u32,
}

impl Character {
    pub fn new(char: char, font: String, size: u32) -> Self {
        Self { char, font, size }
    }
    
    pub fn render(&self, position: (i32, i32), color: String) -> String {
        format!("Rendering '{}' at ({}, {}) with font {} size {} color {}", 
                self.char, position.0, position.1, self.font, self.size, color)
    }
}

// 字符工厂
pub struct CharacterFactory {
    characters: Arc<Mutex<HashMap<String, Arc<Character>>>>,
}

impl CharacterFactory {
    pub fn new() -> Self {
        Self {
            characters: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_character(&self, char: char, font: String, size: u32) -> Arc<Character> {
        let key = format!("{}_{}_{}", char, font, size);
        let mut characters = self.characters.lock().unwrap();
        
        if let Some(character) = characters.get(&key) {
            character.clone()
        } else {
            let character = Arc::new(Character::new(char, font.clone(), size));
            characters.insert(key, character.clone());
            character
        }
    }
}

// 文本渲染器
pub struct TextRenderer {
    factory: CharacterFactory,
}

impl TextRenderer {
    pub fn new() -> Self {
        Self {
            factory: CharacterFactory::new(),
        }
    }
    
    pub fn render_text(&self, text: &str, font: String, size: u32, color: String) -> Vec<String> {
        let mut results = Vec::new();
        let mut x = 0;
        
        for char in text.chars() {
            let character = self.factory.get_character(char, font.clone(), size);
            let position = (x, 0);
            results.push(character.render(position, color.clone()));
            x += size as i32;
        }
        
        results
    }
}
```

### 5.2 图形对象系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 图形享元
pub struct Shape {
    shape_type: String,
    color: String,
}

impl Shape {
    pub fn new(shape_type: String, color: String) -> Self {
        Self { shape_type, color }
    }
    
    pub fn draw(&self, position: (i32, i32), size: (i32, i32)) -> String {
        format!("Drawing {} at ({}, {}) with size ({}, {}) and color {}", 
                self.shape_type, position.0, position.1, size.0, size.1, self.color)
    }
}

// 图形工厂
pub struct ShapeFactory {
    shapes: Arc<Mutex<HashMap<String, Arc<Shape>>>>,
}

impl ShapeFactory {
    pub fn new() -> Self {
        Self {
            shapes: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_shape(&self, shape_type: String, color: String) -> Arc<Shape> {
        let key = format!("{}_{}", shape_type, color);
        let mut shapes = self.shapes.lock().unwrap();
        
        if let Some(shape) = shapes.get(&key) {
            shape.clone()
        } else {
            let shape = Arc::new(Shape::new(shape_type.clone(), color.clone()));
            shapes.insert(key, shape.clone());
            shape
        }
    }
}

// 图形管理器
pub struct GraphicsManager {
    factory: ShapeFactory,
    shapes: Vec<(Arc<Shape>, (i32, i32), (i32, i32))>,
}

impl GraphicsManager {
    pub fn new() -> Self {
        Self {
            factory: ShapeFactory::new(),
            shapes: Vec::new(),
        }
    }
    
    pub fn add_shape(&mut self, shape_type: String, color: String, position: (i32, i32), size: (i32, i32)) {
        let shape = self.factory.get_shape(shape_type, color);
        self.shapes.push((shape, position, size));
    }
    
    pub fn render_all(&self) -> Vec<String> {
        self.shapes.iter()
            .map(|(shape, position, size)| shape.draw(*position, *size))
            .collect()
    }
}
```

### 5.3 网络连接池

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 连接享元
pub struct Connection {
    host: String,
    port: u16,
    protocol: String,
}

impl Connection {
    pub fn new(host: String, port: u16, protocol: String) -> Self {
        Self { host, port, protocol }
    }
    
    pub fn send_data(&self, data: &str) -> String {
        format!("Sending '{}' to {}:{} via {}", data, self.host, self.port, self.protocol)
    }
    
    pub fn receive_data(&self) -> String {
        format!("Receiving data from {}:{} via {}", self.host, self.port, self.protocol)
    }
}

// 连接池
pub struct ConnectionPool {
    connections: Arc<Mutex<HashMap<String, Arc<Connection>>>>,
    last_used: Arc<Mutex<HashMap<String, Instant>>>,
}

impl ConnectionPool {
    pub fn new() -> Self {
        Self {
            connections: Arc::new(Mutex::new(HashMap::new())),
            last_used: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn get_connection(&self, host: String, port: u16, protocol: String) -> Arc<Connection> {
        let key = format!("{}:{}:{}", host, port, protocol);
        let mut connections = self.connections.lock().unwrap();
        let mut last_used = self.last_used.lock().unwrap();
        
        if let Some(connection) = connections.get(&key) {
            last_used.insert(key, Instant::now());
            connection.clone()
        } else {
            let connection = Arc::new(Connection::new(host.clone(), port, protocol.clone()));
            connections.insert(key.clone(), connection.clone());
            last_used.insert(key, Instant::now());
            connection
        }
    }
    
    pub fn cleanup_expired(&self, max_age: Duration) {
        let mut connections = self.connections.lock().unwrap();
        let mut last_used = self.last_used.lock().unwrap();
        
        let now = Instant::now();
        let expired_keys: Vec<String> = last_used.iter()
            .filter(|(_, &ref time)| now.duration_since(*time) > max_age)
            .map(|(key, _)| key.clone())
            .collect();
        
        for key in expired_keys {
            connections.remove(&key);
            last_used.remove(&key);
        }
    }
    
    pub fn get_connection_count(&self) -> usize {
        self.connections.lock().unwrap().len()
    }
}
```

## 6. 变体模式 (Variant Patterns)

### 6.1 复合享元

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 复合享元
pub struct CompositeFlyweight {
    flyweights: Vec<Arc<dyn Flyweight>>,
}

impl CompositeFlyweight {
    pub fn new() -> Self {
        Self {
            flyweights: Vec::new(),
        }
    }
    
    pub fn add_flyweight(&mut self, flyweight: Arc<dyn Flyweight>) {
        self.flyweights.push(flyweight);
    }
}

impl Flyweight for CompositeFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        let results: Vec<String> = self.flyweights.iter()
            .map(|f| f.operation(extrinsic_state))
            .collect();
        format!("Composite: [{}]", results.join(", "))
    }
}
```

### 6.2 享元注册表

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 享元注册表
pub struct FlyweightRegistry {
    registry: Arc<Mutex<HashMap<String, Arc<dyn Flyweight>>>>,
}

impl FlyweightRegistry {
    pub fn new() -> Self {
        Self {
            registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn register(&self, key: String, flyweight: Arc<dyn Flyweight>) {
        let mut registry = self.registry.lock().unwrap();
        registry.insert(key, flyweight);
    }
    
    pub fn get(&self, key: &str) -> Option<Arc<dyn Flyweight>> {
        let registry = self.registry.lock().unwrap();
        registry.get(key).cloned()
    }
    
    pub fn unregister(&self, key: &str) {
        let mut registry = self.registry.lock().unwrap();
        registry.remove(key);
    }
}
```

### 6.3 享元缓存

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 享元缓存
pub struct FlyweightCache {
    cache: Arc<Mutex<HashMap<String, (Arc<dyn Flyweight>, Instant)>>>,
    max_age: Duration,
}

impl FlyweightCache {
    pub fn new(max_age: Duration) -> Self {
        Self {
            cache: Arc::new(Mutex::new(HashMap::new())),
            max_age,
        }
    }
    
    pub fn get_or_create<F>(&self, key: String, factory: F) -> Arc<dyn Flyweight>
    where
        F: FnOnce() -> Arc<dyn Flyweight>
    {
        let mut cache = self.cache.lock().unwrap();
        let now = Instant::now();
        
        // 清理过期项
        cache.retain(|_, (_, time)| now.duration_since(*time) <= self.max_age);
        
        if let Some((flyweight, _)) = cache.get(&key) {
            flyweight.clone()
        } else {
            let flyweight = factory();
            cache.insert(key, (flyweight.clone(), now));
            flyweight
        }
    }
    
    pub fn clear(&self) {
        let mut cache = self.cache.lock().unwrap();
        cache.clear();
    }
}
```

## 7. 质量属性分析 (Quality Attributes Analysis)

### 7.1 内存效率

**定义7.1.1 (享元模式内存效率)**
享元模式的内存效率定义为：
$$\text{MemoryEfficiency}(F) = \frac{|I|}{|S|} \cdot \frac{1}{|E|}$$

**定理7.1.1 (内存效率上界)**
对于享元模式 $F$，内存效率满足：
$$\text{MemoryEfficiency}(F) \leq \frac{|I|}{|I| + |E| \cdot |C|}$$

### 7.2 性能

**定义7.2.1 (享元模式性能)**
享元模式的性能定义为：
$$\text{Performance}(F) = \frac{1}{\text{Complexity}(F)}$$

**定理7.2.1 (性能下界)**
对于享元模式 $F$，性能满足：
$$\text{Performance}(F) \geq \frac{1}{|I| \cdot \log(|I|)}$$

### 7.3 可扩展性

**定义7.3.1 (享元模式可扩展性)**
享元模式的可扩展性定义为：
$$\text{Extensibility}(F) = \frac{|S|}{|I|} \cdot \frac{1}{|P|}$$

**定理7.3.1 (可扩展性下界)**
对于享元模式 $F$，可扩展性满足：
$$\text{Extensibility}(F) \geq \frac{|S|}{|I|} \cdot \frac{1}{|P|}$$

## 8. 总结 (Summary)

享元模式通过分离内部状态和外部状态，实现了对象的共享和内存优化。其形式化模型建立了完整的数学理论基础，包括状态分离理论、对象共享理论和池化管理理论。Rust实现提供了基础、泛型和异步三种实现方式，支持字符渲染、图形对象、网络连接池等多种应用场景。

享元模式的核心优势在于：

1. **内存优化**: 通过共享内部状态减少内存使用
2. **性能提升**: 减少对象创建和销毁的开销
3. **状态分离**: 清晰分离内部状态和外部状态
4. **池化管理**: 高效管理共享对象的生命周期

通过形式化重构，享元模式的理论基础更加坚实，实现更加规范，为内存优化和性能提升提供了强有力的支持。
