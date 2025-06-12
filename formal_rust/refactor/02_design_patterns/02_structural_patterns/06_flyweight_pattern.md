# 享元模式 (Flyweight Pattern) - 形式化重构

## 目录 (Table of Contents)

1. [模式概述](#1-模式概述)
2. [形式化定义](#2-形式化定义)
3. [数学理论](#3-数学理论)
4. [核心定理](#4-核心定理)
5. [Rust实现](#5-rust实现)
6. [应用场景](#6-应用场景)
7. [变体模式](#7-变体模式)
8. [性能分析](#8-性能分析)
9. [总结](#9-总结)

## 1. 模式概述

### 1.1 基本概念

享元模式是一种结构型设计模式，通过共享来高效地支持大量细粒度的对象，减少内存占用。

**核心思想**：

- 将对象的状态分为内部状态（共享）和外部状态（唯一）
- 通过共享内部状态来减少内存使用
- 使用工厂管理享元对象的创建和复用

### 1.2 模式结构

```text
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────────┐
│   Client        │    │  Flyweight       │    │  FlyweightFactory   │
│                 │    │                  │    │                     │
│ - extrinsicState│◄──►│ + operation()    │◄──►│ + getFlyweight()    │
│                 │    │                  │    │                     │
└─────────────────┘    └──────────────────┘    └─────────────────────┘
                                ▲
                                │
                       ┌──────────────────┐
                       │ ConcreteFlyweight│
                       │                  │
                       │ + intrinsicState │
                       │ + operation()    │
                       └──────────────────┘
```

## 2. 形式化定义

### 2.1 享元模式五元组

**定义2.1 (享元模式五元组)**
设 $F = (N, I, S, R, C)$ 为享元模式，其中：

- $N = \{\text{Flyweight}, \text{ConcreteFlyweight}, \text{FlyweightFactory}, \text{Client}\}$
- $I = \{\text{共享对象状态}, \text{减少内存使用}, \text{支持大量对象}\}$
- $S = \{S_{intrinsic}, S_{extrinsic}, S_{shared}, S_{unique}\}$
- $R = \{R_{factory}, R_{client}, R_{state}\}$
- $C = \{C_{sharing}, C_{memory}, C_{performance}\}$

其中：

- $S_{intrinsic}$ 是内部状态集合（共享）
- $S_{extrinsic}$ 是外部状态集合（唯一）
- $S_{shared}$ 是共享对象集合
- $S_{unique}$ 是唯一对象集合
- $R_{factory}$ 是工厂关系
- $R_{client}$ 是客户端关系
- $R_{state}$ 是状态关系
- $C_{sharing}$ 是共享约束
- $C_{memory}$ 是内存约束
- $C_{performance}$ 是性能约束

### 2.2 状态分离理论

**定义2.2 (状态分离)**
对于享元对象 $f$，其状态可以分解为：

$$f.state = f.intrinsic \oplus f.extrinsic$$

其中：

- $f.intrinsic \in S_{intrinsic}$ 是内部状态（共享）
- $f.extrinsic \in S_{extrinsic}$ 是外部状态（唯一）
- $\oplus$ 表示状态组合操作

## 3. 数学理论

### 3.1 共享理论

**定义3.1 (共享关系)**
设 $F$ 为享元工厂，$S_{shared}$ 为共享对象集合，则共享关系定义为：

$$R_{share} = \{(f_1, f_2) \in S_{shared} \times S_{shared} | f_1.intrinsic = f_2.intrinsic\}$$

**性质3.1 (共享等价性)**
共享关系 $R_{share}$ 是一个等价关系，满足：

1. 自反性：$(f, f) \in R_{share}$
2. 对称性：$(f_1, f_2) \in R_{share} \Rightarrow (f_2, f_1) \in R_{share}$
3. 传递性：$(f_1, f_2) \in R_{share} \land (f_2, f_3) \in R_{share} \Rightarrow (f_1, f_3) \in R_{share}$

### 3.2 内存优化理论

**定义3.2 (内存节省函数)**
设 $n$ 为对象总数，$m$ 为唯一内部状态数，则内存节省函数为：

$$\text{MemorySavings}(n, m) = n \cdot |S_{intrinsic}| - m \cdot |S_{intrinsic}| = (n - m) \cdot |S_{intrinsic}|$$

**定理3.1 (内存优化上界)**
对于享元模式，内存使用上界为：

$$\text{MemoryUsage}(n, m) \leq m \cdot |S_{intrinsic}| + n \cdot |S_{extrinsic}|$$

### 3.3 性能理论

**定义3.3 (查找复杂度)**
享元工厂的查找复杂度为：

$$\text{LookupComplexity}(n) = O(\log n)$$

其中 $n$ 是唯一内部状态的数量。

## 4. 核心定理

### 4.1 共享正确性定理

**定理4.1 (共享正确性)**
如果享元工厂正确实现，则对于任意两个享元对象 $f_1, f_2$：

$$f_1.intrinsic = f_2.intrinsic \Rightarrow f_1 \equiv_{intrinsic} f_2$$

**证明**：

1. 根据共享关系定义，$f_1.intrinsic = f_2.intrinsic$ 意味着它们共享相同的内部状态
2. 由于内部状态是共享的，$f_1$ 和 $f_2$ 在内部状态上是等价的
3. 因此 $f_1 \equiv_{intrinsic} f_2$ 成立

### 4.2 内存优化定理

**定理4.2 (内存优化保证)**
对于使用享元模式的系统，内存使用满足：

$$\text{MemoryUsage}_{flyweight} \leq \text{MemoryUsage}_{naive} - \text{MemorySavings}(n, m)$$

**证明**：

1. 朴素实现的内存使用：$\text{MemoryUsage}_{naive} = n \cdot (|S_{intrinsic}| + |S_{extrinsic}|)$
2. 享元模式的内存使用：$\text{MemoryUsage}_{flyweight} = m \cdot |S_{intrinsic}| + n \cdot |S_{extrinsic}|$
3. 内存节省：$\text{MemorySavings}(n, m) = (n - m) \cdot |S_{intrinsic}|$
4. 因此：$\text{MemoryUsage}_{flyweight} = \text{MemoryUsage}_{naive} - \text{MemorySavings}(n, m)$

### 4.3 性能保证定理

**定理4.3 (性能保证)**
享元模式的性能满足：

$$\text{Performance}_{flyweight} = O(\log m) + O(|S_{extrinsic}|)$$

其中 $m$ 是唯一内部状态的数量。

**证明**：

1. 查找享元对象：$O(\log m)$（使用哈希表或树结构）
2. 设置外部状态：$O(|S_{extrinsic}|)$
3. 总性能：$O(\log m) + O(|S_{extrinsic}|)$

### 4.4 状态一致性定理

**定理4.4 (状态一致性)**
对于享元对象 $f$，其状态一致性满足：

$$f.state = f.intrinsic \oplus f.extrinsic \land f.intrinsic \in S_{shared} \land f.extrinsic \in S_{unique}$$

**证明**：

1. 根据状态分离定义，$f.state = f.intrinsic \oplus f.extrinsic$
2. 内部状态来自共享集合：$f.intrinsic \in S_{shared}$
3. 外部状态是唯一的：$f.extrinsic \in S_{unique}$
4. 因此状态一致性成立

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 享元接口
trait Flyweight {
    fn operation(&self, extrinsic_state: &str);
}

// 具体享元
struct ConcreteFlyweight {
    intrinsic_state: String,
}

impl ConcreteFlyweight {
    fn new(intrinsic_state: String) -> Self {
        ConcreteFlyweight { intrinsic_state }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) {
        println!(
            "ConcreteFlyweight: {} - {}",
            self.intrinsic_state, extrinsic_state
        );
    }
}

// 享元工厂
struct FlyweightFactory {
    flyweights: HashMap<String, Arc<ConcreteFlyweight>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        FlyweightFactory {
            flyweights: HashMap::new(),
        }
    }

    fn get_flyweight(&mut self, key: &str) -> Arc<ConcreteFlyweight> {
        if let Some(flyweight) = self.flyweights.get(key) {
            Arc::clone(flyweight)
        } else {
            let flyweight = Arc::new(ConcreteFlyweight::new(key.to_string()));
            self.flyweights.insert(key.to_string(), Arc::clone(&flyweight));
            flyweight
        }
    }

    fn get_flyweight_count(&self) -> usize {
        self.flyweights.len()
    }
}

// 客户端
struct Client {
    factory: FlyweightFactory,
}

impl Client {
    fn new() -> Self {
        Client {
            factory: FlyweightFactory::new(),
        }
    }

    fn use_flyweight(&mut self, intrinsic_state: &str, extrinsic_state: &str) {
        let flyweight = self.factory.get_flyweight(intrinsic_state);
        flyweight.operation(extrinsic_state);
    }
}

fn main() {
    let mut client = Client::new();
    
    // 使用相同的内部状态，不同的外部状态
    client.use_flyweight("SharedState1", "UniqueState1");
    client.use_flyweight("SharedState1", "UniqueState2");
    client.use_flyweight("SharedState2", "UniqueState3");
    
    println!("Unique flyweights created: {}", client.factory.get_flyweight_count());
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

// 泛型享元接口
trait GenericFlyweight<K, V> {
    fn operation(&self, extrinsic_state: V);
    fn get_intrinsic_state(&self) -> &K;
}

// 泛型具体享元
struct GenericConcreteFlyweight<K, V> {
    intrinsic_state: K,
    _phantom: std::marker::PhantomData<V>,
}

impl<K, V> GenericConcreteFlyweight<K, V> {
    fn new(intrinsic_state: K) -> Self {
        GenericConcreteFlyweight {
            intrinsic_state,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<K, V> GenericFlyweight<K, V> for GenericConcreteFlyweight<K, V>
where
    K: Clone + std::fmt::Display,
    V: std::fmt::Display,
{
    fn operation(&self, extrinsic_state: V) {
        println!(
            "GenericFlyweight: {} - {}",
            self.intrinsic_state, extrinsic_state
        );
    }

    fn get_intrinsic_state(&self) -> &K {
        &self.intrinsic_state
    }
}

// 泛型享元工厂
struct GenericFlyweightFactory<K, V> {
    flyweights: HashMap<K, Arc<dyn GenericFlyweight<K, V>>>,
}

impl<K, V> GenericFlyweightFactory<K, V>
where
    K: Clone + Hash + Eq + std::fmt::Display,
    V: std::fmt::Display,
{
    fn new() -> Self {
        GenericFlyweightFactory {
            flyweights: HashMap::new(),
        }
    }

    fn get_flyweight(&mut self, key: K) -> Arc<dyn GenericFlyweight<K, V>> {
        if let Some(flyweight) = self.flyweights.get(&key) {
            Arc::clone(flyweight)
        } else {
            let flyweight = Arc::new(GenericConcreteFlyweight::new(key.clone()));
            self.flyweights.insert(key, Arc::clone(&flyweight));
            flyweight
        }
    }

    fn get_flyweight_count(&self) -> usize {
        self.flyweights.len()
    }
}
```

### 5.3 线程安全实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 线程安全享元工厂
struct ThreadSafeFlyweightFactory {
    flyweights: Arc<RwLock<HashMap<String, Arc<ConcreteFlyweight>>>>,
}

impl ThreadSafeFlyweightFactory {
    fn new() -> Self {
        ThreadSafeFlyweightFactory {
            flyweights: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    fn get_flyweight(&self, key: &str) -> Arc<ConcreteFlyweight> {
        // 先尝试读取
        {
            let flyweights = self.flyweights.read().unwrap();
            if let Some(flyweight) = flyweights.get(key) {
                return Arc::clone(flyweight);
            }
        }

        // 如果不存在，则写入
        {
            let mut flyweights = self.flyweights.write().unwrap();
            if let Some(flyweight) = flyweights.get(key) {
                Arc::clone(flyweight)
            } else {
                let flyweight = Arc::new(ConcreteFlyweight::new(key.to_string()));
                flyweights.insert(key.to_string(), Arc::clone(&flyweight));
                flyweight
            }
        }
    }

    fn get_flyweight_count(&self) -> usize {
        self.flyweights.read().unwrap().len()
    }
}
```

### 5.4 缓存享元实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 缓存享元
struct CachedFlyweight {
    flyweight: Arc<ConcreteFlyweight>,
    last_accessed: Instant,
    access_count: u64,
}

impl CachedFlyweight {
    fn new(flyweight: Arc<ConcreteFlyweight>) -> Self {
        CachedFlyweight {
            flyweight,
            last_accessed: Instant::now(),
            access_count: 1,
        }
    }

    fn access(&mut self) {
        self.last_accessed = Instant::now();
        self.access_count += 1;
    }

    fn is_expired(&self, ttl: Duration) -> bool {
        self.last_accessed.elapsed() > ttl
    }
}

// 缓存享元工厂
struct CachedFlyweightFactory {
    cache: Arc<Mutex<HashMap<String, CachedFlyweight>>>,
    ttl: Duration,
}

impl CachedFlyweightFactory {
    fn new(ttl: Duration) -> Self {
        CachedFlyweightFactory {
            cache: Arc::new(Mutex::new(HashMap::new())),
            ttl,
        }
    }

    fn get_flyweight(&self, key: &str) -> Arc<ConcreteFlyweight> {
        let mut cache = self.cache.lock().unwrap();
        
        // 清理过期项
        cache.retain(|_, cached| !cached.is_expired(self.ttl));
        
        if let Some(cached) = cache.get_mut(key) {
            cached.access();
            Arc::clone(&cached.flyweight)
        } else {
            let flyweight = Arc::new(ConcreteFlyweight::new(key.to_string()));
            cache.insert(
                key.to_string(),
                CachedFlyweight::new(Arc::clone(&flyweight)),
            );
            flyweight
        }
    }

    fn get_cache_stats(&self) -> (usize, u64) {
        let cache = self.cache.lock().unwrap();
        let total_accesses = cache.values().map(|c| c.access_count).sum();
        (cache.len(), total_accesses)
    }
}
```

### 5.5 异步享元实现

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

// 异步享元接口
#[async_trait::async_trait]
trait AsyncFlyweight {
    async fn operation(&self, extrinsic_state: String);
}

// 异步具体享元
struct AsyncConcreteFlyweight {
    intrinsic_state: String,
}

impl AsyncConcreteFlyweight {
    fn new(intrinsic_state: String) -> Self {
        AsyncConcreteFlyweight { intrinsic_state }
    }
}

#[async_trait::async_trait]
impl AsyncFlyweight for AsyncConcreteFlyweight {
    async fn operation(&self, extrinsic_state: String) {
        // 模拟异步操作
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        println!(
            "AsyncFlyweight: {} - {}",
            self.intrinsic_state, extrinsic_state
        );
    }
}

// 异步享元工厂
struct AsyncFlyweightFactory {
    flyweights: Arc<RwLock<HashMap<String, Arc<AsyncConcreteFlyweight>>>>,
}

impl AsyncFlyweightFactory {
    fn new() -> Self {
        AsyncFlyweightFactory {
            flyweights: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    async fn get_flyweight(&self, key: &str) -> Arc<AsyncConcreteFlyweight> {
        // 先尝试读取
        {
            let flyweights = self.flyweights.read().await;
            if let Some(flyweight) = flyweights.get(key) {
                return Arc::clone(flyweight);
            }
        }

        // 如果不存在，则写入
        {
            let mut flyweights = self.flyweights.write().await;
            if let Some(flyweight) = flyweights.get(key) {
                Arc::clone(flyweight)
            } else {
                let flyweight = Arc::new(AsyncConcreteFlyweight::new(key.to_string()));
                flyweights.insert(key.to_string(), Arc::clone(&flyweight));
                flyweight
            }
        }
    }

    async fn get_flyweight_count(&self) -> usize {
        self.flyweights.read().await.len()
    }
}

// 异步客户端
struct AsyncClient {
    factory: AsyncFlyweightFactory,
}

impl AsyncClient {
    fn new() -> Self {
        AsyncClient {
            factory: AsyncFlyweightFactory::new(),
        }
    }

    async fn use_flyweight(&self, intrinsic_state: &str, extrinsic_state: &str) {
        let flyweight = self.factory.get_flyweight(intrinsic_state).await;
        flyweight.operation(extrinsic_state.to_string()).await;
    }
}

#[tokio::main]
async fn main() {
    let client = AsyncClient::new();
    
    // 并发使用享元
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let client = &client;
            tokio::spawn(async move {
                client
                    .use_flyweight("SharedState", &format!("UniqueState{}", i))
                    .await;
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("Unique flyweights: {}", client.factory.get_flyweight_count().await);
}
```

## 6. 应用场景

### 6.1 文本编辑器

```rust
// 字符享元
struct Character {
    char: char,
    font: String,
    size: u32,
    color: String,
}

impl Character {
    fn new(char: char, font: String, size: u32, color: String) -> Self {
        Character {
            char,
            font,
            size,
            color,
        }
    }

    fn render(&self, position: (u32, u32)) {
        println!(
            "Rendering '{}' at ({}, {}) with font: {}, size: {}, color: {}",
            self.char, position.0, position.1, self.font, self.size, self.color
        );
    }
}

// 字符工厂
struct CharacterFactory {
    characters: HashMap<String, Arc<Character>>,
}

impl CharacterFactory {
    fn new() -> Self {
        CharacterFactory {
            characters: HashMap::new(),
        }
    }

    fn get_character(&mut self, char: char, font: &str, size: u32, color: &str) -> Arc<Character> {
        let key = format!("{}_{}_{}_{}", char, font, size, color);
        
        if let Some(character) = self.characters.get(&key) {
            Arc::clone(character)
        } else {
            let character = Arc::new(Character::new(
                char,
                font.to_string(),
                size,
                color.to_string(),
            ));
            self.characters.insert(key, Arc::clone(&character));
            character
        }
    }
}

// 文档
struct Document {
    factory: CharacterFactory,
    characters: Vec<(Arc<Character>, (u32, u32))>,
}

impl Document {
    fn new() -> Self {
        Document {
            factory: CharacterFactory::new(),
            characters: Vec::new(),
        }
    }

    fn add_character(&mut self, char: char, font: &str, size: u32, color: &str, position: (u32, u32)) {
        let character = self.factory.get_character(char, font, size, color);
        self.characters.push((character, position));
    }

    fn render(&self) {
        for (character, position) in &self.characters {
            character.render(*position);
        }
    }
}
```

### 6.2 游戏对象系统

```rust
// 游戏对象享元
struct GameObject {
    mesh: String,
    texture: String,
    animation: String,
}

impl GameObject {
    fn new(mesh: String, texture: String, animation: String) -> Self {
        GameObject {
            mesh,
            texture,
            animation,
        }
    }

    fn render(&self, position: (f32, f32, f32), rotation: (f32, f32, f32)) {
        println!(
            "Rendering object at ({:.2}, {:.2}, {:.2}) with rotation ({:.2}, {:.2}, {:.2})",
            position.0, position.1, position.2, rotation.0, rotation.1, rotation.2
        );
        println!("Mesh: {}, Texture: {}, Animation: {}", self.mesh, self.texture, self.animation);
    }
}

// 游戏对象工厂
struct GameObjectFactory {
    objects: HashMap<String, Arc<GameObject>>,
}

impl GameObjectFactory {
    fn new() -> Self {
        GameObjectFactory {
            objects: HashMap::new(),
        }
    }

    fn get_object(&mut self, mesh: &str, texture: &str, animation: &str) -> Arc<GameObject> {
        let key = format!("{}_{}_{}", mesh, texture, animation);
        
        if let Some(object) = self.objects.get(&key) {
            Arc::clone(object)
        } else {
            let object = Arc::new(GameObject::new(
                mesh.to_string(),
                texture.to_string(),
                animation.to_string(),
            ));
            self.objects.insert(key, Arc::clone(&object));
            object
        }
    }
}

// 游戏世界
struct GameWorld {
    factory: GameObjectFactory,
    instances: Vec<(Arc<GameObject>, (f32, f32, f32), (f32, f32, f32))>,
}

impl GameWorld {
    fn new() -> Self {
        GameWorld {
            factory: GameObjectFactory::new(),
            instances: Vec::new(),
        }
    }

    fn spawn_object(&mut self, mesh: &str, texture: &str, animation: &str, 
                   position: (f32, f32, f32), rotation: (f32, f32, f32)) {
        let object = self.factory.get_object(mesh, texture, animation);
        self.instances.push((object, position, rotation));
    }

    fn render(&self) {
        for (object, position, rotation) in &self.instances {
            object.render(*position, *rotation);
        }
    }
}
```

### 6.3 数据库连接池

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

// 数据库连接享元
struct DatabaseConnection {
    connection_string: String,
    max_connections: u32,
}

impl DatabaseConnection {
    fn new(connection_string: String, max_connections: u32) -> Self {
        DatabaseConnection {
            connection_string,
            max_connections,
        }
    }

    fn execute_query(&self, query: &str) {
        println!(
            "Executing query '{}' on connection: {} (max: {})",
            query, self.connection_string, self.max_connections
        );
    }
}

// 连接池工厂
struct ConnectionPoolFactory {
    pools: HashMap<String, Arc<Mutex<Vec<Arc<DatabaseConnection>>>>>,
}

impl ConnectionPoolFactory {
    fn new() -> Self {
        ConnectionPoolFactory {
            pools: HashMap::new(),
        }
    }

    fn get_connection(&self, connection_string: &str, max_connections: u32) -> Arc<DatabaseConnection> {
        let pool_key = format!("{}_{}", connection_string, max_connections);
        
        if let Some(pool) = self.pools.get(&pool_key) {
            let mut pool = pool.lock().unwrap();
            if let Some(connection) = pool.pop() {
                return connection;
            }
        }
        
        Arc::new(DatabaseConnection::new(connection_string.to_string(), max_connections))
    }

    fn return_connection(&self, connection_string: &str, max_connections: u32, 
                        connection: Arc<DatabaseConnection>) {
        let pool_key = format!("{}_{}", connection_string, max_connections);
        
        if let Some(pool) = self.pools.get(&pool_key) {
            let mut pool = pool.lock().unwrap();
            pool.push(connection);
        }
    }
}
```

## 7. 变体模式

### 7.1 复合享元模式

```rust
// 复合享元
struct CompositeFlyweight {
    flyweights: Vec<Arc<dyn Flyweight>>,
}

impl CompositeFlyweight {
    fn new() -> Self {
        CompositeFlyweight {
            flyweights: Vec::new(),
        }
    }

    fn add_flyweight(&mut self, flyweight: Arc<dyn Flyweight>) {
        self.flyweights.push(flyweight);
    }
}

impl Flyweight for CompositeFlyweight {
    fn operation(&self, extrinsic_state: &str) {
        for flyweight in &self.flyweights {
            flyweight.operation(extrinsic_state);
        }
    }
}
```

### 7.2 享元注册表模式

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// 享元注册表
struct FlyweightRegistry {
    registry: Arc<RwLock<HashMap<String, Arc<dyn Flyweight>>>>,
}

impl FlyweightRegistry {
    fn new() -> Self {
        FlyweightRegistry {
            registry: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    fn register(&self, key: &str, flyweight: Arc<dyn Flyweight>) {
        let mut registry = self.registry.write().unwrap();
        registry.insert(key.to_string(), flyweight);
    }

    fn get(&self, key: &str) -> Option<Arc<dyn Flyweight>> {
        let registry = self.registry.read().unwrap();
        registry.get(key).map(Arc::clone)
    }

    fn unregister(&self, key: &str) {
        let mut registry = self.registry.write().unwrap();
        registry.remove(key);
    }
}
```

### 7.3 享元池模式

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

// 享元池
struct FlyweightPool {
    pool: Arc<Mutex<VecDeque<Arc<dyn Flyweight>>>>,
    max_size: usize,
}

impl FlyweightPool {
    fn new(max_size: usize) -> Self {
        FlyweightPool {
            pool: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
        }
    }

    fn acquire(&self) -> Option<Arc<dyn Flyweight>> {
        let mut pool = self.pool.lock().unwrap();
        pool.pop_front()
    }

    fn release(&self, flyweight: Arc<dyn Flyweight>) {
        let mut pool = self.pool.lock().unwrap();
        if pool.len() < self.max_size {
            pool.push_back(flyweight);
        }
    }

    fn size(&self) -> usize {
        self.pool.lock().unwrap().len()
    }
}
```

## 8. 性能分析

### 8.1 内存使用分析

**定理8.1 (内存使用优化)**
对于包含 $n$ 个对象，$m$ 个唯一内部状态的系统：

$$\text{MemorySavings} = (n - m) \cdot |S_{intrinsic}|$$

**证明**：

1. 朴素实现：每个对象都包含完整的内部状态
2. 享元模式：只有 $m$ 个对象包含内部状态，其余共享
3. 节省内存：$(n - m) \cdot |S_{intrinsic}|$

### 8.2 时间复杂度分析

**定理8.2 (时间复杂度)**
享元模式的时间复杂度为：

- 查找享元：$O(\log m)$
- 创建享元：$O(1)$
- 操作享元：$O(|S_{extrinsic}|)$

其中 $m$ 是唯一内部状态的数量。

### 8.3 空间复杂度分析

**定理8.3 (空间复杂度)**
享元模式的空间复杂度为：

$$\text{SpaceComplexity} = O(m \cdot |S_{intrinsic}| + n \cdot |S_{extrinsic}|)$$

其中：

- $m$ 是唯一内部状态的数量
- $n$ 是对象的总数
- $|S_{intrinsic}|$ 是内部状态的大小
- $|S_{extrinsic}|$ 是外部状态的大小

## 9. 总结

### 9.1 模式优势

1. **内存优化**：通过共享内部状态显著减少内存使用
2. **性能提升**：减少对象创建和销毁的开销
3. **可扩展性**：支持大量细粒度对象的创建
4. **灵活性**：支持动态状态管理

### 9.2 模式限制

1. **复杂性增加**：需要管理内部状态和外部状态的分离
2. **线程安全**：在多线程环境下需要额外的同步机制
3. **调试困难**：共享状态可能导致调试困难

### 9.3 最佳实践

1. **状态分离**：明确区分内部状态和外部状态
2. **工厂管理**：使用工厂统一管理享元对象的创建
3. **线程安全**：在多线程环境下使用适当的同步机制
4. **缓存策略**：根据访问模式选择合适的缓存策略

### 9.4 形式化验证

通过形式化定义和数学证明，我们建立了享元模式的完整理论体系：

1. **共享正确性**：确保共享对象的正确性
2. **内存优化**：提供内存使用的数学保证
3. **性能保证**：建立性能的上下界
4. **状态一致性**：保证状态分离的一致性

这个形式化框架为享元模式的设计、实现和验证提供了坚实的理论基础。
