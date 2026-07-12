# 模式选择最佳实践 (Pattern Selection Best Practices)

> **代码状态**: 混合（原 crate 文档示例，部分代码块为示意片段）
>
> **EN**: Pattern Selection Best Practices
> **Summary**: Provides a systematic guide for selecting design patterns in Rust, including decision trees, scenario-driven recommendations, anti-patterns, pattern composition, Rust-specific concerns, and production checklists.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: L4-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P+A** — Procedure + Application
> **双维定位**: A×Eva — 评估模式选型
> **前置依赖**: [Design Patterns](02_patterns.md) · [Pattern Implementation Comparison](36_pattern_implementation_comparison.md)
> **后置概念**: [Engineering and Production Patterns](82_engineering_and_production_patterns.md) · [Architecture Patterns](35_architecture_patterns.md)
> **定理链**: Requirement ⟹ Pattern Selection ⟹ Validation
> **层级**: L6 生态工程
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
> **后置概念**: [Rust vs C++：形式系统模型 vs 机制工程模型](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
>
> **权威状态**: 本页由 `crates/c09_design_pattern/docs/` 整治迁移而来，作为 `concept/` 中的权威页。

---

## 1. 概述

设计模式的选择应基于具体场景、性能需求和团队能力。本文档提供系统化的选择方法和最佳实践。

### 1.1 选择维度

| 维度         | 考量因素           | 权重       |
| :--- | :--- | :--- |
| **性能要求** | 延迟、吞吐量       | ⭐⭐⭐⭐⭐ |
| **灵活性**   | 扩展性、可维护性   | ⭐⭐⭐⭐   |
| **复杂度**   | 实现成本、学习曲线 | ⭐⭐⭐     |
| **类型安全** | 编译时检查         | ⭐⭐⭐⭐⭐ |
| **并发需求** | 多线程、异步（Async）       | ⭐⭐⭐⭐   |

---

## 2. 模式选择决策树

本节从创建型模式决策树、结构型模式决策树与行为型模式决策树切入，剖析「模式选择决策树」的核心内容。

### 2.1 创建型模式决策树

```text
需要创建对象？
│
├─ 只需一个实例？
│  └─ Singleton (OnceLock)
│
├─ 构造过程复杂？
│  ├─ 需要编译时验证？
│  │  └─ Typestate Builder ⭐推荐
│  └─ 运行时灵活性？
│     └─ Builder
│
├─ 创建逻辑可变？
│  ├─ 类型固定？
│  │  └─ 泛型Factory ⭐推荐
│  └─ 运行时决定？
│     └─ Trait Object Factory
│
└─ 需要克隆对象？
   └─ Prototype (Clone)
```

### 2.2 结构型模式决策树

```text
需要组合对象？
│
├─ 接口不兼容？
│  └─ Adapter
│
├─ 需要添加功能？
│  ├─ 编译时？
│  │  └─ 泛型Decorator ⭐推荐
│  └─ 运行时？
│     └─ Trait Object Decorator
│
├─ 需要控制访问？
│  ├─ 缓存？
│  │  └─ Cache Proxy
│  ├─ 延迟加载？
│  │  └─ Lazy Proxy
│  └─ 权限检查？
│     └─ Protection Proxy
│
└─ 简化复杂接口？
   └─ Facade
```

### 2.3 行为型模式决策树

```text
需要对象交互？
│
├─ 一对多通知？
│  ├─ 同步？
│  │  └─ Sync Observer
│  └─ 异步？
│     └─ Async Observer ⭐推荐
│
├─ 算法可切换？
│  ├─ 编译时？
│  │  └─ 泛型Strategy ⭐推荐
│  └─ 运行时？
│     └─ Trait Object Strategy
│
├─ 请求需要排队/撤销？
│  └─ Command
│
├─ 状态转换？
│  ├─ 编译时验证？
│  │  └─ Typestate ⭐推荐
│  └─ 运行时灵活性？
│     └─ State
│
└─ 遍历集合？
   └─ Iterator (零成本)
```

---

## 3. 场景驱动的模式选择

本节将「场景驱动的模式选择」分解为若干主题： Web服务器场景、插件系统场景与游戏引擎场景。

### 3.1 Web服务器场景

```rust
/// 场景：构建高性能Web服务器
///
/// 需求：
/// - 支持多种路由策略
/// - 中间件支持
/// - 连接池管理
/// - 请求日志

// 1. Singleton: 全局配置
use std::sync::OnceLock;

pub struct ServerConfig {
    pub port: u16,
    pub max_connections: usize,
}

static CONFIG: OnceLock<ServerConfig> = OnceLock::new();

impl ServerConfig {
    pub fn get() -> &'static ServerConfig {
        CONFIG.get().expect("Config not initialized")
    }
}

// 2. Builder: 请求构建
pub struct RequestBuilder {
    path: Option<String>,
    method: Option<String>,
    headers: Vec<(String, String)>,
}

impl RequestBuilder {
    pub fn new() -> Self {
        Self {
            path: None,
            method: None,
            headers: Vec::new(),
        }
    }

    pub fn path(mut self, path: impl Into<String>) -> Self {
        self.path = Some(path.into());
        self
    }

    pub fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    pub fn build(self) -> Result<Request, BuildError> {
        Ok(Request {
            path: self.path.ok_or(BuildError::MissingPath)?,
            method: self.method.unwrap_or_else(|| "GET".to_string()),
            headers: self.headers,
        })
    }
}

// 3. Strategy: 路由策略
pub trait Router: Send + Sync {
    fn route(&self, path: &str) -> Option<Box<dyn Handler>>;
}

pub struct PrefixRouter {
    routes: std::collections::HashMap<String, Box<dyn Handler>>,
}

impl Router for PrefixRouter {
    fn route(&self, path: &str) -> Option<Box<dyn Handler>> {
        self.routes.get(path).map(|h| h.clone_box())
    }
}

// 4. Decorator: 中间件
pub trait Middleware {
    fn handle(&self, request: Request, next: &dyn Handler) -> Response;
}

pub struct LoggingMiddleware;

impl Middleware for LoggingMiddleware {
    fn handle(&self, request: Request, next: &dyn Handler) -> Response {
        println!("[Middleware] {} {}", request.method, request.path);
        let response = next.handle(request);
        println!("[Middleware] Response: {}", response.status);
        response
    }
}

// 5. Object Pool: 连接池
pub struct ConnectionPool {
    connections: tokio::sync::Mutex<Vec<Connection>>,
    max_size: usize,
}

impl ConnectionPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            connections: tokio::sync::Mutex::new(Vec::new()),
            max_size,
        }
    }

    pub async fn acquire(&self) -> Connection {
        let mut conns = self.connections.lock().await;
        conns.pop().unwrap_or_else(|| Connection::new())
    }

    pub async fn release(&self, conn: Connection) {
        let mut conns = self.connections.lock().await;
        if conns.len() < self.max_size {
            conns.push(conn);
        }
    }
}
```

**模式选择总结**:

- ✅ Singleton: 全局配置（线程安全）
- ✅ Builder: 复杂请求构建
- ✅ Strategy: 可插拔路由
- ✅ Decorator: 中间件链
- ✅ Object Pool: 资源复用

### 3.2 插件系统场景

```rust
/// 场景：构建插件系统
///
/// 需求：
/// - 动态加载插件
/// - 插件生命周期管理
/// - 插件间通信

// 1. Abstract Factory: 插件工厂
pub trait PluginFactory: Send + Sync {
    fn create_plugin(&self) -> Box<dyn Plugin>;
    fn plugin_name(&self) -> &str;
}

// 2. Facade: 插件管理器
pub struct PluginManager {
    factories: std::collections::HashMap<String, Box<dyn PluginFactory>>,
    plugins: Vec<Box<dyn Plugin>>,
}

impl PluginManager {
    pub fn new() -> Self {
        Self {
            factories: std::collections::HashMap::new(),
            plugins: Vec::new(),
        }
    }

    pub fn register_factory(&mut self, factory: Box<dyn PluginFactory>) {
        self.factories.insert(factory.plugin_name().to_string(), factory);
    }

    pub fn load_plugin(&mut self, name: &str) -> Result<(), String> {
        let factory = self.factories.get(name)
            .ok_or_else(|| format!("Plugin not found: {}", name))?;

        let plugin = factory.create_plugin();
        plugin.init()?;
        self.plugins.push(plugin);
        Ok(())
    }

    pub fn broadcast(&self, event: &str) {
        for plugin in &self.plugins {
            plugin.on_event(event);
        }
    }
}

// 3. Observer: 插件间通信
pub trait Plugin: Send + Sync {
    fn init(&self) -> Result<(), String>;
    fn on_event(&self, event: &str);
    fn shutdown(&self);
}

pub struct EventBusPlugin;

impl Plugin for EventBusPlugin {
    fn init(&self) -> Result<(), String> {
        println!("[EventBus] Plugin initialized");
        Ok(())
    }

    fn on_event(&self, event: &str) {
        println!("[EventBus] Received event: {}", event);
    }

    fn shutdown(&self) {
        println!("[EventBus] Plugin shutdown");
    }
}
```

**模式选择总结**:

- ✅ Abstract Factory: 创建不同类型插件
- ✅ Facade: 简化插件管理
- ✅ Observer: 事件通知机制
- ✅ Command: 插件命令执行

### 3.3 游戏引擎场景

```rust
/// 场景：游戏引擎架构
///
/// 需求：
/// - 实体组件系统 (ECS)
/// - 状态机 (AI, Animation)
/// - 资源管理

// 1. Flyweight: 共享资源
pub struct TextureCache {
    cache: std::collections::HashMap<String, std::sync::Arc<Texture>>,
}

impl TextureCache {
    pub fn get_or_load(&mut self, path: &str) -> std::sync::Arc<Texture> {
        self.cache.entry(path.to_string())
            .or_insert_with(|| std::sync::Arc::new(Texture::load(path)))
            .clone()
    }
}

// 2. State: AI状态机
pub trait AIState {
    fn update(&self, entity: &mut Entity) -> Option<Box<dyn AIState>>;
}

pub struct IdleState;
pub struct ChaseState { target: EntityId }
pub struct AttackState { target: EntityId }

impl AIState for IdleState {
    fn update(&self, entity: &mut Entity) -> Option<Box<dyn AIState>> {
        if let Some(target) = entity.find_nearby_enemy() {
            return Some(Box::new(ChaseState { target }));
        }
        None
    }
}

impl AIState for ChaseState {
    fn update(&self, entity: &mut Entity) -> Option<Box<dyn AIState>> {
        if entity.distance_to(self.target) < 1.0 {
            return Some(Box::new(AttackState { target: self.target }));
        }
        entity.move_towards(self.target);
        None
    }
}

// 3. Command: 输入系统
pub trait GameCommand {
    fn execute(&self, game: &mut Game);
    fn undo(&self, game: &mut Game);
}

pub struct MoveCommand {
    entity_id: EntityId,
    old_pos: Vec2,
    new_pos: Vec2,
}

impl GameCommand for MoveCommand {
    fn execute(&self, game: &mut Game) {
        game.move_entity(self.entity_id, self.new_pos);
    }

    fn undo(&self, game: &mut Game) {
        game.move_entity(self.entity_id, self.old_pos);
    }
}

// 4. Object Pool: 对象池（弹药、特效等）
pub struct BulletPool {
    active: Vec<Bullet>,
    inactive: Vec<Bullet>,
    max_size: usize,
}

impl BulletPool {
    pub fn spawn(&mut self, pos: Vec2, velocity: Vec2) -> Option<&mut Bullet> {
        if let Some(mut bullet) = self.inactive.pop() {
            bullet.reset(pos, velocity);
            self.active.push(bullet);
            self.active.last_mut()
        } else if self.active.len() < self.max_size {
            let bullet = Bullet::new(pos, velocity);
            self.active.push(bullet);
            self.active.last_mut()
        } else {
            None
        }
    }

    pub fn recycle(&mut self, index: usize) {
        let bullet = self.active.remove(index);
        self.inactive.push(bullet);
    }
}
```

**模式选择总结**:

- ✅ Flyweight: 纹理/模型共享
- ✅ State: AI和动画状态机
- ✅ Command: 输入和回放系统
- ✅ Object Pool: 高频对象复用

---

## 4. 反模式与陷阱

「反模式与陷阱」涉及过度工程、Trait Object 滥用、忽略所有权与锁粒度过大，本节逐一说明其要点。

### 4.1 过度工程

```rust
// ❌ 反模式：过度使用设计模式
pub trait DataProcessor {
    fn process(&self, data: Vec<u8>) -> Vec<u8>;
}

pub struct DataProcessorFactory;
impl DataProcessorFactory {
    pub fn create() -> Box<dyn DataProcessor> {
        Box::new(ConcreteDataProcessor)
    }
}

pub struct DataProcessorBuilder {
    processor: Option<Box<dyn DataProcessor>>,
}

// 实际上只需要：
pub fn process_data(data: Vec<u8>) -> Vec<u8> {
    // 简单处理
    data
}
```

**教训**: 简单问题不需要复杂模式。遵循 YAGNI (You Aren't Gonna Need It) 原则。

### 4.2 Trait Object 滥用

```rust
// ❌ 反模式：不必要的动态分派
pub fn bad_sum(numbers: Vec<Box<dyn Number>>) -> i32 {
    numbers.iter().map(|n| n.value()).sum()
}

// ✅ 正确：使用泛型
pub fn good_sum<T: Number>(numbers: &[T]) -> i32 {
    numbers.iter().map(|n| n.value()).sum()
}
```

**教训**: 优先使用泛型（Generics），仅在需要运行时（Runtime）多态时使用 Trait Object。

### 4.3 忽略所有权

```rust
// ❌ 反模式：不必要的克隆
pub fn bad_observer_notify(observers: &Vec<Observer>, data: String) {
    for observer in observers {
        observer.update(data.clone()); // N次克隆
    }
}

// ✅ 正确：使用借用
pub fn good_observer_notify(observers: &Vec<Observer>, data: &str) {
    for observer in observers {
        observer.update(data); // 零拷贝
    }
}
```

**教训**: 充分利用 Rust 的借用（Borrowing）检查器，避免不必要的克隆。

### 4.4 锁粒度过大

```rust
// ❌ 反模式：持有锁过久
pub fn bad_cache_access(cache: &Mutex<HashMap<String, String>>, key: &str) -> Option<String> {
    let cache = cache.lock().unwrap();
    if let Some(value) = cache.get(key) {
        // 耗时操作，锁一直被持有
        expensive_processing(value);
        return Some(value.clone());
    }
    None
}

// ✅ 正确：缩小临界区
pub fn good_cache_access(cache: &Mutex<HashMap<String, String>>, key: &str) -> Option<String> {
    let value = {
        let cache = cache.lock().unwrap();
        cache.get(key).cloned()
    }; // 锁立即释放

    if let Some(value) = value {
        expensive_processing(&value);
        return Some(value);
    }
    None
}
```

**教训**: 最小化锁持有时间，考虑使用 RwLock 或无锁数据结构。

---

## 5. 模式组合最佳实践

本节从常见模式组合 与 组合示例：HTTP客户端 两个层面剖析「模式组合最佳实践」。

### 5.1 常见模式组合

| 组合                    | 场景       | 示例       |
| :--- | :--- | :--- || **Factory + Singleton** | 全局工厂   | 日志系统   |
| **Builder + Strategy**  | 可配置构建 | HTTP客户端 |
| **Decorator + Proxy**   | 多层包装   | 缓存+日志  |
| **Observer + Command**  | 事件驱动   | GUI系统    |
| **State + Strategy**    | 复杂状态   | 游戏AI     |

### 5.2 组合示例：HTTP客户端

```rust
/// 组合 Builder + Strategy + Decorator + Proxy

// 1. Builder: 构建HTTP客户端
pub struct HttpClientBuilder {
    base_url: Option<String>,
    timeout: Option<Duration>,
    retry_strategy: Option<Box<dyn RetryStrategy>>,
    middlewares: Vec<Box<dyn Middleware>>,
}

impl HttpClientBuilder {
    pub fn new() -> Self {
        Self {
            base_url: None,
            timeout: None,
            retry_strategy: None,
            middlewares: Vec::new(),
        }
    }

    pub fn base_url(mut self, url: String) -> Self {
        self.base_url = Some(url);
        self
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    // 2. Strategy: 重试策略
    pub fn retry_strategy(mut self, strategy: Box<dyn RetryStrategy>) -> Self {
        self.retry_strategy = Some(strategy);
        self
    }

    // 3. Decorator: 中间件
    pub fn add_middleware(mut self, middleware: Box<dyn Middleware>) -> Self {
        self.middlewares.push(middleware);
        self
    }

    pub fn build(self) -> HttpClient {
        HttpClient {
            base_url: self.base_url.unwrap_or_default(),
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            retry_strategy: self.retry_strategy,
            middlewares: self.middlewares,
            // 4. Proxy: 缓存代理
            cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

// 使用示例
pub fn http_client_example() {
    let client = HttpClientBuilder::new()
        .base_url("https://api.example.com".to_string())
        .timeout(Duration::from_secs(10))
        .retry_strategy(Box::new(ExponentialBackoff::new()))
        .add_middleware(Box::new(LoggingMiddleware))
        .add_middleware(Box::new(AuthMiddleware::new("token")))
        .build();

    // client 现在组合了多种模式的优势
}
```

---

## 6. Rust 特有考量

理解「Rust 特有考量」需要把握所有权与生命周期、Send + Sync与错误处理，本节依次展开。

### 6.1 所有权与生命周期

```rust
// 考虑：数据是移动还是借用？
pub trait DataProcessor {
    // 选项1：移动所有权（消费数据）
    fn process_owned(self, data: Vec<u8>) -> Vec<u8>;

    // 选项2：借用（只读）
    fn process_borrowed(&self, data: &[u8]) -> Vec<u8>;

    // 选项3：可变借用（修改数据）
    fn process_mut(&mut self, data: &mut Vec<u8>);
}

// 推荐：根据语义选择
// - 需要消费数据 → 移动
// - 只读访问 → 不可变借用
// - 需要修改 → 可变借用
```

### 6.2 Send + Sync

```rust
// 考虑：是否需要跨线程传递？
pub trait ThreadSafeObserver: Send + Sync {
    fn update(&self, data: &str);
}

// 不需要跨线程时可省略
pub trait SingleThreadObserver {
    fn update(&self, data: &str);
}
```

### 6.3 错误处理

```rust
// 推荐：使用 Result<T, E> 而非异常
pub trait Fallible {
    type Error;

    fn try_operation(&self) -> Result<(), Self::Error>;
}

// 考虑使用 thiserror 或 anyhow
#[derive(Debug, thiserror::Error)]
pub enum PatternError {
    #[error("Invalid state transition")]
    InvalidTransition,

    #[error("Resource not available")]
    ResourceUnavailable,
}
```

---

## 7. 生产环境指南

理解「生产环境指南」需要把握性能检查清单、可维护性检查清单、安全性检查清单与模式选择优先级，本节依次展开。

### 7.1 性能检查清单

- [ ] 避免不必要的堆分配
- [ ] 使用泛型（Generics）而非 Trait Object（性能关键路径）
- [ ] 缩小锁粒度
- [ ] 考虑使用 `#[inline]`
- [ ] 基准测试验证性能假设

### 7.2 可维护性检查清单

- [ ] 文档清晰（rustdoc）
- [ ] 单元测试覆盖
- [ ] 错误处理（Error Handling）完善
- [ ] 避免过度工程
- [ ] 代码审查

### 7.3 安全性检查清单

- [ ] 避免 `unsafe` 或充分注释
- [ ] 输入验证
- [ ] 边界检查
- [ ] 避免 panic（使用 Result）
- [ ] Clippy 和 Miri 检查

### 7.4 模式选择优先级

1. **优先**：零成本抽象（Zero-Cost Abstraction）（泛型、枚举（Enum））
2. **其次**：运行时（Runtime）灵活性（Trait Object）
3. **谨慎**：复杂模式组合
4. **避免**：过度工程

---

## 📚 相关资源

---

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>

## 过渡段

> **过渡**: 从具体场景过渡到决策树，可以系统化地缩小可选模式范围。
>
> **过渡**: 从决策树过渡到 Rust 特有约束，可以排除在所有权（Ownership）与并发模型下不适用的方案。
>
> **过渡**: 从选型结果过渡到生产检查清单，可以将设计决策转化为可验证的工程实践。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 需求明确 ⟹ 模式选型准确 | 清晰的功能与非功能需求 | 避免过度设计或选型失误 |
| 并发约束 ⟹ Send/Sync 要求 | Rust 所有权（Ownership）模型 | 排除不满足线程安全的设计 |
| 团队能力 ⟹ 可维护性 | 熟悉度与工具链支持 | 影响模式的长期落地效果 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Design Patterns: Elements of Reusable Object-Oriented Software (GoF, ACM DL)](https://dl.acm.org/doi/book/10.5555/95489)
- **P2 生态/社区**: [Refactoring.Guru — Design Patterns](https://refactoring.guru/design-patterns) · [The Pragmatic Bookshelf](https://pragprog.com)
