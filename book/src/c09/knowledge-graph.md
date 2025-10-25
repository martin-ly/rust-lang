# 知识图谱

本页展示设计模式的概念关系。

---

## 📊 核心概念关系图

```text
                    [设计模式]
                         |
         +---------------+---------------+
         |               |               |
     [经典模式]    [并发模式]     [Rust特有]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  创建型 结构型 行为型  Actor  CSP  所有权 类型  零成本
  模式   模式   模式   模型  模型  模式   状态  抽象
```

---

## 🎯 概念层次

### 1. 经典设计模式 (GoF Patterns)

**创建型模式** (Creational Patterns):

- **单例模式** (Singleton): 全局唯一实例
- **工厂模式** (Factory): 对象创建抽象
- **建造者模式** (Builder): 复杂对象构建
- **原型模式** (Prototype): 对象克隆
- **抽象工厂** (Abstract Factory): 产品族创建

**结构型模式** (Structural Patterns):

- **适配器模式** (Adapter): 接口转换
- **装饰器模式** (Decorator): 动态添加功能
- **代理模式** (Proxy): 访问控制
- **桥接模式** (Bridge): 抽象与实现分离
- **组合模式** (Composite): 树形结构
- **外观模式** (Facade): 简化接口
- **享元模式** (Flyweight): 共享对象

**行为型模式** (Behavioral Patterns):

- **观察者模式** (Observer): 事件通知
- **策略模式** (Strategy): 算法族
- **命令模式** (Command): 请求对象化
- **状态模式** (State): 状态转换
- **访问者模式** (Visitor): 操作与结构分离
- **迭代器模式** (Iterator): 遍历抽象
- **模板方法** (Template Method): 算法骨架
- **责任链模式** (Chain of Responsibility): 请求传递
- **中介者模式** (Mediator): 交互中心化
- **备忘录模式** (Memento): 状态保存
- **解释器模式** (Interpreter): 语言解释

---

### 2. 并发模式 (Concurrency Patterns)

**核心模式**:

- **Actor模型**: 消息传递并发
- **CSP模型**: 通道通信
- **STM**: 软件事务内存
- **Work-Stealing**: 任务窃取调度
- **Fork-Join**: 分治并行

**Rust实现特点**:

- 所有权保证线程安全
- 类型系统防止数据竞争
- `Send` 和 `Sync` trait
- 零成本抽象

---

### 3. Rust特有模式 (Rust-Specific Patterns)

**所有权模式**:

- **RAII**: 资源自动管理
- **移动语义**: 所有权转移
- **借用检查**: 编译时验证

**类型模式**:

- **新类型模式** (Newtype): 类型安全
- **类型状态模式**: 编译时状态机
- **幻影类型**: 编译时标记

**函数式模式**:

- **组合子模式**: 函数组合
- **迭代器模式**: 零成本抽象
- **闭包模式**: 环境捕获

---

## 🔗 概念关联

### 建造者模式 ←→ Rust所有权

```rust
// Rust建造者模式利用所有权实现类型安全
pub struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
}

impl ConfigBuilder {
    pub fn new() -> Self {
        Self {
            host: None,
            port: None,
        }
    }
    
    // 消费self，返回新的builder
    pub fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    // 消费builder，构建最终对象
    pub fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("Host is required")?,
            port: self.port.unwrap_or(8080),
        })
    }
}

pub struct Config {
    host: String,
    port: u16,
}

// 使用示例
let config = ConfigBuilder::new()
    .host("localhost".to_string())
    .port(3000)
    .build()
    .unwrap();
```

### 类型状态模式 ←→ 编译时验证

```rust
// 使用类型系统表示状态
struct Locked;
struct Unlocked;

struct Door<State> {
    _state: std::marker::PhantomData<State>,
}

impl Door<Locked> {
    fn new() -> Self {
        Door { _state: std::marker::PhantomData }
    }
    
    // 只有锁定的门可以解锁
    fn unlock(self) -> Door<Unlocked> {
        Door { _state: std::marker::PhantomData }
    }
}

impl Door<Unlocked> {
    // 只有解锁的门可以打开
    fn open(&self) {
        println!("Door opened!");
    }
    
    fn lock(self) -> Door<Locked> {
        Door { _state: std::marker::PhantomData }
    }
}

// 编译时保证状态转换正确
let door = Door::<Locked>::new();
// door.open(); // 编译错误！锁定的门不能打开
let door = door.unlock();
door.open(); // ✓ 正确
```

### Actor模式 ←→ 所有权与消息传递

```rust
use tokio::sync::mpsc;

// Actor消息定义
enum ActorMessage {
    Process(String),
    Stop,
}

// Actor结构
struct Actor {
    receiver: mpsc::Receiver<ActorMessage>,
}

impl Actor {
    fn new() -> (Self, mpsc::Sender<ActorMessage>) {
        let (tx, rx) = mpsc::channel(32);
        (Actor { receiver: rx }, tx)
    }
    
    async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                ActorMessage::Process(data) => {
                    println!("Processing: {}", data);
                }
                ActorMessage::Stop => break,
            }
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let (actor, sender) = Actor::new();
    
    // 启动actor
    tokio::spawn(actor.run());
    
    // 发送消息
    sender.send(ActorMessage::Process("Hello".to_string())).await.unwrap();
    sender.send(ActorMessage::Stop).await.unwrap();
}
```

---

## 📚 学习路径图

```text
第一步: 理解经典设计模式
    ↓
第二步: 学习Rust所有权与模式
    ↓
第三步: 掌握并发模式
    ↓
第四步: 应用类型状态模式
    ↓
第五步: 实战与模式组合
```

---

## 🎓 模式分类与应用

### 按用途分类

| 分类 | 目的 | 核心模式 |
|------|------|---------|
| **对象创建** | 灵活创建对象 | Builder, Factory, Singleton |
| **结构组织** | 优化对象关系 | Adapter, Decorator, Proxy |
| **行为协调** | 对象交互 | Observer, Strategy, State |
| **并发控制** | 安全并发 | Actor, CSP, STM |

### 按复杂度分类

| 级别 | 模式 | 学习时间 |
|------|------|---------|
| **入门** | Builder, Factory, Strategy | 1-2周 |
| **进阶** | Adapter, Decorator, Observer | 2-3周 |
| **高级** | Actor, Type-State, Phantom | 3-4周 |

---

## 💡 核心原则

### 1. 编译时保证

```text
类型系统 → 编译时检查 → 运行时零开销
```

### 2. 所有权驱动设计

```text
所有权规则 → 安全并发 → 内存安全
```

### 3. 零成本抽象

```text
高级抽象 → 编译优化 → 原生性能
```

---

## 🔍 Rust 1.90 增强特性

### 1. 异步生态模式

```rust
use std::future::Future;

// 异步建造者模式
pub struct AsyncBuilder {
    config: Config,
}

impl AsyncBuilder {
    pub async fn load_config(mut self) -> Self {
        // 异步加载配置
        self.config = fetch_config().await;
        self
    }
    
    pub async fn build(self) -> Result<Service, Error> {
        Ok(Service::new(self.config).await?)
    }
}
```

### 2. 高级类型模式

```rust
// 使用关联类型和GAT
trait Repository {
    type Entity;
    type Error;
    
    async fn find(&self, id: i64) -> Result<Self::Entity, Self::Error>;
    async fn save(&self, entity: Self::Entity) -> Result<(), Self::Error>;
}

// 具体实现
struct UserRepository;

impl Repository for UserRepository {
    type Entity = User;
    type Error = DbError;
    
    async fn find(&self, id: i64) -> Result<User, DbError> {
        // 实现细节
        Ok(User::default())
    }
    
    async fn save(&self, user: User) -> Result<(), DbError> {
        // 实现细节
        Ok(())
    }
}
```

### 3. 形式化验证模式

```rust
// 使用不变量验证
pub struct SortedVec<T: Ord> {
    inner: Vec<T>,
}

impl<T: Ord> SortedVec<T> {
    pub fn new() -> Self {
        SortedVec { inner: Vec::new() }
    }
    
    // 保证插入后仍然有序
    pub fn insert(&mut self, value: T) {
        let pos = self.inner.binary_search(&value).unwrap_or_else(|e| e);
        self.inner.insert(pos, value);
        // 不变量: inner始终有序
    }
    
    // 安全地返回不可变引用
    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 模式理论
- **[实践指南](./guides.md)** - 实现技巧
- **[代码示例](./examples.md)** - 完整实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [完整模式目录](../../crates/c09_design_pattern/README.md)
- [Rust设计模式](https://rust-unofficial.github.io/patterns/)
- [形式化验证](../../crates/c09_design_pattern/docs/theory/README.md)

### 相关模块

- **[C05: 多线程](../c05/README.md)** - 并发模式基础
- **[C06: 异步编程](../c06/README.md)** - 异步模式
- **[C04: 泛型编程](../c04/README.md)** - 类型模式

---

## 🎯 实践建议

### 模式选择决策树

```text
需要创建对象？
├─ 简单创建 → 工厂模式
├─ 复杂配置 → 建造者模式
└─ 全局唯一 → 单例模式

需要并发？
├─ 消息传递 → Actor模式
├─ 通道通信 → CSP模式
└─ 共享状态 → STM模式

需要状态管理？
├─ 编译时验证 → 类型状态模式
├─ 运行时切换 → 状态模式
└─ 策略选择 → 策略模式
```

---

**掌握设计模式是写出优雅Rust代码的关键！** 🚀
