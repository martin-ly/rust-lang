# C09 设计模式 - 示例中心

> **创建日期**: 2025-10-22
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 本示例集展示经典 GoF 设计模式在 Rust 中的实现，以及 Rust 特有的并发模式、异步模式和类型状态模式。

---

## 示例概览

本目录包含 **20+ 个核心示例**，涵盖设计模式的所有重要类别：

- ✅ 创建型模式 (5种)
- ✅ 结构型模式 (7种)
- ✅ 行为型模式 (11种)
- ✅ Rust 特有模式
- ✅ 并发与异步模式
- ✅ Rust 1.93.0 新特性

---

## 示例分类导航

### 创建型模式 (Creational)

对象创建机制，提升灵活性和复用性。

| 示例 | 描述 | 模式 | 运行命令 |
|------|------|------|----------|
| `singleton.rs` | 单例模式 | Singleton | `cargo run --example singleton` |
| `factory.rs` | 工厂模式 | Factory | `cargo run --example factory` |
| `builder.rs` | 建造者模式 | Builder | `cargo run --example builder` |
| `prototype.rs` | 原型模式 | Prototype | `cargo run --example prototype` |
| `abstract_factory.rs` | 抽象工厂 | Abstract Factory | `cargo run --example abstract_factory` |

### 结构型模式 (Structural)

类和对象的组合方式。

| 示例 | 描述 | 模式 | 运行命令 |
|------|------|------|----------|
| `adapter.rs` | 适配器模式 | Adapter | `cargo run --example adapter` |
| `decorator.rs` | 装饰器模式 | Decorator | `cargo run --example decorator` |
| `composite.rs` | 组合模式 | Composite | `cargo run --example composite` |
| `proxy.rs` | 代理模式 | Proxy | `cargo run --example proxy` |
| `facade.rs` | 外观模式 | Facade | `cargo run --example facade` |
| `flyweight.rs` | 享元模式 | Flyweight | `cargo run --example flyweight` |
| `bridge.rs` | 桥接模式 | Bridge | `cargo run --example bridge` |

### 行为型模式 (Behavioral)

对象间的通信和责任分配。

| 示例 | 描述 | 模式 | 运行命令 |
|------|------|------|----------|
| `observer.rs` | 观察者模式 | Observer | `cargo run --example observer` |
| `strategy.rs` | 策略模式 | Strategy | `cargo run --example strategy` |
| `command.rs` | 命令模式 | Command | `cargo run --example command` |
| `state.rs` | 状态模式 | State | `cargo run --example state` |
| `chain_of_responsibility.rs` | 责任链 | Chain of Responsibility | `cargo run --example chain_of_responsibility` |
| `iterator.rs` | 迭代器模式 | Iterator | `cargo run --example iterator` |
| `template_method.rs` | 模板方法 | Template Method | `cargo run --example template_method` |
| `visitor.rs` | 访问者模式 | Visitor | `cargo run --example visitor` |
| `mediator.rs` | 中介者模式 | Mediator | `cargo run --example mediator` |
| `memento.rs` | 备忘录模式 | Memento | `cargo run --example memento` |
| `interpreter.rs` | 解释器模式 | Interpreter | `cargo run --example interpreter` |

### Rust 特有模式

Rust 语言特性的独特应用。

| 示例 | 描述 | 模式 | 运行命令 |
|------|------|------|----------|
| `typestate.rs` | 类型状态模式 | Typestate | `cargo run --example typestate` |
| `visitor_trait.rs` | Trait 访问者 | Visitor | `cargo run --example visitor_trait` |
| `RAII_guard.rs` | RAII 守卫 | RAII | `cargo run --example RAII_guard` |
| `newtype.rs` | 新型类型 | Newtype | `cargo run --example newtype` |

### 并发与异步模式

并发编程中的高级模式。

| 示例 | 描述 | 模式 | 运行命令 |
|------|------|------|----------|
| `actor_demo.rs` | Actor 模型 | Actor | `cargo run --example actor_demo` |
| `reactor_demo.rs` | Reactor 模式 | Reactor | `cargo run --example reactor_demo` |
| `event_bus_demo.rs` | 事件总线 | Event Bus | `cargo run --example event_bus_demo` |
| `async_trait_demo.rs` | 异步 Trait | Async Trait | `cargo run --example async_trait_demo` |
| `gats_observer_demo.rs` | GATs 观察者 | GATs Observer | `cargo run --example gats_observer_demo` |
| `pipeline_iter_demo.rs` | 流水线迭代器 | Pipeline | `cargo run --example pipeline_iter_demo` |

### Rust 1.93.0 特性示例 ⭐ NEW

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rust_192_features_demo.rs` | Rust 1.93.0 特性演示 | 新语言特性 | `cargo run --example rust_192_features_demo` |
| `rust_191_features_demo.rs` | Rust 1.91 特性演示 | 历史参考 | `cargo run --example rust_191_features_demo` |
| `rust_190_features_demo.rs` | Rust 1.90 特性演示 | 历史参考 | `cargo run --example rust_190_features_demo` |

---

## 如何运行示例

### 基础运行

```bash
# 进入模块目录
cd crates/c09_design_pattern

# 运行创建型模式示例
cargo run --example builder
cargo run --example factory
cargo run --example singleton

# 运行结构型模式示例
cargo run --example adapter
cargo run --example decorator
cargo run --example proxy

# 运行行为型模式示例
cargo run --example observer
cargo run --example strategy
cargo run --example command
```

### 运行 Rust 特有模式

```bash
# 类型状态模式（强烈推荐）
cargo run --example typestate

# 事件总线（异步、背压控制）
cargo run --example event_bus_demo

# GATs 观察者
 cargo run --example gats_observer_demo
```

### 运行异步模式示例

```bash
# 异步事件总线
cargo run --example event_bus_demo

# 原生 async trait
cargo run --example async_trait_demo

# 流水线迭代器
cargo run --example pipeline_iter_demo
```

### 运行测试

```bash
# 运行所有测试
cargo test -p c09_design_pattern

# 运行形式化验证测试
cargo test --lib formal_verification_examples

# 运行所有功能测试
cargo test --all-features
```

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench -p c09_design_pattern

# 运行特定模式基准
cargo bench -p c09_design_pattern -- flyweight
cargo bench -p c09_design_pattern -- proxy_request

# 保存基线
cargo bench -p c09_design_pattern -- --save-baseline main
```

---

## 学习建议

### 初学者路径 (第1-4周)

**第1周: 创建型模式**:

```bash
cargo run --example singleton
cargo run --example factory
cargo run --example builder
cargo run --example prototype
```

- 学习 `OnceLock` 实现单例
- 掌握泛型工厂
- 理解类型状态 Builder
- 学习 `Clone` trait

**第2周: 结构型模式**:

```bash
cargo run --example adapter
cargo run --example decorator
cargo run --example proxy
cargo run --example facade
```

- Trait 适配
- 组合扩展功能
- 智能指针代理
- 简化复杂接口

**第3周: 行为型模式**:

```bash
cargo run --example observer
cargo run --example strategy
cargo run --example command
cargo run --example state
```

- 事件通知系统
- 可插拔算法
- 命令队列
- 状态机实现

**第4周: Rust 特有模式**:

```bash
cargo run --example typestate
cargo run --example RAII_guard
cargo run --example newtype
```

- 编译时状态验证
- 资源自动管理
- 类型安全包装

### 进阶路径 (第5-8周)

1. **学习并发模式**

   ```bash
   cargo run --example actor_demo
   cargo run --example reactor_demo
   cargo run --example event_bus_demo
   ```

   - Actor 消息传递
   - Reactor 事件驱动
   - 异步事件总线

2. **掌握异步模式**

   ```bash
   cargo run --example async_trait_demo
   cargo run --example gats_observer_demo
   ```

   - 原生 async trait
   - GATs 借用视图
   - 零拷贝通知

3. **探索高级模式**

   ```bash
   cargo run --example pipeline_iter_demo
   cargo run --example visitor
   cargo run --example chain_of_responsibility
   ```

   - 返回位 impl Trait
   - Trait 访问者
   - 责任链处理

### 高级路径 (第9周+)

1. **Rust 1.93.0 新特性**

   ```bash
   cargo run --example rust_192_features_demo
   ```

   - let-else 表达式
   - 返回位 impl Trait
   - RPITIT
   - dyn 上行转型

2. **形式化验证**

   ```bash
   cargo test --lib formal_verification_examples
   ```

   - 类型级状态机
   - 终止性证明
   - 并发安全性

---

## 关键概念速查

### Builder 模式 (类型状态)

```rust
struct HttpRequestBuilder<State> {
    url: Option<String>,
    method: Option<HttpMethod>,
    _state: PhantomData<State>,
}

struct Uninitialized;
struct UrlSet;
struct Ready;

impl HttpRequestBuilder<Uninitialized> {
    fn new() -> Self { /* ... */ }
    fn url(self, url: impl Into<String>) -> HttpRequestBuilder<UrlSet> { /* ... */ }
}

impl HttpRequestBuilder<UrlSet> {
    fn method(self, method: HttpMethod) -> HttpRequestBuilder<Ready> { /* ... */ }
}

impl HttpRequestBuilder<Ready> {
    fn build(self) -> HttpRequest { /* ... */ }
}
```

### Observer 模式 (GATs)

```rust
trait Observer {
    type Item;
    fn update(&mut self, item: &Self::Item);
}

// GATs 实现借用视图
trait BorrowingObserver {
    type Item<'a>
    where
        Self: 'a;
    fn update<'a>(&mut self, item: Self::Item<'a>);
}
```

### Strategy 模式

```rust
trait SortStrategy {
    fn sort<T: Ord>(&self, data: &mut [T]);
}

struct QuickSort;
struct MergeSort;

impl SortStrategy for QuickSort {
    fn sort<T: Ord>(&self, data: &mut [T]) {
        data.sort_unstable();
    }
}

fn process_data(data: &mut [i32], strategy: &dyn SortStrategy) {
    strategy.sort(data);
}
```

### Actor 模式

```rust
use tokio::sync::mpsc;

struct Actor {
    receiver: mpsc::Receiver<Message>,
}

enum Message {
    Process(String),
    Stop,
}

impl Actor {
    async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                Message::Process(data) => self.process(data),
                Message::Stop => break,
            }
        }
    }
}
```

---

## 相关文档

### 模块文档

- [模块主页](../README.md) - 完整学习指南
- [文档中心](../docs/README.md) - 详细文档导航
- [主索引](../docs/00_MASTER_INDEX.md) - 文档完整索引

### 理论文档

- [综合设计模式指南](../docs/COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md)
- [异步与同步等价理论](../docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md)
- [Actor 与 Reactor 模式](../docs/ACTOR_REACTOR_PATTERNS.md)
- [设计模式概念族谱](../../../docs/research_notes/DESIGN_PATTERN_CONCEPT_MINDMAP.md)

### 外部资源

- [Refactoring.Guru - 设计模式](https://refactoring.guru/design-patterns)
- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)
- [GoF 设计模式书籍](https://en.wikipedia.org/wiki/Design_Patterns)

---

## 设计原则

### Rust 设计模式原则

1. **组合优于继承**

   ```rust
   // ✅ 使用 Trait 组合
   trait Drawable { fn draw(&self); }
   trait Clickable { fn on_click(&self); }
   struct Button { /* ... */ }
   impl Drawable for Button { /* ... */ }
   impl Clickable for Button { /* ... */ }
   ```

2. **零成本抽象**

   ```rust
   // ✅ 泛型在编译期单态化，零运行时开销
   fn process<T: Strategy>(item: T) { /* ... */ }
   ```

3. **类型状态模式**

   ```rust
   // ✅ 使用类型系统防止非法状态
   Builder<Ready>::build() // 只有 Ready 状态才能 build
   ```

---

*示例基于 Rust 1.94+，Edition 2024*:

[返回模块主页](../README.md) | [返回上级](../README.md)
