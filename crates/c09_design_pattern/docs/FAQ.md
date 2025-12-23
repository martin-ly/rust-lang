# C09 设计模式: 常见问题解答 (FAQ)

> **文档定位**: 设计模式学习和实践中的常见问题快速解答
> **使用方式**: 遇到问题时快速查找解决方案和最佳实践
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [Glossary](./Glossary.md)

## 📊 目录

- [C09 设计模式: 常见问题解答 (FAQ)](#c09-设计模式-常见问题解答-faq)
  - [📊 目录](#-目录)
  - [📋 问题索引](#-问题索引)
  - [基础概念](#基础概念)
    - [Q1: 什么时候应该使用设计模式？](#q1-什么时候应该使用设计模式)
    - [Q2: Rust 中的设计模式与其他语言有什么不同？](#q2-rust-中的设计模式与其他语言有什么不同)
    - [Q3: 如何选择合适的设计模式？](#q3-如何选择合适的设计模式)
  - [创建型模式](#创建型模式)
    - [Q4: Rust 中如何实现线程安全的单例模式？](#q4-rust-中如何实现线程安全的单例模式)
    - [Q5: 建造者模式如何保证必填字段？](#q5-建造者模式如何保证必填字段)
  - [结构型模式](#结构型模式)
    - [Q6: 适配器模式 vs 桥接模式，有什么区别？](#q6-适配器模式-vs-桥接模式有什么区别)
    - [Q7: 何时使用装饰器模式 vs 代理模式？](#q7-何时使用装饰器模式-vs-代理模式)
  - [行为型模式](#行为型模式)
    - [Q8: 观察者模式如何避免借用检查问题？](#q8-观察者模式如何避免借用检查问题)
    - [Q9: 状态模式 vs 策略模式？](#q9-状态模式-vs-策略模式)
  - [并发与异步](#并发与异步)
    - [Q10: async/await vs 线程，如何选择？](#q10-asyncawait-vs-线程如何选择)
    - [Q11: Actor 模式 vs Reactor 模式？](#q11-actor-模式-vs-reactor-模式)
    - [Q12: 如何处理异步递归？](#q12-如何处理异步递归)
  - [性能优化](#性能优化)
    - [Q13: 设计模式会影响性能吗？](#q13-设计模式会影响性能吗)
    - [Q14: 如何测量设计模式的性能？](#q14-如何测量设计模式的性能)
  - [Rust特性](#rust特性)
    - [Q15: Rust 1.90 有哪些与设计模式相关的新特性？](#q15-rust-190-有哪些与设计模式相关的新特性)
  - [实践问题](#实践问题)
    - [Q16: 如何在实际项目中应用设计模式？](#q16-如何在实际项目中应用设计模式)
    - [Q17: 团队如何统一设计模式的使用？](#q17-团队如何统一设计模式的使用)
  - [📚 延伸阅读](#-延伸阅读)

**最后更新**: 2025-10-19
**适用版本**: Rust 1.92.0+ (Edition 2024)
**文档类型**: 📚 问题解答

---

## 📋 问题索引

**快速跳转**:

- [C09 设计模式: 常见问题解答 (FAQ)](#c09-设计模式-常见问题解答-faq)
  - [📊 目录](#-目录)
  - [📋 问题索引](#-问题索引)
  - [基础概念](#基础概念)
    - [Q1: 什么时候应该使用设计模式？](#q1-什么时候应该使用设计模式)
    - [Q2: Rust 中的设计模式与其他语言有什么不同？](#q2-rust-中的设计模式与其他语言有什么不同)
    - [Q3: 如何选择合适的设计模式？](#q3-如何选择合适的设计模式)
  - [创建型模式](#创建型模式)
    - [Q4: Rust 中如何实现线程安全的单例模式？](#q4-rust-中如何实现线程安全的单例模式)
    - [Q5: 建造者模式如何保证必填字段？](#q5-建造者模式如何保证必填字段)
  - [结构型模式](#结构型模式)
    - [Q6: 适配器模式 vs 桥接模式，有什么区别？](#q6-适配器模式-vs-桥接模式有什么区别)
    - [Q7: 何时使用装饰器模式 vs 代理模式？](#q7-何时使用装饰器模式-vs-代理模式)
  - [行为型模式](#行为型模式)
    - [Q8: 观察者模式如何避免借用检查问题？](#q8-观察者模式如何避免借用检查问题)
    - [Q9: 状态模式 vs 策略模式？](#q9-状态模式-vs-策略模式)
  - [并发与异步](#并发与异步)
    - [Q10: async/await vs 线程，如何选择？](#q10-asyncawait-vs-线程如何选择)
    - [Q11: Actor 模式 vs Reactor 模式？](#q11-actor-模式-vs-reactor-模式)
    - [Q12: 如何处理异步递归？](#q12-如何处理异步递归)
  - [性能优化](#性能优化)
    - [Q13: 设计模式会影响性能吗？](#q13-设计模式会影响性能吗)
    - [Q14: 如何测量设计模式的性能？](#q14-如何测量设计模式的性能)
  - [Rust特性](#rust特性)
    - [Q15: Rust 1.90 有哪些与设计模式相关的新特性？](#q15-rust-190-有哪些与设计模式相关的新特性)
  - [实践问题](#实践问题)
    - [Q16: 如何在实际项目中应用设计模式？](#q16-如何在实际项目中应用设计模式)
    - [Q17: 团队如何统一设计模式的使用？](#q17-团队如何统一设计模式的使用)
  - [📚 延伸阅读](#-延伸阅读)

---

## 基础概念

### Q1: 什么时候应该使用设计模式？

**A**: 设计模式应该在遇到特定问题时有针对性地使用：

✅ **适合使用设计模式的场景**:

- 遇到重复出现的设计问题
- 需要提高代码的可维护性和可扩展性
- 团队协作需要统一的架构语言
- 需要解耦复杂的依赖关系

❌ **不适合使用设计模式的场景**:

- 过度设计简单功能
- 为了使用模式而使用模式
- 增加不必要的抽象层次
- 性能敏感且模式引入开销的场景

**示例**:

```rust
// ❌ 过度设计：简单的配置读取不需要单例
fn read_config() -> Config {
    // 直接读取即可
}

// ✅ 合理使用：全局共享的连接池使用单例
use std::sync::OnceLock;
static CONNECTION_POOL: OnceLock<Pool> = OnceLock::new();
```

**相关**: [OVERVIEW.md](./OVERVIEW.md)

---

### Q2: Rust 中的设计模式与其他语言有什么不同？

**A**: Rust 的设计模式需要考虑所有权、借用和生命周期：

**主要区别**:

1. **所有权系统**
   - 必须明确数据的所有权转移
   - 使用 `Arc`/`Rc` 实现共享所有权
   - 生命周期影响模式设计

2. **类型系统**
   - 使用 trait 替代接口和抽象类
   - 泛型提供编译时多态（零成本抽象）
   - trait 对象提供运行时多态

3. **内存安全**
   - 无需手动内存管理
   - 编译时防止数据竞争
   - 类型状态模式保证编译时正确性

**示例**:

```rust
// Java 风格（运行时多态）
trait Strategy {
    fn execute(&self);
}

fn use_strategy(strategy: &dyn Strategy) {
    strategy.execute();
}

// Rust 风格（编译时多态，零成本）
fn use_strategy<S: Strategy>(strategy: &S) {
    strategy.execute();
}
```

**相关**: [Glossary.md](./Glossary.md#零成本抽象-zero-cost-abstraction)

---

### Q3: 如何选择合适的设计模式？

**A**: 根据具体问题和约束条件选择：

**决策树**:

```text
问题类型？
├─ 对象创建 → 创建型模式
│  ├─ 全局唯一 → 单例模式
│  ├─ 复杂构建 → 建造者模式
│  ├─ 类型创建 → 工厂模式
│  └─ 对象克隆 → 原型模式
│
├─ 对象组合 → 结构型模式
│  ├─ 接口转换 → 适配器模式
│  ├─ 功能扩展 → 装饰器模式
│  ├─ 简化接口 → 外观模式
│  └─ 内存优化 → 享元模式
│
├─ 对象行为 → 行为型模式
│  ├─ 事件通知 → 观察者模式
│  ├─ 算法切换 → 策略模式
│  ├─ 链式处理 → 责任链模式
│  └─ 状态转换 → 状态模式
│
└─ 并发处理 → 并发模式
   ├─ 消息传递 → Actor/Channel
   ├─ 事件驱动 → Reactor
   └─ 异步IO → async/await
```

**相关**: [00_MASTER_INDEX.md](./00_MASTER_INDEX.md#按场景导航)

---

## 创建型模式

### Q4: Rust 中如何实现线程安全的单例模式？

**A**: 使用 `OnceLock` (Rust 1.90+) 或 `lazy_static`:

**方案1: OnceLock (推荐)**:

```rust
use std::sync::OnceLock;

static INSTANCE: OnceLock<Config> = OnceLock::new();

pub fn get_config() -> &'static Config {
    INSTANCE.get_or_init(|| {
        Config::from_env()
    })
}
```

**方案2: lazy_static (兼容旧版本)**:

```rust
use lazy_static::lazy_static;

lazy_static! {
    static ref CONFIG: Config = Config::from_env();
}

pub fn get_config() -> &'static Config {
    &CONFIG
}
```

**性能对比**:

- `OnceLock`: 零成本，标准库支持
- `lazy_static`: 需要外部依赖，但兼容性好

**相关**: [src/creational/singleton/](../src/creational/singleton/)

---

### Q5: 建造者模式如何保证必填字段？

**A**: 使用类型状态模式（Typestate Pattern）:

```rust
// 使用类型参数表示状态
struct Builder<NameSet, AgeSet> {
    name: String,
    age: u32,
    email: Option<String>,
    _name: std::marker::PhantomData<NameSet>,
    _age: std::marker::PhantomData<AgeSet>,
}

// 状态标记类型
struct Set;
struct Unset;

impl Builder<Unset, Unset> {
    fn new() -> Self {
        Builder {
            name: String::new(),
            age: 0,
            email: None,
            _name: std::marker::PhantomData,
            _age: std::marker::PhantomData,
        }
    }
}

impl<AgeSet> Builder<Unset, AgeSet> {
    fn name(self, name: String) -> Builder<Set, AgeSet> {
        Builder {
            name,
            age: self.age,
            email: self.email,
            _name: std::marker::PhantomData,
            _age: std::marker::PhantomData,
        }
    }
}

impl<NameSet> Builder<NameSet, Unset> {
    fn age(self, age: u32) -> Builder<NameSet, Set> {
        Builder {
            name: self.name,
            age,
            email: self.email,
            _name: std::marker::PhantomData,
            _age: std::marker::PhantomData,
        }
    }
}

// 只有设置了所有必填字段才能 build
impl Builder<Set, Set> {
    fn build(self) -> Person {
        Person {
            name: self.name,
            age: self.age,
            email: self.email,
        }
    }
}
```

**优点**: 编译时保证，零运行时开销

**相关**: [src/creational/builder/](../src/creational/builder/)

---

## 结构型模式

### Q6: 适配器模式 vs 桥接模式，有什么区别？

**A**: 两者意图和应用场景不同：

| 对比项 | 适配器模式 | 桥接模式 |
|-------|----------|---------|
| **意图** | 接口转换，使不兼容的接口能够协作 | 抽象与实现分离，独立变化 |
| **应用时机** | 现有代码不兼容 | 设计阶段规划 |
| **结构** | 单一转换层 | 两个层次（抽象+实现） |
| **灵活性** | 解决兼容性问题 | 支持多维度扩展 |

**适配器示例**:

```rust
// 现有接口
trait OldApi {
    fn old_method(&self) -> String;
}

// 新接口
trait NewApi {
    fn new_method(&self) -> String;
}

// 适配器
struct Adapter<T: OldApi> {
    old_api: T,
}

impl<T: OldApi> NewApi for Adapter<T> {
    fn new_method(&self) -> String {
        self.old_api.old_method() // 转换调用
    }
}
```

**桥接示例**:

```rust
// 抽象层
trait Renderer {
    fn render(&self, content: &str);
}

// 实现层
struct Shape<R: Renderer> {
    renderer: R,
}

impl<R: Renderer> Shape<R> {
    fn draw(&self, content: &str) {
        self.renderer.render(content);
    }
}
```

**相关**: [src/structural/adapter/](../src/structural/adapter/), [src/structural/bridge/](../src/structural/bridge/)

---

### Q7: 何时使用装饰器模式 vs 代理模式？

**A**: 根据意图选择：

**装饰器模式**:

- **意图**: 动态添加功能
- **场景**: 功能增强、组合多种行为
- **特点**: 可以多层嵌套，保持接口一致

```rust
trait Component {
    fn operation(&self) -> String;
}

struct Decorator<T: Component> {
    inner: T,
    extra: String,
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        format!("{} + {}", self.inner.operation(), self.extra)
    }
}
```

**代理模式**:

- **意图**: 控制访问、延迟加载、权限检查
- **场景**: 访问控制、缓存、日志记录
- **特点**: 单层代理，可能改变行为

```rust
struct Proxy<T> {
    real: Option<T>,
    cached: Option<String>,
}

impl<T: Component> Proxy<T> {
    fn operation(&mut self) -> String {
        if let Some(cached) = &self.cached {
            return cached.clone(); // 缓存
        }
        let result = self.real.as_ref().unwrap().operation();
        self.cached = Some(result.clone());
        result
    }
}
```

**相关**: [src/structural/decorator/](../src/structural/decorator/), [src/structural/proxy/](../src/structural/proxy/)

---

## 行为型模式

### Q8: 观察者模式如何避免借用检查问题？

**A**: 使用多种策略：

**策略1: 使用 Channel (推荐)**:

```rust
use std::sync::mpsc::{channel, Sender};

struct EventBus {
    subscribers: Vec<Sender<Event>>,
}

impl EventBus {
    fn notify(&self, event: Event) {
        for subscriber in &self.subscribers {
            let _ = subscriber.send(event.clone());
        }
    }
}
```

**策略2: GATs + 借用视图 (Rust 1.90+)**:

```rust
trait Observer {
    type View<'a>: 'a where Self: 'a;
    fn update(&self, data: Self::View<'_>);
}

struct Subject<O: Observer> {
    observers: Vec<O>,
    data: String,
}

impl<O: Observer> Subject<O> {
    fn notify(&self) where for<'a> String: Into<O::View<'a>> {
        for observer in &self.observers {
            observer.update((&self.data).into());
        }
    }
}
```

**策略3: Arc + Mutex (线程安全)**:

```rust
use std::sync::{Arc, Mutex};

struct Subject {
    observers: Vec<Arc<Mutex<dyn Observer>>>,
}

impl Subject {
    fn notify(&self, event: &Event) {
        for observer in &self.observers {
            observer.lock().unwrap().update(event);
        }
    }
}
```

**相关**: [src/behavioral/observer/](../src/behavioral/observer/), [examples/gats_observer_demo.rs](../examples/gats_observer_demo.rs)

---

### Q9: 状态模式 vs 策略模式？

**A**: 区别在于意图和结构：

| 对比项 | 状态模式 | 策略模式 |
|-------|---------|---------|
| **意图** | 对象根据状态改变行为 | 选择算法/策略 |
| **谁决定切换** | 状态对象自己决定 | 客户端决定 |
| **状态/策略关系** | 状态之间有转换关系 | 策略独立，可互换 |
| **Rust实现** | 类型状态模式 | trait 对象或泛型 |

**状态模式（类型状态）**:

```rust
struct Document<S> {
    content: String,
    state: std::marker::PhantomData<S>,
}

struct Draft;
struct Published;

impl Document<Draft> {
    fn publish(self) -> Document<Published> {
        Document {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
}

impl Document<Published> {
    fn archive(self) {
        // 只有发布状态才能归档
    }
}
```

**策略模式（编译时多态）**:

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

fn sort_data<S: SortStrategy>(strategy: &S, data: &mut [i32]) {
    strategy.sort(data);
}
```

**相关**: [src/behavioral/state/](../src/behavioral/state/), [src/behavioral/strategy/](../src/behavioral/strategy/)

---

## 并发与异步

### Q10: async/await vs 线程，如何选择？

**A**: 根据任务类型选择：

**使用 async/await**:

- ✅ IO 密集型任务（网络、文件）
- ✅ 需要处理大量并发连接
- ✅ 低内存开销要求
- ✅ 协作式调度足够

**使用线程**:

- ✅ CPU 密集型任务
- ✅ 阻塞操作（同步 API）
- ✅ 需要真正的并行计算
- ✅ 简单的并发模型

**混合使用**:

```rust
// 主异步任务
async fn handle_request() {
    // IO 操作
    let data = fetch_data().await;

    // CPU 密集型操作放到线程池
    let result = tokio::task::spawn_blocking(|| {
        expensive_computation(data)
    }).await.unwrap();

    // 继续异步操作
    save_result(result).await;
}
```

**性能对比**:

- async/await: 单线程可处理数万并发
- 线程: 每线程 ~2MB 栈空间，数千并发已是极限

**相关**: [docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)

---

### Q11: Actor 模式 vs Reactor 模式？

**A**: 两种不同的并发模型：

**Actor 模式**:

- **模型**: 消息传递，每个 Actor 独立
- **调度**: 邮箱队列，异步消息
- **状态**: 每个 Actor 封装自己的状态
- **优点**: 强隔离，易于分布式
- **缺点**: 消息开销，需要序列化

```rust
struct Actor {
    receiver: mpsc::Receiver<Message>,
}

impl Actor {
    async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle(msg).await;
        }
    }
}
```

**Reactor 模式**:

- **模型**: 事件驱动，事件循环
- **调度**: 事件多路复用（epoll/kqueue）
- **状态**: 回调函数处理事件
- **优点**: 高效，单线程高并发
- **缺点**: 回调地狱，不易理解

```rust
struct Reactor {
    events: Vec<Box<dyn EventHandler>>,
}

impl Reactor {
    fn run(&mut self) {
        loop {
            let events = self.poll(); // epoll
            for event in events {
                event.handle();
            }
        }
    }
}
```

**Rust中的实践**:

- Tokio 基于 Reactor 模式
- Actor 可以在 Tokio 上实现

**相关**: [docs/ACTOR_REACTOR_PATTERNS.md](./ACTOR_REACTOR_PATTERNS.md)

---

### Q12: 如何处理异步递归？

**A**: 使用 `Box::pin` 或 `async-recursion` crate：

**方案1: 手动 Box (推荐)**:

```rust
use std::future::Future;
use std::pin::Pin;

fn async_factorial(n: u64) -> Pin<Box<dyn Future<Output = u64> + Send>> {
    Box::pin(async move {
        if n == 0 {
            1
        } else {
            n * async_factorial(n - 1).await
        }
    })
}
```

**方案2: async-recursion crate**:

```rust
use async_recursion::async_recursion;

#[async_recursion]
async fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1).await
    }
}
```

**方案3: 尾递归优化（转迭代）**:

```rust
async fn factorial(n: u64) -> u64 {
    let mut result = 1;
    for i in 1..=n {
        result *= i;
    }
    result
}
```

**性能**: 尾递归 > Box::pin > async-recursion

**相关**: [docs/ASYNC_RECURSION_ANALYSIS.md](./ASYNC_RECURSION_ANALYSIS.md)

---

## 性能优化

### Q13: 设计模式会影响性能吗？

**A**: 取决于实现方式：

**零成本抽象（无性能损失）**:

- ✅ 泛型 + trait (编译时多态)
- ✅ 类型状态模式
- ✅ RPIT (返回位 impl Trait)
- ✅ 编译器内联优化

```rust
// 零成本
fn process<T: Handler>(handler: &T, data: Data) {
    handler.handle(data); // 编译时确定，可内联
}
```

**有运行时开销**:

- ❌ trait 对象 (动态分派)
- ❌ Arc/Mutex (原子操作)
- ❌ Channel (队列操作)
- ❌ 堆分配 (Box/Vec)

```rust
// 有开销
fn process(handler: &dyn Handler, data: Data) {
    handler.handle(data); // 虚函数调用
}
```

**优化建议**:

1. 优先使用编译时多态（泛型）
2. 热路径避免 trait 对象
3. 使用 `#[inline]` 提示编译器
4. 运行 benchmark 验证

**相关**: [benches/](../benches/)

---

### Q14: 如何测量设计模式的性能？

**A**: 使用 Criterion 框架：

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_strategy(c: &mut Criterion) {
    let mut group = c.benchmark_group("strategy_pattern");

    // 编译时多态
    group.bench_function("generic", |b| {
        b.iter(|| {
            let strategy = ConcreteStrategy;
            process_generic(black_box(&strategy));
        });
    });

    // 运行时多态
    group.bench_function("trait_object", |b| {
        b.iter(|| {
            let strategy: &dyn Strategy = &ConcreteStrategy;
            process_dynamic(black_box(strategy));
        });
    });

    group.finish();
}

criterion_group!(benches, benchmark_strategy);
criterion_main!(benches);
```

**运行基准**:

```bash
cargo bench
cargo bench -- --save-baseline main
cargo bench -- --baseline main
```

**相关**: [benches/pattern_benchmarks.rs](../benches/pattern_benchmarks.rs)

---

## Rust特性

### Q15: Rust 1.90 有哪些与设计模式相关的新特性？

**A**: 主要新特性：

**1. RPITIT (返回位 impl Trait in Trait)**:

```rust
trait TextSource {
    fn words(&self) -> impl Iterator<Item = &str>;
}

struct Document { text: String }

impl TextSource for Document {
    fn words(&self) -> impl Iterator<Item = &str> {
        self.text.split_whitespace()
    }
}
```

**2. async fn in trait (原生支持)**:

```rust
trait AsyncHandler {
    async fn handle(&self, data: Data) -> Result<()>;
}

// 无需 async-trait crate
impl AsyncHandler for MyHandler {
    async fn handle(&self, data: Data) -> Result<()> {
        // 异步实现
        Ok(())
    }
}
```

**3. dyn trait upcasting (trait 对象上转型)**:

```rust
trait Super {}
trait Sub: Super {}

fn upcast(sub: &dyn Sub) {
    let sup: &dyn Super = sub; // 自动上转型
}
```

**4. let-else (早退模式)**:

```rust
fn handle(request: Option<Request>) -> Result<()> {
    let Some(req) = request else {
        return Err("No request");
    };
    // 处理 req
    Ok(())
}
```

**5. OnceLock (标准库单例)**:

```rust
use std::sync::OnceLock;

static CONFIG: OnceLock<Config> = OnceLock::new();

fn get_config() -> &'static Config {
    CONFIG.get_or_init(|| Config::load())
}
```

**相关**: [src/rust_190_features.rs](../src/rust_190_features.rs)

---

## 实践问题

### Q16: 如何在实际项目中应用设计模式？

**A**: 遵循渐进式原则：

**步骤1: 识别问题**:

- 重复代码模式
- 紧耦合的组件
- 难以扩展的结构

**步骤2: 选择模式**:

- 参考决策树（Q3）
- 考虑性能约束
- 评估团队熟悉度

**步骤3: 小步重构**:

- 从局部开始
- 编写测试保护
- 渐进式改进

**步骤4: 验证效果**:

- 代码可读性
- 可维护性
- 性能基准

**反模式警告**:

- ❌ 过度工程化
- ❌ 为了模式而模式
- ❌ 忽略简单解决方案

**相关**: [OVERVIEW.md](./OVERVIEW.md)

---

### Q17: 团队如何统一设计模式的使用？

**A**: 建立规范和最佳实践：

**1. 文档化**:

- 维护模式目录
- 记录应用场景
- 提供代码示例

**2. 代码审查**:

- 检查模式使用
- 讨论替代方案
- 分享经验教训

**3. 培训**:

- 定期技术分享
- 结对编程
- 案例学习

**4. 工具支持**:

- Clippy 规则
- 自定义 lint
- 项目模板

**示例规范**:

```toml
# .clippy.toml
avoid-breaking-exported-api = true
enum-variant-names-threshold = 3
```

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [README](./README.md) - 项目概述
- [Glossary](./Glossary.md) - 术语表
- [综合指南](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md) - 深度学习
- [OVERVIEW](./OVERVIEW.md) - 文档概览

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [源码实现](../src/)
