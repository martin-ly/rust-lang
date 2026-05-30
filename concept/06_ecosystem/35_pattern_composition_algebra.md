# 模式组合代数：设计模式的结构化关联与冲突分析
>
> **受众**: [进阶]

> **层级**: L6 生态工程 — 系统设计模式
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: C×Eva — 评价模式组合的正确性与一致性
> **前置概念**: [Patterns](./02_patterns.md) · [Concurrency Patterns](../03_advanced/10_concurrency_patterns.md) · [Async Patterns](../03_advanced/13_async_patterns.md) · [Type System](../01_foundation/04_type_system.md)
> **后置概念**: [Distributed Systems](./18_distributed_systems.md) · [System Design Principles](./05_system_design_principles.md)
> **主要来源**: [GoF — Design Patterns] · [POSA — Pattern-Oriented Software Architecture] · [Category Theory for Programmers, Bartosz Milewski] · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

> **Bloom 层级**: 分析 → 评价 → 创造

## 一、核心命题

> **单独理解 23 个 GoF 模式是不够的。
> 模式在真实系统中以组合形式存在：Observer + Factory + Typestate 共同构成一个响应式状态机；
> Circuit Breaker + Retry + Timeout 构成一个弹性调用链；
> Pipeline + Backpressure + Fan-out 构成一个流处理系统。
> 当前项目的模式文件是"深度孤立"的——每个模式有 1000 行的独立分析，但缺少模式之间的结构化关联、组合规则、冲突检测和选择形式化。**

---

## 二、模式组合的基本操作

### 2.1 四种组合原语

借鉴范畴论的态射复合思想，定义模式组合的四种基本操作：[来源: [Milewski — Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)]

```text
模式组合代数:
  ⊗ (张量积/并行):  Pattern A ⊗ Pattern B = 两个模式同时作用，互不干扰
  ∘ (复合/串行):    Pattern A ∘ Pattern B = B 的输出作为 A 的输入
  ⊕ (和/选择):      Pattern A ⊕ Pattern B = 根据条件选择 A 或 B
  → (精炼/细化):    Pattern A → Pattern B = A 是 B 的特化或实现细节
```

### 2.2 并行组合（⊗）：独立共存[来源: [GoF — Design Patterns](https://en.wikipedia.org/wiki/Design_Patterns)]

```rust
// Observer ⊗ Factory: 事件通知与对象创建独立运行
use std::sync::{Arc, Mutex, Weak};

struct EventSystem {
    observers: Mutex<Vec<Weak<dyn Observer>>>, // Observer 模式
    factory: Box<dyn Factory>,                  // Factory 模式
}

// 两个模式独立运作：
// - Observer 处理事件分发（不关心对象如何创建）
// - Factory 处理对象创建（不关心事件如何分发）
impl EventSystem {
    fn notify(&self, event: Event) {
        // Observer 逻辑
    }

    fn create_widget(&self, spec: Spec) -> Widget {
        self.factory.create(spec) // Factory 逻辑
    }
}
```

**组合不变量**: 若 Pattern A 和 Pattern B 操作不相交的数据集，则 A ⊗ B 安全。

### 2.3 串行复合（∘）：流水线

```rust
// Validation ∘ Transformation ∘ Persistence
// 输入 → [验证] → [转换] → [持久化] → 输出

fn process_request(req: Request) -> Result<Response, Error> {
    let validated = validate(req)?;           // Validation 模式
    let transformed = transform(validated)?;  // Adapter/Transformer 模式
    let persisted = persist(transformed)?;    // Repository 模式
    Ok(Response::success(persisted))
}
```

**组合不变量**: 若 Pattern A 的输出类型满足 Pattern B 的输入约束，则 A ∘ B 类型安全。[来源: [Rust Type System — Trait Bounds](https://doc.rust-lang.org/reference/type-system.html)]

### 2.4 选择和（⊕）：条件分支

```rust
// CircuitBreaker ⊕ Retry ⊕ Fallback
// 根据失败率选择策略

enum ResilienceStrategy {
    CircuitBreaker(CircuitBreaker), // 高失败率：熔断
    Retry(RetryPolicy),             // 中失败率：重试
    Fallback(Fallback),             // 始终：降级
}

impl ResilienceStrategy {
    async fn execute<F, Fut>(&self, operation: F) -> Result<Output, Error>
    where F: Fn() -> Fut, Fut: Future<Output = Result<Output, Error>>
    {
        match self {
            Self::CircuitBreaker(cb) => cb.call(operation).await,
            Self::Retry(retry) => retry.execute(operation).await,
            Self::Fallback(fb) => fb.execute(operation).await,
        }
    }
}
```

### 2.5 精炼（→）：实现细化[来源: [Refactoring Guru — Design Patterns](https://refactoring.guru/design-patterns)]

```rust
// Strategy → Command: 策略的执行被封装为命令

trait Strategy {
    fn execute(&self, data: &Data) -> Result<Output, Error>;
}

// Command 是 Strategy 的特化：将策略执行封装为可撤销的操作
struct StrategyCommand {
    strategy: Box<dyn Strategy>,
    data: Data,
    undo_stack: Vec<Data>, // Command 模式新增：撤销支持
}

impl StrategyCommand {
    fn execute(&mut self) -> Result<Output, Error> {
        self.undo_stack.push(self.data.clone());
        self.strategy.execute(&self.data)
    }

    fn undo(&mut self) {
        if let Some(prev) = self.undo_stack.pop() {
            self.data = prev;
        }
    }
}
```

---

## 三、常见模式组合与冲突矩阵

### 3.1 协同组合（Synergistic Compositions）

| 组合 | 场景 | 协同机制 | Rust 实现 |
|:---|:---|:---|:---|
| **Observer + WeakRef** | 事件通知 | Observer 持有 Weak 引用，打破循环依赖 | `Weak<dyn Observer>` + `Rc<RefCell<Subject>>` |
| **Factory + Typestate** | 有状态对象创建 | Factory 创建 Typestate 对象，编译期保证状态转换合法 | PhantomData + Builder |
| **Strategy + Command** | 可撤销的算法切换 | Strategy 定义算法，Command 封装执行上下文 | `Box<dyn Strategy>` + `Command` trait |
| **Decorator + Trait** | 功能组合 | Trait 提供默认实现，Decorator 通过组合扩展 | `struct Decorator<T: Component>(T)` |
| **CircuitBreaker + Retry + Timeout** | 弹性调用 | 超时触发重试，重试失败触发熔断 | `tower::Service` 中间件链 |
| **Pipeline + Backpressure** | 流处理 | Pipeline 定义数据流，Backpressure 防止内存溢出 | `tokio::sync::mpsc::channel` + bounded buffer |
| **Actor + Channel** | 并发消息传递 | Actor 封装状态，Channel 保证消息顺序 | `actix::Actor` + `tokio::sync::mpsc` |

### 3.2 冲突矩阵（Conflict Matrix）

| 模式 A | 模式 B | 冲突类型 | 说明 | 解决方案 |
|:---|:---|:---:|:---|:---|
| **Singleton** | **Dependency Injection** | 🔴 互斥 | Singleton 隐藏依赖，DI 要求显式注入 | 放弃 Singleton，使用 DI 容器管理单例生命周期 |
| **Global State** | **Thread Safety** | 🔴 互斥 | 全局状态需要锁保护，降低并发性能 | 将全局状态改为 Actor 或 ThreadLocal |
| **Deep Inheritance** | **Composition** | 🟡 张力 | 继承层次过深时组合更难维护 | 优先组合，仅在 is-a 关系时使用继承（trait） |
| **Eager Loading** | **Lazy Initialization** | 🟡 张力 |  eager 启动慢但运行快；lazy 启动快但首次访问慢 | 根据启动时间 SLA 选择 |
| **Strong Consistency** | **High Availability** | 🟡 张力 | CAP 定理约束 | 根据业务需求选择 CP 或 AP |
| **Observer** | **Synchronous Call** | 🟡 张力 | Observer 通常是异步的，同步调用可能阻塞 | 使用 `tokio::spawn` 异步通知 |
| **Retry** | **Idempotency** | 🟡 依赖 | 无幂等保证的重试可能导致重复副作用 | 重试前必须确保操作幂等 |
| **Cache** | **Consistency** | 🟡 张力 | 缓存引入最终一致性 | 使用 TTL + 失效策略 |

---

## 四、模式选择的形式化决策树

### 4.1 问题特征 → 模式选择

```text
需要创建对象？
├── 是 → 对象创建逻辑复杂？
│   ├── 是 → 需要运行时决定类型？
│   │   ├── 是 → Factory Method / Abstract Factory
│   │   └── 否 → Builder（复杂构造）/ Prototype（克隆）
│   └── 否 → 直接构造（struct literal）
└── 否 → 需要组织类/结构体关系？
    ├── 是 → 需要统一接口？
    │   ├── 是 → Adapter（不兼容接口）/ Facade（简化复杂子系统）
    │   └── 否 → Decorator（动态添加功能）/ Proxy（控制访问）
    └── 否 → 需要管理行为变化？
        ├── 是 → 算法变化？
        │   ├── 是 → Strategy（运行时切换算法）
        │   └── 否 → State（状态驱动行为）/ Command（可撤销操作）
        └── 否 → 需要事件通知？
            ├── 是 → Observer（一对多通知）/ Mediator（多对多解耦）
            └── 否 → 需要遍历集合？
                ├── 是 → Iterator（安全遍历）
                └── 否 → 需要复用对象？
                    └── 是 → Flyweight（享元，共享状态）
```

### 4.2 并发场景的模式选择

```text
需要共享状态？
├── 是 → 状态可变？
│   ├── 是 → 需要原子更新？
│   │   ├── 是 → 数据竞争自由？
│   │   │   ├── 是 → Atomic（`AtomicUsize` 等）
│   │   │   └── 否 → Mutex / RwLock（`std::sync`）
│   │   └── 否 → 需要无锁？
│   │       ├── 是 → Lock-free（`crossbeam`）/ Epoch GC
│   │       └── 否 → 顺序执行（`SeqCst`）
│   └── 否 → 不可变共享（`Arc<T>`）
└── 否 → 需要消息传递？
    ├── 是 → 同步/异步？
    │   ├── 同步 → Channel（`std::sync::mpsc` / `crossbeam::channel`）
    │   └── 异步 → Actor（`actix`）/ Async Channel（`tokio::sync::mpsc`）
    └── 否 → 任务并行？
        ├── 是 → Fork-Join（`rayon`）
        └── 否 → 数据并行？
            └── 是 → SIMD / GPU（`wgpu`）
```

---

## 五、Rust 特有的模式组合

### 5.1 Typestate + Builder：编译期状态机

```rust
// Typestate 模式: 编译期保证状态转换合法
struct Uninitialized;
struct Initialized;
struct Running;

struct Server<State> {
    config: Config,
    _state: PhantomData<State>,
}

// Builder 模式: 逐步构造
impl Server<Uninitialized> {
    fn new() -> Self {
        Self { config: Config::default(), _state: PhantomData }
    }

    fn with_port(mut self, port: u16) -> Self {
        self.config.port = port;
        self
    }

    fn initialize(self) -> Server<Initialized> {
        Server { config: self.config, _state: PhantomData }
    }
}

impl Server<Initialized> {
    fn start(self) -> Server<Running> {
        Server { config: self.config, _state: PhantomData }
    }
}

// 编译期防止非法状态转换
let server = Server::new().with_port(8080).initialize().start();
// server.initialize(); // ❌ 编译错误: Server<Running> 没有 initialize 方法
```

### 5.2 Ownership + RAII + Scope Guard：资源安全组合

```rust
// 组合: RAII（资源获取即初始化）+ Scope Guard（作用域守卫）
use std::fs::File;
use std::io::{self, Write};

fn write_atomic(path: &str, data: &[u8]) -> io::Result<()> {
    let tmp_path = format!("{}.tmp", path);

    // RAII: File 在离开作用域时自动关闭
    let mut file = File::create(&tmp_path)?;

    // Scope Guard: 若后续操作失败，删除临时文件
    struct Guard<'a>(&'a str);
    impl<'a> Drop for Guard<'a> {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(self.0);
        }
    }
    let guard = Guard(&tmp_path);

    file.write_all(data)?;
    file.sync_all()?; // 确保数据落盘

    // 成功: 取消 guard（不删除临时文件）
    std::mem::forget(guard);

    // 原子重命名
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}
```

### 5.3 Trait Object + Strategy：动态分发与零成本抽象的融合

```rust
// 编译期多态（零成本）+ 运行期多态（动态分发）的组合

trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<Transaction, Error>;
}

// 编译期策略: 单态化，零运行时开销
struct Checkout<S: PaymentStrategy> {
    strategy: S,
}

impl<S: PaymentStrategy> Checkout<S> {
    fn process(&self, amount: f64) -> Result<Transaction, Error> {
        self.strategy.pay(amount)
    }
}

// 运行期策略: 动态分发，运行时灵活性
struct DynamicCheckout {
    strategy: Box<dyn PaymentStrategy>,
}

impl DynamicCheckout {
    fn set_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = strategy;
    }

    fn process(&self, amount: f64) -> Result<Transaction, Error> {
        self.strategy.pay(amount)
    }
}
```

---

## 六、分布式系统的模式组合

### 6.1 弹性模式组合：CircuitBreaker ∘ Retry ∘ Timeout

```rust
// tower::Service 的组合中间件
use tower::{Service, ServiceBuilder, timeout::TimeoutLayer};
use tower::retry::RetryLayer;

let service = ServiceBuilder::new()
    .layer(TimeoutLayer::new(Duration::from_secs(5)))      // 超时
    .layer(RetryLayer::new(policy))                         // 重试
    .layer(CircuitBreakerLayer::new(failure_threshold))     // 熔断
    .service(backend);

// 执行顺序: Timeout → Retry → CircuitBreaker → Backend
// 语义: 先熔断检查 → 再执行（带重试）→ 每次执行带超时
```

### 6.2 Saga 模式：分布式事务的组合

```rust
// Saga = T1 ∘ T2 ∘ ... ∘ Tn ∘ (Compensation_n ∘ ... ∘ Compensation_1)
// 每个事务 T_i 都有对应的补偿操作 C_i

trait SagaStep {
    fn execute(&self) -> Result<(), Error>;
    fn compensate(&self) -> Result<(), Error>;
}

struct Saga {
    steps: Vec<Box<dyn SagaStep>>,
    completed: Vec<usize>, // 记录已完成的步骤索引
}

impl Saga {
    fn execute(&mut self) -> Result<(), Error> {
        for (i, step) in self.steps.iter().enumerate() {
            match step.execute() {
                Ok(()) => self.completed.push(i),
                Err(e) => {
                    // 回滚: 按逆序执行补偿
                    for &idx in self.completed.iter().rev() {
                        self.steps[idx].compensate()?;
                    }
                    return Err(e);
                }
            }
        }
        Ok(())
    }
}
```

---

## 七、反例与边界测试

### 7.1 反例：Singleton + DI 的冲突

```rust,ignore
// 错误: Singleton 隐藏依赖，与 DI 哲学冲突
struct Logger;

impl Logger {
    fn instance() -> &'static Logger { // Singleton
        static INSTANCE: Logger = Logger;
        &INSTANCE
    }
}

// DI 要求显式注入
trait Service {
    fn process(&self, logger: &Logger); // 显式依赖
}

// 冲突: 使用 Singleton 时，DI 失去了意义
struct BadService;
impl Service for BadService {
    fn process(&self, _logger: &Logger) {
        let logger = Logger::instance(); // 隐藏依赖！
        // ...
    }
}
```

> **解决方案**: 使用 DI 容器管理单例生命周期，而非全局 `instance()` 方法。

### 7.2 边界测试：Observer + Singleton 组合的所有权冲突（编译错误）

```rust,ignore
use std::rc::Rc;
use std::cell::RefCell;

struct Subject {
    observers: Vec<Rc<RefCell<dyn Observer>>>, // ⚠️ 循环引用风险
}

trait Observer {
    fn update(&mut self);
}

struct ConcreteObserver {
    subject: Rc<RefCell<Subject>>, // ❌ 反向引用形成循环
}

impl Observer for ConcreteObserver {
    fn update(&mut self) {
        // 尝试通过 subject 再通知其他 observer → 死锁或 panic
        // self.subject.borrow_mut().notify(); // 运行时 panic!
    }
}

// ❌ 编译错误: `dyn Observer` cannot be sent between threads safely
// 但即使单线程，Rc<RefCell<...>> 的循环引用仍会导致内存泄漏
fn main() {
    let subject = Rc::new(RefCell::new(Subject { observers: vec![] }));
    let observer = Rc::new(RefCell::new(ConcreteObserver { subject: subject.clone() }));
    subject.borrow_mut().observers.push(observer.clone());
    // 循环引用: subject → observer → subject
    // 内存泄漏！即使离开作用域也不会释放
}
```

> **解决方案**: 使用 `Weak<RefCell<Subject>>` 打破循环引用，或改用 `tokio::sync::broadcast` 等无环通道。

### 7.3 边界测试：模式组合的状态空间爆炸

```rust
// 边界测试: 当组合的模式数量增加时，状态空间呈指数增长

// 2 个模式: 4 种状态组合
// 3 个模式: 8 种状态组合
// 4 个模式: 16 种状态组合

// 实际系统中，CircuitBreaker + Retry + Timeout + Fallback = 16 种状态
// 需要状态机或类型系统来管理

use std::sync::atomic::{AtomicUsize, Ordering};

struct ResilienceState {
    circuit: CircuitState,    // Closed / Open / HalfOpen
    retry_count: AtomicUsize, // 0..max
    timeout: Duration,
}

// 类型系统限制非法状态组合
enum CircuitState {
    Closed,     // 正常调用
    Open,       // 熔断，直接失败
    HalfOpen,   // 试探性调用（只允许 1 个请求）
}

// 非法状态: HalfOpen 时 retry_count > 1 → 需要运行时检查
```

---

## 八、模式组合的定理系统

### 8.1 组合安全性定理

> **定理 C-001** [Tier 3]: 若模式 A 和模式 B 操作不相交的数据集，则 A ⊗ B（并行组合）是类型安全的。
>
> **论证**: Rust 的所有权系统保证不相交的数据集不能被同时可变借用。若 A 和 B 只读取共享数据，或各自操作独立数据，则 `A ⊗ B` 无数据竞争。

> **定理 C-002** [Tier 3]: 若模式 A 的输出类型 `T_A` 满足模式 B 的输入约束 `C_B[T]`，则 `A ∘ B`（串行复合）是类型安全的。
> **论证**: Rust 的类型系统保证函数复合的类型一致性。若 `A: Fn() -> T_A` 且 `B: Fn(T) -> U where T: C_B`，则当 `T_A: C_B` 时，`B(A())` 类型正确。

> **定理 C-003** [Tier 3]: Singleton 与 Dependency Injection 在逻辑上互斥——Singleton 隐藏全局依赖，DI 要求依赖显式化。
> **论证**: Singleton 模式通过全局访问点隐藏了依赖关系；DI 模式通过构造函数/参数显式注入依赖。二者对"依赖可见性"的哲学相反，不能在同一设计层级同时使用而不引入矛盾。

---

## 九、知识来源关系

| **论断** | **来源** | **可信度** | **Tier** |
|:---|:---|:---:|:---:|
| 模式组合代数 | [POSA] · [💡 原创分析] | ✅/💡 | Tier 3 |
| 协同组合矩阵 | [GoF] · [💡 原创分析] | ✅/💡 | Tier 3 |
| 冲突矩阵 | [POSA] · [💡 原创分析] | ✅/💡 | Tier 3 |
| Rust Typestate + Builder | [Rust Design Patterns] | ✅ | Tier 2 |
| Saga 模式 | [Hector & Kenneth — Sagas] | ✅ | Tier 2 |
| 组合安全性定理 | [💡 原创分析] | ⚠️ | Tier 3 |

---

> **权威来源**: [GoF — Design Patterns](https://en.wikipedia.org/wiki/Design_Patterns) ·
> [POSA](https://en.wikipedia.org/wiki/Pattern-Oriented_Software_Architecture) ·
> [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) ·
> [Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.90.0+ (Edition 2024)
> **最后更新**: 2026-05-24
> **状态**: ✅ 新建 — 表征空间坐标系

## 十、边界测试：模式组合代数的编译错误

### 10.1 边界测试：状态机组合中的无效转换（编译错误）

```rust,compile_fail
struct StateA;
struct StateB;

impl StateA {
    fn to_b(self) -> StateB { StateB }
}

fn main() {
    let a = StateA;
    let b = a.to_b();
    // ❌ 编译错误: no method named `to_b` found for struct `StateB`
    let _c = b.to_b(); // StateB 没有 to_b 方法
}

// 正确: 使用类型状态模式
struct Machine<S> { _state: std::marker::PhantomData<S> }

struct Idle;
struct Running;

impl Machine<Idle> {
    fn start(self) -> Machine<Running> { Machine { _state: std::marker::PhantomData } }
}

impl Machine<Running> {
    fn stop(self) -> Machine<Idle> { Machine { _state: std::marker::PhantomData } }
}
```

> **修正**: 类型状态模式（Typestate Pattern）将状态机的状态编码为类型参数，非法的状态转换在编译期被拒绝。这是范畴论中**有限状态机作为类型**的直接应用：状态是类型，转换是函数，可达性由类型系统的可达性保证。与运行时状态检查（switch/case）相比，类型状态消除了运行时开销和遗漏分支的可能。[来源: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)]

### 10.2 边界测试：组合子模式的所有权链（编译错误）

```rust,ignore
struct Wrapper<T>(T);

fn main() {
    let w = Wrapper(String::from("hello"));
    let inner = w.0; // move 内部值
    // ❌ 编译错误: borrow of moved value: `w`
    // w.0 已被 move，w 部分初始化
    let _ = w.0;
}

// 正确: 使用解构或引用
fn fixed() {
    let w = Wrapper(String::from("hello"));
    let Wrapper(inner) = w; // ✅ 解构获取所有权
    println!("{}", inner);
}
```

> **修正**: 组合子模式（Combinator Pattern）通过小函数组合构建复杂行为。Rust 的所有权系统要求组合链中的每个中间结果必须正确传递或释放。部分 move（如 `w.0` 被 move 但 `w` 仍被视为整体）会导致编译错误。解构（`let Wrapper(inner) = w`）是安全的替代方案，它明确声明"消耗整个结构体，提取其字段"。这与 Haskell 的无限惰性组合链不同——Rust 的组合是严格的、所有权感知的。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]

### 10.3 边界测试：组合子嵌套过深导致的类型爆炸（编译错误/编译超时）

```rust,ignore
fn main() {
    // ❌ 编译问题: 过度嵌套的组合子导致类型签名指数增长
    let result = option_a()
        .and_then(|a| option_b(a))
        .and_then(|b| option_c(b))
        .and_then(|c| option_d(c))
        .and_then(|d| option_e(d))
        .and_then(|e| option_f(e))
        .and_then(|f| option_g(f))
        .and_then(|g| option_h(g))
        .and_then(|h| option_i(h))
        .and_then(|i| option_j(i));
}

fn option_a() -> Option<i32> { Some(1) }
fn option_b(_: i32) -> Option<i32> { Some(2) }
fn option_c(_: i32) -> Option<i32> { Some(3) }
fn option_d(_: i32) -> Option<i32> { Some(4) }
fn option_e(_: i32) -> Option<i32> { Some(5) }
fn option_f(_: i32) -> Option<i32> { Some(6) }
fn option_g(_: i32) -> Option<i32> { Some(7) }
fn option_h(_: i32) -> Option<i32> { Some(8) }
fn option_i(_: i32) -> Option<i32> { Some(9) }
fn option_j(_: i32) -> Option<i32> { Some(10) }
```

> **修正**: `Option`/`Result` 的 `and_then` 嵌套是**组合子模式**，但过度嵌套导致：1) 类型签名膨胀（每个 `and_then` 增加一层泛型）；2) 编译时间增加（类型推导复杂度）；3) 错误信息难读（10 层嵌套的错误链）。Rust 的替代方案：1) **`?` 运算符**：`let a = option_a()?; let b = option_b(a)?; ...`（扁平化，可读性高）；2) **`async`/`await`**：用异步组合替代同步组合子；3) **do-notation 宏**（如 `try_block!`）。这与 Haskell 的 `do` notation（语法糖扁平化 Monad 嵌套）或 Scala 的 `for` comprehension（类似）不同——Rust 的 `?` 运算符是编译器内建的特殊语法，不是通用 Monad 操作，但提供了等价的扁平化能力。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)] · [来源: [Rust Error Handling](https://doc.rust-lang.org/rust-by-example/error.html)]

---

## 参考来源

> [来源: [GoF — Design Patterns](https://en.wikipedia.org/wiki/Design_Patterns)]
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]
> [来源: [Wikipedia — Category Theory](https://en.wikipedia.org/wiki/Category_theory)]
> [来源: [Wikipedia — Monad](https://en.wikipedia.org/wiki/Monad_(functional_programming))]
> [来源: [Wikipedia — Functor](https://en.wikipedia.org/wiki/Functor)]
> [来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]
