# 模式实现对比 (Pattern Implementation Comparison)

> **代码状态**: 混合（原 crate 文档示例，部分代码块为示意片段）
>
> **EN**: Pattern Implementation Comparison
> **Summary**: Compares different implementation strategies for design patterns in Rust: trait objects vs generics, sync vs async, static vs dynamic dispatch, single vs multi-threaded, zero-cost vs runtime abstraction, and ownership models.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **内容分级**: [综述级]
> **Bloom 层级**: L4-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: A×Eva — 评估模式实现策略
> **前置依赖**: [Design Patterns](01_patterns.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Generics](../../02_intermediate/01_generics/01_generics.md)
> **后置概念**: [Pattern Selection Best Practices](10_pattern_selection_best_practices.md) · [Engineering and Production Patterns](13_engineering_and_production_patterns.md)
> **定理链**: Scenario ⟹ Implementation Strategy ⟹ Trade-off Evaluation
> **层级**: L6 生态工程
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
> **后置概念**: [Rust vs C++：形式系统模型 vs 机制工程模型](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
>
> **权威状态**: 本页由 `crates/c09_design_pattern/docs/` 整治迁移而来，作为 `concept/` 中的权威页。

---

## 1. 概述

Rust 提供了多种方式来实现设计模式，每种方式都有其权衡。
本文档对比不同实现方式的特点、性能和适用场景。

### 1.1 对比维度

| 维度         | 关注点             | 评估指标               |
| :--- | :--- | :--- |
| **性能**     | 执行速度、内存占用 | 吞吐量、延迟、内存开销 |
| **灵活性**   | 扩展性、可维护性   | 代码复杂度、修改成本   |
| **类型安全** | 编译时检查         | 类型错误捕获率         |
| **并发性**   | 多线程安全         | Send/Sync（Sync）实现          |
| **可测试性** | 单元测试、集成测试 | Mock支持、测试覆盖率   |

---

## 2. Trait vs 泛型实现对比

本页把「同一模式 × 不同实现机制」做成对照矩阵，每组对比回答「机制选择改变了什么」。第一组是 Strategy 模式的分派机制对比：

- **Strategy 模式对比**：策略模式的核心是「算法可替换」。Rust 提供两种替换时机——**运行时（Runtime）替换**（trait object：`Box<dyn SortStrategy>`，策略存字段、可中途更换，成本是每次调用一次虚表跳转）与**编译期替换**（泛型（Generics）：`struct Sorter<S: SortStrategy> { strategy: S }`，策略进类型参数、更换策略 = 更换类型，零成本但「同一容器的两个策略实例」是不同类型，不能存入同一 `Vec`）。
- **性能对比**：典型差异不在单次调用（虚表跳转仅 2–5ns），而在「优化可见性」——泛型版策略方法可内联、可常量传播（如比较器是简单闭包（Closures）时整个排序可特化）；`dyn` 版跨编译单元的调用对优化器不透明。决策规则：策略更换频率 > 调用频率量级差异大（如插件系统）→ `dyn`；策略固定但调用密集（如比较器、哈希器）→ 泛型。

本页其余各组对比（同步/异步（Async）、静态/动态工厂、单/多线程单例、零成本/运行时迭代器（Iterator）、所有权（Ownership）模式）都复用同一分析框架：**确定变化点的时机（编译期/运行期），再读机制的成本列**。

### 2.1 Strategy模式对比

Strategy 模式在 Rust 中有两种正交实现，取舍点是**单态化（Monomorphization）成本 vs 动态分派开销**：

| 维度 | Trait Object（`Box<dyn Strategy>`） | 泛型（`S: Strategy`） |
|---|---|---|
| 分派方式 | 虚表查找，运行期 | 单态化，编译期内联 |
| 二进制体积 | 小（一份代码） | 大（每个实例化一份） |
| 异构集合 | ✅ 可存入同一 `Vec` | ❌ 不同类型需枚举（Enum）或装箱 |
| 内联优化 | 几乎不可能 | 完全可行 |
| 适用场景 | 插件、运行期选择策略 | 热路径、编译期已知策略 |

经验法则：每进程策略实例数 >10 且种类固定 → 泛型；策略由配置在运行期装载 → trait object。热路径中虚表查找本身不贵，真正的损失是阻断内联后无法做 SIMD/常量折叠。

#### 方式 1：Trait Object (动态分派)

```rust
/// Strategy接口
pub trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
}

/// 具体策略
pub struct ZipCompression;
pub struct GzipCompression;

impl CompressionStrategy for ZipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // ZIP压缩
        data.to_vec()
    }
}

impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // GZIP压缩
        data.to_vec()
    }
}

/// 上下文 (动态分派)
pub struct Compressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl Compressor {
    pub fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        Self { strategy }
    }

    pub fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data) // 虚函数调用
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }
}

/// 使用示例
pub fn trait_object_example() {
    let mut compressor = Compressor::new(Box::new(ZipCompression));
    compressor.compress(b"data");

    // 运行时切换策略
    compressor.set_strategy(Box::new(GzipCompression));
    compressor.compress(b"data");
}
```

**特点**:

- ✅ 运行时（Runtime）灵活性
- ✅ 易于扩展
- ⚠️ 堆分配 (Box)
- ⚠️ 虚函数调用开销 (~1-3ns)
- ⚠️ 无法内联

#### 方式 2：泛型 (静态分派)

```rust,ignore
/// 上下文 (静态分派)
pub struct GenericCompressor<S: CompressionStrategy> {
    strategy: S,
}

impl<S: CompressionStrategy> GenericCompressor<S> {
    pub fn new(strategy: S) -> Self {
        Self { strategy }
    }

    pub fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data) // 直接调用，可内联
    }
}

/// 使用示例
pub fn generic_example() {
    let compressor1 = GenericCompressor::new(ZipCompression);
    compressor1.compress(b"data");

    let compressor2 = GenericCompressor::new(GzipCompression);
    compressor2.compress(b"data");
}
```

**特点**:

- ✅ 零成本抽象（Zero-Cost Abstraction）
- ✅ 可内联
- ✅ 编译时多态
- ⚠️ 代码膨胀 (单态化（Monomorphization）)
- ⚠️ 不能运行时（Runtime）切换

### 2.2 性能对比

| 实现方式         | 调用开销       | 内存分配 | 二进制大小  | 灵活性 |
| :--- | :--- | :--- | :--- | :--- |
| **Trait Object** | 1-3ns (虚函数) | 堆分配   | 小          | 运行时 |
| **泛型（Generics）**         | 0ns (内联)     | 栈分配   | 大 (单态化) | 编译时 |

**基准测试** (Criterion):

```rust,ignore
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn trait_object_benchmark(c: &mut Criterion) {
    let compressor = Compressor::new(Box::new(ZipCompression));
    let data = vec![0u8; 1024];

    c.bench_function("trait_object_compress", |b| {
        b.iter(|| compressor.compress(black_box(&data)))
    });
}

fn generic_benchmark(c: &mut Criterion) {
    let compressor = GenericCompressor::new(ZipCompression);
    let data = vec![0u8; 1024];

    c.bench_function("generic_compress", |b| {
        b.iter(|| compressor.compress(black_box(&data)))
    });
}

criterion_group!(benches, trait_object_benchmark, generic_benchmark);
criterion_main!(benches);
```

**典型结果**:

```text
trait_object_compress  time: [125.3 ns ... 128.7 ns]
generic_compress       time: [98.2 ns ... 101.5 ns]  (快 ~22%)
```

---

## 3. 同步 vs 异步实现对比

Observer 模式在同步与异步两种实现下，事件传递的**时间语义**根本不同：同步实现中 `notify` 调用直到所有观察者处理完才返回（调用者被阻塞，错误可同步传播）；异步实现中事件入队即返回，观察者在后续轮次处理（调用者与处理解耦，错误需独立通道回传）。

| 维度 | 同步 Observer | 异步 Observer |
|---|---|---|
| 时序保证 | 通知返回 = 处理完成 | 通知返回 ≠ 处理完成 |
| 背压 | 天然（调用者被阻塞） | 需有界 channel 显式控制 |
| 典型实现 | `Vec<Box<dyn Fn(&E)>>` | `tokio::sync::broadcast` |

性能对比的关键不是吞吐而是尾延迟：同步实现在观察者变慢时拖累发布者；异步实现把抖动转移到队列长度上。判定依据：观察者是 UI 更新等必须有序同步的场景选同步；事件量大且允许延迟选异步。

### 3.1 Observer模式对比

Observer 模式在「同步/异步」两个时序模型下的对比：

- **方式 1：同步 Observer**：`Vec<Box<dyn Fn(&Event)>>` 订阅表，`notify` 同步遍历调用——语义简单（「通知返回时所有观察者已处理」），但单个慢观察者阻塞全体（且观察者中再 `notify` 会重入——借用（Borrowing）检查会拦住对订阅表的可变重入，迫使设计改为「快照订阅表」或「两阶段：收集-派发」）。适用：进程内低延迟事件（GUI、配置变更）。
- **方式 2：异步 Observer**：`tokio::sync::broadcast`（多订阅者各收全量，慢订阅者被「lagged」标记跳过旧消息——内置背压语义）或每订阅者一个 `mpsc`（独立队列，慢订阅者背压到发送方）。语义变化是关键：异步观察者「最终处理」而非「立即处理」——发布者对「处理完成」无同步保证（需 oneshot 回执扩展）。适用：跨任务/跨服务事件、可容忍延迟的副作用（审计、缓存失效）。
- **性能对比**：同步版延迟最低（一次函数调用/观察者）但吞吐受最慢观察者钳制；broadcast 版写路径 O(1)（环形缓冲写一次）但慢订阅者丢消息；mpsc 版内存随订阅者数线性增长。选型按「慢观察者的期望行为」：必须等 → 同步；可跳过 → broadcast；必须不丢且可积压 → mpsc + 有界队列监控。

#### 方式 1：同步Observer

```rust
use std::sync::{Arc, Mutex};

pub trait Observer: Send + Sync {
    fn update(&self, data: &str);
}

pub struct Subject {
    observers: Arc<Mutex<Vec<Arc<dyn Observer>>>>,
}

impl Subject {
    pub fn new() -> Self {
        Self {
            observers: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub fn attach(&self, observer: Arc<dyn Observer>) {
        self.observers.lock().unwrap().push(observer);
    }

    pub fn notify(&self, data: &str) {
        let observers = self.observers.lock().unwrap();
        for observer in observers.iter() {
            observer.update(data); // 同步调用，阻塞
        }
    }
}

/// 使用示例
pub fn sync_observer_example() {
    let subject = Subject::new();

    // 假设观察者处理耗时 10ms
    subject.notify("event"); // 阻塞 10ms * N个观察者
}
```

**特点**:

- ✅ 实现简单
- ✅ 顺序保证
- ⚠️ 阻塞执行
- ⚠️ 慢观察者拖累整体性能

#### 方式 2：异步Observer

```rust,ignore
use tokio::sync::{mpsc, RwLock};
use std::sync::Arc;

pub trait AsyncObserver: Send + Sync {
    async fn update(&self, data: String);
}

pub struct AsyncSubject {
    observers: Arc<RwLock<Vec<Arc<dyn AsyncObserver>>>>,
}

impl AsyncSubject {
    pub fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn attach(&self, observer: Arc<dyn AsyncObserver>) {
        self.observers.write().await.push(observer);
    }

    pub async fn notify(&self, data: String) {
        let observers = self.observers.read().await;

        // 并发通知所有观察者
        let mut handles = Vec::new();
        for observer in observers.iter() {
            let observer = Arc::clone(observer);
            let data = data.clone();

            let handle = tokio::spawn(async move {
                observer.update(data).await;
            });

            handles.push(handle);
        }

        // 等待所有观察者完成
        for handle in handles {
            let _ = handle.await;
        }
    }
}

/// 使用示例
pub async fn async_observer_example() {
    let subject = AsyncSubject::new();

    // 假设观察者处理耗时 10ms
    subject.notify("event".to_string()).await; // 并发执行，总耗时 ~10ms
}
```

**特点**:

- ✅ 非阻塞
- ✅ 并发执行
- ✅ 慢观察者不影响其他观察者
- ⚠️ 顺序不保证
- ⚠️ 复杂度更高

### 3.2 性能对比

| 实现方式 | 通知延迟 (10观察者, 各10ms) | CPU使用率 | 内存开销        |
| :--- | :--- | :--- | :--- || **同步** | 100ms (顺序执行)            | 低        | 低              |
| **异步（Async）** | 10-12ms (并发执行)          | 高        | 中等 (task开销) |

---

## 4. 静态 vs 动态分派对比

工厂模式是观察分派方式差异的最佳样本：泛型工厂 `fn create<T: Widget>() -> T` 在编译期为每个 T 单态化出专用代码，零运行时开销但返回类型必须编译期确定；trait 对象工厂 `fn create() -> Box<dyn Widget>` 运行时经 vtable 分派，支持异构集合与运行时选择，代价是每次调用一次间接跳转且阻断内联。判据一句话：创建时机在编译期可知用泛型，运行时才知道用 trait 对象。

### 4.1 工厂模式对比

静态分派与动态分派的分歧点是**类型信息在编译期还是运行期可用**，工厂模式是展示这一分歧的最佳载体：

- **静态分派（枚举工厂）**: `enum Shape { Circle(f64), Rect(f64, f64) }` + `match`——所有变体编译期已知，`match` 穷尽性由编译器检查，调用内联、无虚表跳转；代价是新增变体需修改枚举定义与所有 `match` 点。
- **动态分派（Trait Object 工厂）**: `Box<dyn Shape>`——新增类型只需实现 trait，无需改动既有代码（开闭原则）；代价是虚表调用无法内联、丢失具体类型信息（除非 downcast）。

| 信号 | 倾向 |
|---|---|
| 变体集合稳定、性能敏感 | 枚举 + 静态分派 |
| 插件式扩展、变体由下游定义 | trait object |

判定依据： Rust 生态中“枚举优先”是默认立场，动态分派是扩展点确实开放时的选择。

#### 静态分派 (枚举)

```rust
/// 产品类型
#[derive(Debug, Clone, Copy)]
pub enum VehicleType {
    Car,
    Motorcycle,
    Truck,
}

/// 产品
#[derive(Debug)]
pub enum Vehicle {
    Car { model: String },
    Motorcycle { cc: u32 },
    Truck { capacity: u32 },
}

impl Vehicle {
    pub fn create(vehicle_type: VehicleType) -> Self {
        match vehicle_type {
            VehicleType::Car => Vehicle::Car { model: "Sedan".to_string() },
            VehicleType::Motorcycle => Vehicle::Motorcycle { cc: 600 },
            VehicleType::Truck => Vehicle::Truck { capacity: 5000 },
        }
    }

    pub fn drive(&self) {
        match self {
            Vehicle::Car { model } => println!("Driving car: {}", model),
            Vehicle::Motorcycle { cc } => println!("Riding motorcycle: {}cc", cc),
            Vehicle::Truck { capacity } => println!("Driving truck: {}kg", capacity),
        }
    }
}

/// 使用示例
pub fn static_dispatch_example() {
    let car = Vehicle::create(VehicleType::Car);
    car.drive(); // 静态分派，编译时确定
}
```

**特点**:

- ✅ 零成本
- ✅ 完全内联
- ✅ 编译时优化
- ⚠️ 扩展需修改代码

#### 动态分派 (Trait Object)

```rust
pub trait Vehicle {
    fn drive(&self);
}

pub struct Car { model: String }
pub struct Motorcycle { cc: u32 }
pub struct Truck { capacity: u32 }

impl Vehicle for Car {
    fn drive(&self) {
        println!("Driving car: {}", self.model);
    }
}

impl Vehicle for Motorcycle {
    fn drive(&self) {
        println!("Riding motorcycle: {}cc", self.cc);
    }
}

impl Vehicle for Truck {
    fn drive(&self) {
        println!("Driving truck: {}kg", self.capacity);
    }
}

pub fn create_vehicle(vehicle_type: &str) -> Box<dyn Vehicle> {
    match vehicle_type {
        "car" => Box::new(Car { model: "Sedan".to_string() }),
        "motorcycle" => Box::new(Motorcycle { cc: 600 }),
        "truck" => Box::new(Truck { capacity: 5000 }),
        _ => panic!("Unknown vehicle type"),
    }
}

/// 使用示例
pub fn dynamic_dispatch_example() {
    let car = create_vehicle("car");
    car.drive(); // 动态分派，运行时确定
}
```

**特点**:

- ✅ 易于扩展
- ✅ 插件友好
- ⚠️ 虚函数开销
- ⚠️ 堆分配

---

## 5. 单线程 vs 多线程实现对比

单例模式在 Rust 中因所有权模型而变形，单线程与多线程实现的安全性来源完全不同：

- **单线程**: `thread_local! { static INSTANCE: RefCell<T> = ... }`——无同步开销，但实例不能跨线程传递，本质是“线程局部单例”。
- **多线程**: `static INSTANCE: LazyLock<Mutex<T>> = LazyLock::new(...)`（1.80+ 稳定）——`LazyLock` 保证初始化恰好一次（一次性初始化由 `OnceLock` 语义支撑），`Mutex` 提供内部可变性。

| 维度 | 单线程 | 多线程 |
|---|---|---|
| 同步原语 | 无（`RefCell`） | `Mutex`/`RwLock` |
| 初始化竞争 | 不存在 | 由 `LazyLock` 消除 |
| 性能 | 零开销 | 每次访问有锁开销 |

判定依据：全局状态本身应被质疑——能传参就别用单例；必须用且跨线程时 `LazyLock` 是唯一推荐路径（`lazy_static` crate 已被标准库取代）。

### 5.1 单例模式对比

单例模式在「单线程/多线程」两个并发模型下的对比，核心是「初始化时机 × 同步成本」：

- **单线程单例**：`thread_local! { static X: RefCell<T> = ... }`——每线程一份，无同步成本，但「单例」语义缩为「线程内单例」；或函数内 `static mut`（2024 edition 起引用（Reference）受限）/`static X: RefCell`（非 Sync，只能单线程用——`!Sync` 由类型系统（Type System）强制，误跨线程是编译错误）。
- **多线程单例**：**`std::sync::OnceLock<T>`**（Rust 1.70 稳定——一次初始化 + 无锁读：`get_or_init(f)` 保证 `f` 全局恰好执行一次，读路径是一个原子 load）与 **`once_cell::sync::Lazy`**/`LazyLock`（1.80 稳定为 `std::sync::LazyLock`——首次解引用时初始化，语义更贴近「惰性字段」）。历史方案 `lazy_static!` 宏（Macro）已被 std 原生机制取代。初始化可能失败的场景用 `OnceLock::get_or_try_init`（nightly）或自旋重试模式。
- **性能对比**：`OnceLock` 读 ≈ 一次 `Acquire` 原子 load（x86 上同普通 load）；`Mutex<Option<T>>` 手写版每次访问一次加锁（无竞争 ~20ns）——十倍差距在热路径可观。选型判定：初始化无副作用且值常量 → `const`/`static`（零机制）；惰性 + 不可失败 → `LazyLock`；需显式控制初始化时机/参数 → `OnceLock::get_or_init`。

#### 单线程单例

```rust
use std::cell::RefCell;

/// 单线程单例
pub struct SingleThreadSingleton {
    value: i32,
}

thread_local! {
    static INSTANCE: RefCell<Option<SingleThreadSingleton>> = RefCell::new(None);
}

impl SingleThreadSingleton {
    pub fn get_or_init() -> i32 {
        INSTANCE.with(|instance| {
            let mut instance = instance.borrow_mut();
            if instance.is_none() {
                *instance = Some(SingleThreadSingleton { value: 42 });
            }
            instance.as_ref().unwrap().value
        })
    }
}

/// 使用示例
pub fn single_thread_example() {
    let value = SingleThreadSingleton::get_or_init();
    println!("Value: {}", value);
}
```

**特点**:

- ✅ 无同步开销
- ✅ 快速访问
- ⚠️ 仅限单线程
- ⚠️ 不实现 Send/Sync

#### 多线程单例

```rust
use std::sync::OnceLock;

/// 多线程单例
pub struct MultiThreadSingleton {
    value: i32,
}

static INSTANCE: OnceLock<MultiThreadSingleton> = OnceLock::new();

impl MultiThreadSingleton {
    pub fn get_or_init() -> &'static MultiThreadSingleton {
        INSTANCE.get_or_init(|| MultiThreadSingleton { value: 42 })
    }
}

/// 使用示例
pub fn multi_thread_example() {
    use std::thread;

    let handles: Vec<_> = (0..10)
        .map(|_| {
            thread::spawn(|| {
                let singleton = MultiThreadSingleton::get_or_init();
                println!("Value: {}", singleton.value);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

**特点**:

- ✅ 线程安全
- ✅ 实现 Send + Sync
- ⚠️ 首次访问有同步开销
- ⚠️ 后续访问几乎零成本

### 5.2 性能对比

| 实现方式   | 首次访问         | 后续访问        | 线程安全 | 适用场景   |
| :--- | :--- | :--- | :--- | :--- || **单线程** | ~1ns             | ~1ns            | ❌       | 单线程应用 |
| **多线程** | ~50-100ns (同步) | ~2-5ns (原子读) | ✅       | 多线程应用 |

---

## 6. 零成本 vs 运行时抽象对比

Rust 迭代器是零成本抽象（Zero-Cost Abstraction）的教科书案例：`iter.map(f).filter(g).collect()` 经 LLVM 优化后与手写循环生成相同机器码，因为每个适配器都是具体类型、调用全部可内联。对比运行时抽象（如 Java 的 Stream 或动态分派的迭代器接口），差异在两点：编译期类型完整可见使优化器能做全局内联与逃逸分析；无虚表查找使分支预测更准。性能对比数据通常显示 1-3 倍差距，且随链长增加而扩大。

### 6.1 迭代器模式对比

迭代器模式是「零成本抽象」在 Rust 中最经典的验证场：

- **泛型迭代器**：`fn sum<I: Iterator<Item = u64>>(it: I) -> u64` 编译后展开为与手写循环逐指令等价的机器码（LLVM 对内联迭代器链做完整融合），这是「零成本」的精确含义——**你没有使用的特性不付出代价，使用的特性不比手写代码慢**。
- **装箱迭代器 `Box<dyn Iterator>`**：每次 `next()` 走虚表，迭代器链的融合优化被完全阻断，吞吐可下降 2–10 倍（取决于元素处理成本）。

判定依据：库 API 返回迭代器时用 `impl Iterator<Item = T>`（静态分派且隐藏具体类型）；只有需要存储迭代器或返回多种迭代器类型时才装箱。测量工具：`cargo asm` 对比汇编，或 Criterion 对比吞吐。

#### 零成本抽象 (泛型迭代器)

```rust
/// 零成本迭代器链
pub fn zero_cost_iterator(data: &[i32]) -> i32 {
    data.iter()
        .filter(|&&x| x > 0)     // 编译时内联
        .map(|&x| x * 2)         // 编译时内联
        .sum()                   // 编译时优化
}

/// 使用示例
pub fn zero_cost_example() {
    let data = vec![1, -2, 3, -4, 5];
    let result = zero_cost_iterator(&data);
    println!("Result: {}", result); // Result: 18
}
```

**汇编输出** (优化后):

```asm
; 编译器直接生成优化后的循环
; 无函数调用，完全内联
mov     eax, 0
.loop:
    cmp     [data + rcx], 0
    jle     .skip
    mov     edx, [data + rcx]
    add     edx, edx
    add     eax, edx
.skip:
    add     rcx, 4
    cmp     rcx, len
    jl      .loop
```

#### 运行时抽象 (Boxed迭代器)

```rust
/// 运行时抽象迭代器
pub fn runtime_iterator(data: &[i32]) -> Box<dyn Iterator<Item = i32> + '_> {
    Box::new(
        data.iter()
            .filter(|&&x| x > 0)
            .map(|&x| x * 2)
    )
}

/// 使用示例
pub fn runtime_example() {
    let data = vec![1, -2, 3, -4, 5];
    let iter = runtime_iterator(&data);
    let result: i32 = iter.sum();
    println!("Result: {}", result);
}
```

**特点**:

- ⚠️ 堆分配
- ⚠️ 虚函数调用
- ⚠️ 无法内联

### 6.2 性能对比

| 实现方式   | 执行时间 (100万元素) | 内存分配 | 编译器优化  |
| :--- | :--- | :--- | :--- || **零成本** | 0.5ms                | 0        | ✅ 完全内联 |
| **运行时** | 2.1ms (慢 ~4.2x)     | 堆分配   | ❌ 无法内联 |

**Criterion基准测试**:

```rust,ignore
fn benchmark_iterators(c: &mut Criterion) {
    let data: Vec<i32> = (0..1_000_000).collect();

    c.bench_function("zero_cost_iterator", |b| {
        b.iter(|| zero_cost_iterator(black_box(&data)))
    });

    c.bench_function("runtime_iterator", |b| {
        b.iter(|| {
            let iter = runtime_iterator(black_box(&data));
            iter.sum::<i32>()
        })
    });
}
```

**结果**:

```text
zero_cost_iterator     time: [485.2 μs ... 491.3 μs]
runtime_iterator       time: [2.08 ms ... 2.13 ms]
                       change: +328.9% (慢 4.2x)
```

---

## 7. 内存模型对比

不同模式对所有权的使用策略直接影响内存开销：独占所有权（移动语义）零额外开销但限制共享；`Rc<RefCell<T>>` 用单线程引用计数加运行时借用检查换取共享可变性（16 字节控制块 + 运行时 panic 风险）；`Arc<Mutex<T>>` 用原子计数与互斥锁换取跨线程共享（原子操作（Atomic Operations） + 锁竞争成本）。内存开销对比不仅看字节数，更要看缓存局部性——控制块与数据分离分配会造成额外 cache miss。

### 7.1 所有权模式对比

所有权模式的选择决定了 API 的性能上限与易用性下限，四种方式按成本递增排列：

1. **不可变借用（Immutable Borrow） `&T`**：零成本，适用于只读访问；并发友好（可多读者）。
2. **可变借用（Mutable Borrow） `&mut T`**：零成本且编译期排他，适合原地变换（如 `sort`、`push`）；代价是调用点不能有其他别名。
3. **所有权转移 `T`**：适合消费型 API（builder、转换 `into_*`）；配合移动语义无拷贝，但调用者失去原值。
4. **克隆 `Clone`**：最贵但最灵活；对 `Vec`/`String` 是深拷贝，对 `Arc` 只是原子计数 +1——**克隆前先问类型**。

判定口诀：能用 `&` 不用 `&mut`，能用 `&mut` 不转移所有权，转移所有权优于 `Clone` 深拷贝。API 设计时应让「借用版」与「消费版」成对出现（如 `sort`/`sorted` 风格）。

#### 方式 1：所有权转移 (Move)

```rust
/// 所有权转移
pub fn take_ownership(data: Vec<u8>) -> Vec<u8> {
    // data 被移动进来
    println!("Processing {} bytes", data.len());
    data // 返回所有权
}

pub fn move_example() {
    let data = vec![1, 2, 3];
    let data = take_ownership(data); // 所有权转移，零成本
    // data 现在可用
}
```

**特点**:

- ✅ 零成本
- ✅ 无内存拷贝
- ⚠️ 原变量失效

#### 方式 2：不可变借用（Immutable Borrow）

```rust
/// 不可变借用
pub fn borrow_immutable(data: &Vec<u8>) -> usize {
    println!("Processing {} bytes", data.len());
    data.len()
}

pub fn borrow_example() {
    let data = vec![1, 2, 3];
    let len = borrow_immutable(&data); // 借用，零成本
    // data 仍然可用
    println!("Original data: {:?}", data);
}
```

**特点**:

- ✅ 零成本
- ✅ 原变量仍可用
- ⚠️ 无法修改

#### 方式 3：可变借用（Mutable Borrow）

```rust
/// 可变借用
pub fn borrow_mutable(data: &mut Vec<u8>) {
    data.push(4);
    println!("Added element");
}

pub fn mut_borrow_example() {
    let mut data = vec![1, 2, 3];
    borrow_mutable(&mut data); // 可变借用，零成本
    // data 已被修改
    println!("Modified data: {:?}", data);
}
```

**特点**:

- ✅ 零成本
- ✅ 可修改
- ⚠️ 借用（Borrowing）期间无法同时访问

#### 方式 4：克隆 (Clone)

```rust
/// 克隆
pub fn clone_data(data: &Vec<u8>) -> Vec<u8> {
    data.clone() // 深拷贝
}

pub fn clone_example() {
    let data = vec![1, 2, 3];
    let cloned = clone_data(&data); // 克隆，有成本
    // 两份独立数据
    println!("Original: {:?}, Cloned: {:?}", data, cloned);
}
```

**特点**:

- ⚠️ 有成本 (内存拷贝)
- ✅ 独立数据
- ✅ 并发安全（Concurrency Safety）

### 7.2 内存开销对比

| 模式           | 内存拷贝 | CPU开销 | 适用场景     |
| :--- | :--- | :--- | :--- || **Move**       | 0        | 0       | 转移所有权（Ownership）   |
| **Borrow**     | 0        | 0       | 只读访问     |
| **Mut Borrow** | 0        | 0       | 读写访问     |
| **Clone**      | O(n)     | O(n)    | 需要独立副本 |

---

## 8. 性能开销对比

本页的综合性能对比按「机制 × 成本维度」汇总，选型决策树把各组对比收敛为单一流程：

**综合性能对比表**（典型数量级，x86_64 opt-level=3）：

| 机制 | 调用开销 | 内存开销 | 可内联 | 类型集 |
|:---|:---|:---|:---|:---|
| 泛型单态化 | 0（直接调用） | 代码膨胀 N 份 | ✅ | 编译期闭合 |
| `&dyn Trait` | 2–5ns 间接跳转 | +1 字胖指针 | ❌ | 运行期开放 |
| `Box<dyn Trait>` | 同上 + 堆分配一次 | 堆 + 胖指针 | ❌ | 运行期开放 |
| enum + match | 0–1 分支预测 | 最大变体大小 | ✅ | 编译期闭合 |
| `OnceLock` 单例 | ~1 原子 load | 值 + 状态字 | ✅ 读路径 | — |

**选择决策树**：

```text
变化点（策略/实现）在编译期可知且集合闭合？
├─ 是 → 需要「同类型多实例共存」？
│      ├─ 是 → enum + match（同一类型，模式分派）
│      └─ 否 → 泛型（每实例独立类型，零成本）
└─ 否（插件/异构容器/运行时注册）→
       需要共享/长寿命？├─ 是 → Arc<dyn Trait>
                       └─ 否 → Box<dyn Trait> 或 &dyn Trait
```

决策树的根问题「编译期闭合？」是 GoF 模式在 Rust 中一切机制选择的分水岭——它同时决定性能上限（可内联性）与表达能力（异构共存），不存在「两边最优」的机制。

### 8.1 综合性能对比表

| 模式          | 实现方式     | 调用开销 | 内存开销 | 灵活性 | 类型安全 | 推荐指数   |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- || **Singleton** | OnceLock     | ~2-5ns   | 静态     | 低     | ✅       | ⭐⭐⭐⭐⭐ |
| **Factory**   | 泛型（Generics）         | 0ns      | 栈       | 中     | ✅       | ⭐⭐⭐⭐⭐ |
| **Factory**   | Trait Object | ~2ns     | 堆       | 高     | ✅       | ⭐⭐⭐⭐   |
| **Builder**   | 链式调用     | 0ns      | 栈       | 高     | ✅       | ⭐⭐⭐⭐⭐ |
| **Observer**  | 同步         | ~1ns     | 低       | 中     | ✅       | ⭐⭐⭐     |
| **Observer**  | 异步（Async）         | ~1000ns  | 中       | 高     | ✅       | ⭐⭐⭐⭐⭐ |
| **Strategy**  | 泛型         | 0ns      | 栈       | 低     | ✅       | ⭐⭐⭐⭐⭐ |
| **Strategy**  | Trait Object | ~2ns     | 堆       | 高     | ✅       | ⭐⭐⭐⭐   |
| **Iterator**  | 零成本       | 0ns      | 栈       | 高     | ✅       | ⭐⭐⭐⭐⭐ |
| **Decorator** | 泛型         | 0ns      | 栈       | 低     | ✅       | ⭐⭐⭐⭐   |

### 8.2 选择决策树

```text
需要设计模式？
├─ 性能关键路径？
│  ├─ 是 → 泛型/零成本抽象
│  └─ 否 → Trait Object
│
├─ 需要运行时切换？
│  ├─ 是 → Trait Object/枚举
│  └─ 否 → 泛型
│
├─ 需要并发？
│  ├─ 是 → async/await + Arc
│  └─ 否 → 同步实现
│
└─ 需要扩展性？
   ├─ 是 → Trait + 插件
   └─ 否 → 枚举/泛型
```

---

## 9. 实测示例：静态 vs 动态分派的语义等价与成本边界（2026-07-12 回填）

> **来源**: [TRPL — Using Trait Objects That Allow for Values of Different Types](https://doc.rust-lang.org/book/ch17-02-trait-objects.html) · [Rust Reference — Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html)

§2–§4 对比了 trait 泛型与 trait 对象的实现形态。以下实测证明二者**语义等价、成本不同**：同一 `area()` 逻辑经静态分派（单态化）与动态分派（vtable）调用结果一致，但前者零运行时间接、后者一次指针跳转。rustc 1.97.0 `--edition 2024` 实测：

```rust
trait Shape { fn area(&self) -> f64; }
struct Circle { r: f64 }
impl Shape for Circle {
    fn area(&self) -> f64 { std::f64::consts::PI * self.r * self.r }
}

// 静态分派：编译期为每个 T 单态化一份，无 vtable
fn total_static<T: Shape>(shapes: &[T]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}
// 动态分派：经 &dyn Shape 的 vtable 间接调用
fn total_dynamic(shapes: &[&dyn Shape]) -> f64 {
    shapes.iter().map(|s| s.area()).sum()
}

fn main() {
    let c1 = Circle { r: 2.0 };
    let c2 = Circle { r: 2.0 };
    let a = total_static(&[c1]);
    let b = total_dynamic(&[&c2]);
    assert!((a - b).abs() < 1e-9); // 语义等价
}
```

选型决策（与 §8 性能开销对比呼应）：

- 同构集合 + 性能敏感 → 静态分派（单态化，可内联）；
- 异构集合 / 插件边界 / 二进制体积敏感 → 动态分派（vtable，一次间接）；
- 动态分派的真正成本不只是间接跳转，还包括**阻止内联**后的优化视野丢失（参见 [Dispatch Mechanisms](../../02_intermediate/00_traits/02_dispatch_mechanisms.md)）。

> **权威来源**: [TRPL — Trait Objects](https://doc.rust-lang.org/book/ch17-02-trait-objects.html) · [Rust Reference — Trait Object Types](https://doc.rust-lang.org/reference/types/trait-object.html)（链接 2026-07-12 curl 实测 200；代码 rustc 1.97.0 实测）

---

## 📚 相关资源

---

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>

## 过渡段

> **过渡**: 从模式意图过渡到 trait 与泛型实现，可以理解 Rust 中“接口与实现”的两种主要组织方式。
>
> **过渡**: 从同步/异步选择过渡到并发模型，可以建立性能与复杂度之间的权衡视角。
>
> **过渡**: 从静态/动态分发过渡到可维护性，可以评估长期演进成本与运行时性能。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 泛型实现 ⟹ 零成本运行时 | 编译期单态化 | 性能最优但二进制体积增大 |
| Trait Object 实现 ⟹ 运行时多态 | 通过 vtable 动态分发 | 提升灵活性并减少代码膨胀 |
| async 变体 ⟹ 可扩展并发 | 与异步运行时集成 | 适合高并发 I/O 场景 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Design Patterns: Elements of Reusable Object-Oriented Software (GoF, ACM DL)](https://dl.acm.org/doi/book/10.5555/95489)
- **P2 生态/社区**: [The Pragmatic Bookshelf](https://pragprog.com) · [Microservices.io — 架构模式](https://microservices.io)

## ⚠️ 反例与陷阱

本节以捕获闭包强转 `fn` 指针为反例，展示 Strategy 模式实现中函数指针与闭包的类型边界。

### 反例：捕获闭包不能强转为 `fn` 指针（Strategy 模式）（rustc 1.97.0 实测）

```rust,compile_fail,E0308
fn apply(f: fn(i32) -> i32, x: i32) -> i32 { f(x) }

fn main() {
    let factor = 3;
    let mul = |x| x * factor; // ❌ 捕获环境，不是 fn 指针
    println!("{}", apply(mul, 4));
}
```

**错误**：`E0308 mismatched types: expected fn pointer, found closure`。

### ✅ 修正：参数改为泛型 `Fn` 约束

```rust
fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 { f(x) }

fn main() {
    let factor = 3;
    let mul = |x| x * factor;
    println!("{}", apply(mul, 4)); // 捕获闭包与普通函数统一接受
}
```

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((模式实现对比 Pattern))
    Trait vs 泛型实现对比
      Strategy模式对比
      性能对比
    同步 vs 异步实现对比
      Observer模式对比
      性能对比
    单线程 vs 多线程实现对比
      单例模式对比
      性能对比
    零成本 vs 运行时抽象对比
      迭代器模式对比
      性能对比
    内存模型对比
      所有权模式对比
      内存开销对比
```

> **认知功能**: 本 mindmap 从本页「模式实现对比 Pattern」的章节结构提炼，一级分支对应核心主题，叶子节点为关键子概念，可作为本页的快速导航与复习索引。
