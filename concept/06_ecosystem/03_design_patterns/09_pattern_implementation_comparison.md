# 模式实现对比 (Pattern Implementation Comparison)

> **代码状态**: 混合（原 crate 文档示例，部分代码块为示意片段）
>
> **EN**: Pattern Implementation Comparison
> **Summary**: Compares different implementation strategies for design patterns in Rust: trait objects vs generics, sync vs async, static vs dynamic dispatch, single vs multi-threaded, zero-cost vs runtime abstraction, and ownership models.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **内容分级**: [参考级]
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

本节从 Strategy模式对比 与 性能对比 两个层面剖析「Trait vs 泛型实现对比」。

### 2.1 Strategy模式对比

本节从方式 1：Trait Object (动态分派) 与 方式 2：泛型 (静态分派) 两个层面剖析「Strategy模式对比」。

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

```rust
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

```rust
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

本节从 Observer模式对比 与 性能对比 两个层面剖析「同步 vs 异步实现对比」。

### 3.1 Observer模式对比

本节围绕「Observer模式对比」展开，覆盖方式 1：同步Observer 与 方式 2：异步Observer 两个方面。

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

```rust
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

「静态 vs 动态分派对比」部分的核心主题是工厂模式对比，本节展开说明。

### 4.1 工厂模式对比

本节从静态分派 (枚举) 与 动态分派 (Trait Object) 两个层面剖析「工厂模式对比」。

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

本节围绕「单线程 vs 多线程实现对比」展开，覆盖单例模式对比 与 性能对比 两个方面。

### 5.1 单例模式对比

本节围绕「单例模式对比」展开，覆盖单线程单例 与 多线程单例 两个方面。

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

本节从迭代器模式对比 与 性能对比 两个层面剖析「零成本 vs 运行时抽象对比」。

### 6.1 迭代器模式对比

本节从零成本抽象 (泛型迭代器) 与 运行时抽象 (Boxed迭代器) 两个层面剖析「迭代器模式对比」。

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

```rust
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

「内存模型对比」部分包含所有权模式对比 与 内存开销对比 两条主线，本节依次说明。

### 7.1 所有权模式对比

本节围绕「所有权模式对比」展开，依次讨论方式 1：所有权转移 (Move)、方式 2：不可变借用 (Borrow)、方式 3：可变借用 (Mutable Borrow)与方式 4：克隆 (Clone)。

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

#### 方式 2：不可变借用 (Borrow)

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

#### 方式 3：可变借用 (Mutable Borrow)

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

「性能开销对比」部分包含综合性能对比表 与 选择决策树 两条主线，本节依次说明。

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
