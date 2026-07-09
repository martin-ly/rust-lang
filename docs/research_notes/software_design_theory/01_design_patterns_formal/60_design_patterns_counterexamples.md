# 设计模式反例边界 {#设计模式反例边界}

> **EN**: Design Patterns Counterexamples
> **Summary**: 设计模式反例边界 Design Patterns Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6 (分析/评价)
> **概念族**: 设计模式 / 反例边界
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [设计模式反例边界 {#设计模式反例边界}](#设计模式反例边界-设计模式反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. 单例模式导致全局可变状态 {#1-单例模式导致全局可变状态}](#1-单例模式导致全局可变状态-1-单例模式导致全局可变状态)
    - [现象 {#现象-6}](#现象-现象-6)
    - [问题 {#问题-6}](#问题-问题-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. Observer 模式生命周期（Lifetimes）管理不当 {#2-observer-模式生命周期管理不当}](#2-observer-模式生命周期管理不当-2-observer-模式生命周期管理不当)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [问题 {#问题-6}](#问题-问题-6-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. 滥用内部可变性 {#3-滥用内部可变性}](#3-滥用内部可变性-3-滥用内部可变性)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [问题 {#问题-6}](#问题-问题-6-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. Builder 模式缺失必要字段验证 {#4-builder-模式缺失必要字段验证}](#4-builder-模式缺失必要字段验证-4-builder-模式缺失必要字段验证)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [问题 {#问题-6}](#问题-问题-6-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. 错误使用 `Deref` 模拟继承 {#5-错误使用-deref-模拟继承}](#5-错误使用-deref-模拟继承-5-错误使用-deref-模拟继承)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [问题 {#问题-6}](#问题-问题-6-4)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. 过度泛型（Generics）化 {#6-过度泛型化}](#6-过度泛型化-6-过度泛型化)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [问题 {#问题-6}](#问题-问题-6-5)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. 错误选择 Arc/Mutex 粒度 {#7-错误选择-arcmutex-粒度}](#7-错误选择-arcmutex-粒度-7-错误选择-arcmutex-粒度)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [问题 {#问题-6}](#问题-问题-6-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 1. 单例模式导致全局可变状态 {#1-单例模式导致全局可变状态}

### 现象 {#现象-6}

```rust
use std::sync::Mutex;

static CONFIG: Mutex<AppConfig> = Mutex::new(AppConfig::default());

fn update_config(c: AppConfig) {
    *CONFIG.lock().unwrap() = c;
}
```

### 问题 {#问题-6}

- 隐藏依赖，测试困难。
- 全局锁成为瓶颈。
- 初始化顺序和 panic 恢复难以控制。

### 修复方案 {#修复方案-6}

- 显式传递 `Arc<AppConfig>` 或上下文对象。
- 使用 `OnceLock` / `LazyLock` 做只读全局初始化，避免运行时（Runtime）可变。
- 将可变状态局部化。

---

## 2. Observer 模式生命周期管理不当 {#2-observer-模式生命周期管理不当}

### 现象 {#现象-6}

```rust
struct Subject<'a> {
    observers: Vec<&'a dyn Observer>, // ❌ 观察者生命周期耦合过紧
}
```

### 问题 {#问题-6}

- 难以动态增删观察者。
- 容易因生命周期不匹配导致编译失败或悬垂引用（Reference）。

### 修复方案 {#修复方案-6}

- 使用 `Weak<dyn Observer>` 或 channel（`tokio::sync::mpsc`）解耦。
- 或让 Subject 拥有 Observer：`Vec<Box<dyn Observer>>`。

---

## 3. 滥用内部可变性 {#3-滥用内部可变性}

### 现象 {#现象-6}

```rust
struct Counter {
    value: RefCell<i32>,
}

impl Counter {
    fn increment(&self) {
        *self.value.borrow_mut() += 1;
    }
}
```

### 问题 {#问题-6}

`RefCell` 将编译期检查推迟到运行时，可能 panic：

```rust
let c = Counter { value: RefCell::new(0) };
let a = c.value.borrow();
let b = c.value.borrow_mut(); // ❌ 运行时 panic
```

### 修复方案 {#修复方案-6}

- 优先使用 `&mut self` 暴露可变接口。
- 仅在共享所有权（Ownership）且无法使用 `&mut` 时使用 `RefCell` / `Mutex`。

---

## 4. Builder 模式缺失必要字段验证 {#4-builder-模式缺失必要字段验证}

### 现象 {#现象-6}

```rust
let req = RequestBuilder::new()
    .method("GET")
    .build(); // ❌ 缺少 url
```

### 问题 {#问题-6}

- 运行时才发现必要字段缺失。
- 破坏 Builder 的类型安全优势。

### 修复方案 {#修复方案-6}

- 使用类型状态模式：只有设置 url 后才能调用 `build()`。
- 或让 `build()` 返回 `Result<Request, BuilderError>`。

---

## 5. 错误使用 `Deref` 模拟继承 {#5-错误使用-deref-模拟继承}

### 现象 {#现象-6}

```rust
struct Admin(User);

impl Deref for Admin {
    type Target = User;
    fn deref(&self) -> &User { &self.0 }
}

impl Admin {
    fn ban_user(&self) {
        // 通过 Deref 调用 User 方法，逻辑上像继承
    }
}
```

### 问题 {#问题-6}

- `Deref` 应仅用于智能指针（Smart Pointer）语义，不能表达 is-a 关系。
- 滥用会导致 API 表面不可控，违反 API Guidelines。

### 修复方案 {#修复方案-6}

- 使用组合 + 显式转发方法。
- 若需多态，使用 trait + `dyn Trait`。

---

## 6. 过度泛型化 {#6-过度泛型化}

### 现象 {#现象-6}

```rust
trait Processor<I, O, E, C, S>
where
    E: Error,
    C: Context<S>,
    S: Settings,
{
    fn process(&self, input: I, ctx: &C) -> Result<O, E>;
}
```

### 问题 {#问题-6}

- 类型参数过多，调用方负担大。
- 编译错误信息复杂，可读性差。

### 修复方案 {#修复方案-6}

- 合并相关参数到单一上下文类型。
- 使用关联类型减少泛型参数。
- 必要时用 `dyn Trait` 简化接口。

---

## 7. 错误选择 Arc/Mutex 粒度 {#7-错误选择-arcmutex-粒度}

### 现象 {#现象-6}

```rust
struct Service {
    data: Arc<Mutex<HashMap<String, Vec<User>>>>,
}
```

### 问题 {#问题-6}

- 所有读写共用一把大锁，并发度低。
- `Vec` 操作也可能阻塞其他 key 的访问。

### 修复方案 {#修复方案-6}

- 使用 `RwLock` 或 `DashMap`。
- 拆分锁粒度：每个 key 一个 `Mutex<Vec<User>>`。
- 对读多写少场景使用 `Arc<ArcSwap>` 或 `RwLock`。

---

## 总结 {#总结}

| 反例 | 涉及模式 | 问题 | 修复方向 |
|------|----------|------|----------|
| 全局可变状态 | 单例 | 隐藏依赖、瓶颈 | 依赖注入 / 只读全局 |
| 生命周期耦合 Observer | Observer | 动态管理困难 | Weak / channel |
| 滥用 RefCell | 内部可变性 | 运行时（Runtime） panic | 优先 `&mut self` |
| Builder 缺失验证 | Builder | 运行时错误 | 类型状态 / Result |
| Deref 模拟继承 | 组合 | API 不可控 | 显式转发 / trait |
| 过度泛型化 | 泛型设计 | 可读性差 | 关联类型 / 上下文对象 |
| 锁粒度过大 | 并发架构 | 性能瓶颈 | 拆分锁 / DashMap |

> **权威来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [The Rust Programming Language – Ch 17](https://doc.rust-lang.org/book/ch17-00-oop.html) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [Rustonomicon – Interior Mutability](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)

## 相关概念 {#相关概念}

- [设计模式形式化 README](README.md)
- [边界矩阵](04_boundary_matrix.md)
- [模块（Module）系统代码实践](../../formal_modules/70_module_patterns_and_refactoring.md)
- [并发与异步（Async）反例](../../formal_methods/60_concurrency_async_counterexamples.md)
- [知识图谱索引](../../10_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../../10_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
- [Refactoring Guru](https://refactoring.guru/design-patterns)

## 学术权威参考 {#学术权威参考}

- [Aeneas](https://aeneas-verification.github.io/)
- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
