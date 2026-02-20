# 设计模式快速参考卡片

**模块**: C09 Design Patterns
**Rust 版本**: 1.93.0+
**最后更新**: 2026-01-27

---

## 📋 目录

- [设计模式快速参考卡片](#设计模式快速参考卡片)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
    - [单例模式](#单例模式)
    - [工厂模式](#工厂模式)
  - [📋 常用模式](#-常用模式)
    - [创建型模式](#创建型模式)
    - [结构型模式](#结构型模式)
    - [行为型模式](#行为型模式)
  - [🦀 Rust 特有模式](#-rust-特有模式)
    - [Newtype 模式](#newtype-模式)
    - [RAII 模式](#raii-模式)
    - [类型状态模式](#类型状态模式)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 过度使用设计模式](#反例-1-过度使用设计模式)
    - [反例 2: Builder 缺少必填字段校验](#反例-2-builder-缺少必填字段校验)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与决策树](#形式化理论与决策树)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始

### 单例模式

```rust
use std::sync::{Arc, Mutex, OnceLock};

static INSTANCE: OnceLock<Arc<Mutex<Singleton>>> = OnceLock::new();

struct Singleton {
    data: i32,
}

impl Singleton {
    fn get_instance() -> Arc<Mutex<Self>> {
        INSTANCE.get_or_init(|| {
            Arc::new(Mutex::new(Singleton { data: 42 }))
        }).clone()
    }
}
```

### 工厂模式

```rust
trait Product {
    fn operation(&self) -> String;
}

fn create_product(t: ProductType) -> Box<dyn Product> {
    match t {
        ProductType::A => Box::new(ConcreteProductA),
        ProductType::B => Box::new(ConcreteProductB),
    }
}
```

---

## 📋 常用模式

### 创建型模式

| 模式       | Rust 实现                    | 使用场景       |
| :--- | :--- | :--- || **单例**   | `OnceLock` + `Arc<Mutex<T>>` | 全局配置、日志 |
| **工厂**   | `match` + `Box<dyn Trait>`   | 多态对象创建   |
| **建造者** | 链式方法                     | 复杂对象构建   |

### 结构型模式

| 模式       | Rust 实现                   | 使用场景     |
| :--- | :--- | :--- || **适配器** | `impl NewTrait for OldType` | 接口转换     |
| **装饰器** | 包装器结构体                | 功能扩展     |
| **外观**   | 统一接口                    | 简化复杂系统 |

### 行为型模式

| 模式       | Rust 实现                | 使用场景 |
| :--- | :--- | :--- || **策略**   | `Box<dyn Strategy>`      | 算法选择 |
| **观察者** | `Vec<Arc<dyn Observer>>` | 事件通知 |
| **命令**   | `Box<dyn Command>`       | 操作封装 |

---

## 🦀 Rust 特有模式

### Newtype 模式

```rust
struct UserId(u32);
struct OrderId(u32);

fn process_user(id: UserId) {
    // 类型安全
}
```

### RAII 模式

```rust
struct FileHandle {
    file: std::fs::File,
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        // 自动清理
    }
}
```

### 类型状态模式

```rust
struct Door<State> {
    state: State,
}

struct Open;
struct Closed;

impl Door<Closed> {
    fn open(self) -> Door<Open> {
        Door { state: Open }
    }
}
```

---

## 🚫 反例速查

### 反例 1: 过度使用设计模式

**错误示例**:

```rust
// 简单需求却引入 Builder、Factory、Strategy 等
struct Config;
impl Config {
    fn new() -> Self { Self }
    fn with_a(mut self, _: i32) -> Self { self }
}
```

**原因**: 简单场景过度抽象增加复杂度。

**修正**: 按需引入模式，避免为用而用。

---

### 反例 2: Builder 缺少必填字段校验

**错误示例**:

```rust
let c = Config::builder().build();  // ❌ 必填 host 未设置
```

**原因**: 编译期无法保证必填字段。

**修正**: 将必填字段放入 `new()`，或 `build()` 返回 `Result` 校验。

---

## 📚 相关文档

- [设计模式完整文档](../../../crates/c09_design_pattern/docs/)
- [设计模式 README](../../../crates/c09_design_pattern/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c09_design_pattern/examples/`，可直接运行（例如：`cargo run -p c09_design_pattern --example oncelock_singleton_comprehensive`）。

- [单例与 OnceLock](../../../crates/c09_design_pattern/examples/oncelock_singleton_comprehensive.rs)
- [事件总线](../../../crates/c09_design_pattern/examples/event_bus_demo.rs)
- [观察者与 GAT](../../../crates/c09_design_pattern/examples/gats_observer_demo.rs)
- [管道与迭代器](../../../crates/c09_design_pattern/examples/pipeline_iter_demo.rs)
- [异步 trait 演示](../../../crates/c09_design_pattern/examples/async_trait_demo.rs)
- [dyn upcasting 适配器](../../../crates/c09_design_pattern/examples/dyn_upcasting_adapter.rs)

---

## 📚 相关资源

### 官方文档

- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)

### 项目内部文档

- [完整文档](../../../crates/c09_design_pattern/README.md)
- [设计模式使用指南](../../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md)
- [GoF 模式](../../../crates/c09_design_pattern/docs/tier_02_guides/01_创建型模式指南.md)

### 形式化理论与决策树

- [设计模式边界矩阵](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md) — 23 模式 × 三维边界（安全/支持/表达）
- [设计模式表征能力形式化树图](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md#设计模式表征能力形式化树图) — 模式→实现路径→定理（Mermaid/ASCII 树图）
- [表达边界（等价/近似/不可表达）](../../research_notes/software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md)
- [组件成熟度判定树](../../research_notes/software_design_theory/04_compositional_engineering/README.md#构建能力确定性判定树) — L1–L4 成熟度、CE-T1–T3
- [组件构建能力形式化树图](../../research_notes/software_design_theory/04_compositional_engineering/README.md#组件构建能力形式化树图与-43-模式联合) — 模块→crate→进程→网络、与 43 模式联合

### 相关速查卡

- [类型系统速查卡](./type_system.md) - Trait 与设计模式
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权模式
- [泛型编程速查卡](./generics_cheatsheet.md) - 泛型与模式
- [智能指针速查卡](./smart_pointers_cheatsheet.md) - 指针模式

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
