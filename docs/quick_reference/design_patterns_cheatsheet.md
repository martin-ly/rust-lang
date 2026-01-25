# 设计模式快速参考卡片

**模块**: C09 Design Patterns
**Rust 版本**: 1.93.0+
**最后更新**: 2026-01-26

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
  - [📚 相关文档](#-相关文档)

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

| 模式 | Rust 实现 | 使用场景 |
|------|----------|---------|
| **单例** | `OnceLock` + `Arc<Mutex<T>>` | 全局配置、日志 |
| **工厂** | `match` + `Box<dyn Trait>` | 多态对象创建 |
| **建造者** | 链式方法 | 复杂对象构建 |

### 结构型模式

| 模式 | Rust 实现 | 使用场景 |
|------|----------|---------|
| **适配器** | `impl NewTrait for OldType` | 接口转换 |
| **装饰器** | 包装器结构体 | 功能扩展 |
| **外观** | 统一接口 | 简化复杂系统 |

### 行为型模式

| 模式 | Rust 实现 | 使用场景 |
|------|----------|---------|
| **策略** | `Box<dyn Strategy>` | 算法选择 |
| **观察者** | `Vec<Arc<dyn Observer>>` | 事件通知 |
| **命令** | `Box<dyn Command>` | 操作封装 |

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

## 📚 相关资源

### 官方文档
- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)

### 项目内部文档
- [完整文档](../../crates/c09_design_pattern/README.md)
- [设计模式使用指南](../../docs/DESIGN_PATTERNS_USAGE_GUIDE.md)
- [GoF 模式](../../crates/c09_design_pattern/docs/tier_02_guides/01_GoF设计模式.md)

### 相关速查卡
- [类型系统速查卡](./type_system.md) - Trait 与设计模式
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权模式
- [泛型编程速查卡](./generics_cheatsheet.md) - 泛型与模式
- [智能指针速查卡](./smart_pointers_cheatsheet.md) - 指针模式

---

**最后更新**: 2026-01-26
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
