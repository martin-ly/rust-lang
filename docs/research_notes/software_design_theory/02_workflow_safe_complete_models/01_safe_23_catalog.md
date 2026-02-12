# 23 种安全设计模型索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [23 种安全设计模型索引](#23-种安全设计模型索引)
  - [定义](#定义)
  - [按分类索引](#按分类索引)
  - [选型决策树](#选型决策树)
  - [实现约束与注意事项](#实现约束与注意事项)
  - [与 43 完全模型衔接](#与-43-完全模型衔接)
  - [与理论体系衔接](#与理论体系衔接)

---

## 定义

**23 安全模型** = GoF 23 种设计模式中，在 Rust 中可**纯 Safe**（或无必要 unsafe）实现的模式。

**判定准则**：不依赖 `unsafe`、`static mut`、原始指针解引用；满足所有权、借用、生命周期规则；可用标准库或纯 Safe 第三方 crate 实现。

---

## 按分类索引

### 创建型（5）

| 模式 | 安全实现 | 核心 Rust 机制 | 形式化文档 |
|------|----------|----------------|------------|
| Factory Method | 纯 Safe | trait 工厂方法、泛型 | [factory_method](../01_design_patterns_formal/01_creational/factory_method.md) |
| Abstract Factory | 纯 Safe | 枚举/结构体族、trait | [abstract_factory](../01_design_patterns_formal/01_creational/abstract_factory.md) |
| Builder | 纯 Safe | 方法链、`Option`/类型状态 | [builder](../01_design_patterns_formal/01_creational/builder.md) |
| Prototype | 纯 Safe | `Clone` trait | [prototype](../01_design_patterns_formal/01_creational/prototype.md) |
| Singleton | 纯 Safe（OnceLock/LazyLock） | `std::sync::OnceLock`、`LazyLock` | [singleton](../01_design_patterns_formal/01_creational/singleton.md) |

**创建型说明**：除 Singleton 外，均依赖 trait + 泛型或 Copy/Clone，无共享可变状态；Singleton 使用 OnceLock 避免 `static mut`。

### 结构型（7）

| 模式 | 安全实现 | 核心 Rust 机制 | 形式化文档 |
|------|----------|----------------|------------|
| Adapter | 纯 Safe | 结构体包装、`impl Trait for Wrapper` | [adapter](../01_design_patterns_formal/02_structural/adapter.md) |
| Bridge | 纯 Safe | trait 解耦抽象与实现 | [bridge](../01_design_patterns_formal/02_structural/bridge.md) |
| Composite | 纯 Safe | `Box`、`Vec`、递归枚举 | [composite](../01_design_patterns_formal/02_structural/composite.md) |
| Decorator | 纯 Safe | 结构体委托、泛型递归 | [decorator](../01_design_patterns_formal/02_structural/decorator.md) |
| Facade | 纯 Safe | 模块、`pub` 可见性 | [facade](../01_design_patterns_formal/02_structural/facade.md) |
| Flyweight | 纯 Safe | `Arc`、`Rc`、`HashMap` 缓存 | [flyweight](../01_design_patterns_formal/02_structural/flyweight.md) |
| Proxy | 纯 Safe | 委托、延迟初始化 | [proxy](../01_design_patterns_formal/02_structural/proxy.md) |

**结构型说明**：结构型模式以组合为主，所有权清晰；Flyweight 用 `Arc` 共享 immutable 数据，无数据竞争。

### 行为型（11）

| 模式 | 安全实现 | 核心 Rust 机制 | 形式化文档 |
|------|----------|----------------|------------|
| Chain of Responsibility | 纯 Safe | `Option<Box<Handler>>` 链表 | [chain_of_responsibility](../01_design_patterns_formal/03_behavioral/chain_of_responsibility.md) |
| Command | 纯 Safe | `Fn`、闭包、`Box<dyn Fn()>` | [command](../01_design_patterns_formal/03_behavioral/command.md) |
| Interpreter | 纯 Safe | 枚举 AST、`match` | [interpreter](../01_design_patterns_formal/03_behavioral/interpreter.md) |
| Iterator | 纯 Safe | `Iterator` trait | [iterator](../01_design_patterns_formal/03_behavioral/iterator.md) |
| Mediator | 纯 Safe | 结构体协调、`Weak` 避免循环 | [mediator](../01_design_patterns_formal/03_behavioral/mediator.md) |
| Memento | 纯 Safe | `serde`、`Clone`、快照类型 | [memento](../01_design_patterns_formal/03_behavioral/memento.md) |
| Observer | 纯 Safe（channel/回调） | `mpsc`、`broadcast`、`dyn Fn` | [observer](../01_design_patterns_formal/03_behavioral/observer.md) |
| State | 纯 Safe | 枚举、类型状态、状态机 | [state](../01_design_patterns_formal/03_behavioral/state.md) |
| Strategy | 纯 Safe | trait、`impl Trait` | [strategy](../01_design_patterns_formal/03_behavioral/strategy.md) |
| Template Method | 纯 Safe | trait 默认方法 | [template_method](../01_design_patterns_formal/03_behavioral/template_method.md) |
| Visitor | 纯 Safe | `match`、trait、双重分发 | [visitor](../01_design_patterns_formal/03_behavioral/visitor.md) |

**行为型说明**：Observer 用 channel 替代 OOP 继承；Memento 用 Clone/serde 替代私有状态封装；其余与所有权模型自然契合。

---

## 实现约束与注意事项

| 约束 | 适用模式 | 说明 |
|------|----------|------|
| 无 `static mut` | Singleton | 用 OnceLock/LazyLock |
| `Send`/`Sync` | 跨线程 Observer、Flyweight | 选 `Arc` 而非 `Rc` |
| 生命周期 | Mediator、Chain | 链式结构用 `Box` 避免自引用 |
| 无继承 | Interpreter、Visitor、Template Method | 用枚举 + match、trait 默认方法 |

---

## 与 GoF 原书对应

23 安全模型与 GoF 原书 23 种模式一一对应；无新增、无删减；仅标注 Rust 实现边界。GoF 分类：创建型 5、结构型 7、行为型 11。

---

## 选型决策树

```text
需要哪种模式？
├── 创建型 → 单产品？Factory Method | 产品族？Abstract Factory | 多步骤？Builder | 克隆？Prototype | 全局唯一？Singleton
├── 结构型 → 适配？Adapter | 解耦？Bridge | 树？Composite | 链式扩展？Decorator | 简化？Facade | 共享？Flyweight | 延迟？Proxy
└── 行为型 → 链式？Chain | 可撤销？Command | 求值？Interpreter | 遍历？Iterator | 协调？Mediator | 快照？Memento | 通知？Observer | 状态？State | 算法？Strategy | 骨架？Template | 按类型？Visitor
```

每模式形式化文档见对应链接；选型决策树详见 [03_semantic_boundary_map](03_semantic_boundary_map.md) 按需求反向查模式。

---

## 与 43 完全模型衔接

扩展 20 种企业/分布式模式见 [02_complete_43_catalog](02_complete_43_catalog.md)；23 安全 ⊆ 43 完全；扩展模式绝大部分亦纯 Safe。

---

## 与理论体系衔接

23 安全模型依赖：

- [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../../THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) 第 4 层（应用与边界层）
- [ownership_model](../../formal_methods/ownership_model.md)：所有权、借用、生命周期
- [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)：借用合法性
- [type_system_foundations](../../type_theory/type_system_foundations.md)：穷尽匹配、类型安全
