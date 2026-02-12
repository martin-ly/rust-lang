# 充分表达 vs 非充分表达论证

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [定义](#定义)
- [等价表达的模式](#等价表达的模式)
- [近似表达的模式](#近似表达的模式)
- [不可表达或极难表达](#不可表达或极难表达)
- [扩展模式（43 完全之 20）表达边界](#扩展模式43-完全之20表达边界)
- [等价表达示例（代码级）](#等价表达示例代码级)
- [近似表达示例（代码级）](#近似表达示例代码级)
- [选择建议](#选择建议)
- [不可表达边界的替代策略](#不可表达边界的替代策略)
- [表达边界与性能](#表达边界与性能)
- [与理论衔接](#与理论衔接)

---

## 定义

| 分类 | 定义 |
| :--- | :--- |
| **充分表达** | 与 GoF/OOP 语义等价，无信息损失，实现路径自然 |
| **非充分表达** | 可实现核心意图，但实现方式或约束不同，有语义偏移 |

---

## 等价表达的模式

### 创建型

- **Factory Method**：trait 工厂方法，语义一致
- **Abstract Factory**：枚举/关联类型产品族，等价
- **Builder**：链式构建，类型状态可增强
- **Prototype**：`Clone` trait 直接对应

### 结构型

- **Adapter**：包装 + 委托，等价
- **Bridge**：trait 解耦抽象与实现，等价
- **Composite**：枚举递归结构，等价
- **Decorator**：结构体包装，等价
- **Facade**：模块/结构体，等价
- **Flyweight**：`Arc` 共享，等价
- **Proxy**：委托、延迟，等价

### 行为型

- **Chain of Responsibility**：`Option`/链表传递，等价
- **Command**：闭包即命令对象，等价
- **Iterator**：`Iterator` trait 原生，等价
- **Mediator**：结构体协调，等价
- **State**：枚举/类型状态更严格，等价
- **Strategy**：trait 即策略，等价

**论证**：Rust 的 trait、枚举、所有权、借用可直接对应 OOP 的接口、多态、封装，语义一致。

---

## 近似表达的模式

| 模式 | 偏移原因 | Rust 替代 |
| :--- | :--- | :--- |
| **Singleton** | 无全局可变 | OnceLock、LazyLock |
| **Interpreter** | 无继承 | 枚举 + match |
| **Memento** | 无私有封装 | Clone、serde |
| **Observer** | 无继承 | channel、回调、RefCell |
| **Template Method** | 无继承 | trait 默认方法 |
| **Visitor** | 无 OOP 双重分发 | match 或 trait 模拟 |

**论证**：Rust 采用组合优于继承，枚举 + trait 提供不同但等价的抽象能力。

---

## 不可表达或极难表达

- 依赖全局可变 + 隐式共享的经典 OOP 模式
- 依赖多继承的复杂层次
- 依赖运行时反射的某些企业模式

**论证**：由 [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md) 表达能力边界，Rust 故意限制此类能力以换取安全与可预测性。

---

## 扩展模式（43 完全之 20）表达边界

| 模式 | 表达 | 说明 |
| :--- | :--- | :--- |
| Domain Model | 等价 | 结构体 + 方法 |
| Service Layer | 等价 | 模块 |
| Repository | 等价 | trait |
| Unit of Work | 等价 | 结构体收集变更 |
| Data Mapper | 等价 | 转换函数/结构体 |
| Gateway | 等价 | trait + 实现 |
| MVC | 等价 | 模块分层 |
| DTO | 等价 | 结构体 |
| Value Object | 等价 | 结构体 + Eq |
| Event Sourcing | 等价 | Vec 事件日志 |

---

## 等价表达示例（代码级）

| 模式 | GoF 风格 | Rust 等价 |
| :--- | :--- | :--- |
| Strategy | 接口 + 实现类 | `trait Strategy { fn f(&self, x: T) -> R; }` + `impl` |
| Command | 命令类 | `Box<dyn Fn()>` 或 `trait Command { fn execute(&self); }` |
| Iterator | 迭代器接口 | `Iterator` trait 原生 |
| Factory Method | 虚工厂方法 | `fn create(&self) -> T` in trait |
| Bridge | 抽象类 + 实现类 | `struct A<R: Impl> { impl: R }` |

---

## 近似表达示例（代码级）

| 模式 | GoF 风格 | Rust 近似 | 差异 |
| :--- | :--- | :--- | :--- |
| Singleton | static 单例 | `OnceLock<T>` | 无全局可变，显式初始化 |
| Observer | Subject/Observer 继承 | `mpsc::channel` | 消息传递替代回调注册 |
| Visitor | 双重分发 | `match e { ... }` + `Visitor` trait | 单分发 + 穷尽匹配 |
| Memento | 私有封装快照 | `Clone` / serde | 无私有，需类型可序列化 |

---

## 选择建议

| 需求 | 建议 |
| :--- | :--- |
| 需与 GoF 语义完全一致 | 选用等价表达模式；见上表 |
| 可接受实现差异 | 选用近似表达；Singleton、Observer 等 |
| 跨语言团队 | 文档明确 Rust 与 OOP 差异；见各模式「与 GoF 对比」 |
| 性能敏感 | 等价表达模式多为零成本抽象；Strategy、Iterator 等 |

---

## 不可表达边界的替代策略

| 不可表达 | 替代策略 |
| :--- | :--- |
| 全局可变隐式共享 | 依赖注入、OnceLock、显式传入 |
| 多继承 | trait 多实现 + 组合 |
| 运行时反射 | 宏生成、trait 显式、枚举匹配 |
| 任意子类型 | 显式 trait 约束、newtype 包装 |

---

## 表达边界与性能

| 表达类型 | 性能特征 |
| :--- | :--- |
| 等价表达 | 多为零成本抽象；编译时单态化 |
| 近似表达 | 可能有额外间接（如 channel）；通常可接受 |
| 不可表达 | 无直接替代；需重新设计 |

---

## 与理论衔接

- [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md)：边界定理 EB1–EB6
- [DESIGN_MECHANISM_RATIONALE](../../DESIGN_MECHANISM_RATIONALE.md)：设计机制理由
