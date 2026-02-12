# 充分表达 vs 非充分表达论证

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [充分表达 vs 非充分表达论证](#充分表达-vs-非充分表达论证)
  - [目录](#目录)
  - [定义](#定义)
  - [等价表达的模式](#等价表达的模式)
    - [创建型](#创建型)
    - [结构型](#结构型)
    - [行为型](#行为型)
  - [近似表达的模式](#近似表达的模式)
  - [不可表达或极难表达](#不可表达或极难表达)
  - [扩展模式（43 完全之 20）表达边界](#扩展模式43-完全之-20表达边界)
  - [等价表达示例（代码级）](#等价表达示例代码级)
    - [等价表达完整代码示例](#等价表达完整代码示例)
  - [近似表达示例（代码级）](#近似表达示例代码级)
    - [近似表达完整代码示例](#近似表达完整代码示例)
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
| Domain Model | 等价 | 结构体 + 方法；无贫血模型 |
| Service Layer | 等价 | 模块、`pub fn` 编排 |
| Repository | 等价 | trait + impl |
| Unit of Work | 等价 | 结构体收集变更、`commit()` |
| Data Mapper | 等价 | `From`/`Into`、serde |
| Table Data Gateway | 等价 | 表级 API、async |
| Active Record | 等价 | 对象持 Connection |
| Gateway | 等价 | trait + 实现；FFI 时近似 |
| MVC | 等价 | 模块分层、model/view/controller |
| Front Controller | 等价 | Router、match 路径 |
| DTO | 等价 | 结构体 + serde；无行为 |
| Remote Facade | 等价 | 批量接口、gRPC |
| Value Object | 等价 | 结构体 + Eq、Clone |
| Registry | 等价 | OnceLock、HashMap |
| Identity Map | 等价 | HashMap<Id, Arc<T>> |
| Lazy Load | 等价 | OnceLock、Option |
| Plugin | 等价 | trait + Box<dyn Trait> |
| Optimistic Offline Lock | 等价 | version + CAS |
| Specification | 等价 | trait Spec + and/or |
| Event Sourcing | 等价 | Vec<Event> + fold |

**论证**：扩展 20 绝大部分与 Fowler EAA 语义等价；Rust 的 trait、枚举、所有权可自然表达；Gateway 在 FFI 场景为近似（需 unsafe 封装）。

---

## 等价表达示例（代码级）

| 模式 | GoF 风格 | Rust 等价 |
| :--- | :--- | :--- |
| Strategy | 接口 + 实现类 | `trait Strategy { fn f(&self, x: T) -> R; }` + `impl` |
| Command | 命令类 | `Box<dyn Fn()>` 或 `trait Command { fn execute(&self); }` |
| Iterator | 迭代器接口 | `Iterator` trait 原生 |
| Factory Method | 虚工厂方法 | `fn create(&self) -> T` in trait |
| Bridge | 抽象类 + 实现类 | `struct A<R: Impl> { impl: R }` |

### 等价表达完整代码示例

**Strategy 模式**：

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}
struct QuickSort;
impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) { data.sort_unstable(); }
}
struct Context<S: SortStrategy> { strategy: S }
impl<S: SortStrategy> Context<S> {
    fn execute(&self, data: &mut [i32]) { self.strategy.sort(data); }
}
// 与 GoF：Context 持有 Strategy 接口；Rust 用 trait 等价
```

**Factory Method 模式**：

```rust
trait Product { fn name(&self) -> &str; }
impl Product for String { fn name(&self) -> &str { self } }

trait Creator {
    fn create(&self) -> Box<dyn Product>;
}
struct StringCreator;
impl Creator for StringCreator {
    fn create(&self) -> Box<dyn Product> { Box::new("default".to_string()) }
}
// 虚工厂方法：create 在 trait 中；子类 impl 对应 Rust 的 impl
```

**Bridge 模式**：

```rust
trait Renderer { fn render(&self, s: &str) -> String; }
struct HtmlRenderer;
impl Renderer for HtmlRenderer {
    fn render(&self, s: &str) -> String { format!("<p>{}</p>", s) }
}
struct Page<R: Renderer> { renderer: R, content: String }
impl<R: Renderer> Page<R> {
    fn display(&self) -> String { self.renderer.render(&self.content) }
}
// 抽象与实现解耦；R 可替换，无继承
```

---

## 近似表达示例（代码级）

| 模式 | GoF 风格 | Rust 近似 | 差异 |
| :--- | :--- | :--- | :--- |
| Singleton | static 单例 | `OnceLock<T>` | 无全局可变，显式初始化 |
| Observer | Subject/Observer 继承 | `mpsc::channel` | 消息传递替代回调注册 |
| Visitor | 双重分发 | `match e { ... }` + `Visitor` trait | 单分发 + 穷尽匹配 |
| Memento | 私有封装快照 | `Clone` / serde | 无私有，需类型可序列化 |

### 近似表达完整代码示例

**Singleton 近似**：

```rust
use std::sync::OnceLock;
static INSTANCE: OnceLock<Config> = OnceLock::new();

fn config() -> &'static Config {
    INSTANCE.get_or_init(|| Config::default())
}
// 差异：无全局可变；显式 get_or_init；线程安全由 OnceLock 保证
```

**Observer 近似（channel 替代）**：

```rust
use std::sync::mpsc;
let (tx, rx) = mpsc::channel();
// 发布者：tx.send(event)
// 订阅者：rx.recv() 或 for msg in rx
// 差异：消息传递而非回调注册；一对多需 broadcast channel
```

**Visitor 近似（match 穷尽）**：

```rust
enum Expr { Lit(i32), Add(Box<Expr>, Box<Expr>) }

fn interpret(e: &Expr) -> i32 {
    match e {
        Expr::Lit(n) => *n,
        Expr::Add(a, b) => interpret(a) + interpret(b),
    }
}
// 差异：单分发 match 替代 OOP 双重分发；穷尽匹配保证覆盖
```

**Memento 近似（Clone）**：

```rust
#[derive(Clone, serde::Serialize, serde::Deserialize)]
struct State { data: String }

struct Originator { state: State }
impl Originator {
    fn save(&self) -> State { self.state.clone() }
    fn restore(&mut self, m: State) { self.state = m; }
}
// 差异：无私有封装；State 可被任意修改；需类型 impl Clone/Serialize
```

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
