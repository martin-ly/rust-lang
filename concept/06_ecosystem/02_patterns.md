# Design Patterns（设计模式）

> **层级**: L6 生态工程
> **前置概念**: [Traits](./02_intermediate/01_traits.md) · [Generics](./02_intermediate/02_generics.md) · [Type System](../01_foundation/04_type_system.md)
> **主要来源**: [Rust API Guidelines] · [Rust Design Patterns] · [TRPL]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本
- v1.1 (2026-05-12): Wave 3 扩展——新增模式、反模式、语言对比、学术来源

---

## 一、权威定义

> **[Rust Design Patterns]** Rust design patterns are recurring solutions to common problems in software design using the Rust programming language. They leverage Rust's unique features such as ownership, traits, and the type system.

> **[Wikipedia — Design pattern]** A design pattern is the re-usable form of a solution to a design problem. The idea was introduced by the architect Christopher Alexander and has been adapted for various other disciplines, most notably computer science.
> **来源**: <https://en.wikipedia.org/wiki/Design_pattern>

> **[Wikipedia — Resource acquisition is initialization (RAII)]** Resource acquisition is initialization (RAII) is a programming idiom used in several object-oriented, statically-typed programming languages to describe a particular language behavior. In RAII, holding a resource is a class invariant, and is tied to object lifetime: resource allocation (or acquisition) is done during object creation (specifically initialization), by the constructor, while resource deallocation (release) is done during object destruction (specifically finalization), by the destructor. In other words, resource acquisition must succeed for initialization to succeed.
> **来源**: <https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization>

> **[Wikipedia — Typestate analysis]** Typestate analysis is a technique to do static reasoning about the states of objects. It can be seen as an extension of type systems where the type of an object changes as operations are performed on it.
> **来源**: <https://en.wikipedia.org/wiki/Typestate_analysis>

---

## 二、模式分类矩阵

### 2.1 已有模式扩展

| **模式** | **分类** | **问题** | **Rust 实现** | **关键特性** |
|:---|:---|:---|:---|:---|
| **RAII** | 结构型/资源 | 资源自动释放 | `Drop` trait | 所有权离开作用域时自动清理 |
| **Typestate** | Rust 特有 | 编译期状态验证 | 泛型 + `PhantomData` | 非法状态变为编译错误 |
| **Builder** | 创建型 | 复杂对象构造 | 消费型 Builder | 所有权链确保必填字段 |
| **Newtype** | 结构型 | 类型区分 + 约束 | `struct Wrapper(T)` | 零成本，获得类型安全 |
| **Deref 多态** | 结构型 | 智能指针行为 | `Deref`/`DerefMut` | 自动解引用转换 |
| **FFI 模式** | 结构型 | 与 C 互操作 | `extern "C"` + `repr(C)` | 安全封装层 |

### 2.2 新增模式矩阵

| **模式** | **分类** | **问题** | **Rust 实现** | **关键特性** |
|:---|:---|:---|:---|:---|
| **Command** | 行为型 | 请求参数化与队列化 | `trait Command` + `execute()` | 解耦调用者与接收者 |
| **Visitor** | 行为型 | 异构结构遍历 | Trait + enum / `accept` 方法 | 开放/封闭选择 |
| **Strategy** | 行为型 | 运行时算法切换 | `dyn Trait` / 泛型参数 | 静态/动态分发选择 |
| **State Machine** | 行为型 | 状态转换管理 | enum + `match` / `transition` 方法 | 穷尽性检查保证完整覆盖 |
| **Plugin** | 结构型 | 运行时扩展能力 | `dyn Trait` + 注册表 | 模块热插拔 |

> **来源**: [Rust Design Patterns] · [GoF Design Patterns] · 可信度: ✅

---

## 三、Mermaid 图：模式关系图

```mermaid
graph TD
    A[Design Patterns] --> B[创建型 Creational]
    A --> C[结构型 Structural]
    A --> D[行为型 Behavioral]
    A --> E[Rust 特有 Idiomatic]

    B --> B1[Builder]
    B --> B2[Newtype]

    C --> C1[RAII]
    C --> C2[Deref 多态]
    C --> C3[FFI Wrapper]
    C --> C4[Plugin]

    D --> D1[Command]
    D --> D2[Visitor]
    D --> D3[Strategy]
    D --> D4[State Machine]

    E --> E1[Typestate]
    E --> E2[Zero-cost Abstraction]
    E --> E3[Phantom Types]
```

---

## 四、各模式详解

### 4.1 Command 模式

**定义**：将请求封装为对象，从而使你可用不同的请求、队列或日志来参数化其他对象。

**适用场景**：

- 需要撤销/重做操作
- 请求队列或异步任务
- 操作日志与事务系统

**Rust 实现**：

```rust
trait Command {
    fn execute(&self);
    fn undo(&self);
}

struct AddCommand {
    value: i32,
    // 实际应用中持有接收者引用
}

impl Command for AddCommand {
    fn execute(&self) { /* 执行添加 */ }
    fn undo(&self) { /* 撤销添加 */ }
}

struct Invoker {
    history: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn run(&mut self, cmd: Box<dyn Command>) {
        cmd.execute();
        self.history.push(cmd);
    }
}
```

**与其他语言对比**：

- **Java/C++**: 通常依赖 GC 或智能指针管理命令对象生命周期；Rust 需显式处理所有权，`Box<dyn Command>` 提供了堆分配动态分发。
- **Go**: 使用函数值或接口；Rust 的 trait 对象在 vtable 布局上与 Go interface 类似，但 Rust 要求显式 `Box`/`&dyn`。

> **来源**: [GoF Design Patterns] · [Rust Design Patterns] · 可信度: ✅

### 4.2 Visitor 模式

**定义**：表示一个作用于某对象结构中各元素的操作，使你可以在不改变各元素类的前提下定义作用于这些元素的新操作。

**适用场景**：

- AST（抽象语法树）遍历与代码生成
- 文档对象模型（DOM）处理
- 复杂异构数据结构需要多种遍历策略

**Rust 实现**：

```rust
mod ast {
    pub trait ExprVisitor {
        fn visit_literal(&mut self, val: i64);
        fn visit_add(&mut self, left: &Expr, right: &Expr);
    }

    pub enum Expr {
        Literal(i64),
        Add(Box<Expr>, Box<Expr>),
    }

    impl Expr {
        pub fn accept<V: ExprVisitor>(&self, visitor: &mut V) {
            match self {
                Expr::Literal(v) => visitor.visit_literal(*v),
                Expr::Add(l, r) => visitor.visit_add(l, r),
            }
        }
    }
}
```

**与其他语言对比**：

- **Java/C++**: 经典双重分发（`accept` + `visit`）；Rust 通过 `match` 枚举实现单分发，避免虚函数膨胀，但无法直接扩展现有 enum 的变体（需用 enum/struct 模拟开放访问者）。
- **Haskell**: 利用类型类（type class）和代数数据类型直接建模，Rust 的 enum + trait 在表达能力上非常接近。

> **来源**: [GoF Design Patterns] · [Rust Design Patterns] · 可信度: ✅

### 4.3 Strategy 模式

**定义**：定义一系列算法，把它们一个个封装起来，并且使它们可互相替换。

**适用场景**：

- 排序、搜索等可替换算法
- 不同平台/配置下的行为差异
- 避免大量条件分支

**Rust 实现（动态分发）**：

```rust
trait PaymentStrategy {
    fn pay(&self, amount: u64);
}

struct CreditCard;
impl PaymentStrategy for CreditCard {
    fn pay(&self, amount: u64) { println!("Credit: {}", amount); }
}

struct PayPal;
impl PaymentStrategy for PayPal {
    fn pay(&self, amount: u64) { println!("PayPal: {}", amount); }
}

struct ShoppingCart<'a> {
    strategy: &'a dyn PaymentStrategy,
}

impl<'a> ShoppingCart<'a> {
    fn checkout(&self, amount: u64) {
        self.strategy.pay(amount);
    }
}
```

**Rust 实现（静态分发 / 零成本）**：

```rust
struct ShoppingCart<S: PaymentStrategy> {
    strategy: S,
}

impl<S: PaymentStrategy> ShoppingCart<S> {
    fn checkout(&self, amount: u64) {
        self.strategy.pay(amount);
    }
}
```

**与其他语言对比**：

- **C++**: 模板（静态）+ 虚函数（动态）；Rust 的泛型单态化与 C++ 模板实例化类似，但类型检查更严格。
- **Java**: 接口 + 多态；无静态分发零成本特性，所有策略均为动态。
- **Go**: 接口值隐式实现；Rust trait 需显式实现，静态分发默认内联。

> **来源**: [GoF Design Patterns] · [TRPL] · 可信度: ✅

### 4.4 State Machine 模式

**定义**：允许对象在其内部状态改变时改变它的行为，对象看起来好像修改了它的类。

**适用场景**：

- 协议实现（TCP、HTTP/2 状态机）
- 业务工作流引擎
- 游戏角色状态（Idle、Walk、Attack）

**Rust 实现（enum + match）**：

```rust
enum ConnectionState {
    Closed,
    SynSent,
    Established,
    FinWait,
}

struct Connection {
    state: ConnectionState,
}

impl Connection {
    fn on_event(&mut self, event: Event) {
        self.state = match (&self.state, event) {
            (ConnectionState::Closed, Event::Open) => ConnectionState::SynSent,
            (ConnectionState::SynSent, Event::Ack) => ConnectionState::Established,
            (ConnectionState::Established, Event::Close) => ConnectionState::FinWait,
            (state, _) => {
                println!("Invalid transition");
                return;
            }
        };
    }
}
```

**Rust 实现（Typestate 编译期状态机）**：

```rust
struct Closed;
struct Open;

struct Connection<State> {
    _state: std::marker::PhantomData<State>,
}

impl Connection<Closed> {
    fn open(self) -> Connection<Open> {
        Connection { _state: std::marker::PhantomData }
    }
}

impl Connection<Open> {
    fn send(&self, data: &[u8]) { /* ... */ }
    fn close(self) -> Connection<Closed> {
        Connection { _state: std::marker::PhantomData }
    }
}

// 非法状态不可表示:
// let conn = Connection::<Closed> { _state: PhantomData };
// conn.send(b"hi"); // ❌ 编译错误
```

**与其他语言对比**：

- **C**: 通常用整数状态码 + `switch`，无类型安全，易遗漏状态处理。
- **Rust**: `match` 穷尽性检查强制处理所有状态；Typestate 变体将非法转换上移至编译期。
- **TypeScript**: 可用 discriminated union 模拟，但运行期仍可能处于无效状态。

> **来源**: [Rust Design Patterns] · [TRPL] · 可信度: ✅

### 4.5 Plugin 模式

**定义**：在运行时动态加载并注册扩展模块，无需修改核心代码。

**适用场景**：

- 编辑器/IDE 扩展系统
- Web 服务器中间件链
- 游戏模组（mod）系统

**Rust 实现**：

```rust
use std::collections::HashMap;

trait Plugin {
    fn name(&self) -> &'static str;
    fn execute(&self, input: &str) -> String;
}

struct PluginRegistry {
    plugins: HashMap<String, Box<dyn Plugin>>,
}

impl PluginRegistry {
    fn register(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.insert(plugin.name().to_string(), plugin);
    }

    fn run(&self, name: &str, input: &str) -> Option<String> {
        self.plugins.get(name).map(|p| p.execute(input))
    }
}
```

**动态加载（libloading）**:

```rust
// 使用 `libloading` crate 加载 .dll / .so
use libloading::{Library, Symbol};

type CreatePlugin = unsafe fn() -> *mut dyn Plugin;

unsafe {
    let lib = Library::new("plugin.so").ok()?;
    let create: Symbol<CreatePlugin> = lib.get(b"create_plugin").ok()?;
    let plugin = Box::from_raw(create());
}
```

**与其他语言对比**：

- **Python**: `importlib` 动态导入，运行时灵活但无类型安全；Rust 的 `libloading` + trait 对象在 FFI 边界提供类型约束。
- **Java**: `ServiceLoader` / OSGi 模块化；Rust 无内置类加载器，需手动管理动态库生命周期。
- **C/C++**: `dlopen` / `LoadLibrary`；Rust 的 `libloading` 是对这些 API 的安全封装。

> **来源**: [Rust API Guidelines] · [libloading docs] · 可信度: ✅

---

## 五、反模式（Anti-patterns）

### 5.1 Over-engineering（过度工程）

**定义**：为应对不太可能出现的需求而引入不必要的抽象层次，导致代码复杂度远超实际需要。

**Rust 表现**：

- 为单一函数引入复杂的 Trait 层次和泛型参数，而仅有一个实现。
- 使用 `async` / `tokio` 处理完全同步、I/O 极少的任务。

**避免方法**：YAGNI（You Aren't Gonna Need It）；先用 concrete type 实现，待确需多态时再抽象。

> **来源**: [Rust API Guidelines — Flexibility](https://rust-lang.github.io/api-guidelines/flexibility.html) · 可信度: ✅

### 5.2 Premature abstraction（过早抽象）

**定义**：在问题域尚未稳定、需求尚不清晰时建立抽象边界，导致后续修改牵一发而动全身。

**Rust 表现**：

- 过早将内部模块拆分为独立 crate，导致 Workspace 依赖环。
- 过早定义 `dyn Trait` 接口，而实际调用方只有一处且性能敏感。

**避免方法**：遵循 "三次法则"（Rule of Three）；重复出现三次以上再提取抽象。

> **来源**: [Rust API Guidelines] · [TRPL] · 可信度: ✅

### 5.3 Stringly typed（字符串类型化）

**定义**：使用字符串替代强类型来表示结构化数据或枚举状态，丧失编译期检查能力。

**Rust 表现**：

- 用 `String` 传递命令名称而非 enum。
- 用字符串拼接 SQL / 路径，而非使用类型安全的构造器。

**Rust 对策**：

- 使用 enum + `match`。
- 使用 `std::path::PathBuf` 代替裸字符串路径。
- 使用 `sqlx` 等编译期检查的查询构造器。

```rust
// ❌ Stringly typed
fn run_command(name: &str) { /* ... */ }

// ✅ 强类型
enum Command { Start, Stop, Restart }
fn run_command(cmd: Command) { match cmd { ... } }
```

> **来源**: [Rust API Guidelines — Type Safety](https://rust-lang.github.io/api-guidelines/type-safety.html) · 可信度: ✅

### 5.4 God Object（上帝对象）

**定义**：一个对象或结构体掌握了过多职责和状态，成为系统中所有操作的中心枢纽，违反单一职责原则。

**Rust 表现**：

- 一个 `Context` struct 持有数十个字段和几十种方法。
- `Mutex<GlobalState>` 包裹整个应用状态，导致锁竞争和逻辑纠缠。

**Rust 对策**：

- 按领域拆分 struct，使用组合代替堆砌。
- 利用所有权系统将状态分散到不同模块，通过消息传递（channel）或 Actor 模式通信。

> **来源**: [Rust API Guidelines — Structs](https://rust-lang.github.io/api-guidelines/predictability.html) · 可信度: ✅

---

## 六、与 L1-L3 的概念映射

| 设计模式 | 依赖的 Rust 概念 | 概念来源文件 | 形式化意义 |
|:---|:---|:---|:---|
| RAII | L1 所有权 + Drop trait | `01_foundation/01_ownership.md` | 线性逻辑资源消耗 |
| Typestate | L1 所有权 + L2 泛型 | `01_foundation/`, `02_intermediate/02_generics.md` | 编译期状态机验证 |
| Newtype | L1 类型系统 | `01_foundation/04_type_system.md` | 零大小类型包装 |
| Builder | L2 Trait + 方法链 | `02_intermediate/01_traits.md` | fluent API 构造 |
| Zero-cost Abstraction | L2 单态化 | `02_intermediate/02_generics.md` | 参数多态的编译期消除 |
| Interior Mutability | L1 借用 + L2 内存 | `01_foundation/02_borrowing.md`, `02_intermediate/03_memory_management.md` | 运行时权限检查替代编译期 |
| Command | L2 Trait + L1 所有权 | `02_intermediate/01_traits.md` | 行为参数化 |
| Visitor | L2 Trait + enum | `02_intermediate/01_traits.md` | 结构归纳 |
| Strategy | L2 Trait + 泛型 | `02_intermediate/01_traits.md` | 多态分发 |
| State Machine | L1 enum + match | `01_foundation/04_type_system.md` | 代数数据类型穷尽性 |

---

## 七、学术来源

| **论文/著作** | **作者** | **核心贡献** | **与 Rust 的关联** |
|:---|:---|:---|:---|
| *Design Patterns: Elements of Reusable Object-Oriented Software* (GoF, 1994) | Gamma, Helm, Johnson, Vlissides | 系统化了 23 种经典设计模式 | Rust 社区对 GoF 模式进行了零成本抽象改写 |
| *Rust API Guidelines* (Rust Lang Team) | Rust Lang Team | Rust 生态的 API 设计规范 | 明确提出了 Newtype、Builder、Error 等惯用法 |
| *Typestates for Objects* (Aldrich et al., 2009) | Jonathan Aldrich et al. | 将 Typestate 引入面向对象语言 | Rust 的 PhantomData + 泛型是 Typestate 的工业级实现 |
| *Ownership Types for Flexible Alias Protection* (Clarke et al., 1998) | Dave Clarke et al. | 所有权类型理论基础 | 支撑 RAII 和线性资源管理的学术研究 |

> **来源**: [GoF Book] · [Rust API Guidelines] · [Typestates for Objects](https://dl.acm.org/doi/10.1145/1640089.1640095) · 可信度: ✅

---

## 八、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| RAII 是 Rust 核心模式 | [TRPL] · [Wikipedia: RAII] | ✅ |
| Typestate 利用类型系统 | [Rust Design Patterns] · [Aldrich et al. 2009] | ✅ |
| Newtype 零成本 | [TRPL] · [Rust Reference] | ✅ |
| Command/Visitor/Strategy 为 GoF 经典模式 | [GoF Design Patterns, 1994] | ✅ |
| Stringly typed 为反模式 | [Rust API Guidelines] | ✅ |
| 设计模式定义 | [Wikipedia: Design pattern] | ✅ |
| Typestate analysis 定义 | [Wikipedia: Typestate analysis] | ✅ |
| 所有权类型理论基础 | [Clarke et al. 1998 — Ownership Types] | ✅ |
| CMU 课程涵盖设计模式 | [CMU 17-363 — PL Concepts] | ✅ |
| Stanford 课程涵盖 Rust 模式 | [Stanford CS340R] | ✅ |
| Rust API 设计规范 | [Rust API Guidelines] | ✅ |
| 设计模式系统化 | [Gamma et al. 1994 — Design Patterns: Elements of Reusable Object-Oriented Software] | ✅ |
| Typestate 工业实现 | [Aldrich et al. 2009 — Typestates for Objects, ECOOP] | ✅ |

---

## 九、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权 / Drop | [`../01_foundation/01_ownership.md`](../01_foundation/01_ownership.md) | RAII 根基 |
| 借用规则 | [`../01_foundation/02_borrowing.md`](../01_foundation/02_borrowing.md) | 内部可变性前提 |
| Trait 系统 | [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) | 模式实现基础 |
| 泛型 | [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) | 零成本抽象 |
| 内存管理 | [`../02_intermediate/03_memory_management.md`](../02_intermediate/03_memory_management.md) | 智能指针模式 |
| 错误处理 | [`../02_intermediate/04_error_handling.md`](../02_intermediate/04_error_handling.md) | Result 模式 |
| 工具链 | [`./01_toolchain.md`](./01_toolchain.md) | 工程支撑 |
| 设计模式对比 | [`../05_comparative/03_paradigm_matrix.md`](../05_comparative/03_paradigm_matrix.md) | 范式定位 |

---

## 十、待补充与演进方向（TODOs）

- [ ] **高**: 补充更多 Rust 特有模式（如 GATs 模式、Type Erasure）
- [ ] **高**: 补充 async/await 设计模式
- [ ] **中**: 补充 FFI 边界的安全封装模式深度案例
- [ ] **中**: 补充错误处理模式（`thiserror`/`miette`/`snafu` 对比）
- [ ] **低**: 补充各模式的 benchmark 对比数据
