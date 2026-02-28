# 23 种安全设计模型索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录 {#-目录}

- [23 种安全设计模型索引](#23-种安全设计模型索引)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [定义](#定义)
  - [按分类索引](#按分类索引)
    - [创建型（5）](#创建型5)
    - [结构型（7）](#结构型7)
    - [行为型（11）](#行为型11)
  - [实现约束与注意事项](#实现约束与注意事项)
  - [与 GoF 原书对应](#与-gof-原书对应)
  - [选型决策树](#选型决策树)
  - [典型场景与快速示例](#典型场景与快速示例)
    - [创建型典型场景](#创建型典型场景)
    - [结构型典型场景](#结构型典型场景)
    - [行为型典型场景](#行为型典型场景)
  - [常见陷阱与规避（实质内容）](#常见陷阱与规避实质内容)
    - [创建型陷阱](#创建型陷阱)
    - [结构型陷阱](#结构型陷阱)
    - [行为型陷阱](#行为型陷阱)
  - [与形式化 Def/定理衔接](#与形式化-def定理衔接)
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
| :--- | :--- | :--- | :--- |
| Factory Method | 纯 Safe | trait 工厂方法、泛型 | [factory_method](../01_design_patterns_formal/01_creational/factory_method.md) |
| Abstract Factory | 纯 Safe | 枚举/结构体族、trait | [abstract_factory](../01_design_patterns_formal/01_creational/abstract_factory.md) |
| Builder | 纯 Safe | 方法链、`Option`/类型状态 | [builder](../01_design_patterns_formal/01_creational/builder.md) |
| Prototype | 纯 Safe | `Clone` trait | [prototype](../01_design_patterns_formal/01_creational/prototype.md) |
| Singleton | 纯 Safe（OnceLock/LazyLock） | `std::sync::OnceLock`、`LazyLock` | [singleton](../01_design_patterns_formal/01_creational/singleton.md) |

**创建型说明**：除 Singleton 外，均依赖 trait + 泛型或 Copy/Clone，无共享可变状态；Singleton 使用 OnceLock 避免 `static mut`。

### 结构型（7）

| 模式 | 安全实现 | 核心 Rust 机制 | 形式化文档 |
| :--- | :--- | :--- | :--- |
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
| :--- | :--- | :--- | :--- |
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
| :--- | :--- | :--- |
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

## 典型场景与快速示例

### 创建型典型场景

| 模式 | 典型场景 | 快速示例 |
| :--- | :--- | :--- |
| **Factory Method** | 运行时决定产品类型、插件化创建 | `trait ProductCreator { fn create(&self) -> Box<dyn Product>; }` |
| **Abstract Factory** | 跨平台 UI（按钮+文本框族）、主题切换 | `enum Theme { Dark, Light }` → `impl ButtonFactory for DarkTheme` |
| **Builder** | 多可选参数、链式构造、校验 | `Config::builder().host("x").port(80).build()?` |
| **Prototype** | 克隆代价低于新建、模板复制 | `let copy = original.clone()` |
| **Singleton** | 全局配置、日志、连接池 | `static CONFIG: OnceLock<Config> = OnceLock::new();` |

### 结构型典型场景

| 模式 | 典型场景 | 快速示例 |
| :--- | :--- | :--- |
| **Adapter** | 适配第三方库、旧接口包装 | `impl Target for LegacyAdapter { fn request(&self) -> String { self.legacy_specific() } }` |
| **Bridge** | 抽象与实现解耦、多实现组合 | `struct Page<R: Renderer> { renderer: R }` |
| **Composite** | 树状结构、递归组合 | `enum Node { Leaf(i32), Branch(Vec<Box<Node>>) }` |
| **Decorator** | 链式增强、中间件 | `struct Logging(Box<dyn Service>); impl Service for Logging { fn call(&self) { log(); self.0.call() } }` |
| **Facade** | 简化复杂子系统 | `pub fn simple_api() { a::复杂的(); b::另一套(); }` |
| **Flyweight** | 共享不可变、缓存 | `HashMap::entry(key).or_insert_with(\|\| expensive_create())` |
| **Proxy** | 延迟加载、访问控制 | `struct LazyProxy { inner: OnceLock<Heavy> }` |

### 行为型典型场景

| 模式 | 典型场景 | 快速示例 |
| :--- | :--- | :--- |
| **Chain** | 中间件链、权限校验链 | `Option<Box<Handler>>` 链表，`handle` 失败则 `next.handle()` |
| **Command** | 撤销/重做、队列化操作 | `Box<dyn Fn()>` 或 `trait Command { fn execute(&self); fn undo(&self); }` |
| **Interpreter** | 表达式求值、DSL | `enum Expr { Lit(i32), Add(Box<Expr>, Box<Expr>) }` + `match` |
| **Iterator** | 集合遍历、惰性生成 | `impl Iterator for MyIter { type Item = T; fn next(&mut self) -> Option<T> }` |
| **Mediator** | 多对象协调、避免网状引用 | `struct Mediator { components: Vec<Weak<Component>> }` |
| **Memento** | 快照、撤销栈 | `struct Memento(State); originator.save() -> Memento` |
| **Observer** | 事件通知、订阅发布 | `mpsc::channel` 或 `broadcast::channel` |
| **State** | 状态机、工作流 | `enum State { Draft, Submitted, Shipped }` + `impl` 方法 |
| **Strategy** | 可替换算法、策略模式 | `trait Strategy { fn f(&self, x: T) -> R; }` |
| **Template Method** | 算法骨架、钩子 | `trait Algorithm { fn step1(&self); fn step2(&self); fn run(&self) { self.step1(); self.step2(); } }` |
| **Visitor** | 树遍历、按类型分发 | `fn visit(e: &Expr) -> i32 { match e { ... } }` |

---

## 常见陷阱与规避（实质内容）

### 创建型陷阱

| 模式 | 常见陷阱 | 后果 | 规避 |
| :--- | :--- | :--- | :--- |
| **Singleton** | 用 `static mut` 或 `lazy_static` 旧 API | 数据竞争、UB | 1.93 用 `OnceLock`、`LazyLock`；见 [singleton](../01_design_patterns_formal/01_creational/singleton.md) |
| **Builder** | `build()` 前必填未设 | 运行时 panic | 类型状态 Builder 或 `ok_or(Error::Missing)`；见 [builder](../01_design_patterns_formal/01_creational/builder.md) B-T2 |
| **Abstract Factory** | 单产品用 Abstract Factory | 过度设计 | 用 Factory Method；见 [03_semantic_boundary_map](03_semantic_boundary_map.md) 反模式误选 |
| **Prototype** | `Clone` 浅拷贝共享可变 | 隐式耦合 | 深拷贝或显式 `clone` 文档化；见 [prototype](../01_design_patterns_formal/01_creational/prototype.md) |
| **Factory Method** | 返回 `impl Trait` 时生命周期不足 | 编译错误 | 返回 `Box<dyn Trait>` 或 `Arc<T>`；注意 `'static` 约束 |

### 结构型陷阱

| 模式 | 常见陷阱 | 后果 | 规避 |
| :--- | :--- | :--- | :--- |
| **Flyweight** | 跨线程用 `Rc` | 编译错误 | 用 `Arc`；见 [ownership_model](../../formal_methods/ownership_model.md) Def ARC1 |
| **Composite** | 循环引用（父→子→父） | 内存泄漏 | 用 `Weak` 打破环；见 [composite](../01_design_patterns_formal/02_structural/composite.md) |
| **Decorator** | 多层嵌套 `Box` 分配 | 性能 | 按需用 `impl Trait` 或泛型链；零成本抽象 |
| **Proxy** | 委托对象未 `Send` 却跨线程 | 编译错误 | 确保 `T: Send + Sync`；见 [async_state_machine](../../formal_methods/async_state_machine.md) T6.2 |
| **Adapter** | 适配后泄漏内部类型 | 封装破坏 | 谨慎 `pub`；返回 `impl Trait` 隐藏实现 |

### 行为型陷阱

| 模式 | 常见陷阱 | 后果 | 规避 |
| :--- | :--- | :--- | :--- |
| **Observer** | 共享可变无 `Mutex` | 数据竞争 | 用 `mpsc`、`broadcast` 或 `Arc<Mutex<Vec<Callback>>>`；见 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) T1 |
| **Mediator** | 循环引用 | 泄漏 | `Weak` 打破环；见 [mediator](../01_design_patterns_formal/03_behavioral/mediator.md) |
| **Chain** | 链成环 | 无限循环 | 无环约束、`Option<Box<Handler>>` 终止；见 [chain_of_responsibility](../01_design_patterns_formal/03_behavioral/chain_of_responsibility.md) |
| **Memento** | 恢复非法状态 | 不变式违反 | 校验、`Clone` 约束；见 [memento](../01_design_patterns_formal/03_behavioral/memento.md) |
| **Iterator** | 迭代中修改集合 | 借用冲突 | 先 `collect()` 再修改；见 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) Def FOR1 |

---

## 与形式化 Def/定理衔接

| 模式族 | 形式化文档 | 核心 Def/定理 |
| :--- | :--- | :--- |
| 创建型 | [ownership_model](../../formal_methods/ownership_model.md)、[01_creational](../01_design_patterns_formal/01_creational/) | BOX1、RC1、所有权规则 2、3 |
| 结构型 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)、[02_structural](../01_design_patterns_formal/02_structural/) | 借用规则 1、2，CHAN1、MUTEX1 |
| 行为型 | [async_state_machine](../../formal_methods/async_state_machine.md)、[03_behavioral](../01_design_patterns_formal/03_behavioral/) | T6.2 并发安全、QUERY1 |

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
