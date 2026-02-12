# 语义边界图

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [语义边界图](#语义边界图)
  - [目录](#目录)
  - [总览](#总览)
  - [三维交叉矩阵（扩展）](#三维交叉矩阵扩展)
  - [边界决策树](#边界决策树)
  - [模式选取完整示例（场景→模式→代码）](#模式选取完整示例场景模式代码)
    - [示例 1：跨平台 UI 组件族](#示例-1跨平台-ui-组件族)
    - [示例 2：HTTP 中间件链](#示例-2http-中间件链)
    - [示例 3：可撤销操作（编辑器）](#示例-3可撤销操作编辑器)
    - [示例 4：事件通知（多订阅者）](#示例-4事件通知多订阅者)
    - [示例 5：领域逻辑 + 持久化](#示例-5领域逻辑--持久化)
  - [模式选取示例（简表）](#模式选取示例简表)
  - [反模式：误选](#反模式误选)
  - [形式化边界定理](#形式化边界定理)
  - [边界冲突与化解](#边界冲突与化解)
  - [按需求反向查模式](#按需求反向查模式)
  - [与理论衔接](#与理论衔接)

---

## 总览

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                        语义边界图                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  【安全 vs 非安全】                                                          │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  纯 Safe：23 安全模型主体、扩展 20 绝大部分                             │   │
│  │  需 unsafe：Singleton 部分实现、FFI 绑定、底层同步、Gateway FFI       │   │
│  │  无法表达：极少数 OOP 特化模式（多继承、全局可变隐式共享）              │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  【支持 vs 不支持】                                                          │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  原生支持：GoF 23、std 并发、std 线程                                  │   │
│  │  库支持：async 运行时（tokio）、Rayon、Actor 框架、分布式（tonic）     │   │
│  │  需 FFI：部分分布式/系统级模式、C 库绑定                                │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  【充分 vs 非充分表达】                                                       │   │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  等价表达：大部分 GoF 模式、扩展模式（Repository、Service Layer 等）   │   │
│  │  近似表达：Singleton、Observer、Visitor、Memento、Template Method       │   │
│  │  不可表达：依赖继承/全局可变的经典 OOP 模式                             │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 三维交叉矩阵（扩展）

| 模式/模型 | 安全 | 支持 | 表达 | 说明 |
| :--- | :--- | :--- | :--- | :--- |
| Factory Method | Safe | 原生 | 等价 | trait + impl |
| Abstract Factory | Safe | 原生 | 等价 | 枚举/结构体族 |
| Builder | Safe | 原生 | 等价 | 链式 + build |
| Prototype | Safe | 原生 | 等价 | Clone |
| Singleton | Safe/unsafe | 原生 | 近似 | OnceLock 为 Safe |
| Adapter | Safe | 原生 | 等价 | 包装委托 |
| Bridge | Safe | 原生 | 等价 | trait 解耦 |
| Composite | Safe | 原生 | 等价 | 枚举递归 |
| Strategy | Safe | 原生 | 等价 | trait |
| Observer | Safe | 原生 | 近似 | channel/回调 |
| Repository | Safe | 原生 | 等价 | trait + impl |
| Service Layer | Safe | 原生 | 等价 | 模块/结构体 |
| Actor | Safe | 库 | 等价 | actix |
| 同步 | Safe | 原生 | 等价 | 默认 |
| 异步 | Safe | 库 | 等价 | tokio |
| 并发 | Safe | 原生 | 等价 | std::thread |
| 并行 | Safe | 库 | 等价 | rayon |
| 分布式 | Safe | 库 | 近似 | tonic |
| FFI 绑定 | unsafe | FFI | 近似 | extern |

---

## 边界决策树

```text
选择模式/模型？
├── 需纯 Safe？
│   ├── 是 → 排除 static mut、裸 FFI
│   └── 否 → 可使用 unsafe 封装
├── 需原生支持？
│   ├── 是 → 选用 std、trait、枚举
│   └── 否 → 可选用 tokio、rayon、tonic
└── 需等价表达？
    ├── 是 → 选用 trait、枚举、所有权语义
    └── 否 → 可接受近似（channel 替代 Observer 等）
```

---

## 模式选取完整示例（场景→模式→代码）

以下为**实质内容**：从真实需求出发，到模式选型，到可运行代码骨架。

### 示例 1：跨平台 UI 组件族

**场景**：Windows/Linux 需不同风格的按钮、文本框；运行时根据平台选择。

**选型**：Abstract Factory（产品族）。

**代码骨架**：

```rust
trait Button { fn render(&self) -> String; }
trait TextBox { fn render(&self) -> String; }
trait UIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_textbox(&self) -> Box<dyn TextBox>;
}
struct WinFactory;
impl UIFactory for WinFactory {
    fn create_button(&self) -> Box<dyn Button> { /* Win 风格 */ }
    fn create_textbox(&self) -> Box<dyn TextBox> { /* Win 风格 */ }
}
// 运行时：let factory: Box<dyn UIFactory> = if cfg!(windows) { ... } else { ... };
```

### 示例 2：HTTP 中间件链

**场景**：请求需经认证→日志→限流→业务处理。

**选型**：Chain of Responsibility。

**代码骨架**：

```rust
type Next = Option<Box<dyn Handler>>;
trait Handler {
    fn handle(&self, req: &mut Request, next: Next) -> Response;
}
struct AuthHandler { next: Next }
impl Handler for AuthHandler {
    fn handle(&self, req: &mut Request, next: Next) -> Response {
        if !validate(req) { return Response::unauthorized(); }
        next.map(|n| n.handle(req, self.next)).unwrap_or(Response::ok())
    }
}
// 链：Auth → Log → RateLimit → Service
```

### 示例 3：可撤销操作（编辑器）

**场景**：支持 undo/redo。

**选型**：Command。

**代码骨架**：

```rust
trait Command {
    fn execute(&self, ctx: &mut Context);
    fn undo(&self, ctx: &mut Context);
}
struct InsertCmd { chars: String, pos: usize }
impl Command for InsertCmd {
    fn execute(&self, ctx: &mut Context) { ctx.insert(self.pos, &self.chars); }
    fn undo(&self, ctx: &mut Context) { ctx.delete(self.pos, self.chars.len()); }
}
// 栈：undo_stack.push(cmd.execute()); redo 时 pop 并 undo
```

### 示例 4：事件通知（多订阅者）

**场景**：订单状态变更需通知库存、物流、通知服务。

**选型**：Observer（channel 实现）。

**代码骨架**：

```rust
use tokio::sync::broadcast;
let (tx, _) = broadcast::channel::<OrderEvent>(32);
// 发布者：tx.send(OrderEvent::Shipped { id: 1 });
// 订阅者：let mut rx = tx.subscribe(); while let Ok(e) = rx.recv().await { ... }
```

### 示例 5：领域逻辑 + 持久化

**场景**：订单用例：校验→创建→持久化→发事件。

**选型**：Domain Model + Service Layer + Repository + DTO。

**代码骨架**：

```rust
// Domain Model：Order 含 add_item、submit 等
// Service Layer：OrderService::place_order 编排
// Repository：OrderRepository::save
// DTO：PlaceOrderRequest、OrderResponse 跨边界
```

---

## 模式选取示例（简表）

| 需求 | 推荐模式 | 理由 |
| :--- | :--- | :--- |
| 创建对象但类型由运行时决定 | Factory Method / Abstract Factory | trait + match 或枚举 |
| 多步骤构建 | Builder | 链式 + 类型状态 |
| 适配外部接口 | Adapter | 结构体包装 + impl Trait |
| 解耦抽象与实现 | Bridge | trait 解耦 |
| 树状结构 | Composite | 枚举递归 |
| 运行时替换算法 | Strategy | trait |
| 一对多通知 | Observer | channel 或 回调 |
| 请求沿链传递 | Chain of Responsibility | Option\<Box\<Handler>> |
| 封装操作可撤销 | Command | trait 或 Fn |
| 树遍历 | Composite + Visitor | 枚举 + match |
| 多对象协调 | Mediator | 结构体 + channel/broadcast |
| 延迟加载 | Proxy | OnceLock、委托 |
| 共享不可变 | Flyweight | Arc、HashMap 缓存 |
| 状态转换 | State | 枚举或类型状态 |
| 表达式求值 | Interpreter | 枚举 AST + match |

---

## 反模式：误选

| 误选 | 后果 | 应选 |
| :--- | :--- | :--- |
| 单产品用 Abstract Factory | 过度设计 | Factory Method |
| 简单调用用 Chain | 不必要的链 | 直接调用 |
| 无共享用 Flyweight | 无收益 | 普通创建 |
| 顺序操作用 Mediator | 过度解耦 | 直接调用 |

---

## 形式化边界定理

**Def SB1（语义边界）**：设 $D$ 为设计模式或执行模型，$B_s(D)$、$B_p(D)$、$B_e(D)$ 分别为安全、支持、表达边界（见 [05_boundary_system](../05_boundary_system/README.md)）。

| 定理 | 陈述 | 证明 |
| :--- | :--- | :--- |
| **SB1** | 若 $B_s(D) = \mathrm{Safe}$，则 $D$ 的 Rust 实现不引入 UB | 由 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) 定义 1.1；Safe 子集即编译器静态验证；无 unsafe 则无 UB 契约 |
| **SB2** | 若 $B_p(D) = \mathrm{Native}$，则 $D$ 可仅用 std/core 实现 | 由 [supported_unsupported_matrix](../05_boundary_system/supported_unsupported_matrix.md) Def 1.1、定理 SUM-T1 |
| **SB3** | 若 $B_e(D) = \mathrm{Same}$，则 $D$ 的 Rust 实现与 GoF/OOP 语义等价 | 由 [expressive_inexpressive_matrix](../05_boundary_system/expressive_inexpressive_matrix.md) Def 1.2、定理 EIM-T1 |

**推论 SB-C1**：若 $D$ 满足 $B_s = \mathrm{Safe} \land B_p = \mathrm{Native} \land B_e = \mathrm{Same}$，则 $D$ 可在零依赖下安全、等价实现。

**引理 SB-L1（边界冲突可化解）**：对任意冲突「需 Safe 但传统实现用 unsafe」「需原生但功能在库」「需等价但 Rust 无继承」，存在化解策略（见下表）；策略由 05_boundary_system 与 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) 定义支持。

*证明*：由 Def SB1；化解策略为 Safe 抽象（OnceLock、Mutex）、库依赖评估、trait 组合；各策略在对应文档有形式化论证。∎

---

## 边界冲突与化解

| 冲突 | 化解 |
| :--- | :--- |
| 需 Safe 但模式传统实现用 unsafe | 用 OnceLock、Mutex 等 Safe 抽象替代 static mut |
| 需原生但功能在库 | 评估 std 是否足够；或接受库依赖 |
| 需等价但 Rust 无继承 | 用 trait + 组合；文档化差异 |

---

## 按需求反向查模式

```text
需求 → 模式映射

创建对象？ → Factory Method / Abstract Factory / Builder / Prototype
全局唯一？ → Singleton (OnceLock)
适配接口？ → Adapter
解耦实现？ → Bridge
树状结构？ → Composite
链式扩展？ → Decorator
简化多接口？ → Facade
共享不可变？ → Flyweight
延迟/控制访问？ → Proxy
链式传递？ → Chain of Responsibility
封装可撤销操作？ → Command
表达式求值？ → Interpreter
顺序遍历？ → Iterator
多对象协调？ → Mediator
保存/恢复状态？ → Memento
一对多通知？ → Observer
状态转换？ → State
可替换算法？ → Strategy
算法骨架？ → Template Method
按类型施加操作？ → Visitor

企业/分布式？
├── 领域逻辑 → Domain Model
├── 用例编排 → Service Layer
├── 持久化抽象 → Repository / Unit of Work
├── 跨边界传输 → DTO
├── 外部集成 → Gateway
├── 业务规则 → Specification
└── 审计溯源 → Event Sourcing
```

---

## 与理论衔接

- [ownership_model](../../formal_methods/ownership_model.md)、[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)
- [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md)
- [05_boundary_system](../05_boundary_system/README.md)
- [执行模型边界](../../03_execution_models/06_boundary_analysis.md)：同步/异步/并发/并行/分布式选型
