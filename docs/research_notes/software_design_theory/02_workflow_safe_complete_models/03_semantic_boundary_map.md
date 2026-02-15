# 语义边界图

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 📊 目录

- [语义边界图](#语义边界图)
  - [📊 目录](#-目录)
  - [总览](#总览)
  - [三维交叉矩阵（扩展）](#三维交叉矩阵扩展)
  - [边界决策树](#边界决策树)
  - [模式选取完整示例（场景→模式→代码）](#模式选取完整示例场景模式代码)
    - [示例 1：跨平台 UI 组件族](#示例-1跨平台-ui-组件族)
    - [示例 2：HTTP 中间件链](#示例-2http-中间件链)
    - [示例 3：可撤销操作（编辑器）](#示例-3可撤销操作编辑器)
    - [示例 4：事件通知（多订阅者）](#示例-4事件通知多订阅者)
    - [示例 5：领域逻辑 + 持久化](#示例-5领域逻辑--持久化)
    - [示例 6：可撤销编辑器（完整链条）](#示例-6可撤销编辑器完整链条)
  - [场景化 Safe 决策 3 例（层次推进）](#场景化-safe-决策-3-例层次推进)
    - [场景 7：全局配置（Singleton）](#场景-7全局配置singleton)
    - [场景 8：跨线程缓存（Flyweight + Arc）](#场景-8跨线程缓存flyweight--arc)
    - [场景 9：FFI 绑定（unsafe 封装）](#场景-9ffi-绑定unsafe-封装)
  - [模式选取示例（简表）](#模式选取示例简表)
  - [反模式：误选](#反模式误选)
  - [形式化边界定理](#形式化边界定理)
  - [边界冲突与化解](#边界冲突与化解)
  - [按需求反向查模式](#按需求反向查模式)
    - [快速查找（扩展：20+ 实质场景）](#快速查找扩展20-实质场景)
    - [决策树（精简）](#决策树精简)
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
pub struct Order { id: u64, items: Vec<OrderItem>, status: OrderStatus }
impl Order {
    pub fn add_item(&mut self, item: OrderItem) -> Result<(), String> {
        if self.status != OrderStatus::Draft { return Err("...".into()); }
        self.items.push(item); Ok(())
    }
}

// Service Layer：OrderService::place_order 编排
pub struct OrderService<R: OrderRepository> { repo: R }
impl<R: OrderRepository> OrderService<R> {
    pub fn place_order(&mut self, dto: PlaceOrderDto) -> Result<u64, String> {
        let order = Order::from_dto(&dto)?;
        self.repo.save(&order)?;
        Ok(order.id)
    }
}

// Repository：trait OrderRepository { fn save(&mut self, o: &Order) -> Result<(), String>; }
// DTO：PlaceOrderRequest、OrderResponse 跨边界（serde 序列化）
```

### 示例 6：可撤销编辑器（完整链条）

**场景**：文本编辑器支持 undo/redo，需历史栈与命令封装。

**选型**：Command + Memento（可选）+ State。

**代码骨架**：

```rust
trait Command {
    fn execute(&self, ctx: &mut EditorContext);
    fn undo(&self, ctx: &mut EditorContext);
}
struct InsertCmd { text: String, pos: usize }
impl Command for InsertCmd {
    fn execute(&self, ctx: &mut EditorContext) { ctx.insert(self.pos, &self.text); }
    fn undo(&self, ctx: &mut EditorContext) { ctx.delete(self.pos, self.text.len()); }
}

struct Editor {
    undo_stack: Vec<Box<dyn Command>>,
    redo_stack: Vec<Box<dyn Command>>,
}
impl Editor {
    fn execute(&mut self, cmd: Box<dyn Command>, ctx: &mut EditorContext) {
        cmd.execute(ctx);
        self.undo_stack.push(cmd);
        self.redo_stack.clear();
    }
    fn undo(&mut self, ctx: &mut EditorContext) {
        if let Some(cmd) = self.undo_stack.pop() {
            cmd.undo(ctx);
            self.redo_stack.push(cmd);
        }
    }
}
```

---

## 场景化 Safe 决策 3 例（层次推进）

以下为需求→ Safe 选型→实现路径的实质性决策流程。

### 场景 7：全局配置（Singleton）

**需求**：应用启动时从文件加载配置，全局只读访问；多线程需共享。

**决策**：纯 Safe 优先 → 使用 `OnceLock`；避免 `static mut` / `lazy_static` 中 unsafe。

**实现**：

```rust
use std::sync::OnceLock;

struct AppConfig { db_url: String, log_level: u8 }
static CONFIG: OnceLock<AppConfig> = OnceLock::new();

fn init_config(path: &str) -> Result<(), String> {
    let cfg = AppConfig { db_url: String::from("..."), log_level: 0 };
    CONFIG.set(cfg).map_err(|_| "already init")?;
    Ok(())
}

fn config() -> &'static AppConfig {
    CONFIG.get().expect("config not initialized")
}
// 多线程：config() 返回 &'static，共享只读，Safe
```

**边界**：$B_s = \mathrm{Safe}$，$B_p = \mathrm{Native}$，$B_e = \mathrm{Same}$，符合 SB-C1。

---

### 场景 8：跨线程缓存（Flyweight + Arc）

**需求**：解析器大量重复字符串；多线程共享同一 intern 池。

**决策**：共享不可变 → Flyweight；跨线程 → `Arc` + `RwLock`；避免 `Rc`、`RefCell` 跨线程。

**实现**：

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

struct InternPool {
    map: RwLock<HashMap<String, Arc<str>>>,
}

impl InternPool {
    fn intern(&self, s: &str) -> Arc<str> {
        if let Ok(guard) = self.map.read() {
            if let Some(v) = guard.get(s) {
                return Arc::clone(v);
            }
        }
        let arc = Arc::from(s.to_string().into_boxed_str());
        self.map.write().unwrap().insert(s.to_string(), Arc::clone(&arc));
        arc
    }
}

// 跨线程：Arc<InternPool> 或 &InternPool 可传入 spawn；Arc<str> 为 Send + Sync
let pool = Arc::new(InternPool { map: RwLock::new(HashMap::new()) });
let p2 = Arc::clone(&pool);
std::thread::spawn(move || {
    let _ = p2.intern("hello");
});
```

**边界**：$B_s = \mathrm{Safe}$；`Arc`、`RwLock` 为 Safe 抽象；`Arc<str>` 不可变。

---

### 场景 9：FFI 绑定（unsafe 封装）

**需求**：调用 C 库；对外暴露 Safe Rust API。

**决策**：unsafe 隔离在最小边界；对外提供 Safe 接口 + 契约文档。

**实现**：

```rust
// ffi 模块内
#[repr(C)]
struct CConfig { enabled: i32, timeout: i32 }

extern "C" {
    fn c_init(config: *const CConfig) -> i32;
}

pub fn safe_init(enabled: bool, timeout: i32) -> Result<(), String> {
    let cfg = CConfig {
        enabled: if enabled { 1 } else { 0 },
        timeout,
    };
    let rc = unsafe { c_init(&cfg) };
    if rc == 0 { Ok(()) } else { Err("init failed".into()) }
}
```

**契约**：`c_init` 不修改 `cfg`；不持有 `cfg` 指针；调用方保证 `&cfg` 在调用期间有效（栈上保证）。

**边界**：$B_s = \mathrm{unsafe}$；内部 unsafe 封装；对外 API 为 Safe；符合 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) 封装原则。

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

### 快速查找（扩展：20+ 实质场景）

| 需求描述 | 推荐模式 | 典型 crate/实现 |
| :--- | :--- | :--- |
| 运行时决定产品类型 | Factory Method | trait + impl |
| 跨平台 UI 组件族 | Abstract Factory | 枚举产品族 |
| 配置多步骤构建、必填校验 | Builder | 类型状态、ok_or |
| 克隆已有对象 | Prototype | Clone trait |
| 全局唯一配置/连接池 | Singleton | OnceLock、LazyLock |
| 第三方 API 适配本 trait | Adapter | 结构体包装 + impl Trait |
| UI 抽象与渲染实现解耦 | Bridge | trait + 泛型 |
| 文件系统/表达式树 | Composite | 枚举递归、Box |
| 日志/鉴权链式包装 | Decorator | 结构体包装委托 |
| 多子系统简化入口 | Facade | 模块/结构体 |
| 字体/纹理跨线程共享 | Flyweight | Arc、HashMap 缓存 |
| 懒加载、访问控制 | Proxy | OnceLock、委托 |
| 中间件链、审批流 | Chain of Responsibility | Option\<Box\<Handler>> |
| 可撤销/重做 | Command | Box\<dyn Fn()> |
| DSL 表达式求值 | Interpreter | 枚举 AST + match |
| 集合遍历 | Iterator | Iterator trait |
| 聊天室、多组件协调 | Mediator | 结构体 + channel |
| 快照保存/恢复 | Memento | Clone、serde |
| 事件发布订阅 | Observer | mpsc、broadcast |
| 订单/连接状态机 | State | 枚举或类型状态 |
| 排序/加密算法切换 | Strategy | trait |
| 算法骨架 + 钩子 | Template Method | trait 默认方法 |
| AST 遍历 + 类型操作 | Visitor | match 或 trait |
| 领域逻辑封装 | Domain Model | struct + 方法 |
| 用例编排、事务 | Service Layer | struct + async fn |
| 持久化抽象 | Repository | trait + impl |
| 批量提交 | Unit of Work | 收集 + commit |
| API 请求/响应 | DTO | struct + serde |
| 支付/短信外部调用 | Gateway | trait + HTTP 客户端 |
| 业务规则组合 | Specification | trait Spec + and/or |
| 审计、事件重放 | Event Sourcing | Vec\<Event> + fold |

---

### 决策树（精简）

**设计模式选型决策树**：按需求选模式；各分支对应模式文档见 [01_design_patterns_formal §23 模式多维对比矩阵](../../01_design_patterns_formal/README.md#23-模式多维对比矩阵) 及该节下表「形式化文档」列。上表「快速查找」中「推荐模式」即本决策树叶子。

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
