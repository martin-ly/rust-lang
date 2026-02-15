# Observer 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 行为型
> **安全边界**: 纯 Safe 或 需 Mutex
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 19 行（Observer）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Observer 形式化分析](#observer-形式化分析)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [完整场景示例：订单事件通知（mpsc 单订阅者）](#完整场景示例订单事件通知mpsc-单订阅者)
  - [证明思路](#证明思路)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例](#反例)
  - [选型决策树](#选型决策树)
  - [与 GoF 对比](#与-gof-对比)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Observer 结构）**:

设 $S$ 为主体类型，$O$ 为观察者类型。Observer 满足：

- $S$ 持有观察者集合：$S \supset \mathrm{Collection}\langle O \rangle$
- $\mathit{notify}(s)$ 调用每个 $o \in s.\mathit{observers}$ 的 $\mathit{update}(\mathit{event})$
- 订阅/取消：$\mathit{attach}(s, o)$，$\mathit{detach}(s, o)$

**Axiom OB1**：通知顺序可定义；无循环回调导致栈溢出。

**Axiom OB2**：观察者回调中不可修改主体（或需内部可变性）；否则借用冲突。

**定理 OB-T1**：`mpsc` 或 `broadcast` channel 为纯 Safe；消息传递无共享可变。由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md) 与 Send/Sync。

**定理 OB-T2**：共享 `Rc<RefCell<Vec<Callback>>>` 需 `RefCell` 运行时借用检查；`Mutex` 为 Safe 抽象。由 [ownership_model](../../../formal_methods/ownership_model.md) 与 unsafe 契约。

**推论 OB-C1**：Channel 实现 Observer 为纯 Safe；`mpsc`/`broadcast` 消息传递无共享可变。由 OB-T1、OB-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Observer 结构）、Axiom OB1/OB2（通知顺序、无循环、借用约束） | 上 |
| **属性关系层** | Axiom OB1/OB2 → 定理 OB-T1/OB-T2 → 推论 OB-C1；依赖 borrow、ownership、Send/Sync | 上 |
| **解释论证层** | 证明思路：channel 无共享可变、RefCell 运行时检查；反例：反例小节 | §证明思路、§反例 |

---

## Rust 实现与代码示例

### 方式一：Channel（纯 Safe，推荐）

```rust
use std::sync::mpsc;

struct Subject {
    sender: mpsc::Sender<String>,
}

impl Subject {
    fn new() -> (Self, mpsc::Receiver<String>) {
        let (tx, rx) = mpsc::channel();
        (Self { sender: tx }, rx)
    }
    fn notify(&self, event: &str) {
        let _ = self.sender.send(event.to_string());
    }
}

// 观察者从 Receiver 读取
let (subject, receiver) = Subject::new();
subject.notify("event");
assert_eq!(receiver.recv().unwrap(), "event");
```

### 方式二：回调 Vec（需内部可变）

```rust
use std::cell::RefCell;

type Callback = Box<dyn Fn(&str)>;

struct Subject {
    callbacks: RefCell<Vec<Callback>>,
}

impl Subject {
    fn attach(&self, cb: Callback) {
        self.callbacks.borrow_mut().push(cb);
    }
    fn notify(&self, event: &str) {
        for cb in self.callbacks.borrow().iter() {
            cb(event);
        }
    }
}
```

**形式化对应**：Channel 方式无共享可变；回调方式 `RefCell` 提供运行时借用检查，仍为 Safe。

---

## 完整场景示例：订单事件通知（mpsc 单订阅者）

**场景**：订单服务发布事件；计费模块订阅并处理；跨线程、无共享可变。

```rust
use std::sync::mpsc;
use std::thread;

enum OrderEvent { Created(u64), Paid(u64) }

fn main() {
    let (tx, rx) = mpsc::channel::<OrderEvent>();

    // 订阅者：在独立线程处理事件
    let handle = thread::spawn(move || {
        for ev in rx {
            match ev {
                OrderEvent::Created(id) => println!("[订阅者] 订单 {} 已创建", id),
                OrderEvent::Paid(id) => println!("[订阅者] 订单 {} 已付款", id),
            }
        }
    });

    // 发布者：主线程发送事件
    tx.send(OrderEvent::Created(1)).unwrap();
    tx.send(OrderEvent::Paid(1)).unwrap();
    drop(tx);  // 关闭发送端，rx 循环结束

    handle.join().unwrap();
}
```

**形式化对应**：`tx`/`rx` 为消息传递；无共享可变；Send 约束保证跨线程安全；由 OB-T1 纯 Safe。多订阅者可用 `broadcast::channel` 或每订阅者一对 `mpsc::channel`。

---

## 证明思路

1. **Channel**：Sender/Receiver 分离；无共享状态。Send 转移所有权，符合 ownership。
2. **RefCell**：`borrow()` 与 `borrow_mut()` 互斥在运行时检查；违反时 panic 而非 UB。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Command](command.md) | 观察者可接收命令；命令可作为事件 |
| [Mediator](mediator.md) | 同为解耦；Observer 一对多，Mediator 集中路由 |
| [State](state.md) | 状态转换可通知观察者 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `mpsc::channel` | 单消费者；所有权转移 | 事件队列、任务分发 |
| `broadcast::channel` | 多消费者；克隆消息 | 广播、Pub/Sub |
| `RefCell<Vec<Callback>>` | 回调注册；单线程 | 简单事件、UI 回调 |

---

## 反例

**反例**：`Vec<Box<dyn Fn(&Event)>>` 回调中修改共享可变状态且无 `Mutex` → 数据竞争。应使用 channel 或 `Arc<Mutex<Vec<...>>>`。

---

## 选型决策树

```text
需要一对多通知？
├── 是 → 跨线程？ → mpsc/broadcast channel（纯 Safe）
│       └── 单线程？ → RefCell<Vec<Callback>>
├── 需多对象协调？ → Mediator
└── 需封装操作？ → Command
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| Subject/Observer 继承 | channel 或 回调 Vec | 无继承；消息传递 |
| 注册/注销 | 持有 Sender / Vec push | 等价 |
| 通知顺序 | channel FIFO / Vec 顺序 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | Safe（channel）或 Safe（RefCell/Mutex） |
| 支持 | 原生 |
| 表达 | 近似（无继承） |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Observer 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、定理 OB-T1（L2） |
| 代码 | ✅ | 可运行示例、订单通知 |
| 场景 | ✅ | 典型场景、完整示例 |
| 反例 | ✅ | 反例小节 |
| 衔接 | ✅ | mpsc、Send/Sync、CE-T2 |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
