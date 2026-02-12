# Mediator 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Mediator 结构）**:

设 $M$ 为中介者类型，$C_1, \ldots, C_n$ 为同事类型。Mediator 满足：

- $M$ 持有或可访问 $C_1, \ldots, C_n$
- $C_i$ 通过 $M$ 与 $C_j$ 通信，而非直接引用
- $\mathit{mediate}(m, c_i, \mathit{msg})$ 由 $M$ 路由至目标

**Axiom ME1**：同事间无直接耦合；仅通过中介通信。

**Axiom ME2**：避免循环引用；用 `Weak` 或重构为无环。

**定理 ME-T1**：`Rc`/`Weak` 或 `Arc` 管理循环引用时避免自引用；由 [ownership_model](../../../formal_methods/ownership_model.md) 与借用规则。

**推论 ME-C1**：Mediator 为纯 Safe；`Vec<Box<dyn Fn>>` 或 channel 路由，无 `unsafe`。由 ME-T1 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
struct Mediator {
    handlers: Vec<Box<dyn Fn(&str)>>,
}

impl Mediator {
    fn broadcast(&self, msg: &str) {
        for h in &self.handlers {
            h(msg);
        }
    }
}

// 同事通过 Mediator 通信
let m = Mediator {
    handlers: vec![
        Box::new(|msg| println!("A received: {}", msg)),
        Box::new(|msg| println!("B received: {}", msg)),
    ],
};
m.broadcast("hello");
```

**带 Rc/Weak 的循环引用版本**（同事互不知晓，仅知 Mediator）：

```rust
use std::rc::{Rc, Weak};

struct Mediator { colleagues: Vec<Weak<Colleague>> }
struct Colleague { name: String }

impl Mediator {
    fn broadcast(&self, msg: &str) {
        for w in &self.colleagues {
            if let Some(c) = w.upgrade() {
                println!("{} got: {}", c.name, msg);
            }
        }
    }
}
```

**形式化对应**：`Mediator` 即 $M$；`Colleague` 即 $C_i$；`send` 通过 mediator 路由。

---

## 证明思路

1. **无直接耦合**：Colleague 不持有其他 Colleague；仅持有 Mediator。
2. **Weak 破环**：Mediator 用 `Weak<Colleague>` 避免循环；`upgrade` 获取临时 `Rc`。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 对话框/表单 | 多个控件互不引用，通过 Mediator 协调 |
| 聊天室 | 用户仅知 Mediator，消息经其广播 |
| 工作流编排 | 任务节点通过协调器通信 |
| 事件总线 | 发布/订阅中心化路由 |

---

## 完整场景示例：聊天室（channel 实现）

**场景**：多用户聊天；用户仅知 Mediator，消息经其广播；无直接 P2P 引用。

```rust
use std::sync::mpsc;
use std::thread;

struct ChatMessage { from: String, content: String }

struct ChatMediator {
    tx: mpsc::Sender<ChatMessage>,
}

impl ChatMediator {
    fn broadcast(&self, msg: ChatMessage) {
        let _ = self.tx.send(msg);
    }
}

fn run_room(rx: mpsc::Receiver<ChatMessage>) {
    for msg in rx {
        println!("[broadcast] {}: {}", msg.from, msg.content);
    }
}

// 使用：Mediator 持有 tx；各 Colleague 持 Mediator 引用，发送时 mediator.broadcast(msg)
// let (tx, rx) = mpsc::channel();
// thread::spawn(move || run_room(rx));
// let m = ChatMediator { tx };
// m.broadcast(ChatMessage { from: "A".into(), content: "hi".into() });
```

**形式化对应**：`ChatMediator` 即 $M$；`ChatMessage` 为路由消息；Colleague 仅持 `&ChatMediator`，无直接引用；Axiom ME1 满足。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Observer](observer.md) | 同为解耦；Mediator 集中路由，Observer 一对多 |
| [Facade](../02_structural/facade.md) | Facade 简化接口；Mediator 协调多对象 |
| [Chain of Responsibility](chain_of_responsibility.md) | 链式传递 vs 集中路由 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `Vec<Box<dyn Fn>>` | 广播回调；无同事引用 | 简单事件总线 |
| `Weak<Colleague>` | 同事注册；避免循环 | 需同事身份 |
| channel | 消息传递；完全解耦 | 异步、跨线程 |

---

## 反例：同事直接引用

**错误**：Colleague 直接持有其他 Colleague 的引用，绕过 Mediator。

```rust
struct BadColleague {
    mediator: Rc<Mediator>,
    other: Rc<Colleague>,  // 直接耦合，违反 Axiom ME1
}
```

**后果**：失去中介意义；耦合难以维护；修改路由逻辑需改所有 Colleague。

---

## 选型决策树

```text
需要多对象协调、避免直接耦合？
├── 是 → 集中路由？ → Mediator（结构体 + channel / Weak）
├── 需一对多通知？ → Observer
├── 需简化多接口？ → Facade
└── 需沿链传递？ → Chain of Responsibility
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 中介者接口 | trait 或 结构体 | 等价 |
| 同事注册 | Vec、Weak | 等价 |
| 无直接引用 | 仅持 Mediator | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
