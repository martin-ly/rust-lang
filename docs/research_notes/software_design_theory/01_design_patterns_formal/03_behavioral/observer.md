# Observer 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe 或 需 Mutex

---

## 形式化定义

**Def 1.1（Observer 结构）**

设 $S$ 为主体类型，$O$ 为观察者类型。Observer 满足：

- $S$ 持有观察者集合：$S \supset \mathrm{Collection}\langle O \rangle$
- $\mathit{notify}(s)$ 调用每个 $o \in s.\mathit{observers}$ 的 $\mathit{update}(\mathit{event})$
- 订阅/取消：$\mathit{attach}(s, o)$，$\mathit{detach}(s, o)$

**Axiom OB1**：通知顺序可定义；无循环回调导致栈溢出。

**Axiom OB2**：观察者回调中不可修改主体（或需内部可变性）；否则借用冲突。

**定理 OB-T1**：`mpsc` 或 `broadcast` channel 为纯 Safe；消息传递无共享可变。由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md) 与 Send/Sync。

**定理 OB-T2**：共享 `Rc<RefCell<Vec<Callback>>>` 需 `RefCell` 运行时借用检查；`Mutex` 为 Safe 抽象。由 [ownership_model](../../../formal_methods/ownership_model.md) 与 unsafe 契约。

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

## 证明思路

1. **Channel**：Sender/Receiver 分离；无共享状态。Send 转移所有权，符合 ownership。
2. **RefCell**：`borrow()` 与 `borrow_mut()` 互斥在运行时检查；违反时 panic 而非 UB。

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Command](command.md) | 观察者可接收命令；命令可作为事件 |
| [Mediator](mediator.md) | 同为解耦；Observer 一对多，Mediator 集中路由 |
| [State](state.md) | 状态转换可通知观察者 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| `mpsc::channel` | 单消费者；所有权转移 | 事件队列、任务分发 |
| `broadcast::channel` | 多消费者；克隆消息 | 广播、Pub/Sub |
| `RefCell<Vec<Callback>>` | 回调注册；单线程 | 简单事件、UI 回调 |

---

## 反例

**反例**：`Vec<Box<dyn Fn(&Event)>>` 回调中修改共享可变状态且无 `Mutex` → 数据竞争。应使用 channel 或 `Arc<Mutex<Vec<...>>>`。

---

## 选型决策树

```
需要一对多通知？
├── 是 → 跨线程？ → mpsc/broadcast channel（纯 Safe）
│       └── 单线程？ → RefCell<Vec<Callback>>
├── 需多对象协调？ → Mediator
└── 需封装操作？ → Command
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
|-----|-----------|------|
| Subject/Observer 继承 | channel 或 回调 Vec | 无继承；消息传递 |
| 注册/注销 | 持有 Sender / Vec push | 等价 |
| 通知顺序 | channel FIFO / Vec 顺序 | 等价 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | Safe（channel）或 Safe（RefCell/Mutex） |
| 支持 | 原生 |
| 表达 | 近似（无继承） |
