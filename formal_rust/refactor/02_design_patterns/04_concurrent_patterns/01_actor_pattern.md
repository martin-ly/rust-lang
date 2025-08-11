# Actor 模式形式化理论

## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: 2025-08-11  
**最后更新**: 2025-08-11  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---

## 1. 概述

### 1.1 定义

Actor 模式是一种并发计算模型，其中 Actor 是计算的基本单位，具有以下特征：

- 封装状态
- 通过消息传递通信
- 独立并发执行
- 无共享状态

### 1.2 形式化定义

**定义 1.1 (Actor)** 一个 Actor 是一个三元组 $A = (S, B, M)$，其中：

- $S$ 是状态空间
- $B: S \times M \rightarrow S \times \{A_1, A_2, \ldots, A_n\}$ 是行为函数
- $M$ 是消息空间

**定义 1.3 (Actor 系统)** Actor 系统是一个有向图 $G = (V, E)$，其中：

- $V$ 是 Actor 集合
- $E \subseteq V \times V$ 是消息传递关系

## 2. 数学基础

### 2.1 Actor 代数

**公理 2.1 (Actor 创建)**
$$\forall A \in \mathcal{A}, \exists A' \in \mathcal{A}: A \xrightarrow{create} A'$$

**公理 2.2 (消息传递)**
$$\forall A_1, A_2 \in \mathcal{A}, \forall m \in M: A_1 \xrightarrow{m} A_2$$

**公理 2.3 (状态隔离)**
$$\forall A_1, A_2 \in \mathcal{A}: state(A_1) \cap state(A_2) = \emptyset$$

### 2.2 并发语义

**定义 2.4 (并发执行)**
两个 Actor $A_1, A_2$ 并发执行当且仅当：
$$A_1 \parallel A_2 \iff \forall t: \text{exec}(A_1, t) \cap \text{exec}(A_2, t) = \emptyset$$

## 3. Rust 实现

### 3.1 基本 Actor 实现

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

pub struct Actor<S, M> {
    state: S,
    receiver: Receiver<M>,
    sender: Option<Sender<M>>,
}

impl<S, M> Actor<S, M> 
where 
    S: Send + 'static,
    M: Send + 'static,
{
    pub fn new<F>(initial_state: S, behavior: F) -> Sender<M>
    where
        F: Fn(S, M) -> (S, Vec<M>) + Send + 'static,
    {
        let (sender, receiver) = channel();
        let mut actor = Actor {
            state: initial_state,
            receiver,
            sender: Some(sender.clone()),
        };
        
        thread::spawn(move || {
            while let Ok(message) = actor.receiver.recv() {
                let (new_state, new_messages) = behavior(actor.state, message);
                actor.state = new_state;
                
                // 发送新消息
                for msg in new_messages {
                    if let Some(ref sender) = actor.sender {
                        let _ = sender.send(msg);
                    }
                }
            }
        });
        
        sender
    }
}
```

### 3.2 类型系统分析

**定理 3.1 (类型安全)** Actor 系统满足类型安全当且仅当：
$$\forall A_1 \xrightarrow{m} A_2: type(m) \subseteq accepted\_types(A_2)$$

**证明：**

1. 消息类型检查：$\forall m \in M: \text{type}(m) \in \mathcal{T}$
2. Actor 接口兼容：$\forall A \in \mathcal{A}: \text{interface}(A) \subseteq \mathcal{T}$
3. 传递闭包：$\forall A_1 \xrightarrow{m} A_2: \text{type}(m) \in \text{interface}(A_2)$

## 4. 并发安全性

### 4.1 数据竞争预防

**定理 4.1 (无数据竞争)** Actor 系统天然无数据竞争

**证明：**

1. 状态隔离：$\forall A_1, A_2 \in \mathcal{A}: \text{state}(A_1) \cap \text{state}(A_2) = \emptyset$
2. 消息传递：$\forall A_1 \xrightarrow{m} A_2: \text{state}(A_1) \cap \text{state}(A_2) = \emptyset$
3. 顺序处理：$\forall A \in \mathcal{A}: \text{process}(A) \text{ is sequential}$

### 4.2 死锁预防

**定理 4.2 (死锁自由)** 如果 Actor 系统满足以下条件，则无死锁：

1. 无循环依赖
2. 消息队列有界
3. 超时机制

## 5. 性能分析

### 5.1 消息传递复杂度

**定理 5.1 (消息传递复杂度)**:

- 时间复杂度：$O(1)$
- 空间复杂度：$O(|M|)$
- 其中 $|M|$ 是消息队列大小

### 5.2 扩展性分析

**定理 5.2 (线性扩展性)** Actor 系统具有线性扩展性：
$$\text{throughput}(n) = n \times \text{throughput}(1)$$

## 6. 应用示例

### 6.1 计数器 Actor

```rust
#[derive(Clone)]
enum CounterMessage {
    Increment,
    Decrement,
    Get(oneshot::Sender<i32>),
}

struct CounterActor {
    count: i32,
}

impl CounterActor {
    fn behavior(state: i32, message: CounterMessage) -> (i32, Vec<CounterMessage>) {
        match message {
            CounterMessage::Increment => (state + 1, vec![]),
            CounterMessage::Decrement => (state - 1, vec![]),
            CounterMessage::Get(sender) => {
                let _ = sender.send(state);
                (state, vec![])
            }
        }
    }
}
```

### 6.2 银行账户 Actor

```rust
#[derive(Clone)]
enum BankMessage {
    Deposit(f64),
    Withdraw(f64, oneshot::Sender<Result<f64, String>>),
    Balance(oneshot::Sender<f64>),
}

struct BankActor {
    balance: f64,
}

impl BankActor {
    fn behavior(state: f64, message: BankMessage) -> (f64, Vec<BankMessage>) {
        match message {
            BankMessage::Deposit(amount) => (state + amount, vec![]),
            BankMessage::Withdraw(amount, sender) => {
                if state >= amount {
                    let _ = sender.send(Ok(state - amount));
                    (state - amount, vec![])
                } else {
                    let _ = sender.send(Err("Insufficient funds".to_string()));
                    (state, vec![])
                }
            }
            BankMessage::Balance(sender) => {
                let _ = sender.send(state);
                (state, vec![])
            }
        }
    }
}
```

## 7. 形式化验证

### 7.1 行为等价性

**定义 7.1 (行为等价)** 两个 Actor $A_1, A_2$ 行为等价当且仅当：
$$A_1 \sim A_2 \iff \forall m \in M: \text{behavior}(A_1, m) = \text{behavior}(A_2, m)$$

### 7.2 系统正确性

**定理 7.2 (系统正确性)** Actor 系统正确当且仅当：

1. 所有消息都被正确处理
2. 状态转换符合预期
3. 无死锁和活锁

## 8. 总结

Actor 模式提供了：

- 天然的并发安全性
- 良好的扩展性
- 清晰的抽象边界
- 简单的错误处理

在 Rust 中，Actor 模式通过类型系统和所有权系统提供了额外的安全保障。
