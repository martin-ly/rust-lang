# Actor 模型语义

## 目录

- [Actor 模型语义](#actor-模型语义)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 Actor 模型理论基础](#11-actor-模型理论基础)
    - [1.2 Actor 模型在 Rust 中的适用性](#12-actor-模型在-rust-中的适用性)
    - [1.3 与所有权系统的结合](#13-与所有权系统的结合)
  - [2. Actor 基本语义](#2-actor-基本语义)
    - [2.1 Actor 定义](#21-actor-定义)
      - [2.1.1 Actor 作为计算实体](#211-actor-作为计算实体)
      - [2.1.2 状态封装语义](#212-状态封装语义)
      - [2.1.3 行为定义语义](#213-行为定义语义)
    - [2.2 Actor 生命周期](#22-actor-生命周期)
      - [2.2.1 创建语义](#221-创建语义)
      - [2.2.2 启动语义](#222-启动语义)
      - [2.2.3 停止语义](#223-停止语义)
      - [2.2.4 重启语义](#224-重启语义)
    - [2.3 Actor 身份](#23-actor-身份)
      - [2.3.1 Actor 引用语义](#231-actor-引用语义)
      - [2.3.2 Actor 路径语义](#232-actor-路径语义)
      - [2.3.3 位置透明语义](#233-位置透明语义)
  - [3. 消息传递语义](#3-消息传递语义)
    - [3.1 消息语义](#31-消息语义)
      - [3.1.1 消息不可变性](#311-消息不可变性)
      - [3.1.2 消息序列化](#312-消息序列化)
      - [3.1.3 消息顺序保证](#313-消息顺序保证)
    - [3.2 发送语义](#32-发送语义)
      - [3.2.1 异步发送语义](#321-异步发送语义)
      - [3.2.2 tell vs ask 语义](#322-tell-vs-ask-语义)
      - [3.2.3 消息超时语义](#323-消息超时语义)
    - [3.3 接收语义](#33-接收语义)
      - [3.3.1 邮箱语义](#331-邮箱语义)
      - [3.3.2 消息处理语义](#332-消息处理语义)
      - [3.3.3 选择性接收语义](#333-选择性接收语义)
    - [3.4 消息保证](#34-消息保证)
      - [3.4.1 最多一次语义](#341-最多一次语义)
      - [3.4.2 至少一次语义](#342-至少一次语义)
      - [3.4.3 恰好一次语义](#343-恰好一次语义)
  - [4. Actor 并发语义](#4-actor-并发语义)
    - [4.1 单线程 Actor 语义](#41-单线程-actor-语义)
      - [4.1.1 顺序处理语义](#411-顺序处理语义)
      - [4.1.2 无锁语义](#412-无锁语义)
      - [4.1.3 公平性语义](#413-公平性语义)
    - [4.2 多线程 Actor 语义](#42-多线程-actor-语义)
      - [4.2.1 工作线程池](#421-工作线程池)
      - [4.2.2 邮箱分区](#422-邮箱分区)
      - [4.2.3 负载均衡](#423-负载均衡)
    - [4.3 Actor 隔离语义](#43-actor-隔离语义)
      - [4.3.1 状态隔离](#431-状态隔离)
      - [4.3.2 故障隔离](#432-故障隔离)
      - [4.3.3 资源隔离](#433-资源隔离)
  - [5. 监督树语义](#5-监督树语义)
    - [5.1 监督策略](#51-监督策略)
      - [5.1.1 One-For-One 语义](#511-one-for-one-语义)
      - [5.1.2 One-For-All 语义](#512-one-for-all-语义)
      - [5.1.3 Rest-For-One 语义](#513-rest-for-one-语义)
    - [5.2 故障检测](#52-故障检测)
      - [5.2.1 心跳检测语义](#521-心跳检测语义)
      - [5.2.2 崩溃检测语义](#522-崩溃检测语义)
      - [5.2.3 超时检测语义](#523-超时检测语义)
    - [5.3 恢复语义](#53-恢复语义)
      - [5.3.1 重启语义](#531-重启语义)
      - [5.3.2 升级语义](#532-升级语义)
      - [5.3.3 优雅降级语义](#533-优雅降级语义)
  - [6. Actor 组合模式](#6-actor-组合模式)
    - [6.1 父子关系](#61-父子关系)
    - [6.2 路由器模式](#62-路由器模式)
      - [6.2.1 轮询路由语义](#621-轮询路由语义)
      - [6.2.2 随机路由语义](#622-随机路由语义)
      - [6.2.3 一致性哈希路由语义](#623-一致性哈希路由语义)
      - [6.2.4 广播路由语义](#624-广播路由语义)
    - [6.3 池化模式](#63-池化模式)
  - [7. 持久化语义](#7-持久化语义)
    - [7.1 事件溯源](#71-事件溯源)
    - [7.2 至少一次投递](#72-至少一次投递)
  - [8. 分布式 Actor 语义](#8-分布式-actor-语义)
    - [8.1 远程 Actor](#81-远程-actor)
    - [8.2 集群语义](#82-集群语义)
    - [8.3 位置透明性](#83-位置透明性)
  - [9. 流处理语义](#9-流处理语义)
    - [9.1 Actor 流](#91-actor-流)
    - [9.2 流组合](#92-流组合)
  - [10. 测试语义](#10-测试语义)
    - [10.1 单元测试](#101-单元测试)
    - [10.2 集成测试](#102-集成测试)
  - [11. Rust Actor 框架对比](#11-rust-actor-框架对比)
    - [11.1 Actix 语义](#111-actix-语义)
    - [11.2 Bastion 语义](#112-bastion-语义)
    - [11.3 coerce 语义](#113-coerce-语义)
    - [11.4 Xtra 语义](#114-xtra-语义)
  - [12. Actor 与所有权](#12-actor-与所有权)
    - [12.1 所有权转移](#121-所有权转移)
    - [12.2 生命周期管理](#122-生命周期管理)
    - [12.3 类型安全](#123-类型安全)
  - [13. 性能语义](#13-性能语义)
    - [13.1 吞吐量](#131-吞吐量)
    - [13.2 延迟](#132-延迟)
    - [13.3 内存效率](#133-内存效率)
  - [14. 总结](#14-总结)

---

## 1. 引言

### 1.1 Actor 模型理论基础

**Actor 模型**是由 Carl Hewitt 于 1973 年提出的并发计算模型，它将并发计算的基本单元抽象为 **Actor**，每个 Actor 是一个独立的计算实体，具有以下核心特性：

$$
\text{Actor} = \text{Identity} \times \text{Behavior} \times \text{Mailbox} \times \text{State}
$$

**Actor 模型的三大基本操作：**

| 操作 | 语义 | 形式化表示 |
|-----|------|-----------|
| **创建 (Create)** | 创建新的 Actor | $\text{Create} : \text{Behavior} \to \text{ActorRef}$ |
| **发送 (Send)** | 向 Actor 发送消息 | $\text{Send} : \text{ActorRef} \times \text{Message} \to ()$ |
| **接收 (Receive)** | 处理邮箱中的消息 | $\text{Receive} : \text{Mailbox} \to \text{Behavior}'$ |

**Actor 模型的核心原则：**

1. **封装性**：每个 Actor 封装自己的状态，只能通过消息传递进行交互
2. **位置透明性**：发送者无需知道接收者的物理位置
3. **无共享状态**：Actor 之间不共享内存，避免数据竞争
4. **异步通信**：所有消息传递都是异步的

```rust
// Actor 模型的基本语义示意
trait Actor {
    type Message: Send;
    fn handle_message(&mut self, msg: Self::Message) -> impl Future<Output = ()>;
}

struct ActorRef<M> {
    id: ActorId,
    sender: Box<dyn Sender<M>>,
}

impl<M: Send> ActorRef<M> {
    fn send(&self, msg: M) -> Result<(), SendError> {
        self.sender.send(msg)
    }
}
```

### 1.2 Actor 模型在 Rust 中的适用性

Rust 的所有权系统与 Actor 模型具有天然的契合性：

$$
\text{Rust Ownership} + \text{Actor Model} \implies \text{Safe Concurrency}
$$

**契合点分析：**

| Rust 特性 | Actor 模型需求 | 语义契合 |
|----------|---------------|---------|
| **所有权转移** | 消息传递的所有权转移 | 天然匹配 |
| **Send trait** | 跨线程消息安全 | 编译时保证 |
| **生命周期** | Actor 生命周期管理 | RAII 模式 |
| **类型系统** | 消息类型安全 | 编译时检查 |
| **无共享状态** | Actor 隔离语义 | 理念一致 |

```rust
// Rust 所有权与 Actor 消息传递的语义契合
use std::sync::mpsc;

fn ownership_in_actor_semantics() {
    let (tx, rx) = mpsc::channel::<String>();

    std::thread::spawn(move || {
        let mut state = Vec::new();
        for msg in rx {
            state.push(msg);  // 所有权转移到 Actor
        }
    });

    let data = String::from("important data");
    tx.send(data).unwrap();  // 所有权转移
    // data 不能再使用
}
```

### 1.3 与所有权系统的结合

**消息所有权语义：**

$$
\text{Send}(msg, A_1 \to A_2) \implies \text{Own}(msg, A_1) \leadsto \text{Own}(msg, A_2)
$$

```rust
struct MyActor {
    state: ActorState,
    children: Vec<ActorRef<ChildMsg>>,
}

impl Actor for MyActor {
    async fn handle(&mut self, msg: Self::Message) {
        match msg {
            MyMessage::Update(data) => {
                self.state.data = data;  // 所有权转移到 Actor
            }
            MyMessage::Query(reply_to) => {
                let _ = reply_to.send(self.state.data.clone());
            }
        }
    }
}
```

---

## 2. Actor 基本语义

### 2.1 Actor 定义

#### 2.1.1 Actor 作为计算实体

$$
\text{Actor} \equiv \langle \text{id}, \sigma, \beta, \mu \rangle
$$

```rust
use actix::prelude::*;

struct MyActor {
    id: u64,
    counter: i32,
}

impl Actor for MyActor {
    type Context = Context<Self>;
    fn started(&mut self, _ctx: &mut Self::Context) {
        println!("Actor {} started", self.id);
    }
}

#[derive(Message)]
#[rtype(result = "i32")]
struct Increment(i32);

impl Handler<Increment> for MyActor {
    type Result = i32;
    fn handle(&mut self, msg: Increment, _ctx: &mut Self::Context) -> Self::Result {
        self.counter += msg.0;
        self.counter
    }
}
```

#### 2.1.2 状态封装语义

```rust
use bastion::prelude::*;

struct Counter {
    count: i32,
    history: Vec<i32>,
}

fn counter_behavior(ctx: &mut Context) -> BastionPath {
    receive! { ctx,
        msg: i32 => {
            let counter = ctx.state::<Counter>().unwrap();
            counter.count += msg;
            counter.history.push(counter.count);
        }
    }
}
```

#### 2.1.3 行为定义语义

```rust
use xtra::prelude::*;

struct Greeter {
    greeted: Vec<String>,
}

struct Greet(String);

#[async_trait]
impl Handler<Greet> for Greeter {
    type Return = String;
    async fn handle(&mut self, message: Greet, _ctx: &mut Context<Self>) -> Self::Return {
        let Greet(name) = message;
        self.greeted.push(name.clone());
        format!("Hello, {}!", name)
    }
}
```

### 2.2 Actor 生命周期

#### 2.2.1 创建语义

$$
\text{spawn} : \text{Behavior} \times \text{Args} \to \text{ActorRef}
$$

```rust
use actix::prelude::*;

#[actix_rt::main]
async fn main() {
    let addr = MyActor { id: 1, counter: 0 }.start();
    let addr2 = addr.clone();
    let result = addr.send(Increment(5)).await.unwrap();
}
```

#### 2.2.2 启动语义

```rust
use coerce::actor::system::ActorSystem;

struct MyActor {
    initialized: bool,
}

#[async_trait]
impl Actor for MyActor {
    async fn started(&mut self, ctx: &mut ActorContext) {
        self.initialized = true;
    }
}

async fn spawn_example() {
    let system = ActorSystem::new();
    let actor_ref = system.spawn(MyActor { initialized: false }).await.unwrap();
}
```

#### 2.2.3 停止语义

$$
\text{stop}(a) \implies \text{drain}(\mu_a) \land \text{cleanup}(\sigma_a) \land \text{notify}(\text{supervisor})
$$

```rust
impl Actor for MyActor {
    fn stopping(&mut self, _ctx: &mut Self::Context) -> Running {
        Running::Stop
    }
    fn stopped(&mut self, _ctx: &mut Self::Context) {
        println!("Cleanup complete");
    }
}
```

#### 2.2.4 重启语义

```rust
use bastion::prelude::*;

fn supervision_strategy() -> SupervisionStrategy {
    SupervisionStrategy::OneForOne {
        restart_policy: RestartPolicy::Always,
        restart_after: Duration::from_secs(5),
        max_retries: 3,
    }
}
```

### 2.3 Actor 身份

#### 2.3.1 Actor 引用语义

$$
\text{ActorRef} : \text{Actor} \to \text{Handle}
$$

```rust
fn actor_ref_semantics() {
    let addr = Worker.start();
    let addr2 = addr.clone();
    let addr3 = addr.clone();

    addr.do_send(Task("task1".into()));
    addr2.do_send(Task("task2".into()));
}
```

#### 2.3.2 Actor 路径语义

$$
\text{Path} = /\text{system}/\text{supervisor}/\text{actor}
$$

```rust
async fn find_by_path(system: &ActorSystem) {
    let path = "/user/worker/1";
    if let Some(actor_ref) = system.actor_of_path(path).await {
        println!("Found actor: {:?}", actor_ref.id());
    }
}
```

#### 2.3.3 位置透明语义

```rust
async fn location_transparent_send(
    local_actor: ActorRef<MyActor>,
    remote_actor: ActorRef<MyActor>,
) {
    let _ = local_actor.send(Message::Hello);
    let _ = remote_actor.send(Message::Hello);  // 通过网络发送
}
```

---

## 3. 消息传递语义

### 3.1 消息语义

#### 3.1.1 消息不可变性

$$
\forall m : \text{Message}. \text{immutable}(m) \implies \text{safe\_share}(m)
$$

#### 3.1.2 消息序列化

$$
\text{serialize} : M \to \text{Bytes}
$$

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(tag = "type")]
enum ClusterMessage {
    Heartbeat { node_id: String, timestamp: u64 },
    Command { cmd: String, args: Vec<String> },
}
```

#### 3.1.3 消息顺序保证

$$
\text{send}(a, m_1) \prec \text{send}(a, m_2) \implies \text{receive}(a, m_1) \prec \text{receive}(a, m_2)
$$

### 3.2 发送语义

#### 3.2.1 异步发送语义

$$
\text{send} : \text{ActorRef} \times M \to \text{Future}\langle \text{Result} \rangle
$$

#### 3.2.2 tell vs ask 语义

| 模式 | 语义 | 返回类型 | 使用场景 |
|-----|------|---------|---------|
| **Tell** | 发送即忘 | `()` | 事件通知 |
| **Ask** | 请求-响应 | `Future<Response>` | 需要返回值 |

```rust
fn tell_semantics(addr: Addr<MyActor>) {
    addr.do_send(UpdateData { value: 42 });  // fire-and-forget
}

async fn ask_semantics(addr: Addr<Calculator>) -> i32 {
    addr.send(Add(1, 2)).await.unwrap()
}
```

#### 3.2.3 消息超时语义

$$
\text{ask}(r, m, t) = \begin{cases}
\text{Ok}(v) & \text{if } \text{response} \in t \\
\text{Err}(\text{Timeout}) & \text{otherwise}
\end{cases}
$$

```rust
async fn ask_with_timeout(addr: Addr<DatabaseActor>) -> Result<Row, Error> {
    addr.send(Query("SELECT * FROM users".into()))
        .timeout(Duration::from_secs(5))
        .await
}
```

### 3.3 接收语义

#### 3.3.1 邮箱语义

$$
\mu : \text{Queue}\langle M \rangle
$$

#### 3.3.2 消息处理语义

$$
\text{handle} : M \times \Sigma \to \Sigma' \times \text{Effects}^*
$$

#### 3.3.3 选择性接收语义

```rust
use bastion::prelude::*;

fn selective_receive(ctx: &mut Context) -> BastionPath {
    receive! { ctx,
        msg: HighPriority => handle_urgent(msg),
        msg: NormalPriority => handle_normal(msg),
        after(Duration::from_secs(30)) => handle_timeout()
    }
}
```

### 3.4 消息保证

#### 3.4.1 最多一次语义

$$
P(\text{deliver}(m)) \leq 1
$$

#### 3.4.2 至少一次语义

$$
\text{deliver}(m) \geq 1 \implies \text{ack}(m) \lor \text{retry}(m)
$$

#### 3.4.3 恰好一次语义

$$
\text{deliver}(m) = 1 \iff \text{idempotent}(m) \land \text{dedup}(m)
$$

---

## 4. Actor 并发语义

### 4.1 单线程 Actor 语义

#### 4.1.1 顺序处理语义

$$
\forall m_1, m_2 \in \mu. \text{receive}(m_1) \prec \text{receive}(m_2) \implies \text{handle}(m_1) \prec \text{handle}(m_2)
$$

#### 4.1.2 无锁语义

单线程 Actor 天然无锁。

#### 4.1.3 公平性语义

### 4.2 多线程 Actor 语义

#### 4.2.1 工作线程池

```rust
use actix::prelude::*;

struct CpuIntensiveActor;
impl Actor for CpuIntensiveActor {
    type Context = SyncContext<Self>;
}

fn create_thread_pool() -> Addr<CpuIntensiveActor> {
    SyncArbiter::start(4, || CpuIntensiveActor)
}
```

#### 4.2.2 邮箱分区

#### 4.2.3 负载均衡

### 4.3 Actor 隔离语义

#### 4.3.1 状态隔离

$$
\forall a_1, a_2 : \text{Actor}. a_1 \neq a_2 \implies \sigma_{a_1} \cap \sigma_{a_2} = \emptyset
$$

#### 4.3.2 故障隔离

```rust
use bastion::prelude::*;

fn fault_isolation() {
    Bastion::supervisor(|sp| {
        sp.children(|ch| {
            ch.with_exec(|_ctx| async move {
                panic!("This Actor failed!");
            })
        })
        .with_exec(|ctx| async move {
            loop {  // 即使上面的 Actor panic，这个 Actor 继续运行
                receive! { ctx, msg: String => println!("Still working: {}", msg) }
            }
        })
    }).unwrap();
}
```

#### 4.3.3 资源隔离

---

## 5. 监督树语义

### 5.1 监督策略

#### 5.1.1 One-For-One 语义

$$
\text{failure}(c_i) \implies \text{restart}(c_i) \land \forall j \neq i. \neg\text{affect}(c_j)
$$

```rust
use bastion::prelude::*;

fn one_for_one_supervisor() {
    Bastion::supervisor(|sp| {
        sp.with_strategy(SupervisionStrategy::OneForOne {
            restart_policy: RestartPolicy::Always,
            max_retries: 3,
        })
        .children(|ch| ch.with_exec(worker1))
        .children(|ch| ch.with_exec(worker2))
    }).unwrap();
}
```

#### 5.1.2 One-For-All 语义

$$
\text{failure}(c_i) \implies \forall j. \text{restart}(c_j)
$$

#### 5.1.3 Rest-For-One 语义

$$
\text{failure}(c_i) \implies \forall j > i. \text{restart}(c_j)
$$

### 5.2 故障检测

#### 5.2.1 心跳检测语义

#### 5.2.2 崩溃检测语义

#### 5.2.3 超时检测语义

### 5.3 恢复语义

#### 5.3.1 重启语义

#### 5.3.2 升级语义

#### 5.3.3 优雅降级语义

---

## 6. Actor 组合模式

### 6.1 父子关系

$$
\text{Parent}(p, c) \implies \text{supervise}(p, c) \land \text{lifecycle}(p) \supset \text{lifecycle}(c)
$$

### 6.2 路由器模式

#### 6.2.1 轮询路由语义

$$
\text{route}(m, \{a_1, ..., a_n\}) = a_{(i \mod n)}
$$

#### 6.2.2 随机路由语义

#### 6.2.3 一致性哈希路由语义

#### 6.2.4 广播路由语义

### 6.3 池化模式

---

## 7. 持久化语义

### 7.1 事件溯源

$$
\sigma_n = \text{fold}(\text{apply}, \sigma_0, [e_1, e_2, ..., e_n])
$$

### 7.2 至少一次投递

---

## 8. 分布式 Actor 语义

### 8.1 远程 Actor

$$
\text{ActorRef} = \text{Local}(id) \mid \text{Remote}(node, id)
$$

### 8.2 集群语义

### 8.3 位置透明性

---

## 9. 流处理语义

### 9.1 Actor 流

$$
\text{rate}(\text{producer}) \leq \text{capacity}(\text{consumer}) - \text{backlog}(\text{consumer})
$$

### 9.2 流组合

---

## 10. 测试语义

### 10.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use actix::prelude::*;

    #[actix_rt::test]
    async fn test_counter_actor() {
        let addr = Counter { count: 0 }.start();
        let result = addr.send(Increment(5)).await.unwrap();
        assert_eq!(result, 5);
    }
}
```

### 10.2 集成测试

---

## 11. Rust Actor 框架对比

### 11.1 Actix 语义

- **同步 Actor 语义**：`SyncArbiter` + `SyncContext`
- **异步 Actor 语义**：`Context` + `ResponseFuture`
- **流支持语义**：`StreamHandler`

### 11.2 Bastion 语义

- **监督树语义**：层次化监督
- **容错语义**：panic 捕获和恢复
- **消息传递语义**：`receive!` 宏

### 11.3 coerce 语义

- **远程 Actor 语义**：位置透明的网络通信
- **集群语义**：Gossip 协议和分片
- **持久化语义**：事件溯源支持

### 11.4 Xtra 语义

- **轻量级语义**：最小化 trait 实现
- **异步优先语义**：原生 `async/await`
- **可扩展性语义**：装饰器模式和作用域 Actor

---

## 12. Actor 与所有权

### 12.1 所有权转移

$$
\text{send}(a, m) \implies \text{Own}(m, a_{\text{sender}}) \leadsto \text{Own}(m, a_{\text{receiver}})
$$

### 12.2 生命周期管理

### 12.3 类型安全

---

## 13. 性能语义

### 13.1 吞吐量

- 消息处理速率
- 批处理语义
- 流水线语义

### 13.2 延迟

- 消息传递延迟
- 处理延迟
- 尾延迟优化

### 13.3 内存效率

- Actor 内存占用
- 邮箱内存管理
- 零拷贝优化

---

## 14. 总结

Actor 模型为 Rust 提供了强大的并发编程抽象，其与 Rust 所有权系统的深度结合使得编写安全、高效的并发程序成为可能。
本文档从语义角度深入分析了 Actor 模型的各个方面：

1. **Actor 基本语义**：定义、生命周期、身份
2. **消息传递语义**：发送、接收、保证级别
3. **并发语义**：单线程、多线程、隔离
4. **监督语义**：故障检测、恢复策略
5. **组合模式**：路由、池化、父子关系
6. **持久化语义**：事件溯源、可靠投递
7. **分布式语义**：远程 Actor、集群、位置透明
8. **流处理语义**：背压、缓冲、窗口
9. **测试语义**：单元测试、集成测试、故障注入

通过对比 Actix、Bastion、coerce 和 Xtra 等框架，我们可以看到不同设计哲学下的语义选择。
开发者应根据具体需求选择合适的框架和语义模型，构建可靠的并发系统。
