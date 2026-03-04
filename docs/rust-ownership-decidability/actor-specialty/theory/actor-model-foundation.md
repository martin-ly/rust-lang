# Actor模型理论基础

> **从Hewitt论文到现代实现：Actor模型的完整理论**

---

## 1. Actor模型历史与定义

### 1.1 历史背景

```text
Actor模型发展时间线:

1973  ┌─────────────────────────────────────┐
      │ Carl Hewitt提出Actor模型            │
      │ 论文: "A Universal Modular Actor    │
      │        Formalism for AI"            │
      └─────────────────────────────────────┘
           │
1985  ┌────┴────────────────────────────────┐
      │ Gul Agha形式化Actor语义             │
      │ 论文: "Actors: A Model of           │
      │        Concurrent Computation"      │
      └─────────────────────────────────────┘
           │
1986  ┌────┴────────────────────────────────┐
      │ Erlang诞生 (Ericsson)               │
      │ 第一个工业级Actor语言               │
      └─────────────────────────────────────┘
           │
1995  ┌────┴────────────────────────────────┐
      │ Akka项目开始 (Scala/Java)           │
      │ JVM生态的Actor实现                  │
      └─────────────────────────────────────┘
           │
2009  ┌────┴────────────────────────────────┐
      │ Akka 1.0发布                        │
      │ 企业级Actor框架成熟                 │
      └─────────────────────────────────────┘
           │
2013  ┌────┴────────────────────────────────┐
      │ Actix框架 (Rust)                    │
      │ 高性能Actor系统                     │
      └─────────────────────────────────────┘
           │
2020  ┌────┴────────────────────────────────┐
      │ Bastion框架 (Rust)                  │
      │ 容错Actor系统                       │
      └─────────────────────────────────────┘
           │
2024  ┌────┴────────────────────────────────┐
      │ Rust Actor生态成熟                  │
      │ Actix, Bastion, coerce, Xtra        │
      └─────────────────────────────────────┘
```

### 1.2 Actor定义

**Hewitt原始定义 (1973)**:

> An Actor is an autonomous concurrent object that communicates asynchronously with other Actors.

**形式化定义 ACTOR-DEF-1**:

$$
\text{Actor} = (Behavior, Mailbox, State)
$$

其中：

- $Behavior$ : 消息处理函数 $\text{Message} \times \text{State} \to \text{Effect}$
- $Mailbox$ : 异步消息队列
- $State$ : 内部状态 (对其他Actor不可见)

### 1.3 Actor公理

**Axiom 1: 封装 (Encapsulation)**:

$$
\forall a : \text{Actor}.\ \text{State}(a) \text{ is only accessible to } a
$$

**Axiom 2: 异步通信 (Asynchronous Communication)**:

$$
\text{send}(a_1, a_2, m) \to \text{mailbox}(a_2) \text{ append } m
$$

发送是非阻塞的，消息通过邮箱异步传递。

**Axiom 3: 顺序执行 (Sequential Execution)**:

$$
\forall a : \text{Actor}.\ \text{messages}(a) \text{ processed sequentially}
$$

**Axiom 4: 位置透明 (Location Transparency)**:

$$
\text{send}(a_1, a_2, m) \equiv \text{send}(a_1, a_2', m) \text{ where } a_2 \text{ and } a_2' \text{ are local/remote}
$$

---

## 2. 形式化语义

### 2.1 操作语义

**配置 (Configuration)**:

$$
\mathcal{C} = \{ a_1, a_2, \ldots, a_n \} \cup \{ \text{in-transit messages} \}
$$

**转换规则**:

$$
\frac{a \in \mathcal{C} \quad m = \text{head}(\text{mailbox}(a)) \quad (b', s') = \text{behavior}(a)(m, \text{state}(a))}{\mathcal{C} \to \mathcal{C}'}
$$

其中 $\mathcal{C}'$ 更新Actor状态和可能产生的新消息。

### 2.2 Actor演算

```text
Syntax:
  e ::= a                      (actor identifier)
     |  λx.e                   (abstraction)
     |  e₁ e₂                  (application)
     |  send(e₁, e₂)           (async send)
     |  receive { p => e }     (receive pattern)
     |  become(e)              (behavior replacement)
     |  new Actor(e)           (actor creation)
     |  self                   (current actor)

Patterns:
  p ::= _                      (wildcard)
     |  x                      (variable bind)
     |  C(p₁, ..., pₙ)         (constructor)
```

**归约规则**:

```text
(send rule)
  a₁[send(a₂, v)] → a₁[()] || a₂'s mailbox appended with v

(receive rule)
  a[receive { p => e }] with head(m) matching p
  → a[e[v/p]] where m = head(mailbox)

(become rule)
  a[become(b)] → a with behavior replaced by b

(create rule)
  a[new Actor(b)] → a[a'] || a'[b] where a' is fresh
```

### 2.3 类型系统

```rust
// Actor类型 (伪代码)
type Actor<M, S> = {
    mailbox: Mailbox<M>,
    state: S,
    behavior: fn(M, S) -> Effect<S>,
}

// 效果类型
type Effect<S> =
    | Become(fn(M, S) -> Effect<S>)  // 更换行为
    | Send(ActorRef<M>, M)           // 发送消息
    | Create(Actor<M, S>)            // 创建Actor
    | Stop                           // 终止
    | Continue                       // 继续
```

---

## 3. Actor与其他并发模型对比

### 3.1 模型对比矩阵

| 特性 | Actor | CSP | 共享内存 | Async/Future |
|:-----|:------|:----|:---------|:-------------|
| **通信方式** | 异步消息 | 同步通道 | 共享变量 | Future组合 |
| **耦合度** | 松散 | 中等 | 紧密 | 中等 |
| **容错** | 内置 (监督) | 需实现 | 需实现 | 需实现 |
| **位置透明** | ✅ | ❌ | ❌ | ⚠️ |
| **死锁** | 不可能 | 可能 | 可能 | 可能 |
| **数据竞争** | 不可能 | 不可能 | 可能 | 不可能 (Rust) |
| **扩展性** | 强 | 中等 | 弱 | 中等 |
| **学习曲线** | 中等 | 低 | 低 | 中等 |

### 3.2 与CSP对比

```text
Actor模型:                    CSP模型:
┌─────────┐                  ┌─────────┐
│ Actor A │                  │ Proc A  │
│         │ ──async msg──►   │         │
│ Mailbox │                  │   chan  │◄────►
└────┬────┘                  └────┬────┘
     │                            │
     │ 松散耦合                     │ 紧密耦合
     │                            │
┌────┴────┐                  ┌────┴────┐
│ Actor B │                  │ Proc B  │
│         │ ◄──async msg──   │         │
│ Mailbox │                  │   chan  │◄────►
└─────────┘                  └─────────┘

Actor: 发送方不知道接收方是否处理
CSP: 发送阻塞直到接收方准备好 (同步)
```

**定理 ACTOR-CSP-1**:

Actor模型可以模拟CSP，反之则不然。

$$
\text{CSP} \subset \text{Actor}
$$

### 3.3 与共享内存对比

```text
共享内存并发:                    Actor并发:
┌─────────────────┐            ┌─────────────────┐
│  Thread A       │            │  Actor A        │
│  ┌───────────┐  │            │  ┌───────────┐  │
│  │  Lock     │  │            │  │  State    │  │
│  │  Mutex<T> │◄─┼───┐        │  │  (私有)   │  │
│  └───────────┘  │   │        │  └───────────┘  │
└───────────────┬─┘   │        └────────┬────────┘
                │     │                 │
                │     │                 │ 消息传递
                │     │                 ▼
                ▼     │        ┌─────────────────┐
┌───────────────┴─┐   │        │  Actor B        │
│  Thread B       │   │        │  ┌───────────┐  │
│  ┌───────────┐  │   │        │  │  State    │  │
│  │  Lock     │◄─┼───┘        │  │  (私有)   │  │
│  │  Mutex<T> │  │            │  └───────────┘  │
│  └───────────┘  │            └─────────────────┘
└─────────────────┘

共享内存: 需要锁、易死锁、缓存一致性问题
Actor: 无共享、无锁、天然分布式
```

---

## 4. Actor模型优势

### 4.1 无锁并发

**定理 ACTOR-LOCKFREE-1**:

Actor系统中不需要显式锁。

$$
\text{Actor system} \vdash \text{no explicit locks needed}
$$

**证明**:

1. 每个Actor顺序处理消息
2. 状态仅由拥有Actor访问
3. 消息传递是原子操作
4. ∴ 无数据竞争

### 4.2 容错性

**监督树 (Supervision Tree)**:

```text
                    ┌─────────────┐
                    │  Root       │
                    │ Supervisor  │
                    └──────┬──────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
    ┌──────┴──────┐ ┌──────┴──────┐ ┌──────┴──────┐
    │  Supervisor │ │  Supervisor │ │  Supervisor │
    │   (Type A)  │ │   (Type B)  │ │   (Type C)  │
    └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
           │               │               │
      ┌────┴────┐     ┌────┴────┐     ┌────┴────┐
      │ Worker  │     │ Worker  │     │ Worker  │
      │ Actor   │     │ Actor   │     │ Actor   │
      └─────────┘     └─────────┘     └─────────┘

监督策略:
- One-for-One: 一个失败只重启它
- One-for-All: 一个失败重启所有
- Rest-for-One: 重启失败者和之后启动的
```

### 4.3 位置透明

```rust
// 本地Actor
let local_actor = ctx.actor_of::<MyActor>("local").unwrap();

// 远程Actor (语法相同!)
let remote_actor = ctx.actor_of::<MyActor>(
    "remote@192.168.1.100:8080"
).unwrap();

// 发送消息 (完全相同)
local_actor.tell(msg, None);
remote_actor.tell(msg, None);  // 透明序列化/网络传输
```

---

## 5. Actor模型限制

### 5.1 回调地狱风险

```rust
// 不好的Actor代码 (类似回调地狱)
impl Handler<GetUser> for UserService {
    type Result = ResponseFuture<User>;

    fn handle(&mut self, msg: GetUser, ctx: &mut Context<Self>) -> Self::Result {
        Box::pin(async move {
            let profile = self.profile_svc.send(GetProfile(msg.id)).await?;
            let orders = self.order_svc.send(GetOrders(msg.id)).await?;
            let preferences = self.pref_svc.send(GetPreferences(msg.id)).await?;

            User::from_parts(profile, orders, preferences)
        })
    }
}
```

### 5.2 死锁可能性

虽然Actor模型避免了数据竞争死锁，但仍有逻辑死锁:

```text
Actor A: 发送msg1给B，等待reply1
Actor B: 收到msg1，发送msg2给A，等待reply2
Actor A: 收到msg2，但无法处理，因为还在等待reply1

结果: 死锁!
```

**解决方案**:

1. 使用ask模式带超时
2. 避免循环依赖
3. 使用Future组合

### 5.3 消息排序

**问题**: 消息可能乱序到达

```text
Actor A发送: [msg1, msg2, msg3]
Actor B接收: [msg1, msg3, msg2]  (网络延迟)
```

**解决方案**:

- 序列号排序
- 因果一致性
- Vector clocks

---

## 6. 现代Actor理论扩展

### 6.1 Typed Actors

```rust
// 使用类型系统确保消息安全
trait Actor<M> {
    fn handle(&mut self, msg: M);
}

// 只有UserMsg类型的消息可以发送给UserActor
struct UserActor;
impl Actor<UserMsg> for UserActor {
    fn handle(&mut self, msg: UserMsg) {
        match msg {
            UserMsg::Create(user) => ...,  // 编译时检查!
            UserMsg::Delete(id) => ...,
        }
    }
}
```

### 6.2 流式Actor

```rust
// Actor作为Stream生产者
impl StreamHandler<Data> for SensorActor {
    fn handle(&mut self, item: Data, ctx: &mut Context<Self>) {
        // 处理流中的每个数据点
        self.process(item);
    }

    fn started(&mut self, ctx: &mut Context<Self>) {
        // 启动时开始流
        self.sensor_stream
            .into_actor(self)
            .map(|data, act, ctx| act.handle(data, ctx))
            .finish()
            .spawn(ctx);
    }
}
```

### 6.3 函数式Actor

```rust
// 无状态函数式Actor
fn counter_actor() -> impl Actor<CounterMsg> {
    let mut count = 0;

    move |msg| {
        match msg {
            CounterMsg::Inc => count += 1,
            CounterMsg::Dec => count -= 1,
            CounterMsg::Get(reply) => reply.send(count),
        }
    }
}
```

---

**维护者**: Rust Actor Theory Team
**更新日期**: 2026-03-05
**状态**: ✅ 理论基础完成
