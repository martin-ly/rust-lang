# Session Types 与 Rust 通信协议

**EN**: Session Types and Rust Communication Protocols

> **Summary**: A formal introduction to binary and multiparty session types, their linear typing discipline, and how Rust's ownership/borrowing and channel APIs can encode protocol safety without a native session-type extension.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [Process Calculi for Rust](01_process_calculi_for_rust.md) · [Pi Calculus for Rust](../09_system_semantics/02_pi_calculus_for_rust.md) · [Linear Logic Applications](../01_ownership_logic/03_linear_logic_applications.md) · [Channels](../../03_advanced/00_concurrency/01_concurrency.md)
> **后置概念**: [Algebraic Effects](04_algebraic_effects.md) · [Rust Async/Await](../../03_advanced/01_async/01_async.md) · [Linear Logic](../01_ownership_logic/01_linear_logic.md)

---

> **来源**: [Honda 1993 — *Types for Dyadic Interaction*](https://doi.org/10.1007/3-540-58043-3_19) · [Honda, Yoshida, Carbone 2008 — *Multiparty Asynchronous Session Types*](https://doi.org/10.1145/1328438.1328472) · [Wadler 2012 — *Propositions as Sessions*](https://doi.org/10.1145/2103656.2103661) · [Rust Book — Message Passing](https://doc.rust-lang.org/book/ch16-02-message-passing.html) · [tokio::sync::mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html)
>
> ⚠️ **声明**: 本页呈现的是**形式语义骨架与教学级代码**，用于建立协议类型直觉。Rust 标准库没有原生 session-type 检查；文中涉及的“协议编码”依赖所有权和线性使用约定，而非编译器自动验证协议状态机。

> **权威来源 / Provenance**: Honda, K. (1993). *Types for Dyadic Interaction*. CONCUR 1993 / LNCS 715, 509–523. 该论文首次提出 session type，用线性类型刻画双向通信协议的状态演化；其多党异步扩展见 Honda, Yoshida & Carbone (2008). *Multiparty Asynchronous Session Types*. POPL 2008. 完整 session types 文献索引见 [Session Types Bibliography](http://groups.inf.ed.ac.uk/abcd/session-types-bibliography.html).
>
> 其他权威来源 / Additional authoritative links: [ACM — Honda, Yoshida & Carbone 2008](https://dl.acm.org/doi/10.1145/1328438.1328472) · [ACM — Wadler 2012](https://dl.acm.org/doi/10.1145/2103656.2103661) · [Springer — Honda 1993](https://link.springer.com/chapter/10.1007/3-540-58043-3_19) · [docs.rs — session_types](https://docs.rs/session_types/latest/session_types/)

---

## 🧠 知识结构图

```mermaid
mindmap
  root((Session Types))
    二元会话
      !T.S  发送
      ?T.S  接收
      ⊕{lᵢ:Sᵢ}  内部选择
      &{lᵢ:Sᵢ}  外部选择
      end     终止
    多党会话
      全局类型
      投影到本地类型
      通信图
    线性规则
      通道不可复制
      每次使用改变类型
      必须 consumed
    Rust 编码
      移动所有权通道
      状态机 enum
      Session-type 库
    形式来源
      Honda 1993
      Wadler 2012
      Linear Logic
```

---

## 一、权威定义

**Session type** 描述的是**两个或多个通信参与方之间允许的交互协议**。它把通道（channel）本身当作一个具有状态的线性对象：每发送或接收一次消息，通道的“剩余协议”就发生变化，直到达到终止状态 `end`。

### 1.1 二元会话类型语法

```text
S ::= !T. S       (发送类型 T，然后继续 S)
   |  ?T. S       (接收类型 T，然后继续 S)
   |  ⊕{l₁:S₁, ..., lₙ:Sₙ}   (内部选择：主动选择分支 lᵢ)
   |  &{l₁:S₁, ..., lₙ:Sₙ}   (外部选择：被动接受对方选择的分支)
   |  end         (协议终止)
```

- 对偶（dual）：`!` 与 `?` 互换，`⊕` 与 `&` 互换。
- 线性：通道值必须被**恰好使用一次**，不能丢弃也不能复制。

### 1.2 经典示例：购买协议

```text
Client:  !String. ?i32. ⊕{ Pay: !Card. ?Receipt.end, Quit: end }
Server:  ?String. !i32. &{ Pay: ?Card. !Receipt.end, Quit: end }
```

- Client 先发送商品名，再接收价格，然后选择“支付”或“退出”。
- Server 的协议是 Client 的**对偶**（dual）。

---

## 二、线性逻辑基础

Session types 与**线性逻辑**（Linear Logic）同构 [Wadler 2012]：

| 会话类型 | 线性逻辑连接词 | 直觉 |
|---|---|---|
| `!T.S` | `T ⊗ S` | 发送 T，保留继续协议 S |
| `?T.S` | `T ⅋ S` | 接收 T，保留继续协议 S |
| `⊕{lᵢ:Sᵢ}` | 加法析取 ⊕ | 主动选择 |
| `&{lᵢ:Sᵢ}` | 加法合取 & | 外部选择 |
| `end` | 单位元 1 / ⊥ | 协议结束 |

Rust 的**所有权系统**恰好提供线性使用所需的核心性质：

- 默认 move 语义保证通道不被隐式复制。
- `Drop` 检查保证资源不被静默泄漏（虽然不会检查协议是否完成）。

---

## 三、Rust 编码：用所有权实现线性通道

标准库 `std::sync::mpsc` 或 `tokio::sync::mpsc` 的 Sender/Receiver 已经是**单所有者**、**不可复制**的，因此天然适合编码 session type 的“线性”部分。但标准库不会在类型层面跟踪协议状态。

```rust
use std::sync::mpsc::{channel, Sender, Receiver};

// 教学级：把“发送 i32 后结束”的协议封装成单用结构体。
pub struct SendEnd {
    tx: Sender<i32>,
}

impl SendEnd {
    pub fn send(self, value: i32) {
        self.tx.send(value).unwrap();
    }
}

fn main() {
    let (tx, rx) = channel::<i32>();
    let sess = SendEnd { tx };
    sess.send(42); // 消费 self，之后不能再使用 sess
    assert_eq!(rx.recv().unwrap(), 42);
}
```

### 3.1 状态机编码：协议步骤作为类型

更忠实的编码是把协议的每一步表示为不同的 Rust 类型，从而把“协议错误”转化为**类型错误**或**所有权错误**：

```rust
use std::sync::mpsc::{channel, Receiver, Sender};

// 协议：Client !String. ?i32. end
// 用两个底层 channel 模拟一条双向会话通道；类型状态保证顺序
pub struct Session<S, R> {
    tx: Sender<S>,
    rx: Receiver<R>,
}

pub struct SendName(Session<String, i32>);
pub struct RecvPrice(Session<String, i32>);

impl SendName {
    // 消耗 SendName，返回 RecvPrice：协议状态从 !String 转移到 ?i32
    pub fn send_name(self, name: String) -> RecvPrice {
        self.0.tx.send(name).unwrap();
        RecvPrice(self.0)
    }
}

impl RecvPrice {
    // 消耗 RecvPrice，完成协议 end
    pub fn recv_price(self) -> i32 {
        self.0.rx.recv().unwrap()
    }
}

fn main() {
    let (tx1, rx1) = channel::<String>();
    let (tx2, rx2) = channel::<i32>();

    // 工作线程扮演 Server 的对偶端
    std::thread::spawn(move || {
        let name = rx1.recv().unwrap();
        assert_eq!(name, "apple");
        tx2.send(42).unwrap();
    });

    let client = SendName(Session { tx: tx1, rx: rx2 });
    let client = client.send_name("apple".into());
    let price = client.recv_price();
    assert_eq!(price, 42);
}
```

> 关键点：通过 `self` 消费，`send_name` 之后无法再调用；协议错误变成编译期所有权错误（E0382）。

---

## 四、多党会话类型（Multiparty Session Types）

当通信涉及 ≥3 个角色时，使用**全局类型**（global type）描述整体协议，再**投影**（project）到每个参与者的本地类型。

```text
Global:  A → B:〈String〉. B → C:〈i32〉. A → C:〈bool〉. end
```

投影规则保证：如果每个参与者都遵守自己的本地类型，则全局协议不会死锁、不会角色混淆。

Rust 中典型的多党协议例子是 **actor / 微服务编排**：

- API Gateway → OrderService → PaymentService → NotificationService
- 使用类型状态机或代码生成（如 session-type 库）来静态检查顺序。

---

## 五、Rust 生态中的 Session-Type 库

Rust 目前没有语言级 session type，但社区有一些实验性库：

- **session_types**（早期实验）
- **session-types-rs**
- 基于 `tokio`/`async` 的状态机 DSL

这些库通常利用 Rust 的**类型状态模式**（typestate pattern）把协议状态编码为泛型参数，从而在编译期拒绝错误序列。

---

## 六、反例与边界

### 反例 1：标准库通道无法阻止协议顺序错误

```rust
use std::sync::mpsc::channel;

fn main() {
    let (tx, rx) = channel::<i32>();
    tx.send(1).unwrap();
    tx.send(2).unwrap(); // 协议上可能不允许第二次发送，但编译器不报错
    let _ = rx.recv();
    let _ = rx.recv();
}
```

> 标准库 `Sender<T>` 只约束元素类型 `T`，不约束**发送次数/顺序**。要捕获这类错误，需要 session-type 扩展或类型状态编码。

### 反例 2：错误地在选择前发送数据

```rust,compile_fail,E0382
// 非法：把已经 move 的 tx 再次使用，违反线性规则（E0382）。
use std::sync::mpsc::channel;

fn main() {
    let (tx, rx) = channel::<i32>();
    let _tx2 = tx; // tx 被 move
    tx.send(1).unwrap(); // 错误：use of moved value: `tx` [E0382]
    let _ = rx.recv();
}
```

### 边界：Session types 不能捕获所有并发错误

- **活锁 / 公平性**：session type 保证类型安全，不保证进度或公平调度。
- **超时**：纯 session type 不表达时间约束；需要结合时态逻辑或 runtime 超时机制。
- **崩溃容错**：拜占庭故障、网络分区超出 session type 的范围。

---

## 七、与 Rust 并发原语的映射

| Session Type 概念 | Rust 原语 | 说明 |
|---|---|---|
| Linear channel | `Sender<T>` / `Receiver<T>` | 不可 `Copy`，默认 move |
| `!T.S` | `sender.send(t)` 后进入下一步 | 状态转移靠类型状态编码 |
| `?T.S` | `receiver.recv()` 后进入下一步 |  |
| `⊕{lᵢ:Sᵢ}` | `enum` + `match` | 主动选择分支发送 |
| `&{lᵢ:Sᵢ}` | `enum` + `match` | 被动接收分支选择 |
| `end` | channel 被 drop | 线性逻辑要求最终消耗 |

---

## 八、国际权威参考

- **P1 学术/形式化**
  - [Honda 1993 — *Types for Dyadic Interaction*](https://doi.org/10.1007/3-540-58043-3_19)
  - [Honda, Yoshida, Carbone 2008 — *Multiparty Asynchronous Session Types*](https://doi.org/10.1145/1328438.1328472)
  - [Wadler 2012 — *Propositions as Sessions*](https://doi.org/10.1145/2103656.2103661)
  - [Gay & Hole 2005 — *Subtyping for Session Types in the Pi Calculus*](https://doi.org/10.1007/s00236-005-0177-z)
  - [Pierce 2002 — *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/)

- **P0 官方**
  - [The Rust Programming Language — Message Passing](https://doc.rust-lang.org/book/ch16-02-message-passing.html)
  - [Rust Reference — Channels](https://doc.rust-lang.org/std/sync/mpsc/index.html)
  - [tokio::sync::mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html)

- **P2 生态/社区**
  - [session-types crate](https://crates.io/crates/session_types)
  - [Rust Internals Forum — Concurrency](https://internals.rust-lang.org/)

---

## 嵌入式测验

> **Q1**. Session type `!i32. ?String. end` 中，`!` 表示什么？
>
> - A. 接收
> - B. 发送
> - C. 选择
> - D. 终止
>
> <details><summary>答案</summary>B. 发送（send）。</details>

> **Q2**. Rust 的哪个性质使它能部分模拟 session type 的线性规则？
>
> - A. 垃圾回收
> - B. 所有权与默认 move 语义
> - C. 虚函数表
> - D. 反射
>
> <details><summary>答案</summary>B. 所有权保证通道不可隐式复制。</details>

> **Q3**. 多党会话类型的“全局类型”主要解决什么问题？
>
> - A. 编译器实现
> - B. 多个参与方之间的协议一致性
> - C. 内存分配
> - D. 异常处理
>
> <details><summary>答案</summary>B. 通过投影保证每个本地角色遵守同一全局协议。</details>
