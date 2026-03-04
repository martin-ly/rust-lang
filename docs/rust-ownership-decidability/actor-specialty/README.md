# Actor模型专题

> **从理论到实践：完整的Actor模型指南**

---

## 专题概览

```text
┌─────────────────────────────────────────────────────────────────┐
│                    Actor模型专题                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  📚 理论基础                                                      │
│  ├── Actor模型定义与历史                                          │
│  ├── 形式化语义 (操作语义、Actor演算)                             │
│  ├── 与CSP/共享内存/Async对比                                     │
│  └── 现代理论扩展 (Typed Actors, 流式Actor)                       │
│                                                                  │
│  🔧 Rust实现                                                      │
│  ├── Actix (最流行, Web集成)                                      │
│  ├── Bastion (容错, 监督树)                                       │
│  ├── coerce (分布式, 集群)                                        │
│  └── Xtra (轻量级)                                                │
│                                                                  │
│  🎨 设计模式                                                      │
│  ├── Ask vs Tell, 前摄模式                                        │
│  ├── 监督者模式, Circuit Breaker                                  │
│  ├── 路由模式 (负载均衡、一致性哈希)                              │
│  ├── 状态管理 (FSM, Event Sourcing)                               │
│  └── 通信模式 (Pub-Sub, 请求管道)                                 │
│                                                                  │
│  🌐 分布式Actor                                                   │
│  ├── 集群架构 (发现、分片、单例)                                  │
│  ├── 分布式通信 (gRPC, 序列化)                                    │
│  ├── 容错与一致性 (CAP, Saga, CRDT)                               │
│  └── 网络分区处理                                                 │
│                                                                  │
│  💡 实战示例                                                      │
│  └── 分布式聊天系统 (完整实现)                                    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 目录结构

```text
actor-specialty/
├── README.md                    # 本文件 - 专题导航
├── theory/
│   └── actor-model-foundation.md  # Actor理论基础
├── implementations/
│   └── rust-actor-frameworks.md   # Rust框架对比
├── patterns/
│   └── actor-design-patterns.md   # 设计模式
├── distributed/
│   └── distributed-actors.md      # 分布式Actor
└── examples/
    └── chat-system-example.md     # 聊天系统示例
```

---

## 核心概念

### 什么是Actor模型?

> An Actor is an autonomous concurrent object that communicates asynchronously with other Actors.
> — Carl Hewitt, 1973

```text
Actor = 状态 + 行为 + 邮箱

┌─────────────────────────┐
│        Actor            │
│  ┌─────────────────┐    │
│  │   Mailbox       │    │
│  │   [msg, msg]    │    │
│  └────────┬────────┘    │
│           │ 顺序处理     │
│           ▼              │
│  ┌─────────────────┐    │
│  │   Behavior      │    │
│  │   fn(msg,state) │    │
│  │        ↓        │    │
│  │   New State     │    │
│  │   Send Msgs     │    │
│  └─────────────────┘    │
│                         │
│  ┌─────────────────┐    │
│  │   Private State │    │
│  │   (封装)        │    │
│  └─────────────────┘    │
└─────────────────────────┘

特点:
- 状态封装: 只能通过消息访问
- 异步通信: 发送不阻塞
- 顺序处理: 无并发竞争
- 位置透明: 本地/远程无区别
```

### Actor公理

1. **封装**: 状态仅由Actor访问
2. **异步通信**: 消息通过邮箱传递
3. **顺序执行**: 消息按序处理
4. **位置透明**: 本地和远程Actor使用相同API

---

## 与其他并发模型对比

| 特性 | Actor | CSP | 共享内存 | Async/Future |
|:-----|:------|:----|:---------|:-------------|
| 通信方式 | 异步消息 | 同步通道 | 共享变量 | Future组合 |
| 耦合度 | 松散 | 中等 | 紧密 | 中等 |
| 容错 | 内置 | 需实现 | 需实现 | 需实现 |
| 位置透明 | ✅ | ❌ | ❌ | ⚠️ |
| 死锁 | 不可能 | 可能 | 可能 | 可能 |
| 数据竞争 | 不可能 | 不可能 | 可能 | 不可能(Rust) |

---

## Rust Actor框架对比

| 框架 | 监督树 | 分布式 | Web集成 | 适用场景 |
|:-----|:------:|:------:|:-------:|:---------|
| **Actix** | ⚠️ | ❌ | ✅ | Web后端 |
| **Bastion** | ✅ | ⚠️ | ⚠️ | 高可用系统 |
| **coerce** | ✅ | ✅ | ⚠️ | 微服务/分布式 |
| **Xtra** | ⚠️ | ❌ | ❌ | 学习/轻量 |

---

## 快速开始

### Actix示例

```rust
use actix::prelude::*;

// 定义消息
#[derive(Message)]
#[rtype(result = "i32")]
struct Add(i32, i32);

// 定义Actor
struct Calculator;

impl Actor for Calculator {
    type Context = Context<Self>;
}

// 实现消息处理
impl Handler<Add> for Calculator {
    type Result = i32;

    fn handle(&mut self, msg: Add, _: &mut Context<Self>) -> Self::Result {
        msg.0 + msg.1
    }
}

#[actix::main]
async fn main() {
    let addr = Calculator.start();
    let result = addr.send(Add(10, 20)).await.unwrap();
    println!("10 + 20 = {}", result);
}
```

### Bastion示例

```rust
use bastion::prelude::*;

fn main() {
    Bastion::init();

    Bastion::children(|ch| {
        ch.with_exec(|ctx: BastionContext| async move {
            msg! { ctx.recv().await?,
                msg: i32 => {
                    println!("Received: {}", msg);
                    ctx.answer(msg * 2).await?;
                }
                _: _ => {}
            }
            Ok(())
        })
    });

    Bastion::start();
    Bastion::block_until_stopped();
}
```

---

## 学习路径

### 初学者

1. [理论基础](./theory/actor-model-foundation.md) - 理解核心概念
2. [Actix快速开始](#快速开始) - 动手实践
3. [设计模式](./patterns/actor-design-patterns.md) - 掌握常用模式

### 进阶开发者

1. [框架对比](./implementations/rust-actor-frameworks.md) - 选择合适的框架
2. [分布式Actor](./distributed/distributed-actors.md) - 构建分布式系统
3. [聊天系统示例](./examples/chat-system-example.md) - 完整实战

### 架构师

1. 全部文档 - 系统掌握
2. 关注分布式、容错、性能优化部分

---

## 核心洞见

### Actor模型的优势

1. **无锁并发**: 顺序消息处理，无需显式锁
2. **容错性**: 监督树自动处理失败
3. **位置透明**: 本地和远程Actor统一API
4. **可扩展性**: 天然支持分布式部署

### Actor模型的限制

1. **回调地狱风险**: 需要良好的抽象
2. **逻辑死锁**: 循环请求可能导致死锁
3. **消息排序**: 网络可能导致乱序

---

## 参考资源

### 论文与书籍

- [A Universal Modular Actor Formalism for AI](https://dl.acm.org/doi/10.1145/1624775.1624804) - Hewitt, 1973
- [Actors: A Model of Concurrent Computation](https://dl.acm.org/doi/book/10.5555/7920) - Agha, 1986
- [Akka in Action](https://www.manning.com/books/akka-in-action)

### Rust资源

- [Actix Documentation](https://actix.rs/)
- [Bastion Documentation](https://bastion-rs.github.io/)
- [coerce GitHub](https://github.com/alexburkov/coerce)

---

**维护者**: Rust Actor Specialty Team
**创建日期**: 2026-03-05
**状态**: ✅ 100% 完成
