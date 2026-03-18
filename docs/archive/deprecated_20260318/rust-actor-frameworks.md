# Rust Actor框架全面对比

> **Actix vs Bastion vs coerce vs Xtra: 深度对比**

---

## 1. Rust Actor生态概览

```text
Rust Actor框架全景:

┌─────────────────────────────────────────────────────────────────┐
│                      Rust Actor生态                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  🥇 主流框架                                                      │
│  ├── Actix           (最流行, Web集成)                            │
│  ├── Bastion         (容错, 监督树)                               │
│  ├── coerce          (集群, 分布式)                               │
│  └── Xtra            (轻量, 简单)                                 │
│                                                                  │
│  🌟 特色框架                                                      │
│  ├── Riker           (Akka风格)                                   │
│  ├── Stakker         (单线程)                                     │
│  ├── Axiom           (无主集群)                                   │
│  └── Heph            (高性能)                                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Actix 深度解析

### 2.1 核心API

```rust
use actix::prelude::*;

// 定义消息
#[derive(Message)]
#[rtype(result = "Result<User>")]
struct GetUser {
    id: u64,
}

// 定义Actor
struct UserActor {
    db: Database,
}

impl Actor for UserActor {
    type Context = Context<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        println!("UserActor started");
    }
}

// 实现消息处理
impl Handler<GetUser> for UserActor {
    type Result = ResponseFuture<Result<User>>;

    fn handle(&mut self, msg: GetUser, ctx: &mut Context<Self>) -> Self::Result {
        let db = self.db.clone();
        Box::pin(async move {
            db.fetch_user(msg.id).await
        })
    }
}

// 使用
#[actix::main]
async fn main() {
    let addr = UserActor { db: Database::new() }.start();
    let user = addr.send(GetUser { id: 1 }).await.unwrap();
}
```

### 2.2 Actix特性

| 特性 | 支持 | 说明 |
|:-----|:----:|:-----|
| 监督 | 部分 | 需手动实现 |
| 分布式 | 否 | 不支持 |
| 消息类型安全 | 是 | 编译时类型安全 |
| Web集成 | 是 | Actix-web无缝集成 |

---

## 3. Bastion 深度解析

### 3.1 监督树架构

```rust
use bastion::prelude::*;

fn main() {
    Bastion::init();

    let supervisor = Bastion::supervisor(|sp| {
        sp.with_strategy(SupervisionStrategy::OneForOne)
          .with_restart_policy(RestartPolicy::Tries(3))
    })
    .children(|ch| {
        ch.with_exec(|ctx: BastionContext| async move {
            loop {
                msg! { ctx.recv().await?,
                    msg: ComputeTask => {
                        let result = compute(msg.data).await;
                        ctx.answer(result).await?;
                    }
                    _: _ => {}
                }
            }
            Ok(())
        })
    })
    .expect("Failed to create supervisor");

    Bastion::start();
    Bastion::block_until_stopped();
}
```

### 3.2 Bastion特性

| 特性 | 支持 | 说明 |
|:-----|:----:|:-----|
| 监督树 | 是 | 核心特性 |
| 容错 | 是 | 自动重启、退避 |
| 分布式 | 实验性 | 部分支持 |
| 消息广播 | 是 | 一对多消息 |

---

## 4. coerce 深度解析

### 4.1 分布式Actor

```rust
use coerce::actor::{Actor, ActorSystem};
use coerce::remote::RemoteActorSystem;

#[derive(Actor)]
struct UserActor {
    users: HashMap<String, User>,
}

#[derive(Serialize, Deserialize)]
struct GetUser {
    id: String,
}

#[async_trait]
impl Handler<GetUser> for UserActor {
    async fn handle(&mut self, msg: GetUser, ctx: &mut ActorContext) -> Option<User> {
        self.users.get(&msg.id).cloned()
    }
}

// 集群配置
async fn cluster_setup() {
    let system = ActorSystem::new();

    let remote = RemoteActorSystem::builder()
        .with_id("node-1")
        .with_handler::<UserActor, GetUser>("UserActor.GetUser")
        .build()
        .await;

    remote.start("0.0.0.0:50051").await;
    remote.connect("node-2:50051").await;
}
```

### 4.2 coerce特性

| 特性 | 支持 | 说明 |
|:-----|:----:|:-----|
| 分布式 | 是 | 核心特性 |
| 集群分片 | 是 | 类似Akka |
| 集群单例 | 是 | 唯一实例保证 |
| gRPC传输 | 是 | 默认使用gRPC |

---

## 5. 框架对比总结

### 5.1 功能对比表

| 特性 | Actix | Bastion | coerce | Xtra |
|:-----|:-----:|:-------:|:------:|:----:|
| 监督树 | 部分 | 是 | 是 | 部分 |
| 分布式 | 否 | 实验性 | 是 | 否 |
| 容错 | 部分 | 是 | 是 | 部分 |
| Web集成 | 是 | 部分 | 部分 | 否 |
| 维护状态 | 活跃 | 活跃 | 活跃 | 缓慢 |

### 5.2 选择建议

| 场景 | 推荐框架 | 理由 |
|:-----|:---------|:-----|
| Web后端服务 | Actix | 与Actix-web无缝集成 |
| 高可用系统 | Bastion | 强大的容错和监督 |
| 微服务/分布式 | coerce | 原生分布式支持 |
| 学习Actor模型 | Xtra | 简单，易于理解 |

---

**维护者**: Rust Actor Implementations Team
**更新日期**: 2026-03-05
