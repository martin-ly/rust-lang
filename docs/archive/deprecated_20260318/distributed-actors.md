# 分布式Actor系统

> **位置透明、容错、可扩展的分布式计算**

---

## 1. 分布式Actor基础

### 1.1 分布式系统挑战

```text
分布式Actor面临的挑战:

┌─────────────────────────────────────────────────────────────────┐
│  网络分区                                                        │
│  ┌─────────┐          X          ┌─────────┐                   │
│  │ Node A  │ ◄───────X───────► │ Node B  │                   │
│  │         │          X          │         │                   │
│  └─────────┘          X          └─────────┘                   │
│                       网络中断                                   │
├─────────────────────────────────────────────────────────────────┤
│  消息丢失/乱序                                                   │
│  A发送: [m1, m2, m3]                                            │
│  B收到: [m1, m3]      (m2丢失)                                  │
│  B收到: [m1, m3, m2]  (乱序)                                    │
├─────────────────────────────────────────────────────────────────┤
│  时钟不同步                                                      │
│  Node A时间: 10:00:00                                           │
│  Node B时间: 10:00:05   (5秒偏差)                               │
├─────────────────────────────────────────────────────────────────┤
│  节点故障                                                        │
│  ┌─────────┐                                                    │
│  │ Node C  │ ◄──心跳检测失败── 标记为DOWN                      │
│  │  (DOWN) │                                                    │
│  └─────────┘                                                    │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Actor位置透明

```rust
// 位置透明：本地和远程Actor使用相同API

// 本地Actor
let local_actor = system.actor_of::<MyActor>("local-actor").unwrap();

// 远程Actor (相同代码!)
let remote_actor = system
    .remote_actor::<MyActor>("remote-actor@192.168.1.100:8080")
    .await
    .unwrap();

// 发送消息 (完全相同)
local_actor.tell(msg.clone(), None);
remote_actor.tell(msg, None);  // 自动序列化和网络传输
```

---

## 2. 集群架构

### 2.1 集群节点发现

```rust
use coerce::cluster::{Cluster, NodeId};
use coerce::remote::RemoteActorSystem;

// 配置集群
async fn setup_cluster() {
    let remote = RemoteActorSystem::builder()
        .with_id("node-1")
        .with_tag("dc-us-east")
        .with_listen_addr("0.0.0.0:50051")
        .build()
        .await;

    // 种子节点发现
    for seed in &["node-2:50051", "node-3:50051"] {
        if let Err(e) = remote.connect(seed).await {
            eprintln!("Failed to connect to {}: {}", seed, e);
        }
    }

    // 启动gRPC服务
    remote.start().await;
}

// 节点状态监听
remote.on_node_event(|event| {
    match event {
        NodeEvent::Connected { node_id } => {
            println!("Node {} joined cluster", node_id);
        }
        NodeEvent::Disconnected { node_id } => {
            println!("Node {} left cluster", node_id);
            // 触发重新平衡
        }
    }
});
```

### 2.2 集群分片 (Sharding)

```rust
use coerce::sharding::{ShardRegion, ShardAllocationStrategy};

// 创建分片区域
async fn setup_sharding(system: ActorSystem) {
    let region = ShardRegion::builder("user-actors")
        // 根据用户ID计算分片
        .with_extractor(|cmd: &UserCommand| {
            cmd.user_id.chars().next().unwrap() as u64 % 100
        })
        // 分配策略
        .with_allocation_strategy(ShardAllocationStrategy::LeastAllocated)
        // Actor工厂
        .with_actor_factory(|shard_id| {
            UserActor::new(shard_id)
        })
        .start(system)
        .await;

    // 发送消息 (自动路由到正确分片)
    region.send(UserCommand {
        user_id: "alice".to_string(),
        action: UpdateProfile { ... },
    }).await;
}
```

### 2.3 集群单例 (Singleton)

```rust
use coerce::singleton::ClusterSingleton;

// 集群中只有一个实例
async fn setup_singleton(system: ActorSystem) {
    let coordinator = ClusterSingleton::new(
        system.clone(),
        "coordinator",  // 全局唯一名称
        || CoordinatorActor::new(),
    ).await;

    // 使用单例
    let result = coordinator.ask(CoordinateTask).await;

    // 故障时自动迁移到新节点
}
```

---

## 3. 分布式通信

### 3.1 gRPC传输

```rust
// 定义protobuf消息
// user.proto
/*
syntax = "proto3";

message GetUserRequest {
    string user_id = 1;
}

message GetUserResponse {
    User user = 1;
}

service UserActor {
    rpc GetUser(GetUserRequest) returns (GetUserResponse);
}
*/

// 服务端实现
#[derive(Actor)]
struct UserActor { ... }

#[async_trait]
impl UserService for UserActor {
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<GetUserResponse>, Status> {
        let user = self.get_user_from_db(&request.into_inner().user_id).await;
        Ok(Response::new(GetUserResponse { user }))
    }
}

// 客户端调用
let client = UserActorClient::connect("http://node-2:50051").await?;
let response = client.get_user(GetUserRequest {
    user_id: "user-123".to_string(),
}).await?;
```

### 3.2 消息序列化

```rust
use serde::{Serialize, Deserialize};

// 定义可序列化消息
#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum UserMessage {
    GetUser { id: String },
    CreateUser { name: String, email: String },
    UpdateUser { id: String, updates: UserUpdates },
    DeleteUser { id: String },
}

// Actor注册序列化
RemoteActorSystem::builder()
    .with_handler::<UserActor, UserMessage>("UserActor")
    .build()
    .await;

// 自定义序列化
impl RemoteMessage for UserMessage {
    fn serialize(&self) -> Vec<u8> {
        bincode::serialize(self).unwrap()
    }

    fn deserialize(bytes: &[u8]) -> Result<Self, DeserializeError> {
        bincode::deserialize(bytes).map_err(|e| e.into())
    }
}
```

---

## 4. 容错与一致性

### 4.1 分布式监督

```rust
// 跨节点监督
Bastion::supervisor(|sp| {
    sp.with_strategy(SupervisionStrategy::OneForOne)
      .with_distributed(true)  // 启用分布式监督
})
.children(|ch| {
    ch.with_name("critical-service")
      .with_placement(PlacementStrategy::Distributed)
      .with_exec(critical_actor)
});

// 如果node-1上的实例失败，在node-2上重启
```

### 4.2 分布式事务 (Saga模式)

```rust
struct SagaActor {
    steps: Vec<SagaStep>,
    compensations: Vec<Compensation>,
}

impl SagaActor {
    async fn execute(&mut self, ctx: &mut Context) -> SagaResult {
        let executed = Vec::new();

        for step in &self.steps {
            match step.execute().await {
                Ok(_) => executed.push(step),
                Err(e) => {
                    // 执行补偿操作
                    for completed in executed.iter().rev() {
                        completed.compensate().await;
                    }
                    return SagaResult::Failed(e);
                }
            }
        }

        SagaResult::Success
    }
}

// 使用示例
let saga = SagaBuilder::new()
    .step(ReserveInventory { ... })
    .step(ProcessPayment { ... })
    .step(ShipOrder { ... })
    .compensate(0, ReleaseInventory { ... })  // 如果支付失败，释放库存
    .compensate(1, RefundPayment { ... })      // 如果发货失败，退款
    .build();
```

### 4.3 CRDT Actor

```rust
use crdts::{GSet, Map, Orswot};

struct CRDTActor {
    // 基于CRDT的状态，天然支持最终一致性
    users: Map<String, User, Orswot<String>>,
    online_users: GSet<String>,
}

impl CRDTActor {
    // 本地更新，自动合并
    fn add_user(&mut self, user: User) {
        self.users.update(user.id.clone(), user, self.node_id);
    }

    // 合并来自其他节点的更新
    fn merge(&mut self, other: &Self) {
        self.users.merge(&other.users);
        self.online_users.merge(&other.online_users);
    }
}
```

---

## 5. 网络分区处理

### 5.1 CAP权衡

```text
CAP定理在Actor系统中的体现:

┌─────────────────────────────────────────────────────────────────┐
│                                                                  │
│   CP系统 (一致性优先)              AP系统 (可用性优先)           │
│   ┌──────────────┐                ┌──────────────┐             │
│   │ 两阶段提交    │                │ 最终一致性    │             │
│   │ 分布式锁      │                │ CRDT          │             │
│   │ 强一致性复制  │                │ Gossip协议    │             │
│   └──────────────┘                └──────────────┘             │
│                                                                  │
│   选择:                           选择:                          │
│   - 金融交易                      - 社交网络                     │
│   - 库存管理                      - 游戏状态                     │
│   - 订单系统                      - 日志聚合                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 Split-Brain处理

```rust
// 使用仲裁(Quorum)避免脑裂
struct ClusterMembership {
    nodes: HashSet<NodeId>,
    quorum_size: usize,
}

impl ClusterMembership {
    fn can_make_decision(&self, active_nodes: &HashSet<NodeId>) -> bool {
        active_nodes.len() >= self.quorum_size
    }

    async fn handle_partition(&self, ctx: &mut Context) {
        let active = self.get_active_nodes().await;

        if !self.can_make_decision(&active) {
            // 进入只读模式或停机
            ctx.become(read_only_behavior);
        }
    }
}
```

---

**维护者**: Rust Distributed Actor Team
**更新日期**: 2026-03-05
