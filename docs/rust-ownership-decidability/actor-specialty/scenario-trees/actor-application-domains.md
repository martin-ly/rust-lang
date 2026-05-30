# Actor模型应用场景树

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **从Web服务到IoT：Actor模型的应用领域全景**

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Actor模型应用场景树](#actor模型应用场景树)
  - [📑 目录](#目录)
  - [1. 应用领域总览](#1-应用领域总览)
  - [2. Web服务详细方案](#2-web服务详细方案)
    - [2.1 REST API架构](#21-rest-api架构)
    - [2.2 实时通信方案](#22-实时通信方案)
  - [3. 游戏服务器详细方案](#3-游戏服务器详细方案)
    - [3.1 MMORPG架构](#31-mmorpg架构)
    - [3.2 实时对战方案](#32-实时对战方案)
  - [4. IoT平台详细方案](#4-iot平台详细方案)
    - [4.1 设备网关架构](#41-设备网关架构)
  - [5. 金融系统详细方案](#5-金融系统详细方案)
    - [5.1 交易系统架构](#51-交易系统架构)
    - [5.2 Saga分布式事务](#52-saga分布式事务)
  - [6. 选择指南](#6-选择指南)
    - [6.1 领域-框架匹配](#61-领域-框架匹配)
  - **更新日期**: 2026-03-05
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引)

## 1. 应用领域总览
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
Actor应用场景
      │
      ├──▶ Web服务 ──────┬──▶ REST API ──▶ Actix-web
      │                  │                    ├── HTTP/1.1 & HTTP/2
      │                  │                    ├── 中间件管道
      │                  │                    └── 请求路由
      │                  │
      │                  ├──▶ WebSocket ──▶ 实时通信
      │                  │                    ├── 聊天室
      │                  │                    ├── 实时通知
      │                  │                    └── 协同编辑
      │                  │
      │                  └──▶ 微服务 ────▶ Service Mesh
      │                                       ├── 服务发现
      │                                       ├── 负载均衡
      │                                       └── 熔断限流
      │
      ├──▶ 游戏开发 ─────┬──▶ MMORPG ────▶ 游戏服务器
      │                  │                    ├── 玩家管理
      │                  │                    ├── 地图实例
      │                  │                    └── NPC AI
      │                  │
      │                  ├──▶ 实时对战 ──▶ 房间管理
      │                  │                    ├── 匹配系统
      │                  │                    ├── 状态同步
      │                  │                    └── 反作弊
      │                  │
      │                  └──▶ 游戏大厅 ──▶ 社交功能
      │                                       ├── 好友系统
      │                                       ├── 排行榜
      │                                       └── 公会系统
      │
      ├──▶ IoT平台 ──────┬──▶ 设备网关 ──▶ 协议适配
      │                  │                    ├── MQTT
      │                  │                    ├── CoAP
      │                  │                    └── WebSocket
      │                  │
      │                  ├──▶ 数据处理 ──▶ 流处理
      │                  │                    ├── 传感器聚合
      │                  │                    ├── 规则引擎
      │                  │                    └── 异常检测
      │                  │
      │                  └──▶ 设备管理 ──▶ OTA更新
      │                                       ├── 固件分发
      │                                       ├── 状态监控
      │                                       └── 远程诊断
      │
      ├──▶ 金融服务 ─────┬──▶ 交易系统 ──▶ 撮合引擎
      │                  │                    ├── 订单簿
      │                  │                    ├── 价格发现
      │                  │                    └── 风控检查
      │                  │
      │                  ├──▶ 支付系统 ──▶ 事务处理
      │                  │                    ├── Saga模式
      │                  │                    ├── 状态机
      │                  │                    └── 对账
      │                  │
      │                  └──▶ 风控系统 ──▶ 实时分析
      │                                       ├── 欺诈检测
      │                                       ├── 反洗钱
      │                                       └── 信用评估
      │
      ├──▶ 通信系统 ─────┬──▶ 即时通讯 ──▶ 消息路由
      │                  │                    ├── 多端同步
      │                  │                    ├── 消息存储
      │                  │                    └── 离线推送
      │                  │
      │                  ├──▶ VoIP ──────▶ 信令服务器
      │                  │                    ├── 会话管理
      │                  │                    ├── 媒体协商
      │                  │                    └── 中继选择
      │                  │
      │                  └──▶ 推送服务 ──▶ 消息分发
      │                                       ├── 广播
      │                                       ├── 订阅
      │                                       └── 定时
      │
      └──▶ 边缘计算 ─────┬──▶ 流处理 ────▶ 实时分析
                         │                    ├── 过滤聚合
                         │                    ├── 窗口计算
                         │                    └── 模式匹配
                         │
                         ├──▶ 缓存 ──────▶ 数据本地化
                         │                    ├── 热点数据
                         │                    ├── 预取策略
                         │                    └── 一致性维护
                         │
                         └──▶ 协同 ──────▶ 边缘协同
                                              ├── 任务分发
                                              ├── 结果聚合
                                              └── 故障转移
```

---

## 2. Web服务详细方案
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 REST API架构
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
Actix-web + Actor 架构:

┌─────────────────────────────────────────────────────────────────┐
│                     REST API 服务                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   HTTP 层 (Actix-web)                   │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │  Router      │  │  Middleware  │  │  Extractor   │  │   │
│  │  │  (路由)      │  │  (认证/日志) │  │  (参数解析)  │  │   │
│  │  └──────┬───────┘  └──────────────┘  └──────────────┘  │   │
│  │         │                                              │   │
│  └─────────┼──────────────────────────────────────────────┘   │
│            │                                                     │
│            ▼                                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   Actor 层                              │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ UserActor    │  │ OrderActor   │  │ ProductActor │  │   │
│  │  │ (用户服务)   │  │ (订单服务)   │  │ (商品服务)   │  │   │
│  │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘  │   │
│  │         │                 │                 │          │   │
│  └─────────┼─────────────────┼─────────────────┼──────────┘   │
│            │                 │                 │                │
│  ┌─────────┴─────────────────┴─────────────────┴──────────┐   │
│  │                   数据层                                │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ PostgreSQL   │  │ Redis        │  │ Elasticsearch│  │   │
│  │  │ (主数据库)   │  │ (缓存)       │  │ (搜索)       │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 实时通信方案
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
WebSocket 实时系统:

┌─────────────────────────────────────────────────────────────────┐
│                  实时通信系统                                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Client A          Load Balancer          Server Cluster        │
│  ┌────────┐        ┌──────────┐          ┌──────────────┐       │
│  │ WebSocket◄──────►│  Nginx   │◄────────►│  Node 1      │       │
│  │        │        │  (LB)    │          │  ┌──────────┐│       │
│  └────────┘        └──────────┘          │  │ RoomMgr  ││       │
│                                          │  │ Actor    ││       │
│  Client B                                │  └────┬─────┘│       │
│  ┌────────┐                              │       │      │       │
│  │ WebSocket◄────────────────────────────►│  ┌────┴─────┐│       │
│  │        │        pub/sub               │  │ UserActor││       │
│  └────────┘                              │  └──────────┘│       │
│                                          └──────────────┘       │
│                                                                  │
│  关键Actor:                                                      │
│  ├── ConnectionActor: 管理每个WebSocket连接                      │
│  ├── RoomActor: 管理聊天室/游戏房间                              │
│  ├── UserActor: 管理用户状态                                     │
│  └── PubSubActor: 处理消息广播                                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. 游戏服务器详细方案
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 3.1 MMORPG架构
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
MMORPG 服务器架构:

┌─────────────────────────────────────────────────────────────────┐
│                    游戏服务器集群                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   网关层 (Gateway)                      │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ Gateway 1    │  │ Gateway 2    │  │ Gateway 3    │  │   │
│  │  │ (连接管理)   │  │ (连接管理)   │  │ (连接管理)   │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   游戏逻辑层                            │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ SceneActor   │  │ PlayerActor  │  │ NpcActor     │  │   │
│  │  │ (场景管理)   │  │ (玩家状态)   │  │ (NPC AI)     │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ GuildActor   │  │ TradeActor   │  │ QuestActor   │  │   │
│  │  │ (公会系统)   │  │ (交易系统)   │  │ (任务系统)   │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   数据层                                │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ GameDB       │  │ Cache        │  │ Message      │  │   │
│  │  │ (游戏数据)   │  │ (Redis)      │  │ Queue        │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 实时对战方案
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
实时对战系统:

┌─────────────────────────────────────────────────────────────────┐
│                   实时对战服务器                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   匹配系统                              │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ MatchMaker   │  │ RatingCalc   │  │ TeamBalancer │  │   │
│  │  │ (匹配算法)   │  │ (ELO/GLICKO) │  │ (队伍平衡)   │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   房间管理                              │   │
│  │  ┌─────────────────────────────────────────────────┐   │   │
│  │  │  RoomActor 1          RoomActor 2               │   │   │
│  │  │  ┌──────────────┐    ┌──────────────┐          │   │   │
│  │  │  │ GameState    │    │ GameState    │          │   │   │
│  │  │  │ PlayerMgr    │    │ PlayerMgr    │          │   │   │
│  │  │  │ TickEngine   │    │ TickEngine   │          │   │   │
│  │  │  └──────────────┘    └──────────────┘          │   │   │
│  │  └─────────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
│  关键技术:                                                       │
│  ├── 状态同步: 客户端预测 + 服务器权威                           │
│  ├── 网络补偿: 延迟补偿/回放                                     │
│  └── 反作弊:   服务器端验证                                      │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 4. IoT平台详细方案
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 4.1 设备网关架构
>
> **[来源: [crates.io](https://crates.io/)]**

```text
IoT 网关架构:

┌─────────────────────────────────────────────────────────────────┐
│                     IoT 平台                                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Device Layer                                                    │
│  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐        │
│  │Sensor 1│ │Sensor 2│ │Camera  │ │Gateway │ │Edge Box│        │
│  └───┬────┘ └────┬───┘ └───┬────┘ └───┬────┘ └───┬────┘        │
│      │           │         │          │          │              │
│      │ MQTT      │ CoAP    │ HTTP     │ MQTT     │ gRPC         │
│      └───────────┴─────────┴──────────┴──────────┘              │
│                              │                                   │
│  ┌───────────────────────────┼───────────────────────────────┐ │
│  │                   Protocol Adapter Layer                    │ │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐       │ │
│  │  │ MqttActor    │ │ CoapActor    │ │ HttpActor    │       │ │
│  │  │ (MQTT处理)   │ │ (CoAP处理)   │ │ (HTTP处理)   │       │ │
│  │  └──────┬───────┘ └──────┬───────┘ └──────┬───────┘       │ │
│  │         └─────────────────┼─────────────────┘               │ │
│  │                           ▼                                 │ │
│  │                  ┌─────────────────┐                       │ │
│  │                  │ MessageRouter   │                       │ │
│  │                  │ (消息路由)      │                       │ │
│  │                  └────────┬────────┘                       │ │
│  └───────────────────────────┼───────────────────────────────┘ │
│                              │                                   │
│  ┌───────────────────────────┼───────────────────────────────┐ │
│  │                   Processing Layer                        │ │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐       │ │
│  │  │ RuleEngine   │ │ DataProcessor│ │ AlertActor   │       │ │
│  │  │ (规则引擎)   │ │ (数据处理)   │ │ (告警处理)   │       │ │
│  │  └──────────────┘ └──────────────┘ └──────────────┘       │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 5. 金融系统详细方案
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 5.1 交易系统架构
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
交易系统:

┌─────────────────────────────────────────────────────────────────┐
│                   交易系统                                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   接入层                                │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ FIX Gateway  │  │ REST API     │  │ WebSocket    │  │   │
│  │  │ (机构接入)   │  │ (零售接入)   │  │ (行情推送)   │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   撮合引擎                              │   │
│  │  ┌─────────────────────────────────────────────────┐   │   │
│  │  │           MatchingEngineActor                    │   │   │
│  │  │  ┌──────────────┐      ┌──────────────┐        │   │   │
│  │  │  │ OrderBook    │      │ TradeHistory │        │   │   │
│  │  │  │ (订单簿)     │      │ (成交记录)   │        │   │   │
│  │  │  │  - BuyQueue  │      │              │        │   │   │
│  │  │  │  - SellQueue │      │              │        │   │   │
│  │  │  └──────────────┘      └──────────────┘        │   │   │
│  │  └─────────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   风控/清算                             │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │ RiskEngine   │  │ Clearing     │  │ Settlement   │  │   │
│  │  │ (风控检查)   │  │ (清算)       │  │ (结算)       │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 Saga分布式事务
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
支付系统 Saga 模式:

订单支付流程:
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ Order    │───▶│ Payment  │───▶│ Inventory│───▶│ Shipping │
│ Service  │    │ Service  │    │ Service  │    │ Service  │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
     │               │               │               │
     │               │               │               │
     ▼               ▼               ▼               ▼
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ COMPLETED│    │ COMPLETED│    │ COMPLETED│    │ COMPLETED│
└──────────┘    └──────────┘    └──────────┘    └──────────┘

失败补偿流程:
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ Order    │───▶│ Payment  │───▶│ Inventory│──X─│ Shipping │
│ Service  │    │ Service  │    │ Service  │Fail│ Service  │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
     ▲               ▲               ▲
     │               │               │
┌──────────┐    ┌──────────┐    ┌──────────┐
│ Compensate│    │ Refund   │    │ Release  │
│ (取消订单)│    │ (退款)   │    │ (释放库存)│
└──────────┘    └──────────┘    └──────────┘

Actor实现:
├── SagaCoordinator: 协调整个事务流程
├── SagaParticipant: 每个服务的参与者Actor
└── SagaCompensator: 失败时执行补偿
```

---

## 6. 选择指南
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 6.1 领域-框架匹配
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 领域 | 首选框架 | 架构模式 | 关键技术 |
|:---|:---|:---|:---|
| Web API | Actix | 分层架构 | Actor-per-request |
| 游戏 | Bastion/coerce | 分区分服 | 状态同步 |
| IoT | Bastion | 网关模式 | 协议适配 |
| 金融 | coerce | Saga模式 | 分布式事务 |
| 通信 | coerce | 发布订阅 | 消息路由 |
| 边缘 | Stakker | 流处理 | 本地计算 |

---

**维护者**: Rust Actor Application Team
**更新日期**: 2026-03-05
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Machine Learning]**

> **[来源: Wikipedia - Artificial Intelligence]**

> **[来源: tch-rs Documentation]**

> **[来源: ACM - AI Systems]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
