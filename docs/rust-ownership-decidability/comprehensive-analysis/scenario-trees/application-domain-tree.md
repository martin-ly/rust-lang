# 应用领域解决方案树

## 1. 嵌入式系统

```text
嵌入式系统需求
      │
      ├──▶ 实时性要求? ──▶ 是 ──▶ 确定性调度
      │                          │
      │                          ├──▶ RTIC
      │                          │      ├── 静态优先级
      │                          │      ├── WCET可分析
      │                          │      └── 无堆分配
      │                          │
      │                          └──▶ 传统RTOS
      │                                   ├── FreeRTOS绑定
      │                                   └── 裸机+中断
      │
      └──▶ 异步需求? ──▶ 是 ──▶ Embassy
                        │          ├── 硬件抽象层
                        │          ├── async/await
                        │          └── 定时器集成
                        │
                        └──▶ 否 ──▶ 裸机Rust
                                      ├── 寄存器访问
                                      ├── 中断处理
                                      └── 内存布局控制
```

### 嵌入式解决方案

| 场景 | 解决方案 | 关键库 | 设计模式 |
|:---|:---|:---|:---|
| 传感器读取 | Embassy HAL | embassy-stm32 | RAII、类型状态 |
| 实时控制 | RTIC | cortex-m-rtic | 资源声明、优先级 |
| 无线通信 | Embassy + smoltcp | embassy-net | async、Channel |
| 电机控制 | RTIC | stm32f4xx-hal | 定时器、DMA |
| 低功耗应用 | Embassy | embassy-executor | 空闲休眠、WFI |

---

## 2. Web服务

```text
Web服务架构
      │
      ├──▶ 微服务? ──▶ 是 ──▶ 服务通信
      │                          │
      │                          ├──▶ gRPC
      │                          │      └── tonic
      │                          │
      │                          └──▶ REST
      │                                   ├── Axum
      │                                   └── Actix-web
      │
      ├──▶ 实时功能? ──▶ 是 ──▶ WebSocket
      │                          ├── tokio-tungstenite
      │                          └── actix-web-actors
      │
      └──▶ 传统Web? ──▶ 是 ──▶ 选择框架
                                 │
                                 ├── API优先 → Axum
                                 ├── Actor模型 → Actix-web
                                 └── 快速原型 → Rocket
```

### Web解决方案

| 场景 | 框架 | 数据库 | 部署 |
|:---|:---|:---|:---|
| REST API | Axum | sqlx/diesel | Docker/K8s |
| GraphQL | async-graphql | sqlx | Serverless |
| WebSocket | Actix-web | redis | 集群 |
| gRPC服务 | tonic | 自带 | Sidecar |
| 静态网站 | Actix-files | - | CDN |

---

## 3. 分布式系统

```text
分布式系统需求
      │
      ├──▶ 需要服务发现? ──▶ 是 ──▶ Consul/etcd
      │
      ├──▶ 需要消息队列? ──▶ 是 ──▶ 选择模式
      │                          │
      │                          ├──▶ 发布/订阅 → nats
      │                          ├──▶ 队列 → lapin (RabbitMQ)
      │                          ├──▶ 流 → rdkafka
      │                          └──▶ 内存 → redis
      │
      └──▶ 需要分布式Actor? ──▶ 是 ──▶ coerce
                                        ├── 集群发现
                                        ├── 远程Actor
                                        └── 位置透明
```

### 分布式解决方案

| 模式 | 实现 | 容错 | 一致性 |
|:---|:---|:---:|:---|
| Saga | coerce + 状态机 | ⭐⭐⭐ | 最终一致 |
| CQRS | 分离读写 + 事件溯源 | ⭐⭐⭐⭐ | 最终一致 |
| 分片 | coerce-sharding | ⭐⭐⭐⭐ | 分片内一致 |
| 共识 | raft-rs | ⭐⭐⭐⭐⭐ | 强一致 |
| CRDT | crdts crate | ⭐⭐⭐⭐⭐ | 强最终一致 |

---

## 4. 数据处理

```text
数据处理场景
      │
      ├──▶ 流处理? ──▶ 是 ──▶ 延迟要求
      │                          │
      │                          ├──▶ 低延迟 → fluvio
      │                          │               ├── 原生Rust
      │                          │               └── 高性能
      │                          │
      │                          └──▶ 高吞吐 → 自实现
      │                                           ├── tokio-stream
      │                                           └── 背压控制
      │
      ├──▶ 批处理? ──▶ 是 ──▶ 数据量
      │                          │
      │                          ├──▶ 大数据 → Arrow + DataFusion
      │                          │
      │                          └──▶ 中小数据 → polars
      │
      └──▶ ETL? ──▶ 是 ──▶ 流程编排
                            ├── 自定义pipeline
                            └── 错误重试机制
```

### 数据处理方案

| 场景 | 库 | 特性 | 性能 |
|:---|:---|:---|:---:|
| DataFrame | polars | 查询优化、并行 | ⭐⭐⭐⭐⭐ |
| 流处理 | fluvio | 持久化、分区 | ⭐⭐⭐⭐ |
| OLAP | datafusion | SQL接口、Arrow | ⭐⭐⭐⭐ |
| 序列化 | serde | 零拷贝、派生宏 | ⭐⭐⭐⭐⭐ |
| 压缩 | zstd/lz4 | 流式压缩 | ⭐⭐⭐⭐ |

---

## 5. 网络基础设施

```text
网络基础设施
      │
      ├──▶ 代理/网关? ──▶ 是 ──▶ 性能要求
      │                          │
      │                          ├──▶ 极致 → monoio
      │                          │              ├── io_uring
      │                          │              └── 零拷贝
      │                          │
      │                          └──▶ 通用 → pingora
      │                                         ├── 模块扩展
      │                                         └── 负载均衡
      │
      ├──▶ DNS? ──▶ 是 ──▶ trust-dns
      │                      ├── 安全DNS
      │                      └── DNSSEC
      │
      └──▶ VPN/隧道? ──▶ 是 ──▶ wireguard-rs
                                 └── 现代加密
```

### 网络解决方案

| 组件 | 实现 | 协议 | 特点 |
|:---|:---|:---|:---|
| HTTP客户端 | reqwest/hyper | HTTP/1.1, HTTP/2 | 异步、连接池 |
| HTTP服务器 | hyper | HTTP/1.1, HTTP/2 | 底层、高性能 |
| gRPC | tonic | HTTP/2 + protobuf | 流式、拦截器 |
| WebSocket | tokio-tungstenite | RFC 6455 | 异步、帧处理 |
| TLS | rustls | TLS 1.3 | 安全、纯Rust |
| DNS | trust-dns | DNS/DNSSEC | 递归解析 |

---

## 6. 系统工具

```text
系统工具
      │
      ├──▶ CLI应用? ──▶ 是 ──▶ 交互复杂度
      │                          │
      │                          ├──▶ 简单 → clap
      │                          │             └── 声明式解析
      │                          │
      │                          └──▶ 复杂 → tui-rs/crossterm
      │                                        ├── 终端UI
      │                                        └── 事件处理
      │
      ├──▶ 系统监控? ──▶ 是 ──▶ 指标收集
      │                          ├── prometheus
      │                          └── opentelemetry
      │
      └──▶ 文件处理? ──▶ 是 ──▶ 性能
                                 │
                                 ├──▶ 大文件 → memmap2
                                 └──▶ 小文件 → tokio::fs
```

### 系统工具方案

| 场景 | 库 | 功能 |
|:---|:---|:---|
| CLI解析 | clap | 派生宏、子命令、自动帮助 |
| 终端UI | ratatui | 富文本、布局、事件 |
| 日志 | tracing | 结构化、过滤器、订阅者 |
| 配置 | config | 多源合并、环境变量 |
| 错误处理 | anyhow/eyre | 上下文、回溯 |

---

## 7. 游戏开发

```text
游戏开发
      │
      ├──▶ 2D游戏? ──▶ 是 ──▶ bevy
      │                          ├── ECS架构
      │                          └── 数据驱动
      │
      ├──▶ 3D游戏? ──▶ 是 ──▶ bevy / wgpu
      │                          │
      │                          ├──▶ 游戏引擎 → bevy
      │                          └──▶ 图形底层 → wgpu
      │
      └──▶ 游戏网络? ──▶ 是 ──▶ 同步策略
                                 │
                                 ├──▶ 状态同步 → naia
                                 └──▶ 帧同步 → ggrs
```

### 游戏开发方案

| 模块 | 库 | 特性 |
|:---|:---|:---|
| 引擎 | bevy | ECS、渲染、音频 |
| 物理 | rapier2d/3d | 确定性、跨平台 |
| 图形 | wgpu | WebGPU标准、跨平台 |
| 音频 | rodio | 播放、混音 |
| 输入 | winit | 窗口、事件 |

---

## 8. 区块链/加密货币

```text
区块链开发
      │
      ├──▶ 智能合约? ──▶ 是 ──▶ ink!
      │                          ├── 编译为Wasm
      │                          └── Substrate集成
      │
      ├──▶ 节点实现? ──▶ 是 ──▶ Substrate
      │                          ├── 模块化框架
      │                          └── 共识可插拔
      │
      └──▶ 密码学? ──▶ 是 ──▶ 库选择
                                 │
                                 ├──▶ 通用 → ring
                                 └──▶ 零知识 → bellman
```

### 区块链方案

| 组件 | 实现 | 用途 |
|:---|:---|:---|
| 智能合约 | ink! | Substrate链 |
| 共识 | libp2p | 点对点网络 |
| 存储 | parity-db | 键值存储 |
| 加密 | substrate-primitives | 签名、哈希 |
| WASM | wasmer/wasmtime | 合约执行 |

---

## 9. AI/机器学习

```text
AI/ML
      │
      ├──▶ 推理? ──▶ 是 ──▶ 运行时
      │                          │
      │                          ├──▶ 通用 → tract
      │                          └──▶ 性能 → tch-rs (PyTorch)
      │
      ├──▶ 训练? ─️▶ 是 ─️▶ 平台
      │                          │
      │                          ├──️▶ Python集成 → PyO3
      │                          └──️▶ Rust原生 → burn
      │
      └──️▶ 向量搜索? ─️▶ 是 ─️▶ qdrant
                                 └──️ 近似最近邻
```

### AI/ML方案

| 场景 | 库 | 特点 |
|:---|:---|:---|
| ONNX推理 | tract | 无依赖、边缘部署 |
| PyTorch | tch-rs | C++绑定、完整功能 |
| 训练 | burn | 纯Rust、类型安全 |
| NLP | rust-bert | 预训练模型 |
| 向量DB | qdrant | 相似性搜索 |

---

## 10. 跨领域最佳实践

### 通用架构建议

```text
┌─────────────────────────────────────────────────────────┐
│                    应用架构推荐                          │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  1. 分层设计                                             │
│     ├── Domain: 纯Rust业务逻辑                           │
│     ├── Application: 用例编排                            │
│     ├── Infrastructure: IO/外部服务                      │
│     └── Interface: API/UI                                │
│                                                          │
│  2. 错误处理                                             │
│     ├── 库: thiserror + 枚举                             │
│     └── 应用: anyhow + 上下文                            │
│                                                          │
│  3. 日志/监控                                            │
│     ├── 日志: tracing                                    │
│     ├── 指标: prometheus                                 │
│     └── 链路: opentelemetry                              │
│                                                          │
│  4. 测试策略                                             │
│     ├── 单元: 边界条件                                   │
│     ├── 集成: 组件交互                                   │
│     └── 模糊: cargo-fuzz                                 │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

---

**维护者**: Rust Application Architecture Team
**更新日期**: 2026-03-05
