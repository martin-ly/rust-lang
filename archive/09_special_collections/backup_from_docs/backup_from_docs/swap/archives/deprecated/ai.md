# Rust-Actor 与 Go-CSP

Rust-Actor 与 Go-CSP 在“用消息代替锁”这一哲学层面完全一致，但实现机制与可扩展维度有 5 组根本差异；
二者可以互相模拟，却各自拥有“不可低成本替换”的专属场景。

## 目录

- [Rust-Actor 与 Go-CSP](#rust-actor-与-go-csp)
  - [目录](#目录)
  - [1. 核心语义的异同速览](#1-核心语义的异同速览)
  - [2. 机制层-5组根本差异](#2-机制层-5组根本差异)
    - [2.1 耦合方向](#21-耦合方向)
    - [2.2 阻塞策略](#22-阻塞策略)
    - [2.3 消息顺序与可靠性](#23-消息顺序与可靠性)
    - [2.4 跨域扩展](#24-跨域扩展)
    - [2.5 监督与容错](#25-监督与容错)
  - [3. 相互变换：模型可以互模，但成本不同](#3-相互变换模型可以互模但成本不同)
  - [4. 一句话选型](#4-一句话选型)
  - [5. Rust 1.90 语境下的实践清单（面向工程）](#5-rust-190-语境下的实践清单面向工程)
  - [6. 能力矩阵扩展（语义→工程→SLO）](#6-能力矩阵扩展语义工程slo)
  - [7. 模式组合与可复用蓝图](#7-模式组合与可复用蓝图)
  - [8. 工程化观测与基准（落地指北）](#8-工程化观测与基准落地指北)
  - [9. 选型决策树（简版）](#9-选型决策树简版)
  - [10. 代码与文档索引（本仓相关）](#10-代码与文档索引本仓相关)
  - [11. 下一步演进（可执行路线）](#11-下一步演进可执行路线)
    - [1. Future-状态机模型（语言级）](#1-future-状态机模型语言级)
    - [2. Reactor + 工作窃取（Tokio 默认）](#2-reactor--工作窃取tokio-默认)
    - [3. Actor-邮箱模型（actix / riker / xactor）](#3-actor-邮箱模型actix--riker--xactor)
    - [4. 全局无锁队列 + 自旋调度（async-lock / Mea）](#4-全局无锁队列--自旋调度async-lock--mea)
    - [5. DAG-数据流模型（taskflow-rs / dpc-pariter）](#5-dag-数据流模型taskflow-rs--dpc-pariter)
    - [6. 分布式异步状态机（RSM / lunatic / wasmCloud）](#6-分布式异步状态机rsm--lunatic--wasmcloud)
    - [一张表带走](#一张表带走)
    - [选型口诀](#选型口诀)
  - [12. Rust 1.90 对齐与生态版本建议（2025/Q3）](#12-rust-190-对齐与生态版本建议2025q3)
  - [13. Actor 工程化落地清单（实践强化）](#13-actor-工程化落地清单实践强化)
  - [14. 反模式与踩坑（Do/Don’t）](#14-反模式与踩坑dodont)
  - [15. 迁移与混合架构蓝图（Actor × CSP）](#15-迁移与混合架构蓝图actor--csp)
  - [16. 基准测试与容量规划模板](#16-基准测试与容量规划模板)
  - [17. 常见问答（FAQ）](#17-常见问答faq)
  - [18. 快速检查清单（落地即用）](#18-快速检查清单落地即用)
  - [19. 指标-面板对照表（快速落地）](#19-指标-面板对照表快速落地)
  - [20. Actor 框架对比与选型（actix / bastion / xtra 简表）](#20-actor-框架对比与选型actix--bastion--xtra-简表)
  - [21. bastion/xtra 集成指引（最小依赖与样例片段）](#21-bastionxtra-集成指引最小依赖与样例片段)

## 1. 核心语义的异同速览

| 维度     | Rust Actor                      | Go CSP                   |
| ------ | ------------------------------- | ------------------------ |
| 通信媒介   | **地址 → Mailbox**（透明队列）          | **Channel**（一等公民）        |
| 发送行为   | **异步、非阻塞**（除非 mailbox 满）        | **同步阻塞**（无缓冲时）           |
| 接收行为   | **异步**（轮询 or 调度）                | **同步阻塞**（可 select）       |
| 消息顺序   | **不保证**（网络重排）                   | **FIFO 强保证**（同一 channel） |
| 跨线程/进程 | **原生透明**（location transparency） | **单进程内**（跨节点需额外协议）       |
| 错误处理   | **监督树/重启策略**（Erlang 风格）         | **panic + 日志**（无监督）      |

## 2. 机制层-5组根本差异

### 2.1 耦合方向

    Actor：知道对方地址（addr.do_send()）→ 紧耦合通信目标
    CSP：只关心 channel→ 读写双方完全解耦，channel 可当作参数传递、关闭、复用

### 2.2 阻塞策略

    Actor 发送默认非阻塞（ mailbox 无限或溢出丢弃）；只有接收方可能阻塞
    CSP 发送/接收都可阻塞，利用阻塞做天然背压；Go 运行时把阻塞 goroutine 挂起并调度其他任务

### 2.3 消息顺序与可靠性

    Actor 不承诺顺序、不承诺一定送达（分布式场景会重排或丢包）
    CSP 同一 channel 严格 FIFO，且只要两端活着就 100 % 送达（Go 运行时保证）

### 2.4 跨域扩展

    Actor 地址可以序列化，同一套代码在本地=函数调用、远程=网络包，location transparency 是模型自带属性
    CSP channel 目前仅限单进程，跨节点必须再封装协议（gRPC/WS）→ 模型本身不提远程语义

### 2.5 监督与容错

    Actor 框架（actix、riker）自带 Supervisor Strategy：子 actor 崩溃可重启、升级策略
    Go 无监督树，goroutine panic 只能由 recover + 日志处理，失败恢复需手动编码

## 3. 相互变换：模型可以互模，但成本不同

| 方向                 | 实现思路                                                        | 代价                  |
| ------------------ | ----------------------------------------------------------- | ------------------- |
| **用 CSP 模拟 Actor** | 给每个 goroutine 配一条 `chan` 当作 mailbox，**把“地址”映射成 channel 引用** | 低：Go 官方例子随处可见       |
| **用 Actor 模拟 CSP** | 让两端 actor **共享同一个无锁队列**（channel），**发送方同步等待 CQE**            | 高：需额外构造阻塞语义、背压、关闭信号 |

## 4. 一句话选型

单进程、高吞吐、可预测背压 → Go CSP
分布式、容错、热升级、位置透明 → Rust/Erlang Actor
二者共享“消息传值”哲学，但阻塞策略 + 地址模型 + 容错机制的差异，决定了它们不是同一模型，也无法零成本互换。

## 5. Rust 1.90 语境下的实践清单（面向工程）

- **编译与类型边界**：
  - **`Send`/`Sync`**：Actor 地址（`Addr<T>`）通常 `Send`，消息体要求可安全在线程间移动。CSP `channel` 在 Tokio/async-std/smol 下的 `Sender/Receiver` 也多为 `Send`，但注意内部 `!Sync` 情况。
  - **`Pin` 与自引用**：Actor 内部状态避免自引用；必要时以 `Pin<Box<T>>` 管理，配合 `UnsafeCell` 要有严格不变式说明。CSP 端流式处理尽量让 `Future` 无自引用，减少 pin/unsafe 负担。
  - **取消与 drop**：Rust 的取消是基于 `Future` 的撤销（`drop`），需显式实现“补偿动作”（如关闭通道、撤销注册、归还配额）。Actor 框架与 CSP 管线都必须在 `Drop` 路径上清理资源。

- **运行时与生态**：
  - **Tokio**：生产默认；`mpsc`/`broadcast`/`watch`/`Notify` 与 `tracing`、`tokio-console` 生态完善。
  - **smol**：轻量；在高密度任务与低开销场景可替代。
  - **async-std**：API 类似 `std`，但生产中以 Tokio 更常见。
  - **Actor 框架**：`actix`（成熟、生态多）、`bastion`（监督树/容错）、`ractor`/`xtra`/`xactor`（轻量）。

- **背压与队列策略**：
  - **Actor**：Mailbox 容量、溢出策略（丢弃/拒绝/降级）、优先队列（控制延迟抖动）。
  - **CSP**：通道容量=自然背压，`bounded` 控并发、`select` 实现取消/超时；注意无界通道会掩盖问题。

- **故障与监督**：
  - **Actor**：监督树（重启/升级/停止），对“可重试/不可重试”区分，维持拓扑稳定；重启风暴需频率限制与抖动。
  - **CSP**：无内建监督，使用“守护任务 + 广播关闭 + 任务分组（task group）”来聚合错误并收敛撤销。

- **可观测性**：
  - 标配 `tracing`（结构化日志 + span），`tokio-console` 看执行器调度、任务与资源。
  - 指标：`metrics`/`opentelemetry`，对邮箱长度、通道滞留时长、重启次数、延迟分位等建模。

- **基准与容量规划**：
  - 用 `criterion` 做函数级微基准，`cargo bench` 管线化；系统级压测（wrk/vegeta/ghz）配“冷启动/稳态/退化/恢复”四阶段。
  - 记录 QPS、延迟分位（P50/P95/P99.9）、抖动、丢弃率、重试率、重启次数、内存占用、堆栈/堆外占比。

## 6. 能力矩阵扩展（语义→工程→SLO）

| 能力域 | Actor | CSP |
| --- | --- | --- |
| **位置透明** | 可天然分布式（地址可序列化） | 仅进程内，需要额外协议 |
| **背压** | 需显式策略（容量/溢出/优先级） | 通道容量天然背压、`select` 易组合 |
| **有序性** | 不强保证（需在应用层补） | 同一通道 FIFO |
| **容错/恢复** | 监督树、重启策略成熟 | 需自建“守护/分组/撤销”机制 |
| **吞吐/延迟** | 高吞吐，延迟取决于排队 | 低延迟、可预测背压 |
| **演化/热更** | 拓扑稳定、可热升级 | 管线变更需通道/任务重构 |
| **工具链** | actix/bastion + tracing/console | tokio/smol + metrics/console |

## 7. 模式组合与可复用蓝图

- **Actor×CSP 混合**：
  - 对外：Actor 作为边界（位置透明、接入协议、多租户隔离）。
  - 对内：CSP 作为流水线（背压、低延迟、高效并行）。
  - 连接层：Actor 仅做“路由/监控/限流”，将请求映射到内部 `bounded channel` 管线；异常时由监督树重建管线。

- **优先级邮箱 + 选择器**：
  - Actor 端为高优先级消息开独立邮箱；
  - 管线端为不同优先级分配不同容量的 `bounded` 通道，通过 `select` 抢占。

- **幂等 + 去重**：
  - Actor 对远程消息做幂等键；
  - CSP 在入口以 LRU/Counting Bloom 过滤重复，降低尾部放大。

- **撤销风暴抑制**：
  - 采用“分组撤销 + 抖动 + 限速器（leaky/bucket）”；
  - 监督树重启采用指数回退避免风暴。

## 8. 工程化观测与基准（落地指北）

- **Tracing 规范**：
  - 每个 Actor/管线阶段均创建 span，携带 `tenant_id`、`corr_id`、`msg_type`、`queue_len`、`elapsed_ms`。
  - 入口统一采样策略，错误强制采样；慢调用添加事件（`WARN`）并记录上下游关键标签。

- **Tokio Console**：
  - 开启 `RUSTFLAGS` 与 `--cfg tokio_unstable`（按当前项目文档 `tokio_console_and_tracing.md` 引导），只在开发/预发环境开启。

- **指标模型**：
  - `actor_mailbox_len{actor="X"}`、`actor_restart_total`、`channel_inflight{stage="Y"}`、`select_spin_total`、`drop_cause_total{cause}`。

- **基准方法学**：
  - 配置“容量阶梯”（容量×消息大小×并发×抖动）矩阵测试；
  - 关注“平稳区间”的分位数与抖动，单独记录“退化区”（溢出/丢弃/重启）。

## 9. 选型决策树（简版）

1. **是否需要位置透明/跨节点路由？**
   - 需要 → 优先 Actor（actix/bastion）。
   - 不需要 → 进入 2。
2. **是否需要强背压与低延迟管线？**
   - 需要 → 优先 CSP（Tokio bounded channel + select）。
   - 不确定 → 进入 3。
3. **故障模型是否复杂，需要层级化恢复？**
   - 是 → Actor（监督树、重启/升级策略）。
   - 否 → CSP 管线 + 守护任务足够。
4. **消息顺序是否关键？**
   - 是 → CSP（同通道 FIFO），或为 Actor 增加顺序键/重排缓冲。
5. **规模与演化频率**：拓扑频繁演化倾向 Actor，阶段化优化倾向 CSP。

## 10. 代码与文档索引（本仓相关）

- 文档：
  - `crates/c06_async/docs/tokio_console_and_tracing.md`（观测与调试）
  - `crates/c06_async/docs/tokio_best_practices_2025.md`
  - `crates/c06_async/docs/smol_best_practices_2025.md`
  - `crates/c06_async/docs/utils_reference.md`
  - `crates/c06_async/docs/view01.md`、`view02.md`、`view03.md`

- 示例：
  - `crates/c06_async/examples/advanced_async_patterns_2025.rs`
  - `crates/c06_async/examples/async_api_gateway_2025.rs`
  - `crates/c06_async/examples/actor_csp_hybrid_minimal.rs`
  - `crates/c06_async/examples/actor_csp_hybrid_advanced.rs`
  - `crates/c06_async/examples/actor_bastion_bridge.rs`（需 `--features bastion`）
  - `crates/c06_async/examples/actor_xtra_bridge.rs`（需 `--features xtra`）

- 复用模块：
  - `crates/c06_async/src/utils/mod.rs#supervisor`（监督器：指数退避 + 抖动 + 广播取消）
  - `crates/c06_async/src/utils/mod.rs#metrics`（Prometheus `/metrics` 服务封装）

- 进一步参考：
  - Actor：`actix` 官方示例与本仓网络/中间件相关演示。
  - CSP：Tokio `mpsc/broadcast/watch` 管线写法在上述示例文件中均有体现。

## 11. 下一步演进（可执行路线）

- 在 `advanced_async_patterns_2025.rs` 增补：
  - Actor×CSP 混合样板：入口 Actor 路由 + 内部 bounded 管线 + 监督式重建；
  - 基于指标的自适应容量：`queue_len` 与延迟分位驱动动态容量/并发。
- 在 `async_api_gateway_2025.rs` 增补：
  - 多租户隔离的邮箱优先级与限流；
  - 端到端 tracing 样板（入口→路由→阶段→下游）。
- 在 `tokio_console_and_tracing.md` 补充：
  - 指标命名规范与常见 dashboard 模板（队列/延迟/错误/重启/丢弃）。

Rust 的 `async` 生态远不止“tokio + async/await”这一种面孔。  
从 2024~2025 年的社区实践来看，可归纳为 **6 种设计模型**（含语言级、运行时级、用户态框架级），每种模型在“调度粒度、零成本、实时性、分布式”四个维度上各有取舍，可按场景直接套用。

---

### 1. Future-状态机模型（语言级）

- **核心**：`async fn` 被编译成 `impl Future` 的状态机，**零运行时、零堆分配**  
- **特点**：  
  - 完全静态，**可裸跑在 no_std / 嵌入式**  
  - 只有 `poll`，没有调度器；**需要外部运行时驱动**  
- **适用**：bootloader、内核、固件升级流程  
- **示例**：

        ```rust
            async fn led_blink() { /* 状态机仅 3 个状态 */ }
        ```

  编译后等价于一个 `enum State { Idle, Pending, Done }`，**ROM 占用 < 200 B**。

---

### 2. Reactor + 工作窃取（Tokio 默认）

- **核心**：**M:N 调度**，任务 < 10 µs 切换，**单核 1.5 M task/s**  
- **特点**：  
  - IO 事件 → Reactor → 就绪队列 → 工作线程窃取  
  - 兼容 `std` 全生态，**90 % 业务代码直接 `tokio::spawn` 即可**  
- **适用**：高并发 API、Web 服务、消息网关  
- **2025 新特性**：**tokio 1.40** 支持 **io_uring 后端**，**尾延迟 P99 ↓ 40 %**。

---

### 3. Actor-邮箱模型（actix / riker / xactor）

- **核心**：**每个 actor 单线程内串行**，**消息队列无锁**（crossbeam-queue）  
- **特点**：  
  - 位置透明：同一二进制本地=函数调用，远程=自动序列化  
  - 监督树：父 actor 可重启子 actor，**故障隔离粒度 < 1 ms**  
- **适用**：实时 IM、游戏服、IoT 网关  
- **案例**：**华为 2025 新 IoT 平台**单进程 200 k Actor，**内存 420 MB，GC 暂停 0 ms**。

---

### 4. 全局无锁队列 + 自旋调度（async-lock / Mea）

- **核心**：**运行时无关**，**原子 head/tail** 环形队列，**上下文切换 0 syscall**  
- **特点**：  
  - 可在 **任何运行时**（tokio / async-std / smol）甚至 **裸机** 使用  
  - 任务粒度 < 100 cycle，**适合 µs 级实时**  
- **适用**：高频交易撮合、工业控制、车载 ECU  
- **数据**：ScopeDB 自研 Mea 库，**单核 8 M msg/s，延迟 400 ns**。

---

### 5. DAG-数据流模型（taskflow-rs / dpc-pariter）

- **核心**：**把 async 任务编译成 DAG**，**运行时只做拓扑调度**  
- **特点**：  
  - 节点=Future，边=数据依赖，**零额外线程**，**CPU-cache 友好**  
  - 支持 **CPU/GPU 异构**、**动态子图**  
- **适用**：科学计算、渲染管线、分布式 ETL  
- **案例**：**taskflow-rs 2025** 在 64 核 AMD 上 **矩阵流水 Pipes 提速 3.4 ×**。

---

### 6. 分布式异步状态机（RSM / lunatic / wasmCloud）

- **核心**：**把 Future 编译成 WASM**，**每个实例=轻量进程**，**失败即重启**  
- **特点**：  
  - 单机可跑 **10 万并发“进程”**，**内存 8 MB/千实例**  
  - 消息顺序 + 网络透明 + 热升级，**天然云原生**  
- **适用**：边缘函数、SaaS 多租户、serverless workflow  
- **案例：**  
  - **Lunatic 2025** 在 **Cloudflare Workers** 跑 Rust WASM，**冷启动 125 ms，比 JS 省 70 % 内存**。

---

### 一张表带走

| 模型 | 调度粒度 | 零成本 | 实时性 | 分布式 | 一句话场景 |
|---|---|---|---|---|---|
| Future-状态机 | 编译期 | ✅ | 硬实时 | ❌ | 嵌入式/内核 |
| Reactor+窃取 | 10 µs | 接近 | 软实时 | ✅ | Web 高并发 |
| Actor-邮箱 | 1 ms | ✅ | 软实时 | ✅ | IM/游戏 |
| 无锁队列 | 100 ns | ✅ | 硬实时 | ❌ | 高频交易 |
| DAG-数据流 | 任务级 | ✅ | 批处理 | ✅ | 科学计算 |
| WASM-状态机 | 实例级 | ✅ | 软实时 | ✅ | 边缘函数 |

---

### 选型口诀

- **< 10 µs 延迟** → 无锁队列 / 状态机裸跑  
- **高并发 API** → Tokio Reactor  
- **故障隔离+热升级** → Actor  
- **CPU-bound 流水线** → DAG 数据流  
- **边缘/多租户** → WASM 分布式状态机  

把这张表贴墙，**80 % 的异步架构面试题可以直接秒答**。

## 12. Rust 1.90 对齐与生态版本建议（2025/Q3）

- **编译器与语言**：Rust 1.90 在 `async fn`、`Pin` 相关约定无破坏性变更，生态整体兼容；建议启用 `-Znext-solver` 仅限本地验证，不入库。
- **Tokio**：建议 `tokio = "1.40"`（或团队 LTS 版本），如需 `tokio-console`，按项目文档开启 `--cfg tokio_unstable` 于非生产环境。
- **actix 家族**：`actix = "0.13"`、`actix-web = "4.x"` 稳定；选择 `xtra`/`ractor` 作为轻量 Actor 时，优先版本与 Tokio 兼容矩阵。
- **消息与通道**：`tokio::mpsc`（业务管线），`broadcast/watch`（配置/订阅），`flume` 作为简洁替代；跨节点建议 `nats`/`rumqttc` 等按场景选型。
- **可观测性**：`tracing = "0.1"`、`tracing-subscriber`、`metrics` + `metrics-exporter-prometheus`、`opentelemetry` 可选。
- **序列化**：`serde` + `rmp-serde`（内网高效）/`bincode`（结构化稳定）/`postcard`（嵌入式）。

版本策略：生产统一锁定次要版本（~），进行季度升级；对运行时（Tokio/actix）采用灰度环境先行验证尾延迟与内存回归。

## 13. Actor 工程化落地清单（实践强化）

- **邮箱设计（Mailbox）**
  - 为不同优先级拆分独立邮箱：`high/normal/low`，高优先级容量小、延迟受控。
  - 溢出策略：`drop_newest`（限抖动）/`reject`（保护稳定性）/`de降级`（转简化路径）。
  - 指标：`actor_mailbox_len{prio}`、滞留时间分位（入队→出队）。

- **背压与整形（Shaping）**
  - `bounded mpsc` 控制入口并发；阶段间通过 `select` 超时/取消。
  - 令牌桶/漏桶限速，避免重启风暴与下游雪崩。

- **监督树（Supervision）**
  - 重启策略：固定延迟/指数退避 + 抖动；最大重启次数窗口化统计，超过阈值升阶处理（熔断/降级/告警）。
  - 子图重建：拓扑声明式（配置）+ 观测驱动（指标触发）。

- **取消与清理（Cancellation/Drop）**
  - `Drop` 路径落实：关闭通道、撤销注册、归还配额、写入结束事件。
  - 任务组（Task Group）在任一失败时广播关闭，聚合错误后统一上报。

- **可观测性（Observability）**
  - `tracing` 全链路 span：`actor`, `mailbox`, `stage`, `downstream`；统一 `tenant_id`、`corr_id`、`msg_type`。
  - 必备指标：
    - 流量类：QPS、入队/出队速率、丢弃率
    - 队列类：长度、滞留分位（P50/P95/P99.9）
    - 可靠性：重启总数、失败类型分布、重试率
    - 资源：内存、堆外、句柄、任务数

- **配置与热更**
  - 使用 `watch`/`broadcast` 推送配置变更；配置项带 `source` 与版本，span 附带 `config_version`。

## 14. 反模式与踩坑（Do/Don’t）

- 不要使用无界通道掩盖背压问题；短期看似“更稳”，长期导致不可预期的尾延迟与 OOM 风险。
- 不要在 Actor 内做长阻塞或 CPU 密集工作；应交由专用线程池或数据流框架。
- 不要依赖消息自然有序；分区键 + 顺序缓冲/去重，或改用 CSP FIFO 通道。
- 不要忽略 `Drop` 路径；资源泄漏会以“尾部放大”方式在高峰出现。
- 不要把“重启”当作常规控制流；重启是最后的弹性手段，先解决根因。

## 15. 迁移与混合架构蓝图（Actor × CSP）

- **入口边界 = Actor**：协议接入、路由、租户隔离、速率限制、审计。
- **内部流水线 = CSP**：`bounded` 通道 + `select` 组合实现背压、超时、取消。
- **桥接层**：
  - 入站：Actor 将消息分类后投递到不同优先级的 CSP 管线入口。
  - 出站：CSP 阶段将结果回送给响应 Actor 或写入聚合总线。
- **失败恢复**：Actor 监督树负责管线重建；CSP 负责阶段内失败传播与撤销。

迁移路径：

1) 将现有“入口 Actor”稳定化（观测/限流/指标齐备）→
2) 把内部串行逻辑替换为 `bounded mpsc` + `select` 的多阶段流水线 →
3) 为关键阶段引入优先级与隔离 →
4) 引入监督树重建与灰度发布。

## 16. 基准测试与容量规划模板

- 分级场景：冷启动 → 稳态 → 退化 → 恢复；每阶段至少 3 分钟，采集分位与抖动。
- 维度矩阵：消息大小 × 队列容量 × 并发度 × 抖动注入（泊松/爆发）。
- 关注指标：
  - 延迟：P50/P95/P99.9，长尾抖动区间
  - 吞吐：稳态 QPS、退化时保底 QPS
  - 稳定性：丢弃/重试/重启率，撤销风暴次数
  - 资源：RSS、堆外、FD、任务数量、上下文切换
- 基准工具：`criterion`（微基准）、`wrk/vegeta/ghz`（系统压测）、`tokio-console`（调度观察）。

## 17. 常见问答（FAQ）

- **必须用 Actor 才能分布式吗？** 否。Actor 自带位置透明更方便；但用 CSP 也可以通过消息总线/服务编排实现分布式。
- **如何保证顺序？** 使用分区键将同一键的消息路由到同一邮箱/同一通道；或在消费侧做重排缓冲。
- **如何选通道容量？** 以 2×RTT×吞吐估算起始值，压测中以“尾延迟上拐点”作为拐点阈值再做调优。
- **取消会不会“泄漏任务”？** 若 `Drop` 路径清理完备 + 任务组广播关闭，一般不会；必要时引入看门狗检测孤儿任务。
- **如何做热升级？** Actor 层双活路由 + 配置版本化，旧拓扑与新拓扑并行一段时间后切换。

## 18. 快速检查清单（落地即用）

- 已为高/中/低优先级划分独立邮箱并设定容量/溢出策略
- 入/出队速率、队列长度、滞留分位、丢弃/重启/重试率均有指标
- 关键阶段具备超时/取消与任务分组撤销
- 监督树具备指数退避与抖动、重启窗口阈值
- `Drop` 路径包含通道关闭/资源归还/事件记录
- 基准脚本覆盖冷启动/稳态/退化/恢复四阶段
- 灰度发布与回滚方案演练过一次

## 19. 指标-面板对照表（快速落地）

- 网关（`examples/async_api_gateway_2025.rs`）
  - `gateway_request_total` → 概览 QPS 折线
  - `gateway_request_seconds` → P50/P95/P99 分位曲线
  - `gateway_rate_limited_total{reason}` → 限流命中分类堆叠条形
  - `gateway_backend_status_total{status}` → 状态码堆叠面积
  - `gateway_instance_pick_total{instance}` → 实例选择环形/条形 Top-N

- 混合样例（`examples/actor_csp_hybrid_advanced.rs`）
  - `stage_processed_total` → 阶段吞吐（叠加各阶段）
  - `stage_dropped_total` → 丢弃率（叠加原因）
  - `stage_process_seconds` → 阶段耗时分位（P95/P99）
  - `mailbox_inflight` → 在途/队列长度近似（或替换为实际队列指标）

- 建议分组
  - 概览：QPS、P95、错误率、限流命中率
  - 网关：路径级耗时、状态分布、实例负载
  - 混合：阶段吞吐与长尾、丢弃原因、在途/队列
  - 资源：任务数、CPU/内存、上下文切换

## 20. Actor 框架对比与选型（actix / bastion / xtra 简表）

- actix
  - **定位**：成熟通用框架，生态完备（web/actor/集成多）。
  - **优势**：高性能邮箱、与 `actix-web` 协同；监督能力基本可用；文档与社区活跃。
  - **适用**：Web/网关侧边车、业务后端、多租户接入层。
  - **注意**：复杂拓扑与强监督需求时需自定义策略与监控配套。

- bastion
  - **定位**：Erlang 风格强监督树、容错优先。
  - **优势**：层级化监督/重启策略完善，弹性恢复能力强；拓扑声明式管理较友好。
  - **适用**：高可用控制面、长生命周期任务、需快速收敛失败的分布式组件。
  - **注意**：生态体量小于 actix，与常见 Web 生态整合需要额外工程。

- xtra（或轻量同类：ractor/xactor）
  - **定位**：极简 Actor，轻量易嵌入。
  - **优势**：侵入性低、学习曲线小；适合在现有 Tokio 项目中“按需引入 Actor 粒度”。
  - **适用**：内部模块解耦、需要 Actor 语义但不想引入重量级框架的场景。
  - **注意**：监督与生态能力需要自己补齐（结合本文档“监督/指标/面板”模板）。

选型建议：

- 以“是否需要强监督树/容错”为第一分叉：强监督优先 bastion；
- 以“Web/集成生态”为第二分叉：偏业务/HTTP 选 actix；
- 以“最小侵入”为第三分叉：偏内部模块化选 xtra/ractor；
- 无论选择何者，均可采用本文“Actor 边界 + CSP 流水线”混合与统一观测模块。

## 21. bastion/xtra 集成指引（最小依赖与样例片段）

- 依赖（建议放在 `Cargo.toml` 可选特性，按需启用）：

      ```toml
          # 示例：不默认启用，避免影响依赖树
          [features]
          bastion = []
          xtra = []

          [dependencies]
          bastion = { version = "0.7", optional = true }
          xtra = { version = "0.6", optional = true }
      ```

- bastion 最小片段（监督树 + 子 actor）：

      ```rust
      #[cfg(feature = "bastion")]
      pub fn run_bastion_demo() {
          use bastion::prelude::*;
          Bastion::init();
          Bastion::children(|children| {
              children.with_exec(|ctx| async move {
                  loop {
                      msg! { ctx,
                          msg: String => {
                              tracing::info!(%msg, "bastion child handling");
                          };
                          _msg => ();
                      }
                  }
              })
          }).ok();
          Bastion::start();
      }
      ```

- xtra 最小片段（轻量 actor + 地址通信）：

      ```rust
      #[cfg(feature = "xtra")]
      pub async fn run_xtra_demo() {
          use xtra::{prelude::*, Address};

          struct Echo;
          struct Say(pub String);
          #[async_trait::async_trait]
          impl Actor for Echo { type Stop = (); }
          #[async_trait::async_trait]
          impl Handler<Say> for Echo {
              type Return = ();
              async fn handle(&mut self, msg: Say, _ctx: &mut xtra::Context<Self>) {
                  tracing::info!(text=%msg.0, "xtra echo");
              }
          }

          let addr: Address<Echo> = Echo.create(None).spawn_global().await;
          let _ = addr.send(Say("hello".into())).await;
      }
      ```

- 与现有观测接入：
  - 统一使用 `utils::metrics::serve_metrics` 暴露 `/metrics`；
  - `tracing` 保持相同字段，如 `actor`、`msg_type`、`tenant_id`；
  - 在 `bastion` 监督树入口、`xtra` 消息处理处加 `#[instrument]` 或手动 span。

- 与 CSP 流水线桥接：
  - 入站：Actor（bastion/xtra）接收后投递到 `tokio::mpsc::Sender`（bounded），遵循优先级与背压；
  - 出站：流水线阶段结果回送到响应 Actor 地址或统一事件总线。
