# 测验：网络与异步生态（L6）

> **EN**: Networking and Async Ecosystem Quiz
> **Summary**: L6 standalone quiz on the Rust networking and async ecosystem: web frameworks (Axum/Actix-web/Rocket/Poem), async runtimes (Tokio work-stealing vs Glommio thread-per-core), QUIC/HTTP-3 protocols, and eBPF.
> **受众**: [进阶] / [专家]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L6 生态层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [Web 框架](../04_web_and_networking/03_web_frameworks.md) · [网络协议](../04_web_and_networking/07_network_protocols.md) · [Glommio 与 Thread-per-Core](../04_web_and_networking/05_glommio_and_thread_per_core.md) · [高性能网络服务架构](../04_web_and_networking/08_high_performance_network_service_architecture.md) · [tokio docs](https://docs.rs/tokio)（P2 生态权威 API 文档，curl 200 实测 2026-07-13）
>
> **前置概念**:
> [Web 框架](../04_web_and_networking/03_web_frameworks.md) ·
> [网络协议](../04_web_and_networking/07_network_protocols.md) ·
> [Glommio 与 Thread-per-Core](../04_web_and_networking/05_glommio_and_thread_per_core.md) ·
> [并发与异步（Async）](../../03_advanced/00_concurrency/01_concurrency.md) ·
> [Rust vs Go（并发模型对比）](../../05_comparative/01_systems_languages/03_rust_vs_go.md)

---

> **Bloom 层级**: L2-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对 L6 网络与异步子领域生态格局（框架、运行时（Runtime）、协议）的掌握。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、Web 框架格局

本节考查 Web 框架格局：Q1 定位 Axum 的生态位，Q2 检验运行时绑定策略与权威页兼容性分析的一致性（Coherence）。

### Q1. 🟢【单选】Axum 在 Rust Web 框架生态中的定位是？

- A. 基于 Actor 模型的工业级框架
- B. Tokio 生态的原生扩展，构建于 Tokio、Tower 与 Hyper 之上
- C. 声明式编程与类型安全优先的框架
- D. 模块（Module）化与 OpenAPI 优先的框架

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [Web 框架](../04_web_and_networking/03_web_frameworks.md)：Axum 是 Tokio 生态原生扩展，运行时绑定 Tokio 独占，路由模型为组合式（`Router::merge`/`nest`/`route`），中间件走 Tower Service 生态（`Layer` trait）。A 是 Actix-web（Actor 模型），C 是 Rocket（声明式），D 是 Poem（OpenAPI 优先）。

</details>

---

### Q2. 🟢 以下运行时绑定策略判断，哪一项与权威页的运行时兼容性分析一致？

```rust,ignore
// 伪代码：框架的运行时绑定策略
enum RuntimeBinding {
    Exclusive(&'static str),  // 独占绑定
    Agnostic,                 // 运行时无关
}
```

| 选项 | 判断 |
|:---|:---|
| A | Axum 运行时无关，可在任意 executor 上运行 |
| B | Axum 独占绑定 Tokio；Actix-web 基于自身 Actor 运行时 |
| C | 所有 Rust Web 框架都必须绑定 Tokio |
| D | 运行时选择与框架无关，纯属部署细节 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：Axum 的架构特征明确标注"运行时绑定：Tokio 独占"（构建于 Tokio/Tower/Hyper）；Actix-web 是 Actor 模型的工业级实现，有自身运行时体系。框架选型时需同时确认运行时绑定策略——这是 [Web 框架](../04_web_and_networking/03_web_frameworks.md) §三「异步运行时集成对比」的核心维度。A/C/D 均与兼容性矩阵矛盾。

</details>

---

## 二、异步运行时：Work-Stealing vs Thread-per-Core

本节对比两类异步运行时模型：Q3 辨析 thread-per-core 与 work-stealing 的调度差异，Q4 按低延迟场景做运行时选型。

### Q3. 🟡【单选】Glommio 的 thread-per-core 模型与 Tokio 的 work-stealing 模型相比，下列哪项描述正确？

- A. Glommio 自动负载均衡，编程复杂度更低
- B. Glommio 无线程切换、缓存友好，但负载均衡需手动处理，适用于高频交易/数据库引擎等场景
- C. Tokio 无任务跨线程迁移，缓存局部性更好
- D. 两者在任意负载下性能完全等价

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [Glommio 与 Thread-per-Core](../04_web_and_networking/05_glommio_and_thread_per_core.md) 对比表：thread-per-core（Glommio）无线程切换、缓存友好度最高、负载均衡需手动处理、编程复杂度较高，适用高频交易、数据库引擎、高吞吐网络服务；work-stealing（Tokio）自动负载均衡、编程复杂度较低，适用通用 Web / 微服务。Glommio 还提供 `LocalExecutorBuilder::pin_to_cpu` 做 CPU 绑定与 NUMA 优化。

</details>

---

### Q4. 🟡 某低延迟交易系统评估运行时。按权威页的适用场景判定，下列哪条结论成立？

| 选项 | 判断 |
|:---|:---|
| A | 应选 Tokio：其自动负载均衡必然带来更低尾延迟 |
| B | 应选 Glommio：thread-per-core + CPU 绑定契合高吞吐/低延迟场景，但要接受手动负载均衡与较高编程复杂度 |
| C | 两种运行时不支持同一套 Future 抽象，代码不可迁移 |
| D | 运行时选择只影响开发体验，对性能无实质影响 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：权威页 §四「适用场景与不推荐场景」将高频交易、数据库引擎、高吞吐网络服务列为 thread-per-core 的适用场景，代价是负载均衡需手动处理、编程复杂度较高。A 过度承诺——自动负载均衡不等于低尾延迟；C 错——两者都基于 `std::future::Future`，迁移是运行时 API 层面的事；D 与 §二对比表的缓存友好度差异矛盾。

</details>

---

## 三、QUIC、HTTP/3 与 eBPF

本节覆盖新协议栈：Q5 归纳 QUIC 相对 TCP+TLS 解决的根本问题，Q6 辨析 HTTP/3 的传输层，Q7 考查 aya-rs 的 eBPF 优势。

### Q5. 🟡【多选】QUIC 相对 TCP+TLS 解决的根本问题包括？（选出所有正确项）

- A. 连接建立延迟：3-RTT 降为 1-RTT（重连 0-RTT）
- B. 队头阻塞：流独立，单包丢失只阻塞该流
- C. 连接迁移：以连接 ID 标识，IP 变化不影响连接
- D. 完全消除拥塞控制的必要性

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：按 [网络协议](../04_web_and_networking/07_network_protocols.md) §1.1，QUIC 解决四个根本问题：连接建立延迟（3-RTT → 1-RTT/0-RTT 重连）、队头阻塞（流独立）、连接迁移（连接 ID 而非四元组绑定，NAT 重绑定后不断开）、协议僵化（UDP 封装避免中间盒干扰）。D 错：QUIC 仍需要拥塞控制，只是把传输层逻辑移入用户态。Rust 实现为 quinn。

</details>

---

### Q6. 🟡【判断】HTTP/3 直接基于 TCP 传输，其头部压缩机制 QPACK 与 HTTP/2 的 HPACK 完全通用。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：HTTP/3 是基于 **QUIC**（UDP 之上）的应用层协议，不基于 TCP；其头部压缩为 QPACK，是面向 QUIC 流独立语义重新设计的机制（QUIC 没有 TCP 式的全局有序字节流，HPACK 的依赖序假设不再成立），二者不通用。(Source: [网络协议](../04_web_and_networking/07_network_protocols.md) §二)

</details>

---

### Q7. 🔴【单选】关于 Rust + eBPF（aya-rs）的独特优势，下列哪项最准确？

- A. eBPF 程序只能用 C 编写，Rust 仅能做用户态加载器
- B. Rust 的所有权（Ownership）/借用（Borrowing）模型把内核验证器关注的内存安全（Memory Safety）问题前移到编译期，aya-rs 提供 Rust 编写 eBPF 程序与用户态加载的完整链路
- C. eBPF 允许任意无限循环，Rust 只是语法更现代
- D. aya-rs 绕过内核验证器直接执行字节码

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [网络协议](../04_web_and_networking/07_network_protocols.md) §三，eBPF 的本质是内核可编程——在内核中运行受验证器约束的字节码；aya-rs 让 eBPF 程序与用户态加载器都用 Rust 编写，其独特优势在于 Rust 的内存安全保证与内核验证器的安全目标同构，把一类内存错误前移到编译期。A/C/D 均与 eBPF 的验证器模型矛盾（验证器拒绝无限循环、任意内存访问）。

</details>

---

### Q8. 🔴 某团队设计高吞吐网络服务，方案评审如下。按权威页的性能技术谱系，哪条评审意见成立？

```text
方案：基于 Tokio + 传统 read/write 拷贝路径实现代理；
      压测显示 memcpy 占 CPU 40%。
```

| 选项 | 评审意见 |
|:---|:---|
| A | memcpy 开销不可避免，接受现状 |
| B | 应引入零拷贝技术（如 `bytes::Bytes` 切片（Slice）共享、`sendfile`/`splice` 语义或 Tokio 的零拷贝发送），消除用户态冗余拷贝 |
| C | 改用同步阻塞 I/O 即可消除拷贝 |
| D | 只需加大缓冲区，拷贝次数自然归零 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：[高性能网络服务架构](../04_web_and_networking/08_high_performance_network_service_architecture.md) §1「零拷贝技术深度」指出传统拷贝路径的性能问题正是用户态/内核态间冗余 memcpy；对应手段包括零拷贝原理与实现、缓冲 I/O 优化、批量写入以及 Tokio 零拷贝发送。A 是放弃优化；C 同步阻塞 I/O 不解决拷贝且损害并发；D 加大缓冲只减少系统调用次数，不消除拷贝本身。

</details>

---

### Q9. 🔴【多选】设计一个云原生微服务的网络栈选型，按权威页内容，下列决策合理的有？（选出所有正确项）

- A. 通用 Web/微服务并发模型选 Tokio（work-stealing，自动负载均衡）
- B. 需要连接迁移与 0-RTT 重连的移动场景考虑 QUIC（quinn）
- C. 需要内核级可观测/过滤且追求内存安全时考虑 aya-rs（eBPF）
- D. 任何场景都应优先选择 thread-per-core，因为它缓存最友好

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A/B/C 分别对应三份权威页的明确适用场景：Tokio 面向通用 Web/微服务（[Glommio 与 Thread-per-Core](../04_web_and_networking/05_glommio_and_thread_per_core.md) §二）；QUIC 的连接迁移/0-RTT 适配移动网络（[网络协议](../04_web_and_networking/07_network_protocols.md) §1.1）；aya-rs 面向内核可编程场景（同页 §三）。D 错：thread-per-core 编程复杂度高、负载均衡需手动，权威页明确列出"不推荐场景"，选型应走决策树而非单一最优解。

</details>

---

### Q10. 🟡【判断】`async-std` 仍是 Rust 异步生态的主力活跃运行时，新项目应优先于 Tokio 评估它。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：知识库统一加注的生态状态提示明确指出：`async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。这与 [Glommio 与 Thread-per-Core](../04_web_and_networking/05_glommio_and_thread_per_core.md) §五「生态状态」的口径一致。

</details>

---

## 四、网络安全与协议实现（W3-b 扩展）

本节（W3-b 扩展）考查安全与协议实现：Q11 的 TLS 配置与 Q12 的 `accept` 语义均对照权威页判定。

### Q11. 🟢【单选】在 Rust 异步服务中配置 TLS，按 [网络安全](../12_networking/02_network_security.md) 的实践，推荐的组件组合是？

- A. `openssl` 直接 FFI 调用，自行管理证书生命周期（Lifetimes）
- B. `rustls` + `tokio-rustls`（纯 Rust TLS 实现，装配 `TlsAcceptor`）
- C. 关闭 TLS 改用应用层自研加密
- D. `native-tls` 是唯一可用于生产的选择

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：[网络安全](../12_networking/02_network_security.md) 的示例使用 `tokio_rustls::{TlsAcceptor, rustls}` 装配 `ServerConfig`：rustls 是纯 Rust 的 TLS 1.3（RFC 8446）实现，避免 OpenSSL C 依赖的内存安全风险。A 引入 C FFI 的 UB 面；C 违反"不要自研密码学"原则；D 错——native-tls 只是平台 TLS 的绑定选项之一，不是唯一生产选择。

</details>

---

### Q12. 🟡 以下 TCP 服务器骨架中，`listener.accept().await` 的语义哪项正确？

```rust,ignore
let listener = TcpListener::bind("127.0.0.1:8080").await?;
loop {
    let (socket, addr) = listener.accept().await?;
    tokio::spawn(async move { handle(socket).await });
}
```

| 选项 | 判断 |
|:---|:---|
| A | `accept()` 是阻塞调用，会冻结整个运行时 |
| B | `accept().await` 异步等待新连接，返回 `(TcpStream, SocketAddr)`；每连接 `tokio::spawn` 一个任务实现并发 |
| C | `TcpListener` 一次只能持有一个连接 |
| D | `spawn` 的任务必须运行在独立 OS 线程上 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：按 [网络编程基础](../12_networking/05_networking_basics.md)，`TcpListener::accept().await` 是异步等待——当前任务挂起但不阻塞 executor 线程；返回 `(TcpStream, SocketAddr)` 元组。`tokio::spawn` 把每连接处理交给调度器，任务默认在 work-stealing 线程池的多路复用任务中运行（D 错：不要求独立 OS 线程）。A/C 与异步 accept 语义矛盾。

</details>

---

### Q13. 🟡【判断】WebSocket 协议在握手阶段复用 HTTP 的 Upgrade 机制，握手成功后连接切换为全双工帧协议，不再是 HTTP 语义。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：按 [WebSocket 实时通信](../04_web_and_networking/06_websocket_realtime_communication.md)：WebSocket 以 HTTP `Upgrade: websocket` 握手（含 `Sec-WebSocket-Key` 挑战/响应），101 Switching Protocols 之后连接升级为独立的双向帧协议（文本/二进制/控制帧），后续消息不再经过 HTTP 请求-响应模型。Rust 生态对应 `tokio-tungstenite` 等实现。

</details>

---

### Q14. 🔴【多选】实现自定义二进制协议时，按 [自定义协议实现](../12_networking/03_custom_protocol_implementation.md) 与网络编程实践，下列设计决策合理的有？（选出所有正确项）

- A. 用长度前缀帧（length-prefix framing）界定消息边界，避免 TCP 粘包/拆包问题
- B. 直接在 `TcpStream` 上按固定大小 `read`，假设一次读必得一条完整消息
- C. 用 `bytes::BytesMut` 管理读写缓冲，配合 `tokio-util` 的 `Framed` + 自定义 `Decoder`/`Encoder`
- D. 协议版本号与魔数（magic）放在帧头，便于识别错连与协议演进

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C、D**

**解析**：TCP 是字节流协议，不保留消息边界：长度前缀帧（A）与 `Framed` + `Decoder`/`Encoder`（C）是 Rust 生态的标准做法（`tokio-util::codec`）；帧头放版本号与魔数（D）是协议可演进与错连检测的常规工程实践。B 错：`read` 返回的字节数由内核缓冲与网络状况决定，一次读可能得到半条或多条消息——这是新手实现自定义协议最常见的正确性缺陷。

</details>

---

### Q15. 🔴 某公网服务遭遇慢速连接攻击（Slowloris 类）。按 [网络安全](../12_networking/02_network_security.md) 的防护谱系，下列哪组措施与攻击机理对症？

| 选项 | 措施组合 |
|:---|:---|
| A | 只加大 TLS 密钥长度 |
| B | 连接级超时（握手/读写 deadline）+ 速率限制（rate limiting）+ 并发连接数上限 |
| C | 改用 UDP 即可根治 |
| D | 增大内核 backlog 到无限 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：Slowloris 类攻击的机理是以极慢速度占用连接资源，耗尽服务器的并发连接配额。对症措施是资源维度的防护：连接各阶段超时、`tower`/`governor` 类速率限制、每 IP/全局并发连接上限——这些正是网络安全页认证、速率限制与常见攻击缓解节覆盖的手段。A 与资源耗尽机理无关；C 把问题换成另一套攻击面；D 无限 backlog 反而放大资源占用。

</details>

---

> **变更记录**: 2026-07-12 新建（W3-b：L6 网络/异步生态 quiz，10 题：单选 3 / 代码阅读 3 / 多选 2 / 判断 2；难度 🟢2 / 🟡5 / 🔴3）；2026-07-13 扩展至 15 题（+5 题「网络安全与协议实现」：rustls/TLS、异步 accept、WebSocket 握手、自定义帧协议、Slowloris 防护；难度 🟢3 / 🟡7 / 🔴5）。
