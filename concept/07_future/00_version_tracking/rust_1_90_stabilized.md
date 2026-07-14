> **EN**: Rust 1.90 Stabilized Features
> **Summary**: Authoritative concept page for `Rust 1.90 网络特性参考`. Content migrated from `crates/c10_networks/docs/tier_03_references/03_rust_190_networking_features_reference.md`.
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: A×Ref — 版本特性参考
> **前置依赖**: [Rust Version Tracking](01_rust_version_tracking.md) · [Async](../../03_advanced/01_async/01_async.md) · [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)
> **后置概念**: [Rust 1.91 Stabilized](rust_1_91_stabilized.md) · [Networking Basics](../../06_ecosystem/12_networking/05_networking_basics.md)
> **定理链**: Version Context ⟹ Feature Set ⟹ Migration Impact
>
> **权威来源**: 本页为 `Rust 1.90 Stabilized Features` 的权威概念页；crate 文档仅保留导航 stub。

# Rust 1.90 网络特性参考

> **文档版本**: v1.0.0
> **更新日期**: 2025-10-23
> **Rust 版本**: 1.90+
> **文档层级**: Tier 3 - 技术参考

---

## 0. Rust 1.90.0 特性 × 影响面 × 受益场景矩阵（2026-07-14 对齐 1.97 范式）

> **说明**：本节对齐 [`rust_1_97_stabilized.md`](rust_1_97_stabilized.md) 的矩阵结构，列出 **1.90.0 本列车首次稳定**的核心特性（每版 3–8 条）。
> 下文 §1–§10 为网络编程场景对**既有稳定特性**的应用参考，其真实稳定版本见 §11 版本事实对齐表。
>
> **官方发布说明可访问性实测**（2026-07-14，`curl` HTTP 200）：
> [releases.rs 1.90.0](https://releases.rs/docs/1.90.0/) · [Rust 1.90.0 Release Blog](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)

| 特性 | 影响面 | 受益场景 | 权威源 |
|:---|:---|:---|:---|
| `x86_64-unknown-linux-gnu` 默认使用 lld 链接器 | 编译器 / 链接 | Linux 构建提速、降低链接内存占用 | [Release Blog](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/) · [linkage](../../03_advanced/04_ffi/03_linkage.md) |
| `u{N}::{checked,overflowing,saturating,wrapping}_sub_signed` | 标准库 / 整数 | 无符号-有符号混合减法的溢出可控语义 | [releases.rs](https://releases.rs/docs/1.90.0/) |
| `CStr` / `CString` / `Cow<CStr>` 互比 | 标准库 / FFI | C 字符串互操作无需手动转换 | [releases.rs](https://releases.rs/docs/1.90.0/) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md) |
| `f32`/`f64` `floor`/`ceil`/`trunc`/`fract`/`round`/`round_ties_even` 进入 const | const 上下文 / 数值 | const 数值计算与查找表生成 | [releases.rs](https://releases.rs/docs/1.90.0/) |
| Cargo 多包发布稳定（multi-package publishing） | Cargo | workspace 一键发布多个 crate | [releases.rs](https://releases.rs/docs/1.90.0/) · [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) |
| `x86_64-apple-darwin` 降为 Tier 2（含 host tools） | 平台 | Intel macOS CI/构建策略调整 | [releases.rs](https://releases.rs/docs/1.90.0/) |

---

## 目录

- [Rust 1.90 网络特性参考](#rust-190-网络特性参考)
  - [0. Rust 1.90.0 特性 × 影响面 × 受益场景矩阵（2026-07-14 对齐 1.97 范式）](#0-rust-1900-特性--影响面--受益场景矩阵2026-07-14-对齐-197-范式)
  - [目录](#目录)
  - [1. 异步特性增强](#1-异步特性增强)
    - [1.1 异步Trait稳定化（RPITIT）](#11-异步trait稳定化rpitit)
    - [1.2 异步闭包改进](#12-异步闭包改进)
    - [1.3 async fn in trait生命周期推断](#13-async-fn-in-trait生命周期推断)
  - [2. GATs在网络编程中的应用](#2-gats在网络编程中的应用)
    - [泛型关联类型（Generic Associated Types）](#泛型关联类型generic-associated-types)
  - [3. let-else模式匹配](#3-let-else模式匹配)
    - [网络错误处理](#网络错误处理)
  - [4. impl Trait增强](#4-impl-trait增强)
    - [返回类型优化](#返回类型优化)
  - [5. 常量泛型改进](#5-常量泛型改进)
    - [固定大小缓冲区](#固定大小缓冲区)
  - [6. 迭代器组合子增强](#6-迭代器组合子增强)
    - [网络数据处理](#网络数据处理)
  - [7. 错误处理改进](#7-错误处理改进)
    - [网络错误类型](#网络错误类型)
  - [8. 网络专用特性应用](#8-网络专用特性应用)
    - [Edition 2024 特性（1.85.0+ stable）](#edition-2024-特性1850-stable)
  - [9. 性能优化特性](#9-性能优化特性)
    - [零成本抽象](#零成本抽象)
  - [10. 实战示例集](#10-实战示例集)
    - [完整HTTP客户端（Rust 1.90特性集成）](#完整http客户端rust-190特性集成)
    - [WebSocket服务器（完整特性）](#websocket服务器完整特性)
  - [**下一步**: 04\_网络性能基准参考.md](#下一步-04_网络性能基准参考md)
  - [11. 版本事实对齐与权威来源（2026-07-12 回填）](#11-版本事实对齐与权威来源2026-07-12-回填)
  - [过渡段](#过渡段)
  - [定理链](#定理链)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

---

## 1. 异步特性增强

1.90 周期的异步特性主线是「让 trait 中的 async 真正可用」：

1. **RPITIT（返回位置 impl Trait in Trait）**：trait 方法可声明 `fn get(&self) -> impl Future<Output = T>`，`async fn in trait` 正是其语法糖；静态分派场景不再需要 `async-trait` crate 的 `#[async_trait]`（它会把每个调用装箱为 `Pin<Box<dyn Future>>`，热路径有真实成本）。
2. **异步闭包（RFC 3668）**：`async || ...` 产生实现 `AsyncFn` trait 的闭包——与普通闭包对齐的三种形态（`AsyncFn`/`AsyncFnMut`/`AsyncFnOnce`），解决了「闭包内 await 只能套 `async move` 块且借用语义错误」的长期痛点。
3. **生命周期推断**：async fn in trait 的返回 Future 默认捕获 `&self` 生命周期，`+ use<'lt>` 精确捕获语法处理「不借用 self」的优化场景。

判定依据：库作者定义异步 trait 时优先 RPITIT + `Send` bound 注解；仅当需要 trait object（`dyn`）时退回 `async-trait` 宏。

### 1.1 异步Trait稳定化（RPITIT）

Rust 1.75.0+稳定化了async fn in trait，无需`async-trait`宏（Macro）：

```rust
/// 异步网络客户端Trait (Rust 1.75+)
pub trait AsyncNetworkClient {
    /// 异步连接
    async fn connect(&self, addr: &str) -> Result<(), std::io::Error>;

    /// 异步发送数据（带生命周期）
    async fn send<'a>(&'a self, data: &'a [u8]) -> Result<usize, std::io::Error>;

    /// 异步接收数据
    async fn recv(&self, buf: &mut [u8]) -> Result<usize, std::io::Error>;
}

/// 实现示例
pub struct TcpClient {
    stream: Option<tokio::net::TcpStream>,
}

impl AsyncNetworkClient for TcpClient {
    async fn connect(&self, addr: &str) -> Result<(), std::io::Error> {
        // 自动生成 impl Future<Output = Result<(), std::io::Error>>
        let stream = tokio::net::TcpStream::connect(addr).await?;
        Ok(())
    }

    async fn send<'a>(&'a self, data: &'a [u8]) -> Result<usize, std::io::Error> {
        // 生命周期自动推断
        Ok(data.len())
    }

    async fn recv(&self, buf: &mut [u8]) -> Result<usize, std::io::Error> {
        Ok(0)
    }
}
```

**旧方式 vs 新方式**：

```rust,ignore
// ❌ Rust 1.74及之前（需要async-trait宏）
#[async_trait::async_trait]
pub trait OldAsyncTrait {
    async fn fetch(&self, url: &str) -> Result<String, Error>;
}

// ✅ Rust 1.75+（原生支持）
pub trait NewAsyncTrait {
    async fn fetch(&self, url: &str) -> Result<String, Error>;
}
```

### 1.2 异步闭包改进

```rust
use tokio::task::JoinSet;

/// 异步闭包捕获优化（Rust 1.90）
pub async fn async_closure_example() {
    let client = reqwest::Client::new();
    let urls = vec!["https://example.com", "https://rust-lang.org"];

    // ✅ 异步闭包自动捕获
    let futures = urls.iter().map(|&url| {
        let client = client.clone();
        async move {
            client.get(url).send().await
        }
    });

    let results = futures::future::join_all(futures).await;

    for (i, result) in results.iter().enumerate() {
        println!("URL {}: {:?}", i, result.as_ref().map(|r| r.status()));
    }
}

/// JoinSet并发任务（Rust 1.90改进）
pub async fn joinset_example() {
    let mut set = JoinSet::new();

    for i in 0..10 {
        set.spawn(async move {
            tokio::time::sleep(tokio::time::Duration::from_millis(100 * i)).await;
            i * 2
        });
    }

    while let Some(res) = set.join_next().await {
        println!("Task完成: {:?}", res);
    }
}
```

### 1.3 async fn in trait生命周期推断

```rust
/// 生命周期自动推断（Rust 1.90）
pub trait StreamProcessor {
    /// 自动推断'a生命周期
    async fn process<'a>(&'a mut self, data: &'a [u8]) -> Vec<u8>;

    /// 复杂生命周期推断
    async fn transform<'a, 'b>(&'a self, input: &'b str) -> String
    where
        'b: 'a;
}

/// 实现
pub struct NetworkProcessor;

impl StreamProcessor for NetworkProcessor {
    async fn process<'a>(&'a mut self, data: &'a [u8]) -> Vec<u8> {
        // 生命周期自动对齐
        data.iter().map(|&b| b ^ 0xFF).collect()
    }

    async fn transform<'a, 'b>(&'a self, input: &'b str) -> String
    where
        'b: 'a,
    {
        input.to_uppercase()
    }
}
```

---

## 2. GATs在网络编程中的应用

GAT（泛型关联类型，1.65 稳定）在网络编程中的杀手场景是**零拷贝流式解析**：

- **借用返回类型**：`trait Parser { type Output<'a> where Self: 'a; fn parse<'a>(&'a self, buf: &'a [u8]) -> Self::Output<'a>; }`——关联类型带生命周期参数，解析结果可直接引用输入缓冲（如 `&'a str` 切片），无需 `String` 拷贝；无 GAT 时代只能返回拥有类型或用 `unsafe` 绕。
- **LendingIterator 模式**：`type Item<'a>` 让迭代器产出借用自身的元素（如按行解析的流），标准 `Iterator` 无法表达——这是 GAT 设计的原始动机（RFC 1598）。
- **网络协议栈**：帧解析、HTTP 头部视图（`Header<'a>`）等场景的分配次数可降一个量级。

判定依据：解析热路径（>10⁶ msg/s）先评估 GAT 化能否消除分配；API 复杂度上升明显，非热路径不值得。

### 泛型关联类型（Generic Associated Types）

```rust
use std::pin::Pin;
use futures::Future;

/// 使用GATs定义通用异步流（Rust 1.65+）
pub trait AsyncStream {
    type Item;
    type ReadFuture<'a>: Future<Output = Option<Self::Item>> + 'a
    where
        Self: 'a;

    fn read<'a>(&'a mut self) -> Self::ReadFuture<'a>;
}

/// TCP流实现
pub struct TcpAsyncStream {
    stream: tokio::net::TcpStream,
}

impl AsyncStream for TcpAsyncStream {
    type Item = Vec<u8>;
    type ReadFuture<'a> = Pin<Box<dyn Future<Output = Option<Self::Item>> + 'a>>;

    fn read<'a>(&'a mut self) -> Self::ReadFuture<'a> {
        Box::pin(async move {
            let mut buf = vec![0u8; 1024];
            match tokio::io::AsyncReadExt::read(&mut self.stream, &mut buf).await {
                Ok(n) if n > 0 => {
                    buf.truncate(n);
                    Some(buf)
                }
                _ => None,
            }
        })
    }
}

/// 通用连接抽象
pub trait Connection {
    type Error;
    type SendFuture<'a>: Future<Output = Result<(), Self::Error>> + 'a
    where
        Self: 'a;

    fn send<'a>(&'a mut self, data: &'a [u8]) -> Self::SendFuture<'a>;
}
```

---

## 3. let-else模式匹配

`let ... else` 语法在模式匹配失败时执行发散（diverging）分支，适合网络错误处理中的“早退”（early return）路径。其编译期约束是：`else` 块必须以 `return`/`break`/`continue`/`panic!` 发散，编译器据此保证绑定变量在后续作用域中必然有效。

- **适用判定**: 失败分支只需早退、不依赖错误值细节时，优先 `let-else`；需要按错误种类分支时仍使用 `match`。
- **对比 `if let`**: `let-else` 将成功路径保持在主缩进层级，降低深层嵌套（deep nesting）的认知负担。
- **网络场景**: 解析响应头、校验 TLS 握手状态、解码帧头等“要么拿到值、要么终止连接”的环节。

下面的网络错误处理小节给出完整的错误传播链路示例。

### 网络错误处理

```rust
use std::net::SocketAddr;

/// let-else简化错误处理（Rust 1.65+）
pub fn parse_socket_addr(addr_str: &str) -> Result<SocketAddr, String> {
    // ✅ let-else模式
    let Ok(addr) = addr_str.parse::<SocketAddr>() else {
        return Err(format!("无效地址: {}", addr_str));
    };

    Ok(addr)
}

/// 网络请求验证
pub async fn validate_request(headers: &reqwest::header::HeaderMap) -> Result<String, String> {
    // ✅ let-else链式处理
    let Some(auth_header) = headers.get("Authorization") else {
        return Err("缺少Authorization头".into());
    };

    let Ok(auth_str) = auth_header.to_str() else {
        return Err("Authorization头不是有效UTF-8".into());
    };

    let Some(token) = auth_str.strip_prefix("Bearer ") else {
        return Err("Authorization格式错误".into());
    };

    Ok(token.to_string())
}

/// 配置解析
#[derive(serde::Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
}

pub fn load_config() -> Result<ServerConfig, String> {
    let Ok(config_str) = std::fs::read_to_string("config.json") else {
        return Err("无法读取配置文件".into());
    };

    let Ok(config) = serde_json::from_str::<ServerConfig>(&config_str) else {
        return Err("配置文件JSON格式错误".into());
    };

    Ok(config)
}
```

---

## 4. impl Trait增强

`impl Trait` 返回类型让函数隐藏具体类型、只暴露 trait 接口。1.90 时代配合 trait 中的 `impl Trait`（RPITIT，稳定于 1.75）与 `use<..>` 精确捕获语法（1.82），返回类型优化的重点是**捕获集（capture set）的最小化**。

- **编译期收益**: `impl Iterator<Item = u8> + use<'a, T>` 形式避免无意捕获过多生命周期，使调用方获得更宽松的借用约束。
- **运行时收益**: 返回具体闭包/迭代器类型（而非 `Box<dyn ...>`）保留单态化（monomorphization）与内联机会，是零成本抽象的落点。
- **判定依据**: 公共 API 返回类型泄漏内部实现（如 `Map<Filter<...>>`）时应改为 `impl Trait`；调用方需要命名类型存入结构体字段时，仍需具名类型或 nightly 的 `type_alias_impl_trait`。

下面的返回类型优化小节给出改造前后的对比。

### 返回类型优化

```rust,ignore
use futures::stream::{Stream, StreamExt};
use std::pin::Pin;

/// impl Trait in return position（Rust 1.26+，1.90优化）
pub fn create_http_client() -> impl Future<Output = reqwest::Client> {
    async {
        reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(30))
            .build()
            .unwrap()
    }
}

/// 返回异步流
pub fn fetch_urls(
    urls: Vec<String>,
) -> impl Stream<Item = Result<reqwest::Response, reqwest::Error>> {
    futures::stream::iter(urls)
        .map(|url| async move {
            reqwest::get(&url).await
        })
        .buffered(5) // 并发5个请求
}

/// 复杂返回类型简化
pub fn create_tcp_acceptor(
    addr: &str,
) -> impl Future<Output = Result<impl Stream<Item = tokio::net::TcpStream>, std::io::Error>> {
    let addr = addr.to_string();
    async move {
        let listener = tokio::net::TcpListener::bind(&addr).await?;
        Ok(async_stream::stream! {
            loop {
                if let Ok((stream, _)) = listener.accept().await {
                    yield stream;
                }
            }
        })
    }
}
```

---

## 5. 常量泛型改进

常量泛型（const generics）允许类型以编译期常量为参数，固定大小缓冲区是其最典型的工程形态：`struct RingBuffer<T, const N: usize>`。相比动态 `Vec`，它把容量编码进类型，获得三方面的确定性：

| 维度 | `Vec<T>` | 常量泛型缓冲区 |
|---|---|---|
| 内存位置 | 堆分配 | 栈/内联，零分配 |
| 容量检查 | 运行时 `len/cap` | 编译期 `N`，索引可消除边界检查 |
| 适用场景 | 容量未知/可变 | 网络帧缓冲、固定窗口统计 |

- **判定依据**: 容量上限在协议层已固定（如 MTU 1500、帧头 64 字节）时，用常量泛型获得无分配路径；容量由输入决定时退回 `Vec`。
- **边界**: 稳定的 `min_const_generics` 只支持整数/布尔/字符参数；`generic_const_exprs`（如 `[T; N * 2]`）仍属 nightly。

### 固定大小缓冲区

```rust
/// 常量泛型网络缓冲区（Rust 1.51+，1.90改进）
pub struct FixedBuffer<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> FixedBuffer<N> {
    pub fn new() -> Self {
        Self {
            data: [0; N],
            len: 0,
        }
    }

    pub async fn read_from(&mut self, stream: &mut tokio::net::TcpStream) -> std::io::Result<usize> {
        use tokio::io::AsyncReadExt;

        let n = stream.read(&mut self.data[self.len..]).await?;
        self.len += n;
        Ok(n)
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }
}

/// 使用示例
pub async fn fixed_buffer_example() -> std::io::Result<()> {
    let mut stream = tokio::net::TcpStream::connect("127.0.0.1:8080").await?;

    // 4KB缓冲区
    let mut buffer = FixedBuffer::<4096>::new();
    buffer.read_from(&mut stream).await?;

    println!("读取 {} 字节", buffer.as_slice().len());

    Ok(())
}

/// 常量泛型分包器
pub struct PacketSplitter<const PACKET_SIZE: usize>;

impl<const PACKET_SIZE: usize> PacketSplitter<PACKET_SIZE> {
    pub fn split(data: &[u8]) -> Vec<[u8; PACKET_SIZE]> {
        data.chunks(PACKET_SIZE)
            .map(|chunk| {
                let mut packet = [0u8; PACKET_SIZE];
                packet[..chunk.len()].copy_from_slice(chunk);
                packet
            })
            .collect()
    }
}
```

---

## 6. 迭代器组合子增强

本节专门讨论「迭代器组合子增强」下的网络数据处理。

### 网络数据处理

```rust
use futures::stream::{StreamExt, TryStreamExt};

/// 迭代器链式处理（Rust 1.90优化）
pub async fn process_http_responses(
    urls: Vec<String>,
) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();

    let results = futures::stream::iter(urls)
        .map(|url| {
            let client = client.clone();
            async move {
                client.get(&url).send().await
            }
        })
        .buffered(10) // 并发10个请求
        .try_filter_map(|resp| async move {
            if resp.status().is_success() {
                Ok(Some(resp.text().await?))
            } else {
                Ok(None)
            }
        })
        .try_collect::<Vec<_>>()
        .await?;

    Ok(results)
}

/// 网络统计聚合
pub fn analyze_network_traffic<I>(packets: I) -> NetworkStats
where
    I: Iterator<Item = Packet>,
{
    packets
        .filter(|p| p.size > 0)
        .inspect(|p| println!("处理包: {}", p.id))
        .map(|p| p.size)
        .fold(NetworkStats::default(), |mut stats, size| {
            stats.total_bytes += size as u64;
            stats.packet_count += 1;
            stats
        })
}

#[derive(Default)]
pub struct NetworkStats {
    pub total_bytes: u64,
    pub packet_count: usize,
}

pub struct Packet {
    pub id: u64,
    pub size: usize,
}
```

---

## 7. 错误处理改进

1.90 周期的错误处理改进围绕**结构化错误与传播便捷性**：

1. **网络错误类型设计惯例**：`thiserror` 枚举按「错误来源层」组织变体（Io/Dns/Tls/Http/Timeout），`#[from]` 自动转换 + `#[error(transparent)]` 保持错误链——`std::error::Error::source` 链是生产可观测性的基础（`anyhow` 的 `chain()` 打印）。
2. **`let-else` 与早退**：网络代码大量「取不到就返回」模式（连接拒绝、解析失败），`let-else` 把卫语句压到一行，主路径保持左对齐。
3. **错误上下文化**：`anyhow::Context`（应用层）vs `thiserror`（库层）的分工不变——1.90 周期的改进主要在诊断侧（错误链打印格式、`Termination` trait 的退出码传播）。

判定依据：库 crate 错误类型必须 `Send + Sync + 'static`（`thiserror` 默认满足），否则无法跨 `.await` 传播。

### 网络错误类型

```rust
use std::error::Error;
use std::fmt;

/// 网络错误类型（Rust 1.90优化）
#[derive(Debug)]
pub enum NetworkError {
    Io(std::io::Error),
    Http(reqwest::Error),
    Timeout,
    InvalidAddress(String),
    ConnectionRefused,
    Custom(String),
}

impl fmt::Display for NetworkError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NetworkError::Io(e) => write!(f, "IO错误: {}", e),
            NetworkError::Http(e) => write!(f, "HTTP错误: {}", e),
            NetworkError::Timeout => write!(f, "连接超时"),
            NetworkError::InvalidAddress(addr) => write!(f, "无效地址: {}", addr),
            NetworkError::ConnectionRefused => write!(f, "连接被拒绝"),
            NetworkError::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

impl Error for NetworkError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            NetworkError::Io(e) => Some(e),
            NetworkError::Http(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for NetworkError {
    fn from(err: std::io::Error) -> Self {
        NetworkError::Io(err)
    }
}

impl From<reqwest::Error> for NetworkError {
    fn from(err: reqwest::Error) -> Self {
        NetworkError::Http(err)
    }
}

/// 错误处理示例
pub async fn fetch_with_error_handling(url: &str) -> Result<String, NetworkError> {
    let response = reqwest::get(url).await?;

    if !response.status().is_success() {
        return Err(NetworkError::Custom(format!("HTTP {}", response.status())));
    }

    let text = response.text().await?;
    Ok(text)
}
```

---

## 8. 网络专用特性应用

本节聚焦「网络专用特性应用」，核心内容为 Edition 2024 特性（1.85.0+ stable）。

### Edition 2024 特性（1.85.0+ stable）

```rust
// Edition 2024（1.85.0+ stable）: 改进的 async 块捕获
pub async fn edition_2024_example() {
    let client = reqwest::Client::new();
    let url = "https://example.com";

    // ✅ Edition 2024（1.85.0+ stable）: 自动最小捕获
    let future = async {
        client.get(url).send().await
    };

    // client和url按需捕获，而非整个环境
    let response = future.await;
}

// Edition 2024（1.85.0+ stable）: 改进的生命周期省略
pub async fn improved_lifetime_elision(data: &str) -> &str {
    // 自动推断生命周期
    data
}
```

---

## 9. 性能优化特性

「性能优化特性」部分的核心主题是零成本抽象，本节展开说明。

### 零成本抽象

Rust 1.90 继续强化零成本抽象（Zero-Cost Abstraction），使高层 API 在编译后接近手写底层代码的性能。

```rust
/// 内联优化（Rust 1.90改进）
#[inline(always)]
pub async fn inline_tcp_send(stream: &mut tokio::net::TcpStream, data: &[u8]) -> std::io::Result<()> {
    use tokio::io::AsyncWriteExt;
    stream.write_all(data).await
}

/// SIMD优化（Rust 1.90稳定）
#[cfg(target_arch = "x86_64")]
pub fn simd_checksum(data: &[u8]) -> u32 {
    use std::arch::x86_64::*;

    unsafe {
        let mut sum = _mm_setzero_si128();

        for chunk in data.chunks_exact(16) {
            let vec = _mm_loadu_si128(chunk.as_ptr() as *const __m128i);
            sum = _mm_add_epi32(sum, vec);
        }

        // 提取结果
        let mut result = [0u32; 4];
        _mm_storeu_si128(result.as_mut_ptr() as *mut __m128i, sum);

        result.iter().sum()
    }
}
```

---

## 10. 实战示例集

「实战示例集」部分包含完整HTTP客户端（Rust 1.90特性集成） 与  WebSocket服务器（完整特性） 两条主线，本节依次说明。

### 完整HTTP客户端（Rust 1.90特性集成）

```rust,ignore
use tokio::sync::Semaphore;
use std::sync::Arc;

/// 生产级HTTP客户端
pub struct ModernHttpClient {
    client: reqwest::Client,
    semaphore: Arc<Semaphore>,
}

impl ModernHttpClient {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(std::time::Duration::from_secs(30))
                .pool_max_idle_per_host(10)
                .build()
                .unwrap(),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    /// 并发获取多个URL（使用Rust 1.90特性）
    pub async fn fetch_all(&self, urls: Vec<String>) -> Vec<Result<String, NetworkError>> {
        use futures::stream::{StreamExt, FuturesUnordered};

        urls.into_iter()
            .map(|url| {
                let client = self.client.clone();
                let semaphore = self.semaphore.clone();

                async move {
                    let _permit = semaphore.acquire().await.unwrap();

                    let response = client.get(&url).send().await?;
                    let text = response.text().await?;

                    Ok(text)
                }
            })
            .collect::<FuturesUnordered<_>>()
            .collect::<Vec<_>>()
            .await
    }
}

/// 使用示例
pub async fn modern_client_example() {
    let client = ModernHttpClient::new(10);

    let urls = vec![
        "https://example.com".to_string(),
        "https://rust-lang.org".to_string(),
        "https://crates.io".to_string(),
    ];

    let results = client.fetch_all(urls).await;

    for (i, result) in results.iter().enumerate() {
        println!("URL {}: {:?}", i, result.as_ref().map(|s| s.len()));
    }
}
```

### WebSocket服务器（完整特性）

```rust
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};

/// 现代WebSocket服务器
pub async fn modern_websocket_server() -> std::io::Result<()> {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:9001").await?;

    println!("WebSocket服务器运行在 ws://127.0.0.1:9001");

    while let Ok((stream, addr)) = listener.accept().await {
        tokio::spawn(async move {
            // ✅ let-else处理错误
            let Ok(ws_stream) = accept_async(stream).await else {
                eprintln!("WebSocket握手失败: {}", addr);
                return;
            };

            let (mut write, mut read) = ws_stream.split();

            // ✅ 异步闭包
            while let Some(msg) = read.next().await {
                let Ok(msg) = msg else { break };

                match msg {
                    Message::Text(text) => {
                        println!("[{}] 文本: {}", addr, text);
                        let _ = write.send(Message::Text(format!("回显: {}", text))).await;
                    }
                    Message::Binary(data) => {
                        println!("[{}] 二进制: {} 字节", addr, data.len());
                        let _ = write.send(Message::Binary(data)).await;
                    }
                    Message::Close(_) => break,
                    _ => {}
                }
            }
        });
    }

    Ok(())
}
```

---

**文档完成**: 本参考涵盖了Rust 1.90在网络编程中的所有关键特性应用。

**下一步**: [04\_网络性能基准参考.md](/crates/c10_networks/docs/tier_03_references/04_network_performance_benchmarks_reference.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

> **向下引用（Reference）**: 参见 [01_toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

## 11. 版本事实对齐与权威来源（2026-07-12 回填）

> **背景**：本页迁移自 crate 文档，章节标题中的“1.90 新特性”多为**既有稳定特性在网络场景的应用**，并非 1.90 首次稳定。下表按官方发布说明逐项对齐真实稳定版本，避免读者误读版本边界。

| 本页章节 | 特性 | 真实稳定版本 | 权威来源 |
|:---|:---|:---:|:---|
| 1.1 异步 Trait 稳定化（RPITIT） | `impl Trait` in trait return position | 1.75.0（2023-12-28） | [Rust 1.75.0 Release Blog](https://blog.rust-lang.org/2023/12/28/Rust-1.75.0/) |
| 1.2 异步闭包 | `async \|\| {}` 闭包 | 1.85.0（2025-02-20，Edition 2024 同期） | [Rust 1.85.0 Release Blog](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/) |
| 2. GATs | 泛型关联类型 | 1.65.0（2022-11-03） | [Rust 1.65.0 Release Blog](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0/) |
| 3. let-else | `let ... else` 发散绑定 | 1.65.0 | 同上 |
| 5. 常量泛型 | `min_const_generics` | 1.51.0（2021-03-25） | [Rust 1.51.0 Release Blog](https://blog.rust-lang.org/2021/03/25/Rust-1.51.0/) |

**实测示例（RPITIT，rustc 1.97.0 `--edition 2024` 编译运行通过）**：

```rust
use std::future::Future;

trait Service {
    // RPITIT：trait 方法直接返回 impl Future（1.75 稳定）
    fn fetch(&self, n: u32) -> impl Future<Output = u32> + Send;
}

struct S;
impl Service for S {
    async fn fetch(&self, n: u32) -> u32 { n + 1 }
}

fn main() {
    let _f = S.fetch(41); // 返回的 Future 类型由实现者隐藏
}
```

> **权威来源**: [Rust 1.75.0 Release Blog](https://blog.rust-lang.org/2023/12/28/Rust-1.75.0/) · [Rust 1.85.0 Release Blog](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/) · [Rust 1.65.0 Release Blog](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0/) · [Rust 1.51.0 Release Blog](https://blog.rust-lang.org/2021/03/25/Rust-1.51.0/) · [Rust Release Notes](https://doc.rust-lang.org/releases.html)（链接 2026-07-12 curl 实测 200；代码 rustc 1.97.0 实测）
> 深度概念页：[RPITIT 预研](../03_preview_features/15_rpitit_preview.md) · [Async Closures](../../03_advanced/01_async/07_async_closures.md) · [GATs](../../02_intermediate/00_traits/07_generic_associated_types.md)

---

## 过渡段

> **过渡**: 从版本上下文过渡到特性概览，可以理解 1.90 在异步与类型系统（Type System）方面的重点改进。
>
> **过渡**: 从 RPITIT 与异步闭包（Closures）过渡到网络应用场景，可以评估这些特性对实际代码的影响。
>
> **过渡**: 从特性列表过渡到迁移建议，可以将版本更新转化为可执行的升级步骤。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 版本上下文 ⟹ 特性定位 | 了解 1.90 在 release train 中的位置 | 判断是否需要升级 |
| RPITIT 稳定 ⟹ 异步 trait 人体工学 | `impl Trait` 在 trait 中的返回类型 | 简化异步接口设计 |
| 特性迁移 ⟹ 渐进升级 | 评估影响面后逐步采用 | 降低版本切换风险 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Oxide: The Essence of Rust (arXiv:1903.00982)](https://arxiv.org/abs/1903.00982) · [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523704)
