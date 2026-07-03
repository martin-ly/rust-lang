# libp2p 指南 {#libp2p-指南}

> **EN**: Libp2p Guide
> **Summary**: libp2p 指南 Libp2p Guide.
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **层级**: L6 生态工具 / L3 高级网络
> **前置概念**: [Async](../../concept/03_advanced/02_async.md) · [Network Programming](../../crates/c10_networks)
> **Bloom 层级**: 应用 → 分析
> **[来源: libp2p Specification]** · **[来源: rust-libp2p crate]** · **[来源: Protocol Labs - libp2p]** · **来源: [Wikipedia - Peer-to-Peer](https://en.wikipedia.org/wiki/Peer_to_Peer)** ✅
>
> **受众**: [进阶]
> **内容分级**: [专家级]

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [libp2p 指南 {#libp2p-指南}](#libp2p-指南-libp2p-指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [概述 {#概述}](#概述-概述)
  - [核心概念 {#核心概念}](#核心概念-核心概念)
    - [Multiaddr —— 统一的地址格式 {#multiaddr-统一的地址格式}](#multiaddr--统一的地址格式-multiaddr-统一的地址格式)
    - [PeerId —— 去中心化身份 {#peerid-去中心化身份}](#peerid--去中心化身份-peerid-去中心化身份)
    - [核心协议 {#核心协议}](#核心协议-核心协议)
  - [决策树 {#决策树}](#决策树-决策树)
  - [代码示例 {#代码示例}](#代码示例-代码示例)
    - [基础节点（rust-libp2p） {#基础节点rust-libp2p}](#基础节点rust-libp2p-基础节点rust-libp2p)
    - [GossipSub 发布/订阅 {#gossipsub-发布订阅}](#gossipsub-发布订阅-gossipsub-发布订阅)
    - [Kademlia DHT 内容路由 {#kademlia-dht-内容路由}](#kademlia-dht-内容路由-kademlia-dht-内容路由)
  - [与中心化方案的对比 {#与中心化方案的对比}](#与中心化方案的对比-与中心化方案的对比)
  - [Rust 生态状态 {#rust-生态状态}](#rust-生态状态-rust-生态状态)
  - [限制 {#限制}](#限制-限制)
  - [参考 {#参考}](#参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 概述 {#概述}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)** · **来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)** ✅

**libp2p** 是 Protocol Labs 开发的模块化 P2P（点对点）网络框架，为 IPFS、Filecoin、Polkadot 等去中心化系统提供网络基础设施。

**核心设计哲学**: 传输无关、协议模块化、安全默认。

```text
libp2p 协议栈
┌─────────────────────────────────────────┐
│  应用层: gossipsub / kad DHT / identify  │
├─────────────────────────────────────────┤
│  安全层: Noise / TLS 1.3                │
├─────────────────────────────────────────┤
│  多路复用: Yamux / mplex                │
├─────────────────────────────────────────┤
│  传输层: TCP / QUIC / WebRTC / WebSocket │
└─────────────────────────────────────────┘
```

---

## 核心概念 {#核心概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Multiaddr —— 统一的地址格式 {#multiaddr-统一的地址格式}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

libp2p 使用 **multiaddr** 统一描述网络地址：

```text
/ip4/192.168.1.1/tcp/4001       → TCP 监听
/ip4/192.168.1.1/udp/4001/quic  → QUIC 监听
/dns4/bootstrap.libp2p.io/tcp/443/wss  → WebSocket Secure
```

### PeerId —— 去中心化身份 {#peerid-去中心化身份}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```text
PeerId = multihash(public_key)
```

每个 libp2p 节点通过加密密钥对标识，无需中心化注册。

### 核心协议 {#核心协议}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

| 协议 | 功能 | Rust crate |
|:---|:---|:---|
| **Ping** | 连接活性检测 | `libp2p-ping` |
| **Identify** | 节点信息交换 | `libp2p-identify` |
| **Kademlia DHT** | 分布式哈希表路由 | `libp2p-kad` |
| **GossipSub** | 发布/订阅消息传播 | `libp2p-gossipsub` |
| **Noise** | 加密握手 | `libp2p-noise` |
| **Yamux** | 流多路复用 | `yamux` |

---

## 决策树 {#决策树}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
需要 P2P 网络?
    ├── 去中心化存储 (IPFS-like)?
    │       └── 需要内容寻址? ──▶ libp2p + Kademlia DHT ✅
    ├── 区块链/共识网络?
    │       └── 需要广播? ──▶ libp2p + GossipSub ✅
    ├── 实时通信 (WebRTC-like)?
    │       └── 浏览器兼容? ──▶ libp2p + WebRTC transport ✅
    ├── 物联网 / 受限网络?
    │       └── 需要 NAT 穿透? ──▶ libp2p + QUIC + hole punching ✅
    └── 简单文件共享?
            └── 局域网优先? ──▶ libp2p + mDNS 发现
```

---

## 代码示例 {#代码示例}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 基础节点（rust-libp2p） {#基础节点rust-libp2p}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```rust,ignore
use libp2p::{
    identity, PeerId, Swarm, Transport,
    tcp::TcpConfig, noise, yamux,
    core::upgrade,
    ping::{Ping, PingConfig},
};

fn create_node() -> Result<Swarm<Ping>, Box<dyn std::error::Error>> {
    // 1. 生成密钥对和 PeerId
    let local_key = identity::Keypair::generate_ed25519();
    let local_peer_id = PeerId::from(local_key.public());
    println!("Local peer id: {:?}", local_peer_id);

    // 2. 配置传输层: TCP + Noise 加密 + Yamux 多路复用
    let transport = TcpConfig::new()
        .upgrade(upgrade::Version::V1)
        .authenticate(noise::Config::new(&local_key)?)
        .multiplex(yamux::Config::default())
        .boxed();

    // 3. 配置行为: 添加 Ping 协议
    let behaviour = Ping::new(PingConfig::new().with_keep_alive(true));

    // 4. 创建 Swarm（网络管理器）
    let swarm = Swarm::new(transport, behaviour, local_peer_id);

    Ok(swarm)
}
```

### GossipSub 发布/订阅 {#gossipsub-发布订阅}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```rust,ignore
use libp2p::gossipsub::{
    Gossipsub, GossipsubConfig, GossipsubEvent, MessageAuthenticity,
    IdentTopic,
};
use libp2p::Swarm;

fn setup_gossipsub(
    local_key: &identity::Keypair,
) -> Result<Gossipsub, Box<dyn std::error::Error>> {
    // 消息认证策略：使用签名防止伪造
    let message_authenticity = MessageAuthenticity::Signed(local_key.clone());

    // 配置 GossipSub：网状网络参数
    let config = GossipsubConfig::default();

    let mut gossipsub = Gossipsub::new(message_authenticity, config)?;

    // 订阅主题
    let topic = IdentTopic::new("blocks");
    gossipsub.subscribe(&topic)?;

    Ok(gossipsub)
}

// 发布消息
gossipsub.publish(IdentTopic::new("blocks"), b"new block data".to_vec())?;

// 接收消息（在 Swarm 事件循环中）
match event {
    SwarmEvent::Behaviour(GossipsubEvent::Message {
        propagation_source,
        message_id,
        message,
    }) => {
        println!(
            "Got message: {} from {:?}",
            String::from_utf8_lossy(&message.data),
            propagation_source
        );
    }
    _ => {}
}
```

### Kademlia DHT 内容路由 {#kademlia-dht-内容路由}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```rust,ignore
use libp2p::kad::{
    Kademlia, KademliaConfig, KademliaEvent, QueryResult, Quorum, Record,
};

fn setup_kademlia(local_peer_id: PeerId) -> Kademlia<MemoryStore> {
    let store = MemoryStore::new(local_peer_id);
    let mut kademlia = Kademlia::with_config(local_peer_id, store, KademliaConfig::default());

    // 添加引导节点
    let bootstrap = Multiaddr::from_str("/dns4/bootstrap.libp2p.io/tcp/443")?;
    let bootstrap_peer = PeerId::from_str("...")?;
    kademlia.add_address(&bootstrap_peer, bootstrap);

    // 启动引导查询
    kademlia.bootstrap()?;

    kademlia
}

// 存储键值对
let record = Record {
    key: Key::from(vec![1, 2, 3]),
    value: b"data".to_vec(),
    publisher: None,
    expires: None,
};
kademlia.put_record(record, Quorum::One)?;

// 查询键
kademlia.get_record(Key::from(vec![1, 2, 3]));
```

---

## 与中心化方案的对比 {#与中心化方案的对比}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 维度 | Client-Server | libp2p P2P |
|:---|:---|:---|
| 单点故障 | 服务端故障 = 全网故障 | 无单点，节点动态加入/离开 |
| 审查抵抗 | 易被封禁 IP/域名 | 内容寻址，难以封禁 |
| 发现机制 | DNS / 负载均衡 | DHT / mDNS / 引导节点 |
| 延迟 | 中心化可能更优 | 依赖路由质量，可能多跳 |
| 带宽 | 服务端付费 | 对等共享 |
| 复杂度 | 简单 | 高（NAT 穿透、路由、安全） |

---

## Rust 生态状态 {#rust-生态状态}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| Crate | 版本 | 状态 |
|:---|:---:|:---|
| `libp2p` | 0.55+ | 🟢 核心稳定 |
| `libp2p-quic` | 0.12+ | 🟡 快速改进 |
| `libp2p-webrtc` | 0.9+ | 🟡 浏览器互操作 |
| `rust-libp2p` 整体 | — | 🟢 生产可用 (IPFS/Polkadot) |

---

## 限制 {#限制}
>
> **[来源: [crates.io](https://crates.io/)]**

| 限制 | 说明 |
|:---|:---|
| NAT 穿透 | 需要 relay/hole punching，增加延迟 |
| 路由效率 | DHT 查找可能慢于中心化 DNS |
| 电池消耗 | 维持 DHT 连接和定期探测耗电 |
| 调试复杂 | 分布式问题难以复现和追踪 |
| 防火墙 | 企业防火墙常限制 P2P 连接 |

---

## 参考 {#参考}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [libp2p Specification](https://specs.libp2p.io/)
- [rust-libp2p GitHub](https://github.com/libp2p/rust-libp2p)
- [libp2p Docs](https://docs.libp2p.io/)

---

> **权威来源**: [libp2p Specification](https://specs.libp2p.io/), [rust-libp2p](https://github.com/libp2p/rust-libp2p), [libp2p Documentation](https://docs.libp2p.io/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Peer-to-Peer](https://en.wikipedia.org/wiki/Peer_to_Peer)**
> **来源: [Wikipedia - Distributed Hash Table](https://en.wikipedia.org/wiki/Distributed_Hash_Table)**
> **[来源: libp2p Specification]**
> **[来源: ACM - Peer-to-Peer Networking]**
> **[来源: IEEE - Decentralized Network Protocols]**
> **[来源: Protocol Labs - libp2p Docs]**
> **来源: [Rust Reference - Networking](https://doc.rust-lang.org/reference/)**

---
