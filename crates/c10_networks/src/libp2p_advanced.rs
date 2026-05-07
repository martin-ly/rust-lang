//! libp2p 深度集成 —— 点对点网络协议栈
//!
//! # 概述
//!
//! libp2p 是一个模块化、可扩展的点对点（P2P）网络框架，
//! 由 Protocol Labs 开发，是 IPFS、Filecoin 等项目的基础网络层。
//!
//! # 核心模块
//!
//! | 模块 | 功能 | 协议实现 |
//! |------|------|---------|
//! | Transport | 底层传输 | TCP, QUIC, WebSocket, WebRTC |
//! | Noise | 加密握手 | Noise XX/IK 握手 |
//! | TLS | 备选加密 | TLS 1.3 + libp2p 扩展 |
//! | Yamux | 流多路复用 | Yamux / Mplex |
//! | Kademlia | DHT 路由 | Kademlia DHT |
//! | GossipSub | 消息发布订阅 | GossipSub v1.1 |
//! | Identify | 节点身份交换 | libp2p-identify |
//! | Ping | 连接保活 | libp2p-ping |
//!
//! # 依赖
//! 当前工作区已配置 `libp2p = { version = "0.54.1", features = [...] }`
//!
//! # 参考
//! - [libp2p 官方文档](https://docs.rs/libp2p)
//! - [libp2p 规范](https://github.com/libp2p/specs)

// =========================================================================
// 1. 节点身份与密钥管理
// =========================================================================

/// # libp2p 节点身份
///
/// 每个 libp2p 节点由 `PeerId` 唯一标识，它是节点公钥的哈希。
/// 支持 Ed25519、Secp256k1、RSA 等多种密钥类型。
pub mod identity {
    use libp2p::PeerId;
    use libp2p::identity::Keypair;

    /// 生成新的节点身份
    pub fn generate_identity() -> (Keypair, PeerId) {
        let keypair = Keypair::generate_ed25519();
        let peer_id = PeerId::from(keypair.public());
        (keypair, peer_id)
    }

    /// 从已有密钥恢复身份
    pub fn peer_id_from_public_key(public_key: &libp2p::identity::PublicKey) -> PeerId {
        PeerId::from(public_key.clone())
    }

    /// 序列化密钥对（用于持久化）
    pub fn serialize_keypair(keypair: &Keypair) -> Vec<u8> {
        keypair
            .to_protobuf_encoding()
            .expect("keypair serialization")
    }

    /// 反序列化密钥对
    pub fn deserialize_keypair(bytes: &[u8]) -> Result<Keypair, String> {
        Keypair::from_protobuf_encoding(bytes).map_err(|e| e.to_string())
    }
}

// =========================================================================
// 2. 传输层与网络构建
// =========================================================================

/// # Swarm 构建器
///
/// `Swarm` 是 libp2p 的核心结构，管理所有网络活动：
/// - 监听传入连接
/// - 拨号远程节点
/// - 运行协议行为（behaviour）
pub mod swarm_builder {
    use libp2p::{Swarm, SwarmBuilder, noise, tcp, yamux};
    use std::time::Duration;

    /// 构建基础 TCP + Noise + Yamux Swarm
    ///
    /// 这是最常见的 libp2p 网络配置。
    pub fn build_tcp_swarm<B>(
        keypair: &libp2p::identity::Keypair,
        behaviour: B,
    ) -> Result<Swarm<B>, String>
    where
        B: libp2p::swarm::NetworkBehaviour,
    {
        let swarm = SwarmBuilder::with_existing_identity(keypair.clone())
            .with_tokio()
            .with_tcp(
                tcp::Config::default(),
                noise::Config::new,
                yamux::Config::default,
            )
            .map_err(|e| e.to_string())?
            .with_behaviour(|_| behaviour)
            .map_err(|e| e.to_string())?
            .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(60)))
            .build();

        Ok(swarm)
    }

    // 构建内存传输 Swarm（测试用）
    //
    // # 注意
    // libp2p 0.54.1 中 `MemoryTransport` 需经过 upgrade + authenticate + multiplex
    // 才能满足 `Transport<Output = (PeerId, Muxer)>` 约束。教学代码中推荐使用
    // `build_tcp_swarm` 配合回环地址 (`/ip4/127.0.0.1/tcp/0`) 进行本地测试。
}

// =========================================================================
// 3. Kademlia DHT
// =========================================================================

/// # Kademlia 分布式哈希表
///
/// Kademlia 是 libp2p 的核心路由协议，提供：
/// - 节点发现（Peer Discovery）
/// - 内容路由（Content Routing）
/// - 记录存储（Record Store）
pub mod dht {
    use libp2p::kad::store::MemoryStore;
    use libp2p::kad::{
        Behaviour as KademliaBehaviour, Config as KademliaConfig, Event as KademliaEvent,
        GetProvidersOk, GetRecordOk, QueryResult,
    };
    use libp2p::{Multiaddr, StreamProtocol};

    /// 创建 Kademlia 行为
    pub fn create_kademlia_behaviour(
        local_peer_id: libp2p::PeerId,
    ) -> KademliaBehaviour<MemoryStore> {
        let store = MemoryStore::new(local_peer_id);
        let config = KademliaConfig::new(StreamProtocol::new("/ipfs/kad/1.0.0"));
        KademliaBehaviour::with_config(local_peer_id, store, config)
    }

    /// 处理 Kademlia 事件的概念框架
    pub fn handle_kademlia_event(event: KademliaEvent) {
        match event {
            KademliaEvent::OutboundQueryProgressed { result, .. } => match result {
                QueryResult::GetProviders(Ok(GetProvidersOk::FoundProviders {
                    providers, ..
                })) => {
                    println!("找到 {} 个提供者", providers.len());
                }
                QueryResult::GetRecord(Ok(GetRecordOk::FoundRecord(peer_record))) => {
                    println!("记录找到: {:?}", peer_record.record.key);
                }
                QueryResult::PutRecord(Ok(ok)) => {
                    println!("记录已存储: {:?}", ok.key);
                }
                QueryResult::Bootstrap(Ok(ok)) => {
                    println!("引导完成，peer: {:?}", ok.peer);
                }
                _ => {}
            },
            KademliaEvent::RoutingUpdated {
                peer, is_new_peer, ..
            } => {
                println!("路由表更新: peer={}, new={}", peer, is_new_peer);
            }
            _ => {}
        }
    }

    /// 引导节点配置（Bootstrap Nodes）
    pub struct BootstrapConfig {
        pub peers: Vec<(libp2p::PeerId, Multiaddr)>,
    }

    impl BootstrapConfig {
        /// IPFS 公共引导节点（概念性）
        pub fn ipfs_defaults() -> Self {
            Self { peers: vec![] }
        }
    }
}

// =========================================================================
// 4. GossipSub 发布订阅
// =========================================================================

/// # GossipSub 消息网络
///
/// GossipSub 是 libp2p 的可扩展发布订阅协议，
/// 结合了 mesh 网络（用于低延迟）和 gossip 传播（用于可靠性）。
pub mod pubsub {
    use libp2p::gossipsub::{
        Behaviour as GossipsubBehaviour, Config as GossipsubConfig, Event as GossipsubEvent,
        MessageAuthenticity,
    };
    use libp2p::identity::Keypair;

    /// 创建 GossipSub 行为
    pub fn create_gossipsub_behaviour(keypair: &Keypair) -> Result<GossipsubBehaviour, String> {
        let message_authenticity = MessageAuthenticity::Signed(keypair.clone());
        let config = GossipsubConfig::default();

        GossipsubBehaviour::new(message_authenticity, config)
            .map_err(|e| format!("gossipsub init: {}", e))
    }

    /// 创建带验证策略的 GossipSub
    ///
    /// libp2p 0.54.1 中 `GossipsubConfig` 默认即为 `ValidationMode::Strict`，
    /// 如需自定义需使用 `ConfigBuilder`。
    pub fn create_validated_gossipsub(keypair: &Keypair) -> Result<GossipsubBehaviour, String> {
        create_gossipsub_behaviour(keypair)
    }

    /// 处理 GossipSub 事件
    pub fn handle_gossipsub_event(event: GossipsubEvent) {
        match event {
            GossipsubEvent::Message {
                propagation_source,
                message_id,
                message,
            } => {
                println!(
                    "收到消息 [{}] 来自 {}: {} bytes",
                    message_id,
                    propagation_source,
                    message.data.len()
                );
            }
            GossipsubEvent::Subscribed { peer_id, topic } => {
                println!("Peer {} 订阅了 topic: {}", peer_id, topic);
            }
            GossipsubEvent::Unsubscribed { peer_id, topic } => {
                println!("Peer {} 取消订阅 topic: {}", peer_id, topic);
            }
            _ => {}
        }
    }

    /// 主题命名最佳实践
    pub fn topic_name(application: &str, version: &str, network: &str) -> String {
        format!("/{}/{}/{}", application, version, network)
    }
}

// =========================================================================
// 5. 综合 Behaviour 组合
// =========================================================================

/// # 组合 Behaviour
///
/// 实际 libp2p 节点通常组合多个协议行为。
/// 使用 `libp2p::swarm::NetworkBehaviour` derive macro 组合。
use libp2p::swarm::NetworkBehaviour;
use libp2p::{gossipsub, identify, kad, ping};

/// 完整的 P2P 节点行为
#[derive(NetworkBehaviour)]
pub struct FullNodeBehaviour {
    pub kademlia: kad::Behaviour<kad::store::MemoryStore>,
    pub gossipsub: gossipsub::Behaviour,
    pub identify: identify::Behaviour,
    pub ping: ping::Behaviour,
}

impl FullNodeBehaviour {
    pub fn new(
        keypair: &libp2p::identity::Keypair,
        local_peer_id: libp2p::PeerId,
    ) -> Result<Self, String> {
        let kademlia =
            kad::Behaviour::new(local_peer_id, kad::store::MemoryStore::new(local_peer_id));

        let gossipsub = gossipsub::Behaviour::new(
            gossipsub::MessageAuthenticity::Signed(keypair.clone()),
            gossipsub::Config::default(),
        )
        .map_err(|e| e.to_string())?;

        let identify = identify::Behaviour::new(identify::Config::new(
            "/ipfs/0.1.0".to_string(),
            keypair.public(),
        ));

        let ping = ping::Behaviour::default();

        Ok(Self {
            kademlia,
            gossipsub,
            identify,
            ping,
        })
    }
}

// =========================================================================
// 6. NAT 穿透与网络发现
// =========================================================================

/// # NAT 穿透策略
///
/// libp2p 提供多种 NAT 穿透机制：
/// - **AutoNAT**: 自动检测节点是否可被公网访问
/// - **DCUtR (Direct Connection Upgrade through Relay)**: 通过中继建立直连
/// - **UPnP/NAT-PMP**: 自动端口映射
/// - **Circuit Relay v2**: 中继转发
pub mod nat_traversal {
    /// NAT 类型枚举
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum NatType {
        Public,         // 公网 IP
        FullCone,       // 完全锥形 NAT
        RestrictedCone, // 受限锥形 NAT
        PortRestricted, // 端口受限锥形 NAT
        Symmetric,      // 对称 NAT（最难穿透）
        Unknown,
    }

    /// 穿透策略决策树
    pub fn select_traversal_strategy(nat_type: NatType, has_relay: bool) -> &'static str {
        match (nat_type, has_relay) {
            (NatType::Public, _) => "直接监听公网地址",
            (NatType::FullCone, _) => "直接拨号（预测映射）",
            (NatType::RestrictedCone, true) => "DCUtR 通过 Relay 建立直连",
            (NatType::PortRestricted, true) => "DCUtR + 端口预测",
            (NatType::Symmetric, true) => "长期 Relay 转发（无法直连）",
            (NatType::Unknown, true) => "尝试 DCUtR，若失败则使用 Relay",
            (_, false) => "需要部署 Relay 服务器",
        }
    }
}

// =========================================================================
// 7. Relay 协议
// =========================================================================

/// # Relay 中继协议（Circuit Relay v2）
///
/// 当两个节点均位于 NAT 后方且无法直接建立连接时，可通过 publicly reachable 的
/// **Relay 节点**转发流量，实现 NAT 穿透。
///
/// ## 核心概念
/// - **Reservation**: 客户端向 Relay Server 申请预留一个中继槽位，使得其他节点
///   可以通过该 Relay 与自己建立 circuit。
/// - **Circuit**: 经过 Relay 转发的虚拟连接。Relay Server 负责将来自源节点的数据
///   转发给目标节点。
///
/// ## 角色划分
/// - `Relay Server`: 接受 reservation、转发 circuit 流量。
/// - `Relay Client`: 申请 reservation 并监听通过 Relay 到达的连接，
///   或主动通过 Relay 拨号其他节点。
///
/// ## 与 DCUtR 的协作
/// Relay 通常是 DCUtR 的前置步骤：先通过 Relay 建立 relayed 连接，
/// 再尝试升级为直连（hole punching）。
pub mod relay {
    use libp2p::relay::{Behaviour as RelayBehaviour, Config as RelayConfig, Event as RelayEvent};

    /// 创建 Relay Server 行为（使用默认配置）
    ///
    /// 默认配置包含针对 reservation 和 circuit 的速率限制，
    /// 适合大多数公开中继节点的场景。
    pub fn create_relay_behaviour(local_peer_id: libp2p::PeerId) -> RelayBehaviour {
        let config = RelayConfig::default();
        RelayBehaviour::new(local_peer_id, config)
    }

    /// 处理 Relay 事件的概念框架
    ///
    /// 实际生产环境中应将这些事件接入 tracing/metrics 系统，
    /// 而非直接打印到标准输出。
    pub fn handle_relay_event(event: RelayEvent) {
        match event {
            RelayEvent::ReservationReqAccepted {
                src_peer_id,
                renewed,
            } => {
                println!(
                    "Relay: 接受来自 {} 的 reservation 请求 (renewed={})",
                    src_peer_id, renewed
                );
            }
            RelayEvent::ReservationReqDenied { src_peer_id } => {
                println!("Relay: 拒绝来自 {} 的 reservation 请求", src_peer_id);
            }
            RelayEvent::ReservationTimedOut { src_peer_id } => {
                println!("Relay: 来自 {} 的 reservation 已超时", src_peer_id);
            }
            RelayEvent::CircuitReqAccepted {
                src_peer_id,
                dst_peer_id,
            } => {
                println!(
                    "Relay: 接受 circuit 请求 {} -> {}",
                    src_peer_id, dst_peer_id
                );
            }
            RelayEvent::CircuitReqDenied {
                src_peer_id,
                dst_peer_id,
            } => {
                println!(
                    "Relay: 拒绝 circuit 请求 {} -> {}",
                    src_peer_id, dst_peer_id
                );
            }
            _ => {
                // 包含已废弃或内部事件，可在日志中忽略
            }
        }
    }

    /// 概念：将 Relay 集成到组合 Behaviour
    ///
    /// 在实际项目中，可通过 `#[derive(NetworkBehaviour)]` 将 `relay::Behaviour`
    /// 与其他协议行为组合在一起：
    ///
    /// ```ignore
    /// #[derive(libp2p::swarm::NetworkBehaviour)]
    /// pub struct RelayEnabledBehaviour {
    ///     pub relay: libp2p::relay::Behaviour,
    ///     pub identify: libp2p::identify::Behaviour,
    ///     pub ping: libp2p::ping::Behaviour,
    ///     // ... 其他 behaviour
    /// }
    /// ```
    pub struct RelayIntegrationConcept;
}

// =========================================================================
// 8. AutoNAT
// =========================================================================

/// # AutoNAT 自动 NAT 检测
///
/// AutoNAT 让节点能够自动探测自身是否处于公网可访问状态，
/// 无需手动配置或依赖外部 STUN 服务。
///
/// ## 工作原理
/// 1. 节点向已连接的 peers（或指定的 probe servers）发送 dial-back 请求。
/// 2. 对方尝试回连本节点公布的监听地址。
/// 3. 根据回连结果，节点状态在 `Public`、`Private`、`Unknown` 之间切换。
///
/// ## 应用场景
/// - 动态决定是否需要寻找 Relay 节点（`Private` 时启用 Relay Client）。
/// - 为 DCUtR 决策提供依据（`Public` 或 `FullCone` 时更容易打洞成功）。
/// - 在监控面板中展示节点的网络可达性。
pub mod autonat {
    use libp2p::autonat::{
        Behaviour as AutonatBehaviour, Config as AutonatConfig, Event as AutonatEvent, NatStatus,
    };

    /// 创建 AutoNAT 行为（使用默认配置）
    ///
    /// 默认配置下，AutoNAT 会在启动 15 秒后发起首次探测，
    /// 并在状态变化时通过事件通知调用方。
    pub fn create_autonat_behaviour(local_peer_id: libp2p::PeerId) -> AutonatBehaviour {
        let config = AutonatConfig::default();
        AutonatBehaviour::new(local_peer_id, config)
    }

    /// 处理 AutoNAT 事件
    ///
    /// `StatusChanged` 是最关键的事件，直接决定节点的 NAT 策略。
    pub fn handle_autonat_event(event: AutonatEvent) {
        match event {
            AutonatEvent::StatusChanged { old, new } => {
                println!("AutoNAT: 状态变更 {:?} -> {:?}", old, new);
                match new {
                    NatStatus::Public(addr) => {
                        println!("AutoNAT: 公网可达，地址 {}", addr);
                    }
                    NatStatus::Private => {
                        println!("AutoNAT: 位于 NAT 后方，建议启用 Relay");
                    }
                    NatStatus::Unknown => {
                        println!("AutoNAT: 探测不足，状态未知");
                    }
                }
            }
            AutonatEvent::OutboundProbe(event) => {
                println!("AutoNAT: 出站探测事件 {:?}", event);
            }
            AutonatEvent::InboundProbe(event) => {
                println!("AutoNAT: 入站探测事件 {:?}", event);
            }
        }
    }

    /// 概念：在 `SwarmBuilder` 中使用 AutoNAT
    ///
    /// ```ignore
    /// let behaviour = FullNodeBehaviour {
    ///     autonat: autonat::create_autonat_behaviour(local_peer_id),
    ///     // ... 其他 behaviour
    /// };
    /// let swarm = swarm_builder::build_tcp_swarm(&keypair, behaviour).unwrap();
    /// ```
    pub struct AutonatIntegrationConcept;
}

// =========================================================================
// 9. DCUtR 直连升级
// =========================================================================

/// # DCUtR (Direct Connection Upgrade through Relay)
///
/// DCUtR 协议用于将已有的 relayed 连接升级为直连（hole punching）。
/// 当两个节点通过 Relay 初次握手后，双方同时向对方已观察到的地址发起拨号，
/// 利用 NAT 的端口映射机制尝试“打洞”，从而建立一条不经过中继的直接路径。
///
/// ## 前提条件
/// 1. 双方已通过 Relay 建立连接（至少一方持有有效的 reservation）。
/// 2. 至少有一方能够发起出站连接（或双方均为锥形 NAT）。
/// 3. 已启用 `identify` 协议，以便交换 observed addresses。
///
/// ## 与 Relay 的协同
/// DCUtR 本身不建立连接，而是依赖 Relay 提供的初始连接通道。
/// 成功升级后，应用层应优先使用新的直连，并可选择关闭 relayed 连接。
pub mod dcutr {
    use libp2p::dcutr::{Behaviour as DcutrBehaviour, Event as DcutrEvent};

    /// 创建 DCUtR 行为
    ///
    /// DCUtR 行为维护已知的直连与 relayed 连接映射，
    /// 并在适当时机自动发起 hole punching 尝试。
    pub fn create_dcutr_behaviour(local_peer_id: libp2p::PeerId) -> DcutrBehaviour {
        DcutrBehaviour::new(local_peer_id)
    }

    /// 处理 DCUtR 事件
    ///
    /// 成功升级后，`ConnectionId` 可用于在 `Swarm` 事件循环中识别新直连。
    pub fn handle_dcutr_event(event: DcutrEvent) {
        match event.result {
            Ok(connection_id) => {
                println!(
                    "DCUtR: 与 {} 的直连升级成功，连接 ID {:?}",
                    event.remote_peer_id, connection_id
                );
            }
            Err(ref e) => {
                println!(
                    "DCUtR: 与 {} 的直连升级失败: {}",
                    event.remote_peer_id, e
                );
            }
        }
    }

    /// 概念：DCUtR 与 Relay 协同工作的组合 Behaviour
    ///
    /// ```ignore
    /// #[derive(libp2p::swarm::NetworkBehaviour)]
    /// pub struct HolePunchBehaviour {
    ///     pub relay: libp2p::relay::Behaviour,
    ///     pub dcutr: libp2p::dcutr::Behaviour,
    ///     pub identify: libp2p::identify::Behaviour,
    /// }
    ///
    /// // 1. 通过 Relay 发现对方并建立 relayed 连接
    /// // 2. identify 交换 observed addresses
    /// // 3. DCUtR 自动触发 hole punching
    /// // 4. 成功后 Swarm 产生 ConnectionEstablished 事件（新直连）
    /// ```
    pub struct DcutrIntegrationConcept;
}

// =========================================================================
// 10. 应用模式
// =========================================================================

/// # libp2p 应用模式
///
/// 展示了 libp2p 在不同场景下的架构模式。
pub mod patterns {
    /// 模式 1：去中心化消息应用
    pub struct DecentralizedChat {
        pub topic: String,
        pub relay_peers: Vec<String>,
    }

    /// 模式 2：内容分发网络（CDN）
    pub struct P2pCdn {
        pub content_hash: String,
        pub replication_factor: usize,
    }

    /// 模式 3：区块链网络
    pub struct BlockchainNetwork {
        pub genesis_peers: Vec<String>,
        pub consensus_topic: String,
    }

    /// 模式 4：IoT 设备网络
    pub struct IotMesh {
        pub device_type: String,
        pub heartbeat_interval: std::time::Duration,
    }
}

// =========================================================================
// 11. 测试
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_identity() {
        let (keypair, peer_id) = identity::generate_identity();
        assert_eq!(peer_id, libp2p::PeerId::from(keypair.public()));
    }

    #[test]
    fn test_keypair_serialization() {
        let (keypair, _) = identity::generate_identity();
        let bytes = identity::serialize_keypair(&keypair);
        let restored = identity::deserialize_keypair(&bytes).unwrap();
        assert_eq!(
            libp2p::PeerId::from(keypair.public()),
            libp2p::PeerId::from(restored.public())
        );
    }

    #[test]
    fn test_nat_traversal_strategy() {
        assert_eq!(
            nat_traversal::select_traversal_strategy(nat_traversal::NatType::Public, false),
            "直接监听公网地址"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(nat_traversal::NatType::Symmetric, true),
            "长期 Relay 转发（无法直连）"
        );
    }

    #[test]
    fn test_topic_name() {
        let topic = pubsub::topic_name("myapp", "v1", "mainnet");
        assert_eq!(topic, "/myapp/v1/mainnet");
    }
}

