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
                    providers,
                    ..
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
// 7. 应用模式
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
// 测试
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
