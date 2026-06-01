//! Libp2p Advanced

#![forbid(unsafe_code)]

//! libp2p 深度集成 —— 点对点网络协议栈
//! libp2p —— point to point network protocol stack
//! libp2p 深度集成 —— pointtopointnetwork protocolstack
//! # 概述
//! #
//! # 核心模块
//! # core module
//! | 模块 | 功能 | 协议实现 |
//! | module | functionality | |
//! | module | functionality | 协议Implementation of |
//! | Noise | 加密握手 | Noise XX/IK 握手 |
//! | TLS | 备选加密 | TLS 1.3 + libp2p 扩展 |
//! | TLS | | TLS 1.3 + libp2p |
//! | TLS | 备选Encrypt | TLS 1.3 + libp2p 扩展 |
//! | Yamux | 流多路复用 | Yamux / Mplex |
//! | Kademlia | DHT 路由 | Kademlia DHT |
//! | Identify | 节点身份交换 | libp2p-identify |
//! | Ping | 连接保活 | libp2p-ping |
//! # 依赖
//! #
//! 当前工作区已配置 `libp2p = { version = "0.54.1", features = [...] }`
//! # 参考
//! # reference
//! - [libp2p 官方文档](https://docs.rs/libp2p)
//! - [libp2p 规范](https://github.com/libp2p/specs)

// =========================================================================
// 1. 节点身份与密钥管理
// =========================================================================

/// # libp2p 节点身份
/// # libp2p node
/// 支持 Ed25519、Secp256k1、RSA 等多种密钥类型。
/// Ed25519、Secp256k1、RSA etc. type 。
/// Supports Ed25519、Secp256k1、RSA etc.多种密钥type。
pub mod identity {
    use libp2p::PeerId;
    use libp2p::identity::Keypair;

    /// 生成新的节点身份
    /// node
    pub fn generate_identity() -> (Keypair, PeerId) {
        let keypair = Keypair::generate_ed25519();
        let peer_id = PeerId::from(keypair.public());
        (keypair, peer_id)
    }

    /// 从已有密钥恢复身份
    /// from
    pub fn peer_id_from_public_key(public_key: &libp2p::identity::PublicKey) -> PeerId {
        PeerId::from(public_key.clone())
    }

    /// 序列化密钥对（用于持久化）
    /// sequence key pair （）
    /// sequence to （）
    pub fn serialize_keypair(keypair: &Keypair) -> Vec<u8> {
        keypair
            .to_protobuf_encoding()
            .expect("keypair serialization")
    }

    /// 反序列化密钥对
    /// sequence key pair
    /// sequence to
    pub fn deserialize_keypair(bytes: &[u8]) -> Result<Keypair, String> {
        Keypair::from_protobuf_encoding(bytes).map_err(|e| e.to_string())
    }
}

// =========================================================================
// 2. 传输层与网络构建
// =========================================================================

/// # Swarm 构建器
/// # Swarm builder
/// - 监听传入连接
/// -
/// - 拨号远程节点
/// - node
/// - Run协议行as（behaviour）
pub mod swarm_builder {
    use libp2p::{Swarm, SwarmBuilder, noise, tcp, yamux};
    use std::time::Duration;

    /// 构建基础 TCP + Noise + Yamux Swarm
    /// 构建basis TCP + Noise + Yamux Swarm
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

    /// 构建内存传输 Swarm（测试用）
    /// memory transmission Swarm（）
    /// # 注意
    /// #
    /// `build_tcp_swarm` 配合回环地址 (`/ip4/127.0.0.1/tcp/0`) 进行本地测试。
    /// `build_tcp_swarm` loopback address (`/ip4/127.0.0.1/tcp/0`) this 。
    pub fn build_memory_swarm<B>(
        _keypair: &libp2p::identity::Keypair,
        _behaviour: B,
    ) -> Result<libp2p::Swarm<B>, String>
    where
        B: libp2p::swarm::NetworkBehaviour,
    {
        Err(
            "MemoryTransport 在 libp2p 0.54.1 中需显式 upgrade + authenticate + multiplex \
             才能满足 Transport 约束，教学代码推荐使用 build_tcp_swarm 配合回环地址进行本地测试"
                .to_string(),
        )
    }
}

// =========================================================================
// 3. Kademlia DHT
// =========================================================================

/// # Kademlia 分布式哈希表
/// # Kademlia distribution hash table
/// # Kademlia distribution
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

    /// Create Kademlia 行as
    pub fn create_kademlia_behaviour(
        local_peer_id: libp2p::PeerId,
    ) -> KademliaBehaviour<MemoryStore> {
        let store = MemoryStore::new(local_peer_id);
        let config = KademliaConfig::new(StreamProtocol::new("/ipfs/kad/1.0.0"));
        KademliaBehaviour::with_config(local_peer_id, store, config)
    }

    /// Handle Kademlia 事件conceptframework
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
        /// IP FS node （concept ）
        pub fn ipfs_defaults() -> Self {
            Self { peers: vec![] }
        }
    }
}

// =========================================================================
// 4. GossipSub 发布订阅
// =========================================================================

pub mod pubsub {
    use libp2p::gossipsub::{
        Behaviour as GossipsubBehaviour, Config as GossipsubConfig, Event as GossipsubEvent,
        MessageAuthenticity,
    };
    use libp2p::identity::Keypair;

    pub fn create_gossipsub_behaviour(keypair: &Keypair) -> Result<GossipsubBehaviour, String> {
        let message_authenticity = MessageAuthenticity::Signed(keypair.clone());
        let config = GossipsubConfig::default();

        GossipsubBehaviour::new(message_authenticity, config)
            .map_err(|e| format!("gossipsub init: {}", e))
    }

    pub fn create_validated_gossipsub(keypair: &Keypair) -> Result<GossipsubBehaviour, String> {
        create_gossipsub_behaviour(keypair)
    }

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
    /// best practice
    pub fn topic_name(application: &str, version: &str, network: &str) -> String {
        format!("/{}/{}/{}", application, version, network)
    }
}

// =========================================================================
// 5. 综合 Behaviour 组合
// =========================================================================

/// # 组合 Behaviour
use libp2p::swarm::NetworkBehaviour;
use libp2p::{gossipsub, identify, kad, ping};

/// 完整的 P2P 节点行为
/// complete P2P node as
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
/// # NAT strategy
/// # NAT 穿透strategy
/// libp2p 提供多种 NAT 穿透机制：
/// libp2p NAT mechanism ：
/// - **Circuit Relay v2**: 中继转发
/// - **Circuit Relay v2**: in继转发
pub mod nat_traversal {
    /// NAT 类型枚举
    /// NAT type enum
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
    /// strategy tree
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
/// # Relay in继协议（Circuit Relay v2）
/// **Relay 节点**转发流量，实现 NAT 穿透。
/// **Relay node **flow rate ， NAT 。
/// **Relay node**转发flow rate，Implementation of NAT 穿透。
/// ## 核心概念
/// ## core concept
/// - **Reservation**: 客户端向 Relay Server 申请预留一个中继槽位，使得其他节点
/// - **Reservation**: Relay Server in ，its node
///   转发给目标节点。
///   goal node 。
///   转发给goalnode。
/// ## 角色划分
/// ##
/// - `Relay Server`: 接受 reservation、转发 circuit 流量。
/// - `Relay Server`: Accept reservation、转发 circuit flow rate。
///   或主动通过 Relay 拨号其他节点。
///   or Relay its node 。
/// 再尝试升级as直连（hole punching）。
/// as（hole punching）。
pub mod relay {
    use libp2p::relay::{Behaviour as RelayBehaviour, Config as RelayConfig, Event as RelayEvent};

    /// Create Relay Server 行as（Use默认Configure）
    /// 适合大多数公开中继节点的场景。
    /// in node scenario 。
    pub fn create_relay_behaviour(local_peer_id: libp2p::PeerId) -> RelayBehaviour {
        let config = RelayConfig::default();
        RelayBehaviour::new(local_peer_id, config)
    }

    /// Handle Relay 事件conceptframework
    /// 而非直接打印到标准输出。
    /// while to standard output 。
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
            RelayEvent::ReservationReqDenied { src_peer_id, .. } => {
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
                ..
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

    /// concept：will Relay 集成tocombination Behaviour
    /// 与其他协议行为组合在一起：
    /// rather than as combination in ：
    /// #[derive(libp2p::swarm::NetworkBehaviour)]
    /// pub struct RelayEnabledBehaviour {
    ///     pub relay: libp2p::relay::Behaviour,
    ///     pub identify: libp2p::identify::Behaviour,
    ///     pub ping: libp2p::ping::Behaviour,
    ///     // ... 其他 behaviour
    pub struct RelayIntegrationConcept;
}

// =========================================================================
// 8. AutoNAT
// =========================================================================

/// 无需手动配置或依赖外部 STUN 服务。
/// configuration or outside STUN 。
/// or outside STUN 。
/// ## 工作原理
/// ##
/// 2. 对方尝试回连本节点公布的监听地址。
/// 2. to this node 。
/// 3. 根据回连结果，节点状态在 `Public`、`Private`、`Unknown` 之间切换。
/// 3. according to result ，node state in `Public`、`Private`、`Unknown` 's switching 。
/// ## 应用场景
/// ## application scenario
/// - 在监控面板中展示节点的网络可达性。
/// - in surface in node network 。
pub mod autonat {
    use libp2p::autonat::{
        Behaviour as AutonatBehaviour, Config as AutonatConfig, Event as AutonatEvent, NatStatus,
    };

    /// 并在状态变化时通过事件通知调用方。
    /// and in state event notify 。
    /// and in state 。
    pub fn create_autonat_behaviour(local_peer_id: libp2p::PeerId) -> AutonatBehaviour {
        let config = AutonatConfig::default();
        AutonatBehaviour::new(local_peer_id, config)
    }

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

    /// ```ignore
    /// let behaviour = FullNodeBehaviour {
    ///     autonat: autonat::create_autonat_behaviour(local_peer_id),
    ///     // ... 其他 behaviour
    /// ```
    pub struct AutonatIntegrationConcept;
}

// =========================================================================
// 9. DCUtR 直连升级
// =========================================================================

/// # DCUtR (Direct Connection Upgrade through Relay)
///
/// 利用 NAT 的端口映射机制尝试“打洞”，从而建立一条不经过中继的直接路径。
/// NAT mechanism “”，thereby in 。
/// ## 前提条件
/// ## prerequisite condition
/// 1. 双方已Via Relay 建立Connect（至少一方持有effective reservation）。
/// 2. 至少有一方能够发起出站连接（或双方均为锥形 NAT）。
/// 2. can （or as NAT ）。
/// 3. 已启用 `identify` 协议，以便交换 observed addresses。
/// 3. 已启用 `identify` 协议，以便exchange observed addresses。
/// ## and Relay 协同
pub mod dcutr {
    use libp2p::dcutr::{Behaviour as DcutrBehaviour, Event as DcutrEvent};

    /// 并在适当时机自动发起 hole punching 尝试。
    /// and in when hole punching 。
    pub fn create_dcutr_behaviour(local_peer_id: libp2p::PeerId) -> DcutrBehaviour {
        DcutrBehaviour::new(local_peer_id)
    }

    pub fn handle_dcutr_event(event: DcutrEvent) {
        match event.result {
            Ok(connection_id) => {
                println!(
                    "DCUtR: 与 {} 的直连升级成功，连接 ID {:?}",
                    event.remote_peer_id, connection_id
                );
            }
            Err(ref e) => {
                println!("DCUtR: 与 {} 的直连升级失败: {}", event.remote_peer_id, e);
            }
        }
    }

    /// #[derive(libp2p::swarm::NetworkBehaviour)]
    /// pub struct HolePunchBehaviour {
    ///     pub relay: libp2p::relay::Behaviour,
    ///     pub dcutr: libp2p::dcutr::Behaviour,
    ///     pub identify: libp2p::identify::Behaviour,
    /// }
    ///
    /// // 1. 通过 Relay 发现对方并建立 relayed 连接
    /// // 1. Relay to and relayed
    /// // 2. identify 交换 observed addresses
    pub struct DcutrIntegrationConcept;
}

// =========================================================================
// 10. 应用模式
// =========================================================================

/// # libp2p 应用模式
/// # libp2p application
pub mod patterns {
    /// 模式 1：去中心化消息应用
    /// 1：center message application
    /// 1：center application
    pub struct DecentralizedChat {
        pub topic: String,
        pub relay_peers: Vec<String>,
    }

    /// 模式 2：内容分发网络（CDN）
    /// 2：CDN （CDN）
    /// 模式 2：CDN（CDN）
    pub struct P2pCdn {
        pub content_hash: String,
        pub replication_factor: usize,
    }

    /// 模式 3：区块链网络
    /// 3：blockchain network
    /// 3：network
    pub struct BlockchainNetwork {
        pub genesis_peers: Vec<String>,
        pub consensus_topic: String,
    }

    /// 模式 4：IoT 设备网络
    /// 4：IoT network
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

    /// 测试密钥对的序列化与反序列化往返
    /// key pair sequence and sequence
    /// to sequence and sequence
    #[test]
    fn test_keypair_serialization() {
        let (keypair, _) = identity::generate_identity();
        let bytes = identity::serialize_keypair(&keypair);
        assert!(!bytes.is_empty());
        let restored = identity::deserialize_keypair(&bytes).unwrap();
        assert_eq!(
            libp2p::PeerId::from(keypair.public()),
            libp2p::PeerId::from(restored.public())
        );
    }

    #[test]
    fn test_peer_id_from_public_key() {
        let (keypair, peer_id) = identity::generate_identity();
        let recovered = identity::peer_id_from_public_key(&keypair.public());
        assert_eq!(peer_id, recovered);
    }

    #[test]
    fn test_create_kademlia_behaviour() {
        let (_, peer_id) = identity::generate_identity();
        let _behaviour = dht::create_kademlia_behaviour(peer_id);
    }

    #[test]
    fn test_create_gossipsub_behaviour() {
        let (keypair, _) = identity::generate_identity();
        let behaviour = pubsub::create_gossipsub_behaviour(&keypair);
        assert!(behaviour.is_ok());
    }

    /// 测试 NAT 穿透策略在不同 NAT 类型组合下的输出
    /// NAT strategy in NAT type combination under
    #[test]
    fn test_select_traversal_strategy_all_combinations() {
        use nat_traversal::NatType;

        // Public: 始终直接监听
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Public, false),
            "直接监听公网地址"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Public, true),
            "直接监听公网地址"
        );

        // FullCone: 始终直接拨号
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::FullCone, false),
            "直接拨号（预测映射）"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::FullCone, true),
            "直接拨号（预测映射）"
        );

        // RestrictedCone: 有 relay 时使用 DCUtR，否则需要部署 Relay
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::RestrictedCone, true),
            "DCUtR 通过 Relay 建立直连"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::RestrictedCone, false),
            "需要部署 Relay 服务器"
        );

        // PortRestricted: 有 relay 时使用 DCUtR + 端口预测，否则需要部署 Relay
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::PortRestricted, true),
            "DCUtR + 端口预测"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::PortRestricted, false),
            "需要部署 Relay 服务器"
        );

        // Symmetric: 有 relay 时长期转发，否则需要部署 Relay
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Symmetric, true),
            "长期 Relay 转发（无法直连）"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Symmetric, false),
            "需要部署 Relay 服务器"
        );

        // Unknown: 有 relay 时尝试 DCUtR，否则需要部署 Relay
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Unknown, true),
            "尝试 DCUtR，若失败则使用 Relay"
        );
        assert_eq!(
            nat_traversal::select_traversal_strategy(NatType::Unknown, false),
            "需要部署 Relay 服务器"
        );
    }

    #[test]
    fn test_nat_type_coverage() {
        let variants = [
            nat_traversal::NatType::Public,
            nat_traversal::NatType::FullCone,
            nat_traversal::NatType::RestrictedCone,
            nat_traversal::NatType::PortRestricted,
            nat_traversal::NatType::Symmetric,
            nat_traversal::NatType::Unknown,
        ];
        for nat in &variants {
            // 确保每个变体都能进入 match 分支且不 panic
            let strategy = nat_traversal::select_traversal_strategy(*nat, true);
            assert!(!strategy.is_empty());
            let strategy = nat_traversal::select_traversal_strategy(*nat, false);
            assert!(!strategy.is_empty());
        }
    }

    #[test]
    fn test_build_memory_swarm_returns_err() {
        let (keypair, _) = identity::generate_identity();
        let behaviour = libp2p::ping::Behaviour::default();
        let result = swarm_builder::build_memory_swarm(&keypair, behaviour);
        match result {
            Err(err) => {
                assert!(
                    err.contains("MemoryTransport") || err.contains("build_tcp_swarm"),
                    "错误信息应提示 MemoryTransport 限制或推荐 build_tcp_swarm: {}",
                    err
                );
            }
            Ok(_) => panic!("build_memory_swarm 应返回错误"),
        }
    }

    /// 测试 build_tcp_swarm 能成功构建 Swarm
    /// Test for build_tcp_swarm 能成功构建 Swarm
    #[test]
    fn test_build_tcp_swarm() {
        let (keypair, peer_id) = identity::generate_identity();
        let behaviour = dht::create_kademlia_behaviour(peer_id);
        let result = swarm_builder::build_tcp_swarm(&keypair, behaviour);
        assert!(result.is_ok());
    }

    #[test]
    fn test_full_node_behaviour_new() {
        let (keypair, peer_id) = identity::generate_identity();
        let behaviour = FullNodeBehaviour::new(&keypair, peer_id);
        assert!(behaviour.is_ok());
    }

    #[test]
    fn test_create_relay_behaviour() {
        let (_, peer_id) = identity::generate_identity();
        let _behaviour = relay::create_relay_behaviour(peer_id);
    }

    #[test]
    fn test_create_autonat_behaviour() {
        let (_, peer_id) = identity::generate_identity();
        let _behaviour = autonat::create_autonat_behaviour(peer_id);
    }

    #[test]
    fn test_create_dcutr_behaviour() {
        let (_, peer_id) = identity::generate_identity();
        let _behaviour = dcutr::create_dcutr_behaviour(peer_id);
    }

    /// 测试主题名称格式
    #[test]
    fn test_topic_name() {
        let topic = pubsub::topic_name("myapp", "v1", "mainnet");
        assert_eq!(topic, "/myapp/v1/mainnet");
    }
}
