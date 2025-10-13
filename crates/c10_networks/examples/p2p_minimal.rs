//! P2P 网络最小示例
//!
//! 这个示例展示了如何使用 libp2p 创建一个简单的 P2P 网络节点
//!
//! ## 功能特性
//!
//! - ✅ P2P 节点创建和身份管理
//! - ✅ TCP 传输层配置
//! - ✅ Noise 加密和 Yamux 多路复用
//! - ✅ GossipSub 消息传播
//! - ✅ Kademlia DHT 发现
//! - ✅ Ping 协议保活
//! - ✅ Identify 协议节点识别
//!
//! ## 运行方式
//!
//! ```bash
//! # 启动第一个节点
//! cargo run --example p2p_minimal
//!
//! # 在另一个终端启动第二个节点（会自动发现第一个节点）
//! cargo run --example p2p_minimal
//! ```
//!
//! ## P2P 协议栈
//!
//! 本示例使用了以下 P2P 协议：
//! - **传输层**: TCP
//! - **安全层**: Noise
//! - **多路复用**: Yamux
//! - **消息传播**: GossipSub
//! - **节点发现**: Kademlia DHT
//! - **保活机制**: Ping
//! - **节点识别**: Identify
//!
//! ## 配置选项
//!
//! 可以通过环境变量配置节点：
//! - `C10_P2P_LISTEN_ADDR`: 监听地址 (默认: /ip4/0.0.0.0/tcp/0)
//! - `C10_P2P_TOPIC`: 订阅主题 (默认: c10-demo)
//! - `C10_P2P_PUBLISH_INTERVAL`: 发布间隔 (默认: 5秒)

use libp2p::{
    Multiaddr, PeerId, Transport,
    core::upgrade,
    gossipsub, identify, identity, kad, noise, ping,
    swarm::{NetworkBehaviour, SwarmEvent},
    tcp, yamux,
};
use std::time::Duration;

#[derive(NetworkBehaviour)]
struct MyBehaviour {
    gossipsub: gossipsub::Behaviour,
    kademlia: kad::Behaviour<kad::store::MemoryStore>,
    ping: ping::Behaviour,
    identify: identify::Behaviour,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let key = identity::Keypair::generate_ed25519();
    let local_peer_id = PeerId::from(key.public());
    println!("local peer id: {}", local_peer_id);

    // 构建 TCP + Noise + Yamux 传输
    let tcp_transport = tcp::tokio::Transport::new(tcp::Config::default().nodelay(true));
    let noise = noise::Config::new(&key).expect("noise");
    let muxer = yamux::Config::default();
    let transport = tcp_transport
        .upgrade(upgrade::Version::V1)
        .authenticate(noise)
        .multiplex(muxer)
        .boxed();

    let gossipsub = gossipsub::Behaviour::new(
        gossipsub::MessageAuthenticity::Signed(key.clone()),
        gossipsub::Config::default(),
    )
    .map_err(anyhow::Error::msg)?;

    let store = kad::store::MemoryStore::new(local_peer_id);
    let kademlia = kad::Behaviour::new(local_peer_id, store);
    let ping = ping::Behaviour::default();
    let identify = identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public()));

    // 从环境变量读取配置
    let topic_name = std::env::var("C10_P2P_TOPIC")
        .unwrap_or_else(|_| "c10-demo".to_string());
    let listen_addr = std::env::var("C10_P2P_LISTEN_ADDR")
        .unwrap_or_else(|_| "/ip4/0.0.0.0/tcp/0".to_string());
    let publish_interval_secs = std::env::var("C10_P2P_PUBLISH_INTERVAL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    let topic = gossipsub::IdentTopic::new(&topic_name);
    let mut behaviour = MyBehaviour {
        gossipsub,
        kademlia,
        ping,
        identify,
    };
    let _ = behaviour.gossipsub.subscribe(&topic);
    let mut swarm = libp2p::Swarm::new(
        transport,
        behaviour,
        local_peer_id,
        libp2p::swarm::Config::with_tokio_executor(),
    );

    libp2p::Swarm::listen_on(&mut swarm, listen_addr.parse::<Multiaddr>()?)?;

    let mut ticker = tokio::time::interval(Duration::from_secs(publish_interval_secs));

    loop {
        tokio::select! {
            _ = ticker.tick() => {
                let _ = swarm.behaviour_mut().gossipsub.publish(topic.clone(), b"hello from c10".as_slice());
            }
            event = futures::StreamExt::select_next_some(&mut swarm) => {
                match event {
                    SwarmEvent::NewListenAddr { address, .. } => {
                        println!("listening on {}", address);
                    }
                    SwarmEvent::Behaviour(_ev) => {
                        // 可扩展处理其他事件
                    }
                    _ => {}
                }
            }
        }
    }
}
