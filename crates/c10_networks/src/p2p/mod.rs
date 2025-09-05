//! P2P 模块（身份、发现、DHT、发布订阅、NAT 可达性）

pub mod identity;
pub mod discovery;
pub mod dht;
pub mod pubsub;
pub mod nat;

/// 对外暴露的最小统一接口
pub struct P2pConfig {
    pub node_name: String,
}

impl Default for P2pConfig {
    fn default() -> Self {
        Self { node_name: "c10-p2p".into() }
    }
}


