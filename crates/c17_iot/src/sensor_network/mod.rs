//! 传感器网络模块
//! 
//! 提供传感器网络管理、路由、数据聚合等功能

pub mod routing;
pub mod network_topology;

pub use routing::{Route, RoutingAlgorithm};
pub use network_topology::{NetworkTopology, NetworkNode, NodeType, Capability};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum SensorNetworkError {
    #[error("网络连接失败: {0}")]
    ConnectionFailed(String),
    #[error("节点未找到: {0}")]
    NodeNotFound(String),
    #[error("路由失败: {0}")]
    RoutingFailed(String),
    #[error("数据包损坏: {0}")]
    PacketCorrupted(String),
    #[error("网络拓扑错误: {0}")]
    TopologyError(String),
}
