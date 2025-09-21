//! 网络拓扑模块
//! 
//! 定义网络拓扑相关的数据结构和类型

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::net::SocketAddr;
use chrono::{DateTime, Utc};
use super::SensorNetworkError;

/// 网络拓扑
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkTopology {
    /// 网络节点映射
    nodes: HashMap<String, NetworkNode>,
    /// 网络连接映射
    connections: HashMap<String, HashSet<String>>,
    /// 网络ID
    pub network_id: String,
    /// 网络名称
    pub name: String,
    /// 网络描述
    pub description: Option<String>,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后更新时间
    pub updated_at: DateTime<Utc>,
}

impl NetworkTopology {
    /// 创建新的网络拓扑
    pub fn new(network_id: String, name: String) -> Self {
        let now = Utc::now();
        Self {
            nodes: HashMap::new(),
            connections: HashMap::new(),
            network_id,
            name,
            description: None,
            created_at: now,
            updated_at: now,
        }
    }

    /// 添加网络节点
    pub fn add_node(&mut self, node: NetworkNode) -> Result<(), SensorNetworkError> {
        if self.nodes.contains_key(&node.id) {
            return Err(SensorNetworkError::TopologyError(
                format!("节点 {} 已存在", node.id)
            ));
        }

        self.nodes.insert(node.id.clone(), node.clone());
        self.connections.insert(node.id.clone(), HashSet::new());
        self.updated_at = Utc::now();
        Ok(())
    }

    /// 移除网络节点
    pub fn remove_node(&mut self, node_id: &str) -> Result<(), SensorNetworkError> {
        if !self.nodes.contains_key(node_id) {
            return Err(SensorNetworkError::NodeNotFound(node_id.to_string()));
        }

        // 移除节点
        self.nodes.remove(node_id);
        self.connections.remove(node_id);

        // 移除所有与该节点相关的连接
        for connections in self.connections.values_mut() {
            connections.remove(node_id);
        }

        self.updated_at = Utc::now();
        Ok(())
    }

    /// 添加网络连接
    pub fn add_connection(&mut self, from: &str, to: &str) -> Result<(), SensorNetworkError> {
        if !self.nodes.contains_key(from) {
            return Err(SensorNetworkError::NodeNotFound(from.to_string()));
        }
        if !self.nodes.contains_key(to) {
            return Err(SensorNetworkError::NodeNotFound(to.to_string()));
        }

        self.connections.get_mut(from)
            .ok_or_else(|| SensorNetworkError::TopologyError("连接映射错误".to_string()))?
            .insert(to.to_string());

        self.updated_at = Utc::now();
        Ok(())
    }

    /// 移除网络连接
    pub fn remove_connection(&mut self, from: &str, to: &str) -> Result<(), SensorNetworkError> {
        if let Some(connections) = self.connections.get_mut(from) {
            connections.remove(to);
            self.updated_at = Utc::now();
        }
        Ok(())
    }

    /// 获取网络节点
    pub fn get_node(&self, node_id: &str) -> Option<&NetworkNode> {
        self.nodes.get(node_id)
    }

    /// 获取所有网络节点
    pub fn get_all_nodes(&self) -> Vec<&NetworkNode> {
        self.nodes.values().collect()
    }

    /// 获取节点的连接
    pub fn get_node_connections(&self, node_id: &str) -> Option<&HashSet<String>> {
        self.connections.get(node_id)
    }

    /// 检查两个节点是否连接
    pub fn is_connected(&self, from: &str, to: &str) -> bool {
        self.connections.get(from)
            .map(|connections| connections.contains(to))
            .unwrap_or(false)
    }

    /// 获取网络统计信息
    pub fn get_statistics(&self) -> NetworkStatistics {
        let mut node_type_count = HashMap::new();
        let mut capability_count = HashMap::new();

        for node in self.nodes.values() {
            // 统计节点类型
            let type_name = match node.node_type {
                NodeType::Sensor => "传感器",
                NodeType::Actuator => "执行器",
                NodeType::Gateway => "网关",
                NodeType::Router => "路由器",
            };
            *node_type_count.entry(type_name.to_string()).or_insert(0) += 1;

            // 统计能力
            for capability in &node.capabilities {
                let cap_name = match capability {
                    Capability::Temperature => "温度",
                    Capability::Humidity => "湿度",
                    Capability::Pressure => "压力",
                    Capability::Light => "光照",
                    Capability::Motion => "运动",
                    Capability::Control => "控制",
                    Capability::Routing => "路由",
                };
                *capability_count.entry(cap_name.to_string()).or_insert(0) += 1;
            }
        }

        NetworkStatistics {
            total_nodes: self.nodes.len(),
            total_connections: self.connections.values().map(|c| c.len()).sum(),
            node_type_distribution: node_type_count,
            capability_distribution: capability_count,
            network_density: self.calculate_network_density(),
        }
    }

    /// 计算网络密度
    fn calculate_network_density(&self) -> f64 {
        let n = self.nodes.len();
        if n <= 1 {
            return 0.0;
        }

        let max_connections = n * (n - 1);
        let actual_connections: usize = self.connections.values().map(|c| c.len()).sum();
        
        actual_connections as f64 / max_connections as f64
    }

    /// 查找最短路径
    pub fn find_shortest_path(&self, from: &str, to: &str) -> Result<Vec<String>, SensorNetworkError> {
        if !self.nodes.contains_key(from) {
            return Err(SensorNetworkError::NodeNotFound(from.to_string()));
        }
        if !self.nodes.contains_key(to) {
            return Err(SensorNetworkError::NodeNotFound(to.to_string()));
        }

        if from == to {
            return Ok(vec![from.to_string()]);
        }

        // 使用BFS算法查找最短路径
        let mut queue = std::collections::VecDeque::new();
        let mut visited = HashSet::new();
        let mut parent: HashMap<String, String> = HashMap::new();

        queue.push_back(from.to_string());
        visited.insert(from.to_string());

        while let Some(current) = queue.pop_front() {
            if current == to {
                // 重构路径
                let mut path = Vec::new();
                let mut node = to.to_string();
                
                while let Some(parent_node) = parent.get(&node) {
                    path.push(node);
                    node = parent_node.clone();
                }
                path.push(from.to_string());
                path.reverse();
                
                return Ok(path);
            }

            if let Some(connections) = self.connections.get(&current) {
                for neighbor in connections {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor.clone());
                        parent.insert(neighbor.clone(), current.clone());
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }

        Err(SensorNetworkError::RoutingFailed(
            format!("无法找到从 {} 到 {} 的路径", from, to)
        ))
    }
}

/// 网络节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkNode {
    /// 节点ID
    pub id: String,
    /// 节点地址
    pub address: SocketAddr,
    /// 节点类型
    pub node_type: NodeType,
    /// 节点能力
    pub capabilities: Vec<Capability>,
    /// 最后心跳时间
    pub last_heartbeat: DateTime<Utc>,
    /// 电池电量 (0-100)
    pub battery_level: Option<u8>,
    /// 信号强度 (dBm)
    pub signal_strength: Option<i8>,
    /// 节点状态
    pub status: NodeStatus,
    /// 节点元数据
    pub metadata: HashMap<String, String>,
    /// 节点位置
    pub location: Option<NodeLocation>,
}

impl NetworkNode {
    /// 创建新的网络节点
    pub fn new(
        id: String,
        address: SocketAddr,
        node_type: NodeType,
        capabilities: Vec<Capability>,
    ) -> Self {
        Self {
            id,
            address,
            node_type,
            capabilities,
            last_heartbeat: Utc::now(),
            battery_level: None,
            signal_strength: None,
            status: NodeStatus::Offline,
            metadata: HashMap::new(),
            location: None,
        }
    }

    /// 更新心跳时间
    pub fn update_heartbeat(&mut self) {
        self.last_heartbeat = Utc::now();
    }

    /// 更新电池电量
    pub fn update_battery_level(&mut self, level: f64) {
        self.battery_level = Some(level as u8);
        self.update_heartbeat();
    }

    /// 更新信号强度
    pub fn update_signal_strength(&mut self, strength: f64) {
        self.signal_strength = Some(strength as i8);
        self.update_heartbeat();
    }

    /// 更新节点状态
    pub fn update_status(&mut self, status: NodeStatus) {
        self.status = status;
        self.update_heartbeat();
    }

    /// 检查节点是否在线
    pub fn is_online(&self) -> bool {
        matches!(self.status, NodeStatus::Online)
    }

    /// 检查节点是否需要维护
    pub fn needs_maintenance(&self) -> bool {
        matches!(self.status, NodeStatus::Maintenance) ||
        (self.battery_level.is_some() && self.battery_level.unwrap() < 20)
    }

    /// 添加元数据
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// 获取元数据
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

/// 节点类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum NodeType {
    /// 传感器节点
    Sensor,
    /// 执行器节点
    Actuator,
    /// 网关节点
    Gateway,
    /// 路由器节点
    Router,
}

impl NodeType {
    /// 获取节点类型描述
    pub fn description(&self) -> &'static str {
        match self {
            NodeType::Sensor => "传感器节点",
            NodeType::Actuator => "执行器节点",
            NodeType::Gateway => "网关节点",
            NodeType::Router => "路由器节点",
        }
    }
}

/// 节点能力
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Capability {
    /// 温度测量
    Temperature,
    /// 湿度测量
    Humidity,
    /// 压力测量
    Pressure,
    /// 光照测量
    Light,
    /// 运动检测
    Motion,
    /// 设备控制
    Control,
    /// 数据路由
    Routing,
}

impl Capability {
    /// 获取能力描述
    pub fn description(&self) -> &'static str {
        match self {
            Capability::Temperature => "温度测量",
            Capability::Humidity => "湿度测量",
            Capability::Pressure => "压力测量",
            Capability::Light => "光照测量",
            Capability::Motion => "运动检测",
            Capability::Control => "设备控制",
            Capability::Routing => "数据路由",
        }
    }
}

/// 节点状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum NodeStatus {
    /// 在线
    Online,
    /// 离线
    Offline,
    /// 维护中
    Maintenance,
    /// 错误状态
    Error,
    /// 休眠状态
    Sleeping,
}

impl NodeStatus {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            NodeStatus::Online => "在线",
            NodeStatus::Offline => "离线",
            NodeStatus::Maintenance => "维护中",
            NodeStatus::Error => "错误",
            NodeStatus::Sleeping => "休眠",
        }
    }
}

/// 节点位置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeLocation {
    /// 经度
    pub longitude: f64,
    /// 纬度
    pub latitude: f64,
    /// 海拔 (米)
    pub altitude: Option<f32>,
    /// 位置描述
    pub description: Option<String>,
}

impl NodeLocation {
    /// 创建新的节点位置
    pub fn new(longitude: f64, latitude: f64) -> Self {
        Self {
            longitude,
            latitude,
            altitude: None,
            description: None,
        }
    }

    /// 设置海拔
    pub fn with_altitude(mut self, altitude: f64) -> Self {
        self.altitude = Some(altitude as f32);
        self
    }

    /// 设置位置描述
    pub fn with_description(mut self, description: String) -> Self {
        self.description = Some(description);
        self
    }

    /// 计算与另一个位置的距离 (米)
    pub fn distance_to(&self, other: &NodeLocation) -> f64 {
        const EARTH_RADIUS: f64 = 6371000.0; // 地球半径 (米)
        
        let lat1_rad = self.latitude.to_radians();
        let lat2_rad = other.latitude.to_radians();
        let delta_lat = (other.latitude - self.latitude).to_radians();
        let delta_lon = (other.longitude - self.longitude).to_radians();

        let a = (delta_lat / 2.0).sin().powi(2) +
                lat1_rad.cos() * lat2_rad.cos() * (delta_lon / 2.0).sin().powi(2);
        let c = 2.0 * a.sqrt().atan2((1.0 - a).sqrt());

        EARTH_RADIUS * c
    }
}

/// 网络统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkStatistics {
    /// 总节点数
    pub total_nodes: usize,
    /// 总连接数
    pub total_connections: usize,
    /// 节点类型分布
    pub node_type_distribution: HashMap<String, usize>,
    /// 能力分布
    pub capability_distribution: HashMap<String, usize>,
    /// 网络密度
    pub network_density: f64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr};

    #[test]
    fn test_network_topology_creation() {
        let topology = NetworkTopology::new(
            "network_001".to_string(),
            "Test Network".to_string(),
        );

        assert_eq!(topology.network_id, "network_001");
        assert_eq!(topology.name, "Test Network");
        assert_eq!(topology.nodes.len(), 0);
    }

    #[test]
    fn test_add_remove_node() {
        let mut topology = NetworkTopology::new(
            "network_001".to_string(),
            "Test Network".to_string(),
        );

        let node = NetworkNode::new(
            "node_001".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 8080),
            NodeType::Sensor,
            vec![Capability::Temperature],
        );

        assert!(topology.add_node(node).is_ok());
        assert_eq!(topology.nodes.len(), 1);

        assert!(topology.remove_node("node_001").is_ok());
        assert_eq!(topology.nodes.len(), 0);
    }

    #[test]
    fn test_add_remove_connection() {
        let mut topology = NetworkTopology::new(
            "network_001".to_string(),
            "Test Network".to_string(),
        );

        let node1 = NetworkNode::new(
            "node_001".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 8080),
            NodeType::Sensor,
            vec![Capability::Temperature],
        );

        let node2 = NetworkNode::new(
            "node_002".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 2)), 8080),
            NodeType::Gateway,
            vec![Capability::Routing],
        );

        topology.add_node(node1).unwrap();
        topology.add_node(node2).unwrap();

        assert!(topology.add_connection("node_001", "node_002").is_ok());
        assert!(topology.is_connected("node_001", "node_002"));

        assert!(topology.remove_connection("node_001", "node_002").is_ok());
        assert!(!topology.is_connected("node_001", "node_002"));
    }

    #[test]
    fn test_shortest_path() {
        let mut topology = NetworkTopology::new(
            "network_001".to_string(),
            "Test Network".to_string(),
        );

        // 创建线性网络: node1 -> node2 -> node3
        let node1 = NetworkNode::new(
            "node_001".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 8080),
            NodeType::Sensor,
            vec![Capability::Temperature],
        );

        let node2 = NetworkNode::new(
            "node_002".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 2)), 8080),
            NodeType::Router,
            vec![Capability::Routing],
        );

        let node3 = NetworkNode::new(
            "node_003".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 3)), 8080),
            NodeType::Gateway,
            vec![Capability::Routing],
        );

        topology.add_node(node1).unwrap();
        topology.add_node(node2).unwrap();
        topology.add_node(node3).unwrap();

        topology.add_connection("node_001", "node_002").unwrap();
        topology.add_connection("node_002", "node_003").unwrap();

        let path = topology.find_shortest_path("node_001", "node_003").unwrap();
        assert_eq!(path, vec!["node_001", "node_002", "node_003"]);
    }

    #[test]
    fn test_node_location_distance() {
        let location1 = NodeLocation::new(116.3974, 39.9093); // 北京
        let location2 = NodeLocation::new(121.4737, 31.2304); // 上海

        let distance = location1.distance_to(&location2);
        assert!(distance > 1000000.0); // 距离应该大于1000公里
        assert!(distance < 1200000.0); // 距离应该小于1200公里
    }
}
