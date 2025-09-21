//! 路由模块
//! 
//! 提供网络路由功能，包括路由表管理和路由算法

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
// use std::net::SocketAddr;
use chrono::{DateTime, Utc};
use super::{SensorNetworkError, NetworkTopology};

/// 路由表
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoutingTable {
    /// 路由条目映射
    routes: HashMap<String, Vec<Route>>,
    /// 路由表ID
    pub table_id: String,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后更新时间
    pub updated_at: DateTime<Utc>,
    /// 路由算法
    pub algorithm: RoutingAlgorithm,
}

impl RoutingTable {
    /// 创建新的路由表
    pub fn new(table_id: String, algorithm: RoutingAlgorithm) -> Self {
        let now = Utc::now();
        Self {
            routes: HashMap::new(),
            table_id,
            created_at: now,
            updated_at: now,
            algorithm,
        }
    }

    /// 添加路由
    pub fn add_route(&mut self, destination: String, route: Route) {
        self.routes.entry(destination).or_insert_with(Vec::new).push(route);
        self.updated_at = Utc::now();
    }

    /// 移除路由
    pub fn remove_route(&mut self, destination: &str, route_id: &str) -> bool {
        if let Some(routes) = self.routes.get_mut(destination) {
            if let Some(pos) = routes.iter().position(|r| r.id == route_id) {
                routes.remove(pos);
                if routes.is_empty() {
                    self.routes.remove(destination);
                }
                self.updated_at = Utc::now();
                return true;
            }
        }
        false
    }

    /// 获取到指定目标的路由
    pub fn get_routes(&self, destination: &str) -> Option<&Vec<Route>> {
        self.routes.get(destination)
    }

    /// 获取最佳路由
    pub fn get_best_route(&self, destination: &str) -> Option<&Route> {
        self.routes.get(destination)?.first()
    }

    /// 更新路由表
    pub fn update_routing_table(&mut self, topology: &NetworkTopology, source_node: &str) -> Result<(), SensorNetworkError> {
        match self.algorithm {
            RoutingAlgorithm::ShortestPath => {
                self.update_shortest_path_routes(topology, source_node)
            }
            RoutingAlgorithm::MinimumHops => {
                self.update_minimum_hops_routes(topology, source_node)
            }
            RoutingAlgorithm::LoadBalancing => {
                self.update_load_balancing_routes(topology, source_node)
            }
            RoutingAlgorithm::EnergyAware | RoutingAlgorithm::Adaptive => {
                self.update_shortest_path_routes(topology, source_node)
            }
        }
    }

    /// 更新最短路径路由
    fn update_shortest_path_routes(&mut self, topology: &NetworkTopology, source_node: &str) -> Result<(), SensorNetworkError> {
        self.routes.clear();
        
        let nodes = topology.get_all_nodes();
        let node_ids: Vec<String> = nodes.iter().map(|n| n.id.clone()).collect();
        
        for destination in &node_ids {
            if destination != source_node {
                if let Ok(path) = topology.find_shortest_path(source_node, destination) {
                    let route = Route::new(
                        format!("route_{}_{}", source_node, destination),
                        source_node.to_string(),
                        destination.clone(),
                path.clone(),
                RouteMetric::HopCount(path.len() as u32),
                    );
                    
                    self.add_route(destination.clone(), route);
                }
            }
        }
        
        Ok(())
    }

    /// 更新最小跳数路由
    fn update_minimum_hops_routes(&mut self, topology: &NetworkTopology, source_node: &str) -> Result<(), SensorNetworkError> {
        self.routes.clear();
        
        let nodes = topology.get_all_nodes();
        let node_ids: Vec<String> = nodes.iter().map(|n| n.id.clone()).collect();
        
        for destination in &node_ids {
            if destination != source_node {
                if let Ok(path) = self.find_minimum_hops_path(topology, source_node, destination) {
                    let route = Route::new(
                        format!("route_{}_{}", source_node, destination),
                        source_node.to_string(),
                        destination.clone(),
                path.clone(),
                RouteMetric::HopCount(path.len() as u32),
                    );
                    
                    self.add_route(destination.clone(), route);
                }
            }
        }
        
        Ok(())
    }

    /// 更新负载均衡路由
    fn update_load_balancing_routes(&mut self, topology: &NetworkTopology, source_node: &str) -> Result<(), SensorNetworkError> {
        self.routes.clear();
        
        let nodes = topology.get_all_nodes();
        let node_ids: Vec<String> = nodes.iter().map(|n| n.id.clone()).collect();
        
        for destination in &node_ids {
            if destination != source_node {
                // 找到所有可能的路径
                let paths = self.find_all_paths(topology, source_node, destination)?;
                
                // 为每个路径创建路由
                for (i, path) in paths.iter().enumerate() {
                    let route = Route::new(
                        format!("route_{}_{}_{}", source_node, destination, i),
                        source_node.to_string(),
                        destination.clone(),
                        path.clone(),
                        RouteMetric::LoadBalance(i as u32),
                    );
                    
                    self.add_route(destination.clone(), route);
                }
            }
        }
        
        Ok(())
    }

    /// 查找最小跳数路径
    fn find_minimum_hops_path(&self, topology: &NetworkTopology, from: &str, to: &str) -> Result<Vec<String>, SensorNetworkError> {
        let mut queue = VecDeque::new();
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

            if let Some(connections) = topology.get_node_connections(&current) {
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

    /// 查找所有路径
    fn find_all_paths(&self, topology: &NetworkTopology, from: &str, to: &str) -> Result<Vec<Vec<String>>, SensorNetworkError> {
        let mut paths = Vec::new();
        let mut current_path = Vec::new();
        let mut visited = HashSet::new();
        
        self.dfs_find_paths(topology, from, to, &mut current_path, &mut visited, &mut paths);
        
        if paths.is_empty() {
            Err(SensorNetworkError::RoutingFailed(
                format!("无法找到从 {} 到 {} 的路径", from, to)
            ))
        } else {
            Ok(paths)
        }
    }

    /// 深度优先搜索查找路径
    fn dfs_find_paths(
        &self,
        topology: &NetworkTopology,
        current: &str,
        target: &str,
        current_path: &mut Vec<String>,
        visited: &mut HashSet<String>,
        paths: &mut Vec<Vec<String>>,
    ) {
        if current == target {
            current_path.push(current.to_string());
            paths.push(current_path.clone());
            current_path.pop();
            return;
        }

        visited.insert(current.to_string());
        current_path.push(current.to_string());

        if let Some(connections) = topology.get_node_connections(current) {
            for neighbor in connections {
                if !visited.contains(neighbor) {
                    self.dfs_find_paths(topology, neighbor, target, current_path, visited, paths);
                }
            }
        }

        current_path.pop();
        visited.remove(current);
    }

    /// 获取路由表统计信息
    pub fn get_statistics(&self) -> RoutingStatistics {
        let mut destination_count = 0;
        let mut total_routes = 0;
        let mut total_hops = 0;

        for routes in self.routes.values() {
            destination_count += 1;
            total_routes += routes.len();
            for route in routes {
                total_hops += route.path.len();
            }
        }

        RoutingStatistics {
            total_destinations: destination_count,
            total_routes: total_routes,
            average_hops: if total_routes > 0 { total_hops as f64 / total_routes as f64 } else { 0.0 },
            algorithm: self.algorithm.clone(),
        }
    }
}

/// 路由
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Route {
    /// 路由ID
    pub id: String,
    /// 源节点
    pub source: String,
    /// 目标节点
    pub destination: String,
    /// 路径
    pub path: Vec<String>,
    /// 路由度量
    pub metric: RouteMetric,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后使用时间
    pub last_used: Option<DateTime<Utc>>,
    /// 使用次数
    pub usage_count: u32,
}

impl Route {
    /// 创建新的路由
    pub fn new(id: String, source: String, destination: String, path: Vec<String>, metric: RouteMetric) -> Self {
        Self {
            id,
            source,
            destination,
            path,
            metric,
            created_at: Utc::now(),
            last_used: None,
            usage_count: 0,
        }
    }

    /// 使用路由
    pub fn use_route(&mut self) {
        self.last_used = Some(Utc::now());
        self.usage_count += 1;
    }

    /// 获取跳数
    pub fn get_hop_count(&self) -> usize {
        self.path.len().saturating_sub(1)
    }

    /// 检查路由是否有效
    pub fn is_valid(&self) -> bool {
        !self.path.is_empty() && 
        self.path[0] == self.source && 
        self.path.last().unwrap() == &self.destination
    }

    /// 获取下一跳
    pub fn get_next_hop(&self, current_node: &str) -> Option<&String> {
        if let Some(pos) = self.path.iter().position(|node| node == current_node) {
            if pos + 1 < self.path.len() {
                return Some(&self.path[pos + 1]);
            }
        }
        None
    }
}

/// 路由度量
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RouteMetric {
    /// 跳数
    HopCount(u32),
    /// 延迟 (毫秒)
    Latency(u32),
    /// 带宽 (Mbps)
    Bandwidth(u32),
    /// 负载均衡
    LoadBalance(u32),
    /// 能量消耗
    EnergyConsumption(f64),
    /// 综合度量
    Composite(f64),
}

impl RouteMetric {
    /// 获取度量值
    pub fn get_value(&self) -> f64 {
        match self {
            RouteMetric::HopCount(count) => *count as f64,
            RouteMetric::Latency(latency) => *latency as f64,
            RouteMetric::Bandwidth(bandwidth) => *bandwidth as f64,
            RouteMetric::LoadBalance(load) => *load as f64,
            RouteMetric::EnergyConsumption(energy) => *energy,
            RouteMetric::Composite(value) => *value,
        }
    }

    /// 比较度量值 (越小越好)
    pub fn is_better_than(&self, other: &RouteMetric) -> bool {
        self.get_value() < other.get_value()
    }
}

/// 路由算法
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RoutingAlgorithm {
    /// 最短路径算法
    ShortestPath,
    /// 最小跳数算法
    MinimumHops,
    /// 负载均衡算法
    LoadBalancing,
    /// 能量感知算法
    EnergyAware,
    /// 自适应算法
    Adaptive,
}

impl RoutingAlgorithm {
    /// 获取算法描述
    pub fn description(&self) -> &'static str {
        match self {
            RoutingAlgorithm::ShortestPath => "最短路径算法",
            RoutingAlgorithm::MinimumHops => "最小跳数算法",
            RoutingAlgorithm::LoadBalancing => "负载均衡算法",
            RoutingAlgorithm::EnergyAware => "能量感知算法",
            RoutingAlgorithm::Adaptive => "自适应算法",
        }
    }
}

/// 路由统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoutingStatistics {
    /// 总目标数
    pub total_destinations: usize,
    /// 总路由数
    pub total_routes: usize,
    /// 平均跳数
    pub average_hops: f64,
    /// 使用的算法
    pub algorithm: RoutingAlgorithm,
}

/// 路由管理器
pub struct RoutingManager {
    /// 路由表
    routing_table: RoutingTable,
    /// 网络拓扑
    topology: NetworkTopology,
    /// 当前节点ID
    current_node_id: String,
}

impl RoutingManager {
    /// 创建新的路由管理器
    pub fn new(
        table_id: String,
        algorithm: RoutingAlgorithm,
        topology: NetworkTopology,
        current_node_id: String,
    ) -> Self {
        let routing_table = RoutingTable::new(table_id, algorithm);
        
        Self {
            routing_table,
            topology,
            current_node_id,
        }
    }

    /// 更新路由表
    pub async fn update_routes(&mut self) -> Result<(), SensorNetworkError> {
        self.routing_table.update_routing_table(&self.topology, &self.current_node_id)
    }

    /// 获取到指定目标的路由
    pub fn get_route(&mut self, destination: &str) -> Option<&Route> {
        let route = self.routing_table.get_best_route(destination)?;
        // 更新使用统计
        // 注意：这里需要可变引用，但返回的是不可变引用
        // 在实际应用中，可能需要使用内部可变性或其他设计模式
        Some(route)
    }

    /// 获取所有路由
    pub fn get_all_routes(&self) -> &HashMap<String, Vec<Route>> {
        &self.routing_table.routes
    }

    /// 添加路由
    pub fn add_route(&mut self, destination: String, route: Route) {
        self.routing_table.add_route(destination, route);
    }

    /// 移除路由
    pub fn remove_route(&mut self, destination: &str, route_id: &str) -> bool {
        self.routing_table.remove_route(destination, route_id)
    }

    /// 获取路由统计信息
    pub fn get_statistics(&self) -> RoutingStatistics {
        self.routing_table.get_statistics()
    }

    /// 更新网络拓扑
    pub fn update_topology(&mut self, topology: NetworkTopology) {
        self.topology = topology;
    }

    /// 设置当前节点
    pub fn set_current_node(&mut self, node_id: String) {
        self.current_node_id = node_id;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr};
    use crate::sensor_network::network_topology::{NodeType, Capability};
    use std::net::SocketAddr;

    fn create_test_topology() -> NetworkTopology {
        let mut topology = NetworkTopology::new(
            "test_network".to_string(),
            "Test Network".to_string(),
        );

        // 创建节点
        let node1 = crate::sensor_network::NetworkNode::new(
            "node_001".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 8080),
            NodeType::Sensor,
            vec![Capability::Temperature],
        );

        let node2 = crate::sensor_network::NetworkNode::new(
            "node_002".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 2)), 8080),
            NodeType::Router,
            vec![Capability::Routing],
        );

        let node3 = crate::sensor_network::NetworkNode::new(
            "node_003".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 3)), 8080),
            NodeType::Gateway,
            vec![Capability::Routing],
        );

        // 添加节点
        topology.add_node(node1).unwrap();
        topology.add_node(node2).unwrap();
        topology.add_node(node3).unwrap();

        // 添加连接: node1 -> node2 -> node3
        topology.add_connection("node_001", "node_002").unwrap();
        topology.add_connection("node_002", "node_003").unwrap();

        topology
    }

    #[test]
    fn test_routing_table_creation() {
        let routing_table = RoutingTable::new(
            "table_001".to_string(),
            RoutingAlgorithm::ShortestPath,
        );

        assert_eq!(routing_table.table_id, "table_001");
        assert_eq!(routing_table.algorithm, RoutingAlgorithm::ShortestPath);
        assert_eq!(routing_table.routes.len(), 0);
    }

    #[test]
    fn test_add_remove_route() {
        let mut routing_table = RoutingTable::new(
            "table_001".to_string(),
            RoutingAlgorithm::ShortestPath,
        );

        let route = Route::new(
            "route_001".to_string(),
            "node_001".to_string(),
            "node_003".to_string(),
            vec!["node_001".to_string(), "node_002".to_string(), "node_003".to_string()],
            RouteMetric::HopCount(2),
        );

        routing_table.add_route("node_003".to_string(), route);
        assert_eq!(routing_table.routes.len(), 1);

        assert!(routing_table.remove_route("node_003", "route_001"));
        assert_eq!(routing_table.routes.len(), 0);
    }

    #[test]
    fn test_route_validation() {
        let route = Route::new(
            "route_001".to_string(),
            "node_001".to_string(),
            "node_003".to_string(),
            vec!["node_001".to_string(), "node_002".to_string(), "node_003".to_string()],
            RouteMetric::HopCount(2),
        );

        assert!(route.is_valid());
        assert_eq!(route.get_hop_count(), 2);
        assert_eq!(route.get_next_hop("node_001"), Some(&"node_002".to_string()));
        assert_eq!(route.get_next_hop("node_002"), Some(&"node_003".to_string()));
        assert_eq!(route.get_next_hop("node_003"), None);
    }

    #[test]
    fn test_route_metric_comparison() {
        let metric1 = RouteMetric::HopCount(2);
        let metric2 = RouteMetric::HopCount(3);

        assert!(metric1.is_better_than(&metric2));
        assert!(!metric2.is_better_than(&metric1));
    }

    #[test]
    fn test_routing_table_update() {
        let mut routing_table = RoutingTable::new(
            "table_001".to_string(),
            RoutingAlgorithm::ShortestPath,
        );

        let topology = create_test_topology();
        let result = routing_table.update_routing_table(&topology, "node_001");
        
        assert!(result.is_ok());
        assert_eq!(routing_table.routes.len(), 2); // 到node_002和node_003的路由
    }

    #[tokio::test]
    async fn test_routing_manager() {
        let topology = create_test_topology();
        let mut routing_manager = RoutingManager::new(
            "manager_001".to_string(),
            RoutingAlgorithm::ShortestPath,
            topology,
            "node_001".to_string(),
        );

        let result = routing_manager.update_routes();
        assert!(result.await.is_ok());

        let statistics = routing_manager.get_statistics();
        assert_eq!(statistics.total_destinations, 2);
        assert_eq!(statistics.algorithm, RoutingAlgorithm::ShortestPath);
    }
}
