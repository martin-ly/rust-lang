//! TCP 协议实现模块
//! 
//! 本模块提供了基于 Rust 1.89 的 TCP 协议实现，
//! 包括连接管理、状态机、流量控制等功能。

pub mod state;
pub mod connection;

pub use state::{TcpState, TcpEvent, TcpStateMachine};
pub use connection::{TcpConnection, TcpConnectionConfig, TcpConnectionStats};

use crate::error::{NetworkError, NetworkResult};
use std::time::Duration;
use tokio::sync::Mutex;
use std::collections::HashMap;

/// TCP 连接池
#[allow(unused)]
#[derive(Debug)]
pub struct TcpConnectionPool {
    connections: Mutex<HashMap<u64, TcpConnection>>,
    next_id: Mutex<u64>,
    max_connections: usize,
    connection_timeout: Duration,
}

impl TcpConnectionPool {
    /// 创建新的连接池
    pub fn new(max_connections: usize, connection_timeout: Duration) -> Self {
        Self {
            connections: Mutex::new(HashMap::new()),
            next_id: Mutex::new(0),
            max_connections,
            connection_timeout,
        }
    }

    /// 创建新连接
    pub async fn create_connection(&self, config: TcpConnectionConfig) -> NetworkResult<u64> {
        let mut connections = self.connections.lock().await;
        
        if connections.len() >= self.max_connections {
            return Err(NetworkError::Other("Connection pool exhausted".to_string()));
        }

        let mut next_id = self.next_id.lock().await;
        let id = *next_id;
        *next_id += 1;

        let connection = TcpConnection::new(id, config);
        connections.insert(id, connection);

        Ok(id)
    }

    /// 获取连接
    pub async fn get_connection(&self, id: u64) -> Option<TcpConnection> {
        let mut connections = self.connections.lock().await;
        connections.remove(&id)
    }

    /// 移除连接
    pub async fn remove_connection(&self, id: u64) -> bool {
        let mut connections = self.connections.lock().await;
        connections.remove(&id).is_some()
    }

    /// 清理超时连接
    pub async fn cleanup_timeout_connections(&self) -> usize {
        let mut connections = self.connections.lock().await;
        let mut to_remove = Vec::new();

        for (id, connection) in connections.iter() {
            if connection.is_timeout() {
                to_remove.push(*id);
            }
        }

        let count = to_remove.len();
        for id in to_remove {
            connections.remove(&id);
        }

        count
    }

    /// 获取连接统计信息
    pub async fn get_stats(&self) -> TcpPoolStats {
        let connections = self.connections.lock().await;
        let mut stats = TcpPoolStats {
            total_connections: connections.len(),
            established_connections: 0,
            closed_connections: 0,
            timeout_connections: 0,
            total_send_buffer_size: 0,
            total_recv_buffer_size: 0,
        };

        for connection in connections.values() {
            match connection.state() {
                TcpState::Established => stats.established_connections += 1,
                TcpState::Closed => stats.closed_connections += 1,
                _ => {}
            }

            if connection.is_timeout() {
                stats.timeout_connections += 1;
            }

            stats.total_send_buffer_size += connection.send_buffer.len();
            stats.total_recv_buffer_size += connection.recv_buffer.len();
        }

        stats
    }
}

/// TCP 连接池统计信息
#[derive(Debug, Clone)]
pub struct TcpPoolStats {
    pub total_connections: usize,
    pub established_connections: usize,
    pub closed_connections: usize,
    pub timeout_connections: usize,
    pub total_send_buffer_size: usize,
    pub total_recv_buffer_size: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_tcp_connection_pool() {
        let pool = TcpConnectionPool::new(10, Duration::from_secs(30));
        
        let config = TcpConnectionConfig::default();
        let connection_id = pool.create_connection(config).await.unwrap();
        
        assert_eq!(connection_id, 0);
        
        let stats = pool.get_stats().await;
        assert_eq!(stats.total_connections, 1);
    }

    #[tokio::test]
    async fn test_tcp_connection_pool_cleanup() {
        let pool = TcpConnectionPool::new(10, Duration::from_millis(100));
        
        let config = TcpConnectionConfig::default();
        let _connection_id = pool.create_connection(config).await.unwrap();
        
        // 等待超时
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        let cleaned = pool.cleanup_timeout_connections().await;
        assert_eq!(cleaned, 1);
        
        let stats = pool.get_stats().await;
        assert_eq!(stats.total_connections, 0);
    }
}