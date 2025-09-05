//! 套接字模块
//! 
//! 本模块提供了基于 Rust 1.89 的现代套接字封装，
//! 支持 TCP 和 UDP 协议，以及异步网络编程。

pub mod tcp;
pub mod udp;

pub use tcp::{TcpConfig, TcpSocket, TcpListenerWrapper};
pub use udp::{UdpConfig, UdpSocketWrapper};

use crate::error::{NetworkError, NetworkResult};
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

/// 套接字类型枚举
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SocketType {
    Tcp,
    Udp,
}

/// 套接字工具函数
pub mod utils {
    use super::*;
    use std::net::ToSocketAddrs;

    /// 解析地址字符串
    pub fn parse_address(addr: &str) -> NetworkResult<SocketAddr> {
        addr.to_socket_addrs()?
            .next()
            .ok_or_else(|| NetworkError::Configuration("Invalid address".to_string()))
    }

    /// 创建本地回环地址
    pub fn localhost(port: u16) -> SocketAddr {
        SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), port)
    }

    /// 创建任意地址
    pub fn any(port: u16) -> SocketAddr {
        SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), port)
    }

    /// 检查端口是否可用
    pub async fn is_port_available(addr: SocketAddr) -> bool {
        tokio::net::TcpListener::bind(addr).await.is_ok()
    }

    /// 获取可用端口
    pub async fn get_available_port() -> NetworkResult<u16> {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await?;
        let addr = listener.local_addr()?;
        Ok(addr.port())
    }
}

/// 套接字工厂
pub struct SocketFactory;

impl SocketFactory {
    /// 创建 TCP 套接字
    pub fn create_tcp_socket(config: TcpConfig) -> TcpSocket {
        TcpSocket::new(config)
    }

    /// 创建 UDP 套接字
    pub async fn create_udp_socket(config: UdpConfig) -> NetworkResult<UdpSocketWrapper> {
        UdpSocketWrapper::new(config).await
    }

    /// 创建 TCP 监听器
    pub async fn create_tcp_listener(config: TcpConfig) -> NetworkResult<TcpListenerWrapper> {
        TcpListenerWrapper::new(config).await
    }

    /// 创建 UDP 套接字并绑定
    pub async fn create_udp_socket_bind(addr: SocketAddr) -> NetworkResult<UdpSocketWrapper> {
        UdpSocketWrapper::bind(addr).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_tcp_socket_creation() {
        let config = TcpConfig {
            address: utils::localhost(0),
            ..Default::default()
        };
        
        let socket = TcpSocket::new(config);
        assert!(!socket.is_connected());
        assert!(socket.local_addr().is_none());
        assert!(socket.peer_addr().is_none());
    }

    #[tokio::test]
    async fn test_udp_socket_creation() {
        let config = UdpConfig {
            address: utils::localhost(0),
            ..Default::default()
        };
        
        let socket = UdpSocketWrapper::new(config).await.unwrap();
        assert_eq!(socket.local_addr().ip(), Ipv4Addr::LOCALHOST);
    }

    #[tokio::test]
    async fn test_socket_factory() {
        let tcp_config = TcpConfig::default();
        let udp_config = UdpConfig::default();
        
        // 测试 TCP 套接字创建
        let tcp_socket = SocketFactory::create_tcp_socket(tcp_config);
        assert!(!tcp_socket.is_connected());
        
        // 测试 UDP 套接字创建
        let udp_socket = SocketFactory::create_udp_socket(udp_config).await.unwrap();
        assert_eq!(udp_socket.local_addr().ip(), Ipv4Addr::LOCALHOST);
    }

    #[tokio::test]
    async fn test_utils() {
        // 测试地址解析
        let addr = utils::parse_address("127.0.0.1:8080").unwrap();
        assert_eq!(addr, utils::localhost(8080));
        
        // 测试本地回环地址
        let localhost = utils::localhost(8080);
        assert_eq!(localhost.ip(), Ipv4Addr::LOCALHOST);
        assert_eq!(localhost.port(), 8080);
        
        // 测试任意地址
        let any = utils::any(8080);
        assert_eq!(any.ip(), Ipv4Addr::UNSPECIFIED);
        assert_eq!(any.port(), 8080);
        
        // 测试端口可用性检查
        let available = utils::is_port_available(utils::localhost(0)).await;
        assert!(available);
        
        // 测试获取可用端口
        let port = utils::get_available_port().await.unwrap();
        assert!(port > 0);
    }
}