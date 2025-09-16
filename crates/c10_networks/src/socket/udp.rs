//! UDP 套接字实现

use crate::error::{NetworkError, NetworkResult};
use std::net::{Ipv4Addr, SocketAddr};
use std::time::Duration;
use tokio::net::UdpSocket;
use tokio::time::timeout;

/// UDP 套接字配置
#[derive(Debug, Clone)]
pub struct UdpConfig {
    pub address: SocketAddr,
    pub timeout: Option<Duration>,
    pub buffer_size: usize,
    pub broadcast: bool,
    pub multicast_loop_v4: bool,
}

impl Default for UdpConfig {
    fn default() -> Self {
        Self {
            address: "127.0.0.1:8080".parse().unwrap(),
            timeout: Some(Duration::from_secs(30)),
            buffer_size: 8192,
            broadcast: false,
            multicast_loop_v4: false,
        }
    }
}

/// UDP 套接字封装
#[derive(Debug)]
pub struct UdpSocketWrapper {
    socket: UdpSocket,
    config: UdpConfig,
    local_addr: SocketAddr,
}

impl UdpSocketWrapper {
    /// 创建新的 UDP 套接字
    pub async fn new(config: UdpConfig) -> NetworkResult<Self> {
        let socket = UdpSocket::bind(config.address).await?;
        let local_addr = socket.local_addr()?;

        Ok(Self {
            socket,
            config,
            local_addr,
        })
    }

    /// 绑定到指定地址
    pub async fn bind(addr: SocketAddr) -> NetworkResult<Self> {
        let socket = UdpSocket::bind(addr).await?;
        let local_addr = socket.local_addr()?;

        Ok(Self {
            socket,
            config: UdpConfig::default(),
            local_addr,
        })
    }

    /// 发送数据到指定地址
    pub async fn send_to(&self, data: &[u8], addr: SocketAddr) -> NetworkResult<usize> {
        match self.config.timeout {
            Some(timeout_duration) => timeout(timeout_duration, self.socket.send_to(data, addr))
                .await
                .map_err(|_| NetworkError::Timeout(timeout_duration))
                .and_then(|result| result.map_err(Into::into)),
            None => self.socket.send_to(data, addr).await.map_err(Into::into),
        }
    }

    /// 接收数据
    pub async fn recv_from(&self, buffer: &mut [u8]) -> NetworkResult<(usize, SocketAddr)> {
        match self.config.timeout {
            Some(timeout_duration) => timeout(timeout_duration, self.socket.recv_from(buffer))
                .await
                .map_err(|_| NetworkError::Timeout(timeout_duration))
                .and_then(|result| result.map_err(Into::into)),
            None => self.socket.recv_from(buffer).await.map_err(Into::into),
        }
    }

    /// 连接到指定地址（用于已连接套接字）
    pub async fn connect(&self, addr: SocketAddr) -> NetworkResult<()> {
        self.socket.connect(addr).await?;
        Ok(())
    }

    /// 发送数据（已连接套接字）
    pub async fn send(&self, data: &[u8]) -> NetworkResult<usize> {
        match self.config.timeout {
            Some(timeout_duration) => timeout(timeout_duration, self.socket.send(data))
                .await
                .map_err(|_| NetworkError::Timeout(timeout_duration))
                .and_then(|result| result.map_err(Into::into)),
            None => self.socket.send(data).await.map_err(Into::into),
        }
    }

    /// 接收数据（已连接套接字）
    pub async fn recv(&self, buffer: &mut [u8]) -> NetworkResult<usize> {
        match self.config.timeout {
            Some(timeout_duration) => timeout(timeout_duration, self.socket.recv(buffer))
                .await
                .map_err(|_| NetworkError::Timeout(timeout_duration))
                .and_then(|result| result.map_err(Into::into)),
            None => self.socket.recv(buffer).await.map_err(Into::into),
        }
    }

    /// 获取本地地址
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// 设置广播
    pub fn set_broadcast(&self, broadcast: bool) -> NetworkResult<()> {
        self.socket.set_broadcast(broadcast)?;
        Ok(())
    }

    /// 设置多播
    pub fn set_multicast_loop_v4(&self, multicast_loop_v4: bool) -> NetworkResult<()> {
        self.socket.set_multicast_loop_v4(multicast_loop_v4)?;
        Ok(())
    }

    /// 加入多播组
    pub fn join_multicast_v4(&self, multiaddr: Ipv4Addr, interface: Ipv4Addr) -> NetworkResult<()> {
        self.socket.join_multicast_v4(multiaddr, interface)?;
        Ok(())
    }

    /// 离开多播组
    pub fn leave_multicast_v4(
        &self,
        multiaddr: Ipv4Addr,
        interface: Ipv4Addr,
    ) -> NetworkResult<()> {
        self.socket.leave_multicast_v4(multiaddr, interface)?;
        Ok(())
    }
}
