//! TCP 套接字实现

use crate::error::{NetworkError, NetworkResult};
use std::net::SocketAddr;
use std::time::Duration;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::time::timeout;

/// TCP 套接字配置
#[derive(Debug, Clone)]
pub struct TcpConfig {
    pub address: SocketAddr,
    pub timeout: Option<Duration>,
    pub buffer_size: usize,
    pub keep_alive: bool,
    pub tcp_nodelay: bool,
}

impl Default for TcpConfig {
    fn default() -> Self {
        Self {
            address: "127.0.0.1:8080".parse().unwrap(),
            timeout: Some(Duration::from_secs(30)),
            buffer_size: 8192,
            keep_alive: true,
            tcp_nodelay: true,
        }
    }
}

/// TCP 套接字封装
#[derive(Debug)]
pub struct TcpSocket {
    stream: Option<TcpStream>,
    config: TcpConfig,
    local_addr: Option<SocketAddr>,
    peer_addr: Option<SocketAddr>,
}

impl TcpSocket {
    /// 创建新的 TCP 套接字
    pub fn new(config: TcpConfig) -> Self {
        Self {
            stream: None,
            config,
            local_addr: None,
            peer_addr: None,
        }
    }

    /// 作为客户端连接到服务器
    pub async fn connect(&mut self) -> NetworkResult<()> {
        let stream = TcpStream::connect(self.config.address).await?;
        
        if self.config.tcp_nodelay {
            stream.set_nodelay(true)?;
        }
        
        self.local_addr = Some(stream.local_addr()?);
        self.peer_addr = Some(stream.peer_addr()?);
        self.stream = Some(stream);
        
        Ok(())
    }

    /// 异步读取数据
    pub async fn read(&mut self, buffer: &mut [u8]) -> NetworkResult<usize> {
        if let Some(ref mut stream) = self.stream {
            match self.config.timeout {
                Some(timeout_duration) => {
                    timeout(timeout_duration, stream.read(buffer))
                        .await
                        .map_err(|_| NetworkError::Timeout(timeout_duration))
                        .and_then(|result| result.map_err(Into::into))
                }
                None => stream.read(buffer).await.map_err(Into::into),
            }
        } else {
            Err(NetworkError::Connection("Not connected".to_string()))
        }
    }

    /// 异步写入数据
    pub async fn write(&mut self, data: &[u8]) -> NetworkResult<usize> {
        if let Some(ref mut stream) = self.stream {
            match self.config.timeout {
                Some(timeout_duration) => {
                    timeout(timeout_duration, stream.write(data))
                        .await
                        .map_err(|_| NetworkError::Timeout(timeout_duration))
                        .and_then(|result| result.map_err(Into::into))
                }
                None => stream.write(data).await.map_err(Into::into),
            }
        } else {
            Err(NetworkError::Connection("Not connected".to_string()))
        }
    }

    /// 检查是否已连接
    pub fn is_connected(&self) -> bool {
        self.stream.is_some()
    }

    /// 获取本地地址
    pub fn local_addr(&self) -> Option<SocketAddr> {
        self.local_addr
    }

    /// 获取对端地址
    pub fn peer_addr(&self) -> Option<SocketAddr> {
        self.peer_addr
    }
}

/// TCP 监听器封装
pub struct TcpListenerWrapper {
    listener: TcpListener,
    config: TcpConfig,
}

impl TcpListenerWrapper {
    /// 创建新的 TCP 监听器
    pub async fn new(config: TcpConfig) -> NetworkResult<Self> {
        let listener = TcpListener::bind(config.address).await?;
        Ok(Self { listener, config })
    }

    /// 接受新的连接
    pub async fn accept(&self) -> NetworkResult<(TcpSocket, SocketAddr)> {
        let (stream, peer_addr) = self.listener.accept().await?;
        let local_addr = stream.local_addr()?;
        
        let socket = TcpSocket {
            stream: Some(stream),
            config: self.config.clone(),
            local_addr: Some(local_addr),
            peer_addr: Some(peer_addr),
        };
        
        Ok((socket, peer_addr))
    }

    /// 获取监听地址
    pub fn local_addr(&self) -> NetworkResult<SocketAddr> {
        self.listener.local_addr().map_err(Into::into)
    }
}
