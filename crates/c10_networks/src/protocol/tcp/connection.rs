//! TCP 连接管理

use crate::error::{NetworkError, NetworkResult};
use crate::socket::{TcpConfig, TcpSocket};
use bytes::BytesMut;
use std::net::SocketAddr;
use std::time::{Duration, Instant};

use super::state::{TcpState, TcpStateMachine};

/// TCP 连接配置
#[derive(Debug, Clone)]
pub struct TcpConnectionConfig {
    pub local_addr: SocketAddr,
    pub remote_addr: SocketAddr,
    pub timeout: Duration,
    pub keep_alive: bool,
    pub tcp_nodelay: bool,
    pub send_buffer_size: usize,
    pub recv_buffer_size: usize,
    pub max_segment_size: usize,
    pub window_size: u16,
}

impl Default for TcpConnectionConfig {
    fn default() -> Self {
        Self {
            local_addr: "127.0.0.1:0".parse().unwrap(),
            remote_addr: "127.0.0.1:8080".parse().unwrap(),
            timeout: Duration::from_secs(30),
            keep_alive: true,
            tcp_nodelay: true,
            send_buffer_size: 8192,
            recv_buffer_size: 8192,
            max_segment_size: 1460,
            window_size: 65535,
        }
    }
}

/// TCP 连接
#[derive(Debug)]
pub struct TcpConnection {
    pub id: u64,
    pub state_machine: TcpStateMachine,
    pub config: TcpConnectionConfig,
    pub socket: Option<TcpSocket>,
    pub created_at: Instant,
    pub last_activity: Instant,
    pub send_buffer: BytesMut,
    pub recv_buffer: BytesMut,
    pub sequence_number: u32,
    pub acknowledgment_number: u32,
    pub window_size: u16,
    pub congestion_window: u32,
    pub slow_start_threshold: u32,
    pub retransmission_timeout: Duration,
}

impl TcpConnection {
    /// 创建新的 TCP 连接
    pub fn new(id: u64, config: TcpConnectionConfig) -> Self {
        let now = Instant::now();
        let timeout = config.timeout;
        Self {
            id,
            state_machine: TcpStateMachine::new(),
            config,
            socket: None,
            created_at: now,
            last_activity: now - timeout - Duration::from_millis(1),
            send_buffer: BytesMut::new(),
            recv_buffer: BytesMut::new(),
            sequence_number: 0,
            acknowledgment_number: 0,
            window_size: 65535,
            congestion_window: 1,
            slow_start_threshold: 65535,
            retransmission_timeout: Duration::from_millis(1000),
        }
    }

    /// 建立连接
    pub async fn connect(&mut self) -> NetworkResult<()> {
        if !self
            .state_machine
            .can_execute(&super::state::TcpEvent::Open)
        {
            return Err(NetworkError::Protocol(
                "Invalid state for connection".to_string(),
            ));
        }

        let tcp_config = TcpConfig {
            address: self.config.remote_addr,
            timeout: Some(self.config.timeout),
            buffer_size: self.config.recv_buffer_size,
            keep_alive: self.config.keep_alive,
            tcp_nodelay: self.config.tcp_nodelay,
        };

        let mut socket = TcpSocket::new(tcp_config);
        socket.connect().await?;

        self.socket = Some(socket);
        self.state_machine
            .transition(super::state::TcpEvent::Open)?;
        self.last_activity = Instant::now();

        Ok(())
    }

    /// 发送数据
    pub async fn send(&mut self, data: &[u8]) -> NetworkResult<usize> {
        if !self.state_machine.current_state().can_send_data() {
            return Err(NetworkError::Protocol(
                "Connection not established".to_string(),
            ));
        }

        if let Some(ref mut socket) = self.socket {
            let sent = socket.write(data).await?;
            self.last_activity = Instant::now();
            Ok(sent)
        } else {
            Err(NetworkError::Connection("No socket available".to_string()))
        }
    }

    /// 接收数据
    pub async fn receive(&mut self, buffer: &mut [u8]) -> NetworkResult<usize> {
        if !self.state_machine.current_state().can_receive_data() {
            return Err(NetworkError::Protocol(
                "Connection not established".to_string(),
            ));
        }

        if let Some(ref mut socket) = self.socket {
            let received = socket.read(buffer).await?;
            self.last_activity = Instant::now();
            Ok(received)
        } else {
            Err(NetworkError::Connection("No socket available".to_string()))
        }
    }

    /// 关闭连接
    pub async fn close(&mut self) -> NetworkResult<()> {
        if !self
            .state_machine
            .can_execute(&super::state::TcpEvent::Close)
        {
            return Err(NetworkError::Protocol(
                "Invalid state for close".to_string(),
            ));
        }

        self.state_machine
            .transition(super::state::TcpEvent::Close)?;

        if let Some(socket) = self.socket.take() {
            drop(socket); // 关闭连接
        }

        Ok(())
    }

    /// 检查连接是否超时
    pub fn is_timeout(&self) -> bool {
        self.last_activity.elapsed() > self.config.timeout
    }

    /// 获取当前状态
    pub fn state(&self) -> &TcpState {
        self.state_machine.current_state()
    }

    /// 获取连接统计信息
    pub fn get_stats(&self) -> TcpConnectionStats {
        TcpConnectionStats {
            id: self.id,
            state: self.state().clone(),
            created_at: self.created_at,
            last_activity: self.last_activity,
            send_buffer_size: self.send_buffer.len(),
            recv_buffer_size: self.recv_buffer.len(),
            sequence_number: self.sequence_number,
            acknowledgment_number: self.acknowledgment_number,
            window_size: self.window_size,
            congestion_window: self.congestion_window,
        }
    }

    /// 更新拥塞窗口（慢启动）
    pub fn update_congestion_window(&mut self) {
        if self.congestion_window < self.slow_start_threshold {
            // 慢启动阶段
            self.congestion_window =
                std::cmp::min(self.congestion_window * 2, self.slow_start_threshold);
        } else {
            // 拥塞避免阶段
            self.congestion_window += 1;
        }
    }

    /// 处理拥塞（快速重传）
    pub fn handle_congestion(&mut self) {
        self.slow_start_threshold = std::cmp::max(self.congestion_window / 2, 2);
        self.congestion_window = 1;
    }
}

/// TCP 连接统计信息
#[derive(Debug, Clone)]
pub struct TcpConnectionStats {
    pub id: u64,
    pub state: TcpState,
    pub created_at: Instant,
    pub last_activity: Instant,
    pub send_buffer_size: usize,
    pub recv_buffer_size: usize,
    pub sequence_number: u32,
    pub acknowledgment_number: u32,
    pub window_size: u16,
    pub congestion_window: u32,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_tcp_connection_creation() {
        let config = TcpConnectionConfig::default();
        let connection = TcpConnection::new(1, config);

        assert_eq!(connection.id, 1);
        assert_eq!(*connection.state(), TcpState::Closed);
        assert!(!connection.state().can_send_data());
        assert!(!connection.state().can_receive_data());
    }

    #[tokio::test]
    async fn test_tcp_congestion_control() {
        let config = TcpConnectionConfig::default();
        let mut connection = TcpConnection::new(1, config);

        // 测试慢启动
        connection.update_congestion_window();
        assert_eq!(connection.congestion_window, 2);

        connection.update_congestion_window();
        assert_eq!(connection.congestion_window, 4);

        // 测试拥塞处理
        connection.handle_congestion();
        assert_eq!(connection.congestion_window, 1);
        assert_eq!(connection.slow_start_threshold, 2);
    }

    #[test]
    fn test_tcp_connection_stats() {
        let config = TcpConnectionConfig::default();
        let connection = TcpConnection::new(1, config);
        let stats = connection.get_stats();

        assert_eq!(stats.id, 1);
        assert_eq!(stats.state, TcpState::Closed);
        assert_eq!(stats.send_buffer_size, 0);
        assert_eq!(stats.recv_buffer_size, 0);
    }
}
