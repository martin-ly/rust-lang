# C10 Networks 协议实现指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`DOCUMENTATION_STYLE_GUIDE.md`](DOCUMENTATION_STYLE_GUIDE.md)。


## 📊 目录

- [📋 目录](#目录)
- [🎯 概述](#概述)
  - [1. 协议实现原则](#1-协议实现原则)
    - [1.1 核心原则](#11-核心原则)
    - [1.2 设计模式](#12-设计模式)
  - [2. 实现架构](#2-实现架构)
    - [2.1 分层架构](#21-分层架构)
    - [2.2 组件架构](#22-组件架构)
  - [3. 开发流程](#3-开发流程)
    - [3.1 开发步骤](#31-开发步骤)
    - [3.2 代码规范](#32-代码规范)
- [🔧 TCP协议实现](#tcp协议实现)
  - [1. 状态机设计](#1-状态机设计)
    - [1.1 TCP状态定义](#11-tcp状态定义)
    - [1.2 连接管理](#12-连接管理)
  - [2. 数据包处理](#2-数据包处理)
    - [2.1 TCP数据包结构](#21-tcp数据包结构)
  - [3. 拥塞控制](#3-拥塞控制)
    - [3.1 拥塞控制算法](#31-拥塞控制算法)
  - [4. 错误处理](#4-错误处理)
    - [4.1 错误类型定义](#41-错误类型定义)
- [🌐 HTTP协议实现](#http协议实现)
  - [1. 请求处理](#1-请求处理)
    - [1.1 HTTP请求结构](#11-http请求结构)
  - [2. 响应生成](#2-响应生成)
    - [2.1 HTTP响应结构](#21-http响应结构)
  - [3. 头部管理](#3-头部管理)
    - [3.1 HTTP头部处理](#31-http头部处理)
  - [4. 连接管理](#4-连接管理)
    - [4.1 HTTP连接池](#41-http连接池)
- [🔌 WebSocket协议实现](#websocket协议实现)
  - [1. 握手处理](#1-握手处理)
    - [1.1 WebSocket握手](#11-websocket握手)
  - [2. 帧处理](#2-帧处理)
    - [2.1 WebSocket帧结构](#21-websocket帧结构)
- [🔗 相关文档](#相关文档)


## 📋 目录

- [C10 Networks 协议实现指南](#c10-networks-协议实现指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [1. 协议实现原则](#1-协议实现原则)
      - [1.1 核心原则](#11-核心原则)
      - [1.2 设计模式](#12-设计模式)
    - [2. 实现架构](#2-实现架构)
      - [2.1 分层架构](#21-分层架构)
      - [2.2 组件架构](#22-组件架构)
    - [3. 开发流程](#3-开发流程)
      - [3.1 开发步骤](#31-开发步骤)
      - [3.2 代码规范](#32-代码规范)
  - [🔧 TCP协议实现](#-tcp协议实现)
    - [1. 状态机设计](#1-状态机设计)
      - [1.1 TCP状态定义](#11-tcp状态定义)
      - [1.2 连接管理](#12-连接管理)
    - [2. 数据包处理](#2-数据包处理)
      - [2.1 TCP数据包结构](#21-tcp数据包结构)
    - [3. 拥塞控制](#3-拥塞控制)
      - [3.1 拥塞控制算法](#31-拥塞控制算法)
    - [4. 错误处理](#4-错误处理)
      - [4.1 错误类型定义](#41-错误类型定义)
  - [🌐 HTTP协议实现](#-http协议实现)
    - [1. 请求处理](#1-请求处理)
      - [1.1 HTTP请求结构](#11-http请求结构)
    - [2. 响应生成](#2-响应生成)
      - [2.1 HTTP响应结构](#21-http响应结构)
    - [3. 头部管理](#3-头部管理)
      - [3.1 HTTP头部处理](#31-http头部处理)
    - [4. 连接管理](#4-连接管理)
      - [4.1 HTTP连接池](#41-http连接池)
  - [🔌 WebSocket协议实现](#-websocket协议实现)
    - [1. 握手处理](#1-握手处理)
      - [1.1 WebSocket握手](#11-websocket握手)
    - [2. 帧处理](#2-帧处理)
      - [2.1 WebSocket帧结构](#21-websocket帧结构)
  - [🔗 相关文档](#-相关文档)

## 🎯 概述

本文档提供了C10 Networks项目中各种网络协议的详细实现指南，包括设计原则、架构模式、实现细节和测试策略。

### 1. 协议实现原则

#### 1.1 核心原则

1. **正确性**: 严格遵循协议规范
2. **性能**: 优化内存使用和CPU效率
3. **安全性**: 防范各种安全威胁
4. **可维护性**: 代码清晰、模块化
5. **可扩展性**: 支持协议扩展和定制

#### 1.2 设计模式

| 模式 | 描述 | 应用场景 |
|------|------|----------|
| 状态机模式 | 管理协议状态转换 | TCP连接状态、HTTP会话状态 |
| 策略模式 | 可插拔的算法实现 | 拥塞控制、加密算法 |
| 观察者模式 | 事件通知机制 | 连接状态变化、错误事件 |
| 工厂模式 | 对象创建管理 | 协议处理器、连接工厂 |

### 2. 实现架构

#### 2.1 分层架构

```rust
// 协议实现分层架构
pub trait ProtocolLayer {
    fn process(&mut self, data: &[u8]) -> Result<Vec<u8>, ProtocolError>;
    fn get_layer_type(&self) -> LayerType;
}

pub struct ProtocolStack {
    layers: Vec<Box<dyn ProtocolLayer>>,
}

impl ProtocolStack {
    pub fn new() -> Self {
        Self {
            layers: Vec::new(),
        }
    }
    
    pub fn add_layer(&mut self, layer: Box<dyn ProtocolLayer>) {
        self.layers.push(layer);
    }
    
    pub fn process_data(&mut self, data: &[u8]) -> Result<Vec<u8>, ProtocolError> {
        let mut current_data = data.to_vec();
        
        for layer in &mut self.layers {
            current_data = layer.process(&current_data)?;
        }
        
        Ok(current_data)
    }
}
```

#### 2.2 组件架构

```rust
// 协议组件架构
pub struct ProtocolComponent {
    processor: Box<dyn ProtocolProcessor>,
    validator: Box<dyn ProtocolValidator>,
    serializer: Box<dyn ProtocolSerializer>,
    deserializer: Box<dyn ProtocolDeserializer>,
}

impl ProtocolComponent {
    pub fn process_packet(&self, packet: &[u8]) -> Result<ProcessedPacket, ProtocolError> {
        // 验证数据包
        self.validator.validate(packet)?;
        
        // 反序列化
        let message = self.deserializer.deserialize(packet)?;
        
        // 处理消息
        let response = self.processor.process(message)?;
        
        // 序列化响应
        let response_packet = self.serializer.serialize(response)?;
        
        Ok(ProcessedPacket::new(response_packet))
    }
}
```

### 3. 开发流程

#### 3.1 开发步骤

1. **需求分析**: 明确协议功能和性能要求
2. **设计阶段**: 设计状态机、数据结构和接口
3. **实现阶段**: 编写核心逻辑和错误处理
4. **测试阶段**: 单元测试、集成测试、压力测试
5. **优化阶段**: 性能调优和安全加固
6. **文档阶段**: 编写API文档和使用示例

#### 3.2 代码规范

```rust
// 协议实现代码规范示例
pub struct TcpProtocol {
    state: TcpState,
    config: TcpConfig,
    statistics: TcpStatistics,
}

impl TcpProtocol {
    /// 创建新的TCP协议实例
    /// 
    /// # 参数
    /// * `config` - TCP配置参数
    /// 
    /// # 返回值
    /// 返回TCP协议实例
    /// 
    /// # 示例
    /// ```rust
    /// let config = TcpConfig::default();
    /// let protocol = TcpProtocol::new(config);
    /// ```
    pub fn new(config: TcpConfig) -> Self {
        Self {
            state: TcpState::Closed,
            config,
            statistics: TcpStatistics::new(),
        }
    }
    
    /// 处理TCP数据包
    /// 
    /// # 参数
    /// * `packet` - TCP数据包
    /// 
    /// # 返回值
    /// 处理结果，包含响应数据包或错误
    pub fn process_packet(&mut self, packet: &TcpPacket) -> Result<Option<TcpPacket>, TcpError> {
        // 更新统计信息
        self.statistics.update_packet_count();
        
        // 验证数据包
        self.validate_packet(packet)?;
        
        // 根据当前状态处理数据包
        match self.state {
            TcpState::Closed => self.handle_closed_state(packet),
            TcpState::Listen => self.handle_listen_state(packet),
            TcpState::SynSent => self.handle_syn_sent_state(packet),
            TcpState::SynReceived => self.handle_syn_received_state(packet),
            TcpState::Established => self.handle_established_state(packet),
            TcpState::FinWait1 => self.handle_fin_wait1_state(packet),
            TcpState::FinWait2 => self.handle_fin_wait2_state(packet),
            TcpState::CloseWait => self.handle_close_wait_state(packet),
            TcpState::LastAck => self.handle_last_ack_state(packet),
            TcpState::Closing => self.handle_closing_state(packet),
            TcpState::TimeWait => self.handle_time_wait_state(packet),
        }
    }
}
```

## 🔧 TCP协议实现

### 1. 状态机设计

#### 1.1 TCP状态定义

```rust
// TCP状态机实现
#[derive(Debug, Clone, PartialEq)]
pub enum TcpState {
    Closed,
    Listen,
    SynSent,
    SynReceived,
    Established,
    FinWait1,
    FinWait2,
    CloseWait,
    LastAck,
    Closing,
    TimeWait,
}

pub struct TcpStateMachine {
    current_state: TcpState,
    connection_info: TcpConnectionInfo,
    timer_manager: TimerManager,
}

impl TcpStateMachine {
    pub fn new() -> Self {
        Self {
            current_state: TcpState::Closed,
            connection_info: TcpConnectionInfo::new(),
            timer_manager: TimerManager::new(),
        }
    }
    
    pub fn transition(&mut self, event: TcpEvent) -> Result<(), TcpError> {
        let next_state = self.get_next_state(&self.current_state, &event)?;
        
        // 执行状态转换
        self.execute_transition(&self.current_state, &next_state, &event)?;
        
        // 更新当前状态
        self.current_state = next_state;
        
        Ok(())
    }
    
    fn get_next_state(&self, current: &TcpState, event: &TcpEvent) -> Result<TcpState, TcpError> {
        match (current, event) {
            (TcpState::Closed, TcpEvent::PassiveOpen) => Ok(TcpState::Listen),
            (TcpState::Closed, TcpEvent::ActiveOpen) => Ok(TcpState::SynSent),
            (TcpState::Listen, TcpEvent::ReceiveSyn) => Ok(TcpState::SynReceived),
            (TcpState::SynSent, TcpEvent::ReceiveSynAck) => Ok(TcpState::Established),
            (TcpState::SynReceived, TcpEvent::ReceiveAck) => Ok(TcpState::Established),
            (TcpState::Established, TcpEvent::SendFin) => Ok(TcpState::FinWait1),
            (TcpState::Established, TcpEvent::ReceiveFin) => Ok(TcpState::CloseWait),
            (TcpState::FinWait1, TcpEvent::ReceiveAck) => Ok(TcpState::FinWait2),
            (TcpState::FinWait1, TcpEvent::ReceiveFin) => Ok(TcpState::Closing),
            (TcpState::FinWait2, TcpEvent::ReceiveFin) => Ok(TcpState::TimeWait),
            (TcpState::CloseWait, TcpEvent::SendFin) => Ok(TcpState::LastAck),
            (TcpState::LastAck, TcpEvent::ReceiveAck) => Ok(TcpState::Closed),
            (TcpState::Closing, TcpEvent::ReceiveAck) => Ok(TcpState::TimeWait),
            (TcpState::TimeWait, TcpEvent::Timeout) => Ok(TcpState::Closed),
            _ => Err(TcpError::InvalidTransition),
        }
    }
    
    fn execute_transition(&mut self, from: &TcpState, to: &TcpState, event: &TcpEvent) -> Result<(), TcpError> {
        // 执行状态转换动作
        match (from, to) {
            (TcpState::Closed, TcpState::SynSent) => {
                self.send_syn_packet()?;
                self.start_retransmission_timer()?;
            }
            (TcpState::SynSent, TcpState::Established) => {
                self.stop_retransmission_timer()?;
                self.establish_connection()?;
            }
            (TcpState::Established, TcpState::FinWait1) => {
                self.send_fin_packet()?;
                self.start_fin_timer()?;
            }
            (TcpState::TimeWait, TcpState::Closed) => {
                self.cleanup_connection()?;
            }
            _ => {}
        }
        
        Ok(())
    }
}
```

#### 1.2 连接管理

```rust
// TCP连接管理
pub struct TcpConnection {
    id: ConnectionId,
    state: TcpState,
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    send_buffer: SendBuffer,
    receive_buffer: ReceiveBuffer,
    congestion_control: CongestionControl,
    flow_control: FlowControl,
}

impl TcpConnection {
    pub fn new(id: ConnectionId, local_addr: SocketAddr, remote_addr: SocketAddr) -> Self {
        Self {
            id,
            state: TcpState::Closed,
            local_addr,
            remote_addr,
            send_buffer: SendBuffer::new(),
            receive_buffer: ReceiveBuffer::new(),
            congestion_control: CongestionControl::new(),
            flow_control: FlowControl::new(),
        }
    }
    
    pub fn send_data(&mut self, data: &[u8]) -> Result<(), TcpError> {
        if self.state != TcpState::Established {
            return Err(TcpError::ConnectionNotEstablished);
        }
        
        // 将数据添加到发送缓冲区
        self.send_buffer.append(data)?;
        
        // 尝试发送数据
        self.try_send_data()?;
        
        Ok(())
    }
    
    pub fn receive_data(&mut self) -> Result<Vec<u8>, TcpError> {
        if self.state != TcpState::Established {
            return Err(TcpError::ConnectionNotEstablished);
        }
        
        // 从接收缓冲区获取数据
        self.receive_buffer.extract_data()
    }
    
    fn try_send_data(&mut self) -> Result<(), TcpError> {
        let window_size = self.flow_control.get_window_size();
        let congestion_window = self.congestion_control.get_window_size();
        let send_window = window_size.min(congestion_window);
        
        if send_window > 0 {
            let data_to_send = self.send_buffer.get_data(send_window as usize)?;
            if !data_to_send.is_empty() {
                self.send_packet(data_to_send)?;
            }
        }
        
        Ok(())
    }
}
```

### 2. 数据包处理

#### 2.1 TCP数据包结构

```rust
// TCP数据包结构
#[derive(Debug, Clone)]
pub struct TcpPacket {
    header: TcpHeader,
    payload: Vec<u8>,
    checksum: u16,
}

#[derive(Debug, Clone)]
pub struct TcpHeader {
    source_port: u16,
    dest_port: u16,
    sequence_number: u32,
    acknowledgment_number: u32,
    data_offset: u8,
    flags: TcpFlags,
    window_size: u16,
    checksum: u16,
    urgent_pointer: u16,
    options: Vec<TcpOption>,
}

#[derive(Debug, Clone)]
pub struct TcpFlags {
    pub ns: bool,    // ECN-nonce
    pub cwr: bool,   // Congestion Window Reduced
    pub ece: bool,   // ECN-Echo
    pub urg: bool,   // Urgent
    pub ack: bool,   // Acknowledgment
    pub psh: bool,   // Push
    pub rst: bool,   // Reset
    pub syn: bool,   // Synchronize
    pub fin: bool,   // Finish
}

impl TcpPacket {
    pub fn new(header: TcpHeader, payload: Vec<u8>) -> Self {
        let mut packet = Self {
            header,
            payload,
            checksum: 0,
        };
        
        // 计算校验和
        packet.checksum = packet.calculate_checksum();
        packet.header.checksum = packet.checksum;
        
        packet
    }
    
    pub fn serialize(&self) -> Vec<u8> {
        let mut data = Vec::new();
        
        // 序列化头部
        data.extend_from_slice(&self.header.source_port.to_be_bytes());
        data.extend_from_slice(&self.header.dest_port.to_be_bytes());
        data.extend_from_slice(&self.header.sequence_number.to_be_bytes());
        data.extend_from_slice(&self.header.acknowledgment_number.to_be_bytes());
        
        // 数据偏移和标志
        let data_offset_flags = ((self.header.data_offset as u16) << 12) | self.header.flags.to_u16();
        data.extend_from_slice(&data_offset_flags.to_be_bytes());
        
        data.extend_from_slice(&self.header.window_size.to_be_bytes());
        data.extend_from_slice(&self.header.checksum.to_be_bytes());
        data.extend_from_slice(&self.header.urgent_pointer.to_be_bytes());
        
        // 序列化选项
        for option in &self.header.options {
            data.extend_from_slice(&option.serialize());
        }
        
        // 添加负载
        data.extend_from_slice(&self.payload);
        
        data
    }
    
    pub fn deserialize(data: &[u8]) -> Result<Self, TcpError> {
        if data.len() < 20 {
            return Err(TcpError::InvalidPacketSize);
        }
        
        let mut offset = 0;
        
        // 反序列化头部
        let source_port = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        let dest_port = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        let sequence_number = u32::from_be_bytes([
            data[offset], data[offset + 1], data[offset + 2], data[offset + 3]
        ]);
        offset += 4;
        
        let acknowledgment_number = u32::from_be_bytes([
            data[offset], data[offset + 1], data[offset + 2], data[offset + 3]
        ]);
        offset += 4;
        
        let data_offset_flags = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        let data_offset = ((data_offset_flags >> 12) & 0xF) as u8;
        let flags = TcpFlags::from_u16(data_offset_flags & 0x1FF);
        
        let window_size = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        let checksum = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        let urgent_pointer = u16::from_be_bytes([data[offset], data[offset + 1]]);
        offset += 2;
        
        // 反序列化选项
        let options_len = (data_offset as usize * 4) - 20;
        let mut options = Vec::new();
        if options_len > 0 {
            let options_data = &data[offset..offset + options_len];
            options = TcpOption::deserialize_all(options_data)?;
            offset += options_len;
        }
        
        let header = TcpHeader {
            source_port,
            dest_port,
            sequence_number,
            acknowledgment_number,
            data_offset,
            flags,
            window_size,
            checksum,
            urgent_pointer,
            options,
        };
        
        let payload = data[offset..].to_vec();
        
        Ok(Self {
            header,
            payload,
            checksum,
        })
    }
    
    fn calculate_checksum(&self) -> u16 {
        // TCP校验和计算
        let mut checksum = 0u32;
        
        // 伪头部
        checksum += self.header.source_port as u32;
        checksum += self.header.dest_port as u32;
        checksum += 6u32; // TCP协议号
        checksum += (20 + self.payload.len()) as u32;
        
        // 头部数据
        let header_data = self.serialize_header_without_checksum();
        for chunk in header_data.chunks(2) {
            if chunk.len() == 2 {
                checksum += u16::from_be_bytes([chunk[0], chunk[1]]) as u32;
            } else {
                checksum += (chunk[0] as u32) << 8;
            }
        }
        
        // 负载数据
        for chunk in self.payload.chunks(2) {
            if chunk.len() == 2 {
                checksum += u16::from_be_bytes([chunk[0], chunk[1]]) as u32;
            } else {
                checksum += (chunk[0] as u32) << 8;
            }
        }
        
        // 折叠校验和
        while checksum >> 16 != 0 {
            checksum = (checksum & 0xFFFF) + (checksum >> 16);
        }
        
        !checksum as u16
    }
}
```

### 3. 拥塞控制

#### 3.1 拥塞控制算法

```rust
// TCP拥塞控制实现
pub struct CongestionControl {
    state: CongestionState,
    window_size: u32,
    threshold: u32,
    round_trip_time: Duration,
    retransmission_timeout: Duration,
}

#[derive(Debug, Clone)]
pub enum CongestionState {
    SlowStart,
    CongestionAvoidance,
    FastRetransmit,
    FastRecovery,
}

impl CongestionControl {
    pub fn new() -> Self {
        Self {
            state: CongestionState::SlowStart,
            window_size: 1,
            threshold: 65535,
            round_trip_time: Duration::from_millis(100),
            retransmission_timeout: Duration::from_millis(200),
        }
    }
    
    pub fn on_packet_sent(&mut self, packet_size: usize) {
        match self.state {
            CongestionState::SlowStart => {
                self.window_size += packet_size as u32;
                if self.window_size >= self.threshold {
                    self.state = CongestionState::CongestionAvoidance;
                }
            }
            CongestionState::CongestionAvoidance => {
                self.window_size += (packet_size as u32 * packet_size as u32) / self.window_size;
            }
            CongestionState::FastRetransmit => {
                // 在快速重传状态下不增加窗口
            }
            CongestionState::FastRecovery => {
                // 在快速恢复状态下不增加窗口
            }
        }
    }
    
    pub fn on_packet_loss(&mut self) {
        match self.state {
            CongestionState::SlowStart | CongestionState::CongestionAvoidance => {
                self.threshold = self.window_size / 2;
                self.window_size = 1;
                self.state = CongestionState::SlowStart;
            }
            CongestionState::FastRetransmit => {
                self.state = CongestionState::FastRecovery;
            }
            CongestionState::FastRecovery => {
                // 已经在快速恢复状态
            }
        }
    }
    
    pub fn on_duplicate_ack(&mut self) {
        match self.state {
            CongestionState::SlowStart | CongestionState::CongestionAvoidance => {
                self.state = CongestionState::FastRetransmit;
            }
            CongestionState::FastRetransmit => {
                self.state = CongestionState::FastRecovery;
            }
            CongestionState::FastRecovery => {
                self.window_size += 1;
            }
        }
    }
    
    pub fn on_new_ack(&mut self) {
        match self.state {
            CongestionState::FastRecovery => {
                self.window_size = self.threshold;
                self.state = CongestionState::CongestionAvoidance;
            }
            _ => {}
        }
    }
    
    pub fn get_window_size(&self) -> u32 {
        self.window_size
    }
    
    pub fn get_threshold(&self) -> u32 {
        self.threshold
    }
}
```

### 4. 错误处理

#### 4.1 错误类型定义

```rust
// TCP错误处理
#[derive(Debug, thiserror::Error)]
pub enum TcpError {
    #[error("连接未建立")]
    ConnectionNotEstablished,
    
    #[error("无效的数据包大小: {0}")]
    InvalidPacketSize(usize),
    
    #[error("无效的状态转换: {from:?} -> {to:?}")]
    InvalidTransition { from: TcpState, to: TcpState },
    
    #[error("校验和错误: 期望 {expected}, 实际 {actual}")]
    ChecksumError { expected: u16, actual: u16 },
    
    #[error("序列号错误: 期望 {expected}, 实际 {actual}")]
    SequenceNumberError { expected: u32, actual: u32 },
    
    #[error("窗口大小错误: {0}")]
    WindowSizeError(u16),
    
    #[error("超时错误: {timeout:?}")]
    TimeoutError { timeout: Duration },
    
    #[error("缓冲区满")]
    BufferFull,
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("协议错误: {0}")]
    ProtocolError(String),
}

impl TcpError {
    pub fn is_recoverable(&self) -> bool {
        match self {
            TcpError::TimeoutError { .. } => true,
            TcpError::IoError(_) => true,
            TcpError::BufferFull => true,
            _ => false,
        }
    }
    
    pub fn should_retry(&self) -> bool {
        match self {
            TcpError::TimeoutError { .. } => true,
            TcpError::IoError(_) => true,
            _ => false,
        }
    }
}
```

## 🌐 HTTP协议实现

### 1. 请求处理

#### 1.1 HTTP请求结构

```rust
// HTTP请求实现
#[derive(Debug, Clone)]
pub struct HttpRequest {
    method: HttpMethod,
    uri: String,
    version: HttpVersion,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Head,
    Options,
    Patch,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HttpVersion {
    Http1_0,
    Http1_1,
    Http2_0,
}

impl HttpRequest {
    pub fn new(method: HttpMethod, uri: String, version: HttpVersion) -> Self {
        Self {
            method,
            uri,
            version,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
    
    pub fn add_header(&mut self, name: String, value: String) {
        self.headers.insert(name.to_lowercase(), value);
    }
    
    pub fn get_header(&self, name: &str) -> Option<&String> {
        self.headers.get(&name.to_lowercase())
    }
    
    pub fn set_body(&mut self, body: Vec<u8>) {
        self.body = body;
        self.add_header("content-length".to_string(), body.len().to_string());
    }
    
    pub fn serialize(&self) -> Vec<u8> {
        let mut data = Vec::new();
        
        // 请求行
        let request_line = format!("{} {} {}\r\n", 
            self.method.to_string(), 
            self.uri, 
            self.version.to_string()
        );
        data.extend_from_slice(request_line.as_bytes());
        
        // 头部
        for (name, value) in &self.headers {
            let header_line = format!("{}: {}\r\n", name, value);
            data.extend_from_slice(header_line.as_bytes());
        }
        
        // 空行
        data.extend_from_slice(b"\r\n");
        
        // 主体
        data.extend_from_slice(&self.body);
        
        data
    }
    
    pub fn deserialize(data: &[u8]) -> Result<Self, HttpError> {
        let mut lines = data.split(|&b| b == b'\n');
        
        // 解析请求行
        let request_line = lines.next()
            .ok_or(HttpError::InvalidRequest)?;
        let request_line = std::str::from_utf8(request_line)
            .map_err(|_| HttpError::InvalidEncoding)?;
        
        let parts: Vec<&str> = request_line.trim().split_whitespace().collect();
        if parts.len() != 3 {
            return Err(HttpError::InvalidRequest);
        }
        
        let method = HttpMethod::from_str(parts[0])?;
        let uri = parts[1].to_string();
        let version = HttpVersion::from_str(parts[2])?;
        
        let mut request = HttpRequest::new(method, uri, version);
        
        // 解析头部
        for line in lines {
            let line = std::str::from_utf8(line)
                .map_err(|_| HttpError::InvalidEncoding)?;
            let line = line.trim();
            
            if line.is_empty() {
                break;
            }
            
            if let Some((name, value)) = line.split_once(':') {
                request.add_header(name.trim().to_string(), value.trim().to_string());
            }
        }
        
        // 解析主体
        let body_start = data.windows(4).position(|w| w == b"\r\n\r\n")
            .ok_or(HttpError::InvalidRequest)? + 4;
        request.body = data[body_start..].to_vec();
        
        Ok(request)
    }
}
```

### 2. 响应生成

#### 2.1 HTTP响应结构

```rust
// HTTP响应实现
#[derive(Debug, Clone)]
pub struct HttpResponse {
    version: HttpVersion,
    status_code: u16,
    reason_phrase: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

impl HttpResponse {
    pub fn new(version: HttpVersion, status_code: u16, reason_phrase: String) -> Self {
        Self {
            version,
            status_code,
            reason_phrase,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
    
    pub fn ok() -> Self {
        Self::new(HttpVersion::Http1_1, 200, "OK".to_string())
    }
    
    pub fn not_found() -> Self {
        Self::new(HttpVersion::Http1_1, 404, "Not Found".to_string())
    }
    
    pub fn internal_server_error() -> Self {
        Self::new(HttpVersion::Http1_1, 500, "Internal Server Error".to_string())
    }
    
    pub fn add_header(&mut self, name: String, value: String) {
        self.headers.insert(name.to_lowercase(), value);
    }
    
    pub fn get_header(&self, name: &str) -> Option<&String> {
        self.headers.get(&name.to_lowercase())
    }
    
    pub fn set_body(&mut self, body: Vec<u8>) {
        self.body = body;
        self.add_header("content-length".to_string(), self.body.len().to_string());
    }
    
    pub fn set_json_body(&mut self, data: &serde_json::Value) -> Result<(), HttpError> {
        let json_str = serde_json::to_string(data)
            .map_err(|_| HttpError::SerializationError)?;
        self.set_body(json_str.into_bytes());
        self.add_header("content-type".to_string(), "application/json".to_string());
        Ok(())
    }
    
    pub fn serialize(&self) -> Vec<u8> {
        let mut data = Vec::new();
        
        // 状态行
        let status_line = format!("{} {} {}\r\n", 
            self.version.to_string(), 
            self.status_code, 
            self.reason_phrase
        );
        data.extend_from_slice(status_line.as_bytes());
        
        // 头部
        for (name, value) in &self.headers {
            let header_line = format!("{}: {}\r\n", name, value);
            data.extend_from_slice(header_line.as_bytes());
        }
        
        // 空行
        data.extend_from_slice(b"\r\n");
        
        // 主体
        data.extend_from_slice(&self.body);
        
        data
    }
}
```

### 3. 头部管理

#### 3.1 HTTP头部处理

```rust
// HTTP头部管理
pub struct HttpHeaderManager {
    headers: HashMap<String, String>,
    case_sensitive: bool,
}

impl HttpHeaderManager {
    pub fn new() -> Self {
        Self {
            headers: HashMap::new(),
            case_sensitive: false,
        }
    }
    
    pub fn add_header(&mut self, name: String, value: String) {
        let key = if self.case_sensitive {
            name
        } else {
            name.to_lowercase()
        };
        self.headers.insert(key, value);
    }
    
    pub fn get_header(&self, name: &str) -> Option<&String> {
        let key = if self.case_sensitive {
            name.to_string()
        } else {
            name.to_lowercase()
        };
        self.headers.get(&key)
    }
    
    pub fn remove_header(&mut self, name: &str) -> Option<String> {
        let key = if self.case_sensitive {
            name.to_string()
        } else {
            name.to_lowercase()
        };
        self.headers.remove(&key)
    }
    
    pub fn has_header(&self, name: &str) -> bool {
        let key = if self.case_sensitive {
            name.to_string()
        } else {
            name.to_lowercase()
        };
        self.headers.contains_key(&key)
    }
    
    pub fn get_content_length(&self) -> Option<usize> {
        self.get_header("content-length")
            .and_then(|v| v.parse().ok())
    }
    
    pub fn get_content_type(&self) -> Option<&String> {
        self.get_header("content-type")
    }
    
    pub fn get_connection(&self) -> Option<&String> {
        self.get_header("connection")
    }
    
    pub fn is_keep_alive(&self) -> bool {
        self.get_connection()
            .map(|v| v.to_lowercase() == "keep-alive")
            .unwrap_or(false)
    }
    
    pub fn set_content_length(&mut self, length: usize) {
        self.add_header("content-length".to_string(), length.to_string());
    }
    
    pub fn set_content_type(&mut self, content_type: String) {
        self.add_header("content-type".to_string(), content_type);
    }
    
    pub fn set_keep_alive(&mut self, keep_alive: bool) {
        let value = if keep_alive {
            "keep-alive"
        } else {
            "close"
        };
        self.add_header("connection".to_string(), value.to_string());
    }
}
```

### 4. 连接管理

#### 4.1 HTTP连接池

```rust
// HTTP连接管理
pub struct HttpConnectionPool {
    connections: HashMap<SocketAddr, Vec<HttpConnection>>,
    max_connections_per_host: usize,
    max_idle_time: Duration,
    keep_alive_timeout: Duration,
}

pub struct HttpConnection {
    stream: TcpStream,
    last_used: Instant,
    is_idle: bool,
    host: String,
    port: u16,
}

impl HttpConnectionPool {
    pub fn new() -> Self {
        Self {
            connections: HashMap::new(),
            max_connections_per_host: 10,
            max_idle_time: Duration::from_secs(30),
            keep_alive_timeout: Duration::from_secs(60),
        }
    }
    
    pub async fn get_connection(&mut self, host: &str, port: u16) -> Result<HttpConnection, HttpError> {
        let addr = SocketAddr::new(host.parse()?, port);
        
        // 查找空闲连接
        if let Some(connections) = self.connections.get_mut(&addr) {
            for (i, conn) in connections.iter_mut().enumerate() {
                if conn.is_idle && conn.last_used.elapsed() < self.max_idle_time {
                    conn.is_idle = false;
                    conn.last_used = Instant::now();
                    return Ok(connections.remove(i));
                }
            }
        }
        
        // 创建新连接
        let stream = TcpStream::connect(addr).await?;
        Ok(HttpConnection {
            stream,
            last_used: Instant::now(),
            is_idle: false,
            host: host.to_string(),
            port,
        })
    }
    
    pub fn return_connection(&mut self, mut connection: HttpConnection) {
        let addr = SocketAddr::new(connection.host.parse().unwrap(), connection.port);
        
        connection.is_idle = true;
        connection.last_used = Instant::now();
        
        self.connections.entry(addr)
            .or_insert_with(Vec::new)
            .push(connection);
    }
    
    pub fn cleanup_idle_connections(&mut self) {
        let now = Instant::now();
        
        for connections in self.connections.values_mut() {
            connections.retain(|conn| {
                !conn.is_idle || now.duration_since(conn.last_used) < self.max_idle_time
            });
        }
    }
}
```

## 🔌 WebSocket协议实现

### 1. 握手处理

#### 1.1 WebSocket握手

```rust
// WebSocket握手实现
pub struct WebSocketHandshake {
    request: HttpRequest,
    response: HttpResponse,
    key: String,
    accept_key: String,
}

impl WebSocketHandshake {
    pub fn new(request: HttpRequest) -> Result<Self, WebSocketError> {
        // 验证请求
        Self::validate_request(&request)?;
        
        // 提取密钥
        let key = request.get_header("sec-websocket-key")
            .ok_or(WebSocketError::MissingKey)?;
        
        // 生成接受密钥
        let accept_key = Self::generate_accept_key(key)?;
        
        Ok(Self {
            request,
            response: HttpResponse::new(HttpVersion::Http1_1, 101, "Switching Protocols".to_string()),
            key: key.clone(),
            accept_key,
        })
    }
    
    fn validate_request(request: &HttpRequest) -> Result<(), WebSocketError> {
        // 检查方法
        if request.method != HttpMethod::Get {
            return Err(WebSocketError::InvalidMethod);
        }
        
        // 检查版本
        if request.version != HttpVersion::Http1_1 {
            return Err(WebSocketError::InvalidVersion);
        }
        
        // 检查必需的头部
        if !request.has_header("upgrade") {
            return Err(WebSocketError::MissingUpgrade);
        }
        
        if !request.has_header("connection") {
            return Err(WebSocketError::MissingConnection);
        }
        
        if !request.has_header("sec-websocket-key") {
            return Err(WebSocketError::MissingKey);
        }
        
        if !request.has_header("sec-websocket-version") {
            return Err(WebSocketError::MissingVersion);
        }
        
        // 检查头部值
        if request.get_header("upgrade").unwrap().to_lowercase() != "websocket" {
            return Err(WebSocketError::InvalidUpgrade);
        }
        
        if !request.get_header("connection").unwrap().to_lowercase().contains("upgrade") {
            return Err(WebSocketError::InvalidConnection);
        }
        
        if request.get_header("sec-websocket-version").unwrap() != "13" {
            return Err(WebSocketError::InvalidWebSocketVersion);
        }
        
        Ok(())
    }
    
    fn generate_accept_key(key: &str) -> Result<String, WebSocketError> {
        use sha1::{Sha1, Digest};
        use base64::Engine;
        
        let mut hasher = Sha1::new();
        hasher.update(key.as_bytes());
        hasher.update(b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11");
        let hash = hasher.finalize();
        
        Ok(base64::engine::general_purpose::STANDARD.encode(hash))
    }
    
    pub fn generate_response(&mut self) -> HttpResponse {
        self.response.add_header("upgrade".to_string(), "websocket".to_string());
        self.response.add_header("connection".to_string(), "upgrade".to_string());
        self.response.add_header("sec-websocket-accept".to_string(), self.accept_key.clone());
        
        self.response.clone()
    }
}
```

### 2. 帧处理

#### 2.1 WebSocket帧结构

```rust
// WebSocket帧实现
#[derive(Debug, Clone)]
pub struct WebSocketFrame {
    fin: bool,
    rsv1: bool,
    rsv2: bool,
    rsv3: bool,
    opcode: OpCode,
    mask: bool,
    payload_length: u64,
    masking_key: Option<[u8; 4]>,
    payload: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OpCode {
    Continuation = 0,
    Text = 1,
    Binary = 2,
    Close = 8,
    Ping = 9,
    Pong = 10,
}

impl WebSocketFrame {
    pub fn new(opcode: OpCode, payload: Vec<u8>) -> Self {
        Self {
            fin: true,
            rsv1: false,
            rsv2: false,
            rsv3: false,
            opcode,
            mask: false,
            payload_length: payload.len() as u64,
            masking_key: None,
            payload,
        }
    }
    
    pub fn text_frame(text: &str) -> Self {
        Self::new(OpCode::Text, text.as_bytes().to_vec())
    }
    
    pub fn binary_frame(data: Vec<u8>) -> Self {
        Self::new(OpCode::Binary, data)
    }
    
    pub fn close_frame(code: u16, reason: &str) -> Self {
        let mut payload = Vec::new();
        payload.extend_from_slice(&code.to_be_bytes());
        payload.extend_from_slice(reason.as_bytes());
        Self::new(OpCode::Close, payload)
    }
    
    pub fn ping_frame(data: Vec<u8>) -> Self {
        Self::new(OpCode::Ping, data)
    }
    
    pub fn pong_frame(data: Vec<u8>) -> Self {
        Self::new(OpCode::Pong, data)
    }
    
    pub fn serialize(&self) -> Vec<u8> {
        let mut data = Vec::new();
        
        // 第一个字节
        let mut first_byte = 0u8;
        if self.fin { first_byte |= 0x80; }
        if self.rsv1 { first_byte |= 0x40; }
        if self.rsv2 { first_byte |= 0x20; }
        if self.rsv3 { first_byte |= 0x10; }
        first_byte |= self.opcode as u8;
        data.push(first_byte);
        
        // 第二个字节
        let mut second_byte = 0u8;
        if self.mask { second_byte |= 0x80; }
        
        if self.payload_length < 126 {
            second_byte |= self.payload_length as u8;
            data.push(second_byte);
        } else if self.payload_length < 65536 {
            second_byte |= 126;
            data.push(second_byte);
            data.extend_from_slice(&(self.payload_length as u16).to_be_bytes());
        } else {
            second_byte |= 127;
            data.push(second_byte);
            data.extend_from_slice(&self.payload_length.to_be_bytes());
        }
        
        // 掩码密钥
        if self.mask {
            if let Some(key) = self.masking_key {
                data.extend_from_slice(&key);
            }
        }
        
        // 负载
        let mut payload = self.payload.clone();
        if self.mask {
            if let Some(key) = self.masking_key {
                for (i, byte) in payload.iter_mut().enumerate() {
                    *byte ^= key[i % 4];
                }
            }
        }
        data.extend_from_slice(&payload);
        
        data
    }
    
    pub fn deserialize(data: &[u8]) -> Result<Self, WebSocketError> {
        if data.len() < 2 {
            return Err(WebSocketError::InsufficientData);
        }
        
        let mut offset = 0;
        
        // 第一个字节
        let first_byte = data[offset];
        offset += 1;
        
        let fin = (first_byte & 0x80) != 0;
        let rsv1 = (first_byte & 0x40) != 0;
        let rsv2 = (first_byte & 0x20) != 0;
        let rsv3 = (first_byte & 0x10) != 0;
        let opcode = OpCode::from_u8(first_byte & 0x0F)?;
        
        // 第二个字节
        let second_byte = data[offset];
        offset += 1;
        
        let mask = (second_byte & 0x80) != 0;
        let payload_length = second_byte & 0x7F;
        
        let payload_length = match payload_length {
            0..=125 => payload_length as u64,
            126 => {
                if data.len() < offset + 2 {
                    return Err(WebSocketError::InsufficientData);
                }
                let length = u16::from_be_bytes([data[offset], data[offset + 1]]);
                offset += 2;
                length as u64
            }
            127 => {
                if data.len() < offset + 8 {
                    return Err(WebSocketError::InsufficientData);
                }
                let length = u64::from_be_bytes([
                    data[offset], data[offset + 1], data[offset + 2], data[offset + 3],
                    data[offset + 4], data[offset + 5], data[offset + 6], data[offset + 7]
                ]);
                offset += 8;
                length
            }
            _ => return Err(WebSocketError::InvalidPayloadLength),
        };
        
        // 掩码密钥
        let masking_key = if mask {
            if data.len() < offset + 4 {
                return Err(WebSocketError::InsufficientData);
            }
            let key = [
                data[offset], data[offset + 1], data[offset + 2], data[offset + 3]
            ];
            offset += 4;
            Some(key)
        } else {
            None
        };
        
        // 负载
        if data.len() < offset + payload_length as usize {
            return Err(WebSocketError::InsufficientData);
        }
        
        let mut payload = data[offset..offset + payload_length as usize].to_vec();
        
        // 应用掩码
        if mask {
            if let Some(key) = masking_key {
                for (i, byte) in payload.iter_mut().enumerate() {
                    *byte ^= key[i % 4];
                }
            }
        }
        
        Ok(Self {
            fin,
            rsv1,
            rsv2,
            rsv3,
            opcode,
            mask,
            payload_length,
            masking_key,
            payload,
        })
    }
}
```

## 🔗 相关文档

- [网络通信理论](NETWORK_COMMUNICATION_THEORY.md) - 网络通信的理论基础
- [数学基础](MATHEMATICAL_FOUNDATIONS.md) - 网络编程的数学基础
- [网络通信概念](NETWORK_COMMUNICATION_CONCEPTS.md) - 网络通信概念详解
- [形式化证明](FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md) - 形式化证明和数学论证
- [示例与应用场景](EXAMPLES_AND_APPLICATION_SCENARIOS.md) - 实际应用示例
- [网络理论与通信机制](NETWORK_THEORY_AND_COMMUNICATION_MECHANISMS.md) - 网络理论和通信机制
- [性能优化指南](PERFORMANCE_OPTIMIZATION_GUIDE.md) - 性能优化的详细指导
- [API文档](API_DOCUMENTATION.md) - API接口的详细说明

---

**C10 Networks 协议实现指南** - 从理论到实践的网络协议实现！

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
