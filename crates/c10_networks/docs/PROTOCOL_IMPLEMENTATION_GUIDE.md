# C10 Networks 协议实现指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [C10 Networks 协议实现指南](#c10-networks-协议实现指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔧 协议实现架构](#-协议实现架构)
    - [核心设计原则](#核心设计原则)
    - [协议栈架构](#协议栈架构)
  - [📡 TCP协议实现](#-tcp协议实现)
    - [TCP状态机](#tcp状态机)
    - [TCP数据包处理](#tcp数据包处理)
  - [🌐 HTTP协议实现](#-http协议实现)
    - [HTTP请求/响应](#http请求响应)
    - [HTTP客户端实现](#http客户端实现)
  - [🔌 WebSocket协议实现](#-websocket协议实现)
    - [WebSocket握手](#websocket握手)
    - [WebSocket帧处理](#websocket帧处理)
  - [🔍 DNS协议实现](#-dns协议实现)
    - [DNS查询](#dns查询)
  - [🔒 TLS协议实现](#-tls协议实现)
    - [TLS握手](#tls握手)
  - [⚡ 性能优化](#-性能优化)
    - [零拷贝优化](#零拷贝优化)
    - [连接池优化](#连接池优化)
  - [🧪 测试策略](#-测试策略)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
  - [📚 参考资源](#-参考资源)

## 🎯 概述

本指南详细介绍了C10 Networks中各种网络协议的实现方法，包括设计原理、代码实现、性能优化和测试策略。

## 🔧 协议实现架构

### 核心设计原则

1. **模块化设计**: 每个协议独立实现，便于维护和测试
2. **异步优先**: 基于Tokio的异步I/O，提高并发性能
3. **类型安全**: 利用Rust类型系统保证协议正确性
4. **错误处理**: 统一的错误处理机制
5. **可扩展性**: 支持协议扩展和自定义实现

### 协议栈架构

```rust
// 协议栈核心结构
pub struct ProtocolStack {
    // 应用层协议
    application_layer: ApplicationLayer,
    // 传输层协议
    transport_layer: TransportLayer,
    // 网络层协议
    network_layer: NetworkLayer,
    // 数据链路层协议
    link_layer: LinkLayer,
}

// 协议处理接口
pub trait ProtocolHandler {
    type Message;
    type Error;
    
    async fn handle_message(&mut self, message: Self::Message) -> Result<(), Self::Error>;
    async fn send_message(&mut self, message: Self::Message) -> Result<(), Self::Error>;
}
```

## 📡 TCP协议实现

### TCP状态机

```rust
// TCP状态定义
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcpState {
    CLOSED,
    LISTEN,
    SYN_SENT,
    SYN_RECEIVED,
    ESTABLISHED,
    FIN_WAIT_1,
    FIN_WAIT_2,
    CLOSE_WAIT,
    LAST_ACK,
    TIME_WAIT,
}

// TCP连接
pub struct TcpConnection {
    state: TcpState,
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    seq_num: u32,
    ack_num: u32,
    window_size: u16,
    send_buffer: VecDeque<u8>,
    recv_buffer: VecDeque<u8>,
}

impl TcpConnection {
    // 状态转换
    pub fn transition(&mut self, event: TcpEvent) -> NetworkResult<()> {
        match (&self.state, event) {
            (TcpState::CLOSED, TcpEvent::PassiveOpen) => {
                self.state = TcpState::LISTEN;
                Ok(())
            }
            (TcpState::CLOSED, TcpEvent::ActiveOpen) => {
                self.state = TcpState::SYN_SENT;
                self.send_syn().await?;
                Ok(())
            }
            (TcpState::SYN_SENT, TcpEvent::SynAckReceived) => {
                self.state = TcpState::ESTABLISHED;
                self.send_ack().await?;
                Ok(())
            }
            // 其他状态转换...
            _ => Err(NetworkError::InvalidTransition),
        }
    }
}
```

### TCP数据包处理

```rust
// TCP数据包
pub struct TcpPacket {
    source_port: u16,
    dest_port: u16,
    seq_num: u32,
    ack_num: u32,
    flags: TcpFlags,
    window_size: u16,
    checksum: u16,
    data: Vec<u8>,
}

// TCP数据包处理
impl TcpPacket {
    pub fn parse(data: &[u8]) -> NetworkResult<Self> {
        if data.len() < 20 {
            return Err(NetworkError::InvalidPacket);
        }
        
        let source_port = u16::from_be_bytes([data[0], data[1]]);
        let dest_port = u16::from_be_bytes([data[2], data[3]]);
        let seq_num = u32::from_be_bytes([data[4], data[5], data[6], data[7]]);
        let ack_num = u32::from_be_bytes([data[8], data[9], data[10], data[11]]);
        
        // 解析其他字段...
        
        Ok(TcpPacket {
            source_port,
            dest_port,
            seq_num,
            ack_num,
            flags: TcpFlags::from_byte(data[13]),
            window_size: u16::from_be_bytes([data[14], data[15]]),
            checksum: u16::from_be_bytes([data[16], data[17]]),
            data: data[20..].to_vec(),
        })
    }
    
    pub fn serialize(&self) -> Vec<u8> {
        let mut packet = Vec::new();
        
        packet.extend_from_slice(&self.source_port.to_be_bytes());
        packet.extend_from_slice(&self.dest_port.to_be_bytes());
        packet.extend_from_slice(&self.seq_num.to_be_bytes());
        packet.extend_from_slice(&self.ack_num.to_be_bytes());
        
        // 序列化其他字段...
        
        packet
    }
}
```

## 🌐 HTTP协议实现

### HTTP请求/响应

```rust
// HTTP请求
pub struct HttpRequest {
    method: HttpMethod,
    uri: String,
    version: HttpVersion,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

// HTTP响应
pub struct HttpResponse {
    version: HttpVersion,
    status: HttpStatusCode,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

impl HttpRequest {
    pub fn parse(data: &[u8]) -> NetworkResult<Self> {
        let lines: Vec<&str> = std::str::from_utf8(data)?
            .lines()
            .collect();
        
        if lines.is_empty() {
            return Err(NetworkError::InvalidRequest);
        }
        
        // 解析请求行
        let request_line: Vec<&str> = lines[0].split_whitespace().collect();
        if request_line.len() != 3 {
            return Err(NetworkError::InvalidRequest);
        }
        
        let method = HttpMethod::from_str(request_line[0])?;
        let uri = request_line[1].to_string();
        let version = HttpVersion::from_str(request_line[2])?;
        
        // 解析头部
        let mut headers = HashMap::new();
        let mut body_start = 0;
        
        for (i, line) in lines.iter().enumerate().skip(1) {
            if line.is_empty() {
                body_start = i + 1;
                break;
            }
            
            if let Some((key, value)) = line.split_once(':') {
                headers.insert(key.trim().to_string(), value.trim().to_string());
            }
        }
        
        // 解析正文
        let body = if body_start < lines.len() {
            lines[body_start..].join("\n").into_bytes()
        } else {
            Vec::new()
        };
        
        Ok(HttpRequest {
            method,
            uri,
            version,
            headers,
            body,
        })
    }
}
```

### HTTP客户端实现

```rust
// HTTP客户端
pub struct HttpClient {
    config: HttpConfig,
    connection_pool: ConnectionPool,
}

impl HttpClient {
    pub async fn get(&self, url: &str) -> NetworkResult<HttpResponse> {
        let request = HttpRequest {
            method: HttpMethod::GET,
            uri: url.to_string(),
            version: HttpVersion::Http1_1,
            headers: HashMap::new(),
            body: Vec::new(),
        };
        
        self.send_request(request).await
    }
    
    pub async fn post(&self, url: &str, data: &[u8]) -> NetworkResult<HttpResponse> {
        let mut headers = HashMap::new();
        headers.insert("Content-Length".to_string(), data.len().to_string());
        
        let request = HttpRequest {
            method: HttpMethod::POST,
            uri: url.to_string(),
            version: HttpVersion::Http1_1,
            headers,
            body: data.to_vec(),
        };
        
        self.send_request(request).await
    }
    
    async fn send_request(&self, request: HttpRequest) -> NetworkResult<HttpResponse> {
        // 获取连接
        let mut connection = self.connection_pool.get_connection(&request.uri).await?;
        
        // 发送请求
        let request_data = request.serialize();
        connection.write_all(&request_data).await?;
        
        // 读取响应
        let mut response_data = Vec::new();
        connection.read_to_end(&mut response_data).await?;
        
        // 解析响应
        HttpResponse::parse(&response_data)
    }
}
```

## 🔌 WebSocket协议实现

### WebSocket握手

```rust
// WebSocket握手
pub struct WebSocketHandshake {
    request: HttpRequest,
    response: HttpResponse,
}

impl WebSocketHandshake {
    pub async fn perform_handshake(
        &mut self,
        stream: &mut TcpStream,
    ) -> NetworkResult<()> {
        // 发送握手请求
        let request_data = self.request.serialize();
        stream.write_all(&request_data).await?;
        
        // 读取握手响应
        let mut response_data = Vec::new();
        stream.read_to_end(&mut response_data).await?;
        
        // 解析响应
        self.response = HttpResponse::parse(&response_data)?;
        
        // 验证握手
        self.validate_handshake()?;
        
        Ok(())
    }
    
    fn validate_handshake(&self) -> NetworkResult<()> {
        // 检查状态码
        if self.response.status != HttpStatusCode::SwitchingProtocols {
            return Err(NetworkError::HandshakeFailed);
        }
        
        // 检查Upgrade头
        if self.response.headers.get("Upgrade") != Some(&"websocket".to_string()) {
            return Err(NetworkError::HandshakeFailed);
        }
        
        // 检查Connection头
        if self.response.headers.get("Connection") != Some(&"Upgrade".to_string()) {
            return Err(NetworkError::HandshakeFailed);
        }
        
        // 验证Sec-WebSocket-Accept
        let expected_accept = self.calculate_accept_key();
        if self.response.headers.get("Sec-WebSocket-Accept") != Some(&expected_accept) {
            return Err(NetworkError::HandshakeFailed);
        }
        
        Ok(())
    }
}
```

### WebSocket帧处理

```rust
// WebSocket帧
pub struct WebSocketFrame {
    fin: bool,
    opcode: WebSocketOpcode,
    mask: bool,
    payload_len: u64,
    masking_key: Option<[u8; 4]>,
    payload: Vec<u8>,
}

impl WebSocketFrame {
    pub fn parse(data: &[u8]) -> NetworkResult<Self> {
        if data.len() < 2 {
            return Err(NetworkError::InvalidFrame);
        }
        
        let fin = (data[0] & 0x80) != 0;
        let opcode = WebSocketOpcode::from_u4(data[0] & 0x0F)?;
        let mask = (data[1] & 0x80) != 0;
        
        let mut payload_len = (data[1] & 0x7F) as u64;
        let mut offset = 2;
        
        // 解析负载长度
        if payload_len == 126 {
            if data.len() < offset + 2 {
                return Err(NetworkError::InvalidFrame);
            }
            payload_len = u16::from_be_bytes([data[offset], data[offset + 1]]) as u64;
            offset += 2;
        } else if payload_len == 127 {
            if data.len() < offset + 8 {
                return Err(NetworkError::InvalidFrame);
            }
            payload_len = u64::from_be_bytes([
                data[offset], data[offset + 1], data[offset + 2], data[offset + 3],
                data[offset + 4], data[offset + 5], data[offset + 6], data[offset + 7],
            ]);
            offset += 8;
        }
        
        // 解析掩码
        let masking_key = if mask {
            if data.len() < offset + 4 {
                return Err(NetworkError::InvalidFrame);
            }
            let key = [
                data[offset], data[offset + 1], data[offset + 2], data[offset + 3],
            ];
            offset += 4;
            Some(key)
        } else {
            None
        };
        
        // 解析负载
        if data.len() < offset + payload_len as usize {
            return Err(NetworkError::InvalidFrame);
        }
        
        let mut payload = data[offset..offset + payload_len as usize].to_vec();
        
        // 应用掩码
        if let Some(key) = masking_key {
            for (i, byte) in payload.iter_mut().enumerate() {
                *byte ^= key[i % 4];
            }
        }
        
        Ok(WebSocketFrame {
            fin,
            opcode,
            mask,
            payload_len,
            masking_key,
            payload,
        })
    }
}
```

## 🔍 DNS协议实现

### DNS查询

```rust
// DNS查询
pub struct DnsQuery {
    id: u16,
    flags: DnsFlags,
    questions: Vec<DnsQuestion>,
    answers: Vec<DnsRecord>,
    authorities: Vec<DnsRecord>,
    additional: Vec<DnsRecord>,
}

// DNS问题
pub struct DnsQuestion {
    name: String,
    record_type: DnsRecordType,
    class: DnsClass,
}

impl DnsQuery {
    pub fn parse(data: &[u8]) -> NetworkResult<Self> {
        if data.len() < 12 {
            return Err(NetworkError::InvalidPacket);
        }
        
        let id = u16::from_be_bytes([data[0], data[1]]);
        let flags = DnsFlags::from_bytes([data[2], data[3]]);
        
        let question_count = u16::from_be_bytes([data[4], data[5]]);
        let answer_count = u16::from_be_bytes([data[6], data[7]]);
        let authority_count = u16::from_be_bytes([data[8], data[9]]);
        let additional_count = u16::from_be_bytes([data[10], data[11]]);
        
        let mut offset = 12;
        
        // 解析问题
        let mut questions = Vec::new();
        for _ in 0..question_count {
            let (question, new_offset) = DnsQuestion::parse(&data[offset..])?;
            questions.push(question);
            offset = new_offset;
        }
        
        // 解析答案
        let mut answers = Vec::new();
        for _ in 0..answer_count {
            let (record, new_offset) = DnsRecord::parse(&data[offset..])?;
            answers.push(record);
            offset = new_offset;
        }
        
        Ok(DnsQuery {
            id,
            flags,
            questions,
            answers,
            authorities: Vec::new(),
            additional: Vec::new(),
        })
    }
}
```

## 🔒 TLS协议实现

### TLS握手

```rust
// TLS握手
pub struct TlsHandshake {
    client_random: [u8; 32],
    server_random: [u8; 32],
    cipher_suite: CipherSuite,
    session_id: Vec<u8>,
    certificates: Vec<Certificate>,
}

impl TlsHandshake {
    pub async fn perform_handshake(
        &mut self,
        stream: &mut TcpStream,
    ) -> NetworkResult<()> {
        // 发送ClientHello
        let client_hello = self.create_client_hello();
        self.send_handshake_message(stream, &client_hello).await?;
        
        // 接收ServerHello
        let server_hello = self.receive_handshake_message(stream).await?;
        self.process_server_hello(server_hello)?;
        
        // 接收Certificate
        let certificate = self.receive_handshake_message(stream).await?;
        self.process_certificate(certificate)?;
        
        // 接收ServerHelloDone
        let server_hello_done = self.receive_handshake_message(stream).await?;
        self.process_server_hello_done(server_hello_done)?;
        
        // 发送ClientKeyExchange
        let client_key_exchange = self.create_client_key_exchange();
        self.send_handshake_message(stream, &client_key_exchange).await?;
        
        // 发送ChangeCipherSpec
        self.send_change_cipher_spec(stream).await?;
        
        // 发送Finished
        let finished = self.create_finished();
        self.send_handshake_message(stream, &finished).await?;
        
        // 接收ChangeCipherSpec
        self.receive_change_cipher_spec(stream).await?;
        
        // 接收Finished
        let server_finished = self.receive_handshake_message(stream).await?;
        self.process_finished(server_finished)?;
        
        Ok(())
    }
}
```

## ⚡ 性能优化

### 零拷贝优化

```rust
// 零拷贝缓冲区
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    read_pos: usize,
    write_pos: usize,
}

impl ZeroCopyBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity],
            read_pos: 0,
            write_pos: 0,
        }
    }
    
    pub fn write(&mut self, data: &[u8]) -> NetworkResult<usize> {
        let available = self.data.len() - self.write_pos;
        let to_write = data.len().min(available);
        
        if to_write > 0 {
            self.data[self.write_pos..self.write_pos + to_write].copy_from_slice(&data[..to_write]);
            self.write_pos += to_write;
        }
        
        Ok(to_write)
    }
    
    pub fn read(&mut self, buf: &mut [u8]) -> NetworkResult<usize> {
        let available = self.write_pos - self.read_pos;
        let to_read = buf.len().min(available);
        
        if to_read > 0 {
            buf[..to_read].copy_from_slice(&self.data[self.read_pos..self.read_pos + to_read]);
            self.read_pos += to_read;
        }
        
        Ok(to_read)
    }
}
```

### 连接池优化

```rust
// 连接池
pub struct ConnectionPool {
    connections: HashMap<String, VecDeque<Connection>>,
    max_connections_per_host: usize,
    max_idle_time: Duration,
}

impl ConnectionPool {
    pub async fn get_connection(&mut self, uri: &str) -> NetworkResult<Connection> {
        let host = self.extract_host(uri)?;
        
        if let Some(connections) = self.connections.get_mut(&host) {
            while let Some(connection) = connections.pop_front() {
                if connection.is_healthy() {
                    return Ok(connection);
                }
            }
        }
        
        // 创建新连接
        let connection = self.create_connection(&host).await?;
        Ok(connection)
    }
    
    pub fn return_connection(&mut self, uri: &str, connection: Connection) {
        let host = self.extract_host(uri).unwrap();
        
        if let Some(connections) = self.connections.get_mut(&host) {
            if connections.len() < self.max_connections_per_host {
                connections.push_back(connection);
            }
        }
    }
}
```

## 🧪 测试策略

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_tcp_connection_establishment() {
        let mut connection = TcpConnection::new();
        
        // 测试主动打开
        connection.transition(TcpEvent::ActiveOpen).await.unwrap();
        assert_eq!(connection.state, TcpState::SYN_SENT);
        
        // 测试接收SYN-ACK
        connection.transition(TcpEvent::SynAckReceived).await.unwrap();
        assert_eq!(connection.state, TcpState::ESTABLISHED);
    }
    
    #[test]
    fn test_http_request_parsing() {
        let request_data = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";
        let request = HttpRequest::parse(request_data).unwrap();
        
        assert_eq!(request.method, HttpMethod::GET);
        assert_eq!(request.uri, "/");
        assert_eq!(request.version, HttpVersion::Http1_1);
        assert_eq!(request.headers.get("Host"), Some(&"example.com".to_string()));
    }
}
```

### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    
    #[tokio::test]
    async fn test_http_client_server() {
        // 启动测试服务器
        let server = TestHttpServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 创建客户端
        let client = HttpClient::new();
        
        // 发送请求
        let response = client.get(&format!("http://{}", server_addr)).await.unwrap();
        
        assert_eq!(response.status, HttpStatusCode::OK);
    }
}
```

## 📚 参考资源

1. [RFC 793 - Transmission Control Protocol](https://tools.ietf.org/html/rfc793)
2. [RFC 2616 - Hypertext Transfer Protocol](https://tools.ietf.org/html/rfc2616)
3. [RFC 6455 - The WebSocket Protocol](https://tools.ietf.org/html/rfc6455)
4. [RFC 1035 - Domain Names](https://tools.ietf.org/html/rfc1035)
5. [RFC 8446 - The Transport Layer Security Protocol](https://tools.ietf.org/html/rfc8446)

---

**协议实现指南版本**: v1.0  
**最后更新**: 2025年1月  
**维护者**: C10 Networks 开发团队
