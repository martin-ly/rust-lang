# Rust网络编程理论

## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: 2025-08-11  
**最后更新**: 2025-08-11  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---



**版本**: 1.0.0  
**维护者**: Rust语言形式化理论项目组  
**最后更新**: 2025-01-27  
**主题**: 网络编程理论与实现

## 1. 理论基础

### 1.1 网络编程本质

网络编程是构建分布式系统的核心技术，涉及网络协议、数据传输、连接管理等底层网络功能。

**数学定义**:

```
network_programming ::= protocol_stack + socket_interface + data_transmission
socket ::= endpoint + protocol + address_family
connection ::= client_socket + server_socket + data_channel
```

### 1.2 网络协议栈理论

网络协议栈定义了数据在网络中传输的规则和格式。

**OSI七层模型**:

```
应用层 (Application Layer)
表示层 (Presentation Layer)
会话层 (Session Layer)
传输层 (Transport Layer)
网络层 (Network Layer)
数据链路层 (Data Link Layer)
物理层 (Physical Layer)
```

### 1.3 Socket编程理论

Socket是网络编程的基础抽象，提供了进程间通信的接口。

**Socket类型**:

```rust
// 流式Socket (TCP)
SOCK_STREAM -> 可靠、有序、双向通信

// 数据报Socket (UDP)
SOCK_DGRAM -> 不可靠、无序、单向通信

// 原始Socket
SOCK_RAW -> 直接访问底层协议
```

## 2. 类型规则

### 2.1 Socket类型规则

```rust
// Socket地址类型
pub struct SocketAddr {
    ip: IpAddr,
    port: u16,
}

// Socket类型
pub enum SocketType {
    Stream,    // TCP
    Datagram,  // UDP
    Raw,       // 原始Socket
}

// 协议类型
pub enum Protocol {
    TCP,
    UDP,
    ICMP,
    Custom(u8),
}

// 网络接口
pub struct NetworkInterface {
    name: String,
    ip_addresses: Vec<IpAddr>,
    mac_address: Option<MacAddr>,
    mtu: u16,
}
```

### 2.2 网络事件类型规则

```rust
// 网络事件
pub enum NetworkEvent {
    Connected(SocketAddr),
    Disconnected(SocketAddr),
    DataReceived(Vec<u8>),
    DataSent(usize),
    Error(NetworkError),
}

// 网络错误
pub enum NetworkError {
    ConnectionRefused,
    ConnectionTimeout,
    ConnectionReset,
    HostUnreachable,
    NetworkUnreachable,
    InvalidAddress,
    PermissionDenied,
}
```

### 2.3 协议类型规则

```rust
// HTTP请求
pub struct HttpRequest {
    method: HttpMethod,
    uri: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

// HTTP响应
pub struct HttpResponse {
    status_code: u16,
    status_text: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

// WebSocket帧
pub struct WebSocketFrame {
    fin: bool,
    opcode: WebSocketOpcode,
    mask: bool,
    payload: Vec<u8>,
}
```

## 3. 算法实现

### 3.1 TCP服务器实现

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;

pub struct TcpServer {
    listener: TcpListener,
    clients: HashMap<SocketAddr, TcpStream>,
    handlers: HashMap<String, Box<dyn RequestHandler>>,
}

impl TcpServer {
    pub async fn new(addr: &str) -> Result<Self, std::io::Error> {
        let listener = TcpListener::bind(addr).await?;
        
        Ok(TcpServer {
            listener,
            clients: HashMap::new(),
            handlers: HashMap::new(),
        })
    }
    
    pub fn add_handler(&mut self, path: String, handler: Box<dyn RequestHandler>) {
        self.handlers.insert(path, handler);
    }
    
    pub async fn start(&mut self) -> Result<(), std::io::Error> {
        println!("TCP Server listening on {}", self.listener.local_addr()?);
        
        loop {
            let (socket, addr) = self.listener.accept().await?;
            println!("New connection from: {}", addr);
            
            let handlers = self.handlers.clone();
            tokio::spawn(async move {
                Self::handle_connection(socket, addr, handlers).await;
            });
        }
    }
    
    async fn handle_connection(
        mut socket: TcpStream,
        addr: SocketAddr,
        handlers: HashMap<String, Box<dyn RequestHandler>>,
    ) {
        let mut buffer = [0; 1024];
        
        loop {
            match socket.read(&mut buffer).await {
                Ok(0) => {
                    println!("Connection closed by {}", addr);
                    break;
                }
                Ok(n) => {
                    let request = String::from_utf8_lossy(&buffer[..n]);
                    let response = Self::process_request(&request, &handlers).await;
                    
                    if let Err(e) = socket.write_all(response.as_bytes()).await {
                        eprintln!("Failed to send response: {}", e);
                        break;
                    }
                }
                Err(e) => {
                    eprintln!("Error reading from socket: {}", e);
                    break;
                }
            }
        }
    }
    
    async fn process_request(
        request: &str,
        handlers: &HashMap<String, Box<dyn RequestHandler>>,
    ) -> String {
        let lines: Vec<&str> = request.lines().collect();
        if lines.is_empty() {
            return "HTTP/1.1 400 Bad Request\r\n\r\n".to_string();
        }
        
        let first_line: Vec<&str> = lines[0].split_whitespace().collect();
        if first_line.len() < 2 {
            return "HTTP/1.1 400 Bad Request\r\n\r\n".to_string();
        }
        
        let method = first_line[0];
        let path = first_line[1];
        
        if let Some(handler) = handlers.get(path) {
            match handler.handle(method, path).await {
                Ok(response) => response,
                Err(_) => "HTTP/1.1 500 Internal Server Error\r\n\r\n".to_string(),
            }
        } else {
            "HTTP/1.1 404 Not Found\r\n\r\n".to_string()
        }
    }
}

pub trait RequestHandler: Send + Sync {
    async fn handle(&self, method: &str, path: &str) -> Result<String, std::io::Error>;
}
```

### 3.2 UDP服务器实现

```rust
use tokio::net::UdpSocket;
use std::collections::HashMap;

pub struct UdpServer {
    socket: UdpSocket,
    handlers: HashMap<String, Box<dyn UdpHandler>>,
}

impl UdpServer {
    pub async fn new(addr: &str) -> Result<Self, std::io::Error> {
        let socket = UdpSocket::bind(addr).await?;
        
        Ok(UdpServer {
            socket,
            handlers: HashMap::new(),
        })
    }
    
    pub fn add_handler(&mut self, command: String, handler: Box<dyn UdpHandler>) {
        self.handlers.insert(command, handler);
    }
    
    pub async fn start(&mut self) -> Result<(), std::io::Error> {
        println!("UDP Server listening on {}", self.socket.local_addr()?);
        
        let mut buffer = [0; 1024];
        
        loop {
            match self.socket.recv_from(&mut buffer).await {
                Ok((n, addr)) => {
                    let data = String::from_utf8_lossy(&buffer[..n]);
                    let response = self.process_udp_request(&data).await;
                    
                    if let Err(e) = self.socket.send_to(response.as_bytes(), addr).await {
                        eprintln!("Failed to send response: {}", e);
                    }
                }
                Err(e) => {
                    eprintln!("Error receiving data: {}", e);
                }
            }
        }
    }
    
    async fn process_udp_request(&self, data: &str) -> String {
        let parts: Vec<&str> = data.split_whitespace().collect();
        if parts.is_empty() {
            return "ERROR: Empty request".to_string();
        }
        
        let command = parts[0];
        let args = &parts[1..];
        
        if let Some(handler) = self.handlers.get(command) {
            match handler.handle(args).await {
                Ok(response) => response,
                Err(_) => "ERROR: Handler failed".to_string(),
            }
        } else {
            format!("ERROR: Unknown command '{}'", command)
        }
    }
}

pub trait UdpHandler: Send + Sync {
    async fn handle(&self, args: &[&str]) -> Result<String, std::io::Error>;
}
```

### 3.3 HTTP客户端实现

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

pub struct HttpClient {
    timeout: Duration,
    user_agent: String,
}

impl HttpClient {
    pub fn new() -> Self {
        HttpClient {
            timeout: Duration::from_secs(30),
            user_agent: "Rust-HTTP-Client/1.0".to_string(),
        }
    }
    
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    
    pub fn with_user_agent(mut self, user_agent: String) -> Self {
        self.user_agent = user_agent;
        self
    }
    
    pub async fn get(&self, url: &str) -> Result<HttpResponse, NetworkError> {
        let request = HttpRequest {
            method: HttpMethod::GET,
            uri: url.to_string(),
            headers: HashMap::new(),
            body: Vec::new(),
        };
        
        self.send_request(request).await
    }
    
    pub async fn post(&self, url: &str, body: Vec<u8>) -> Result<HttpResponse, NetworkError> {
        let mut headers = HashMap::new();
        headers.insert("Content-Length".to_string(), body.len().to_string());
        
        let request = HttpRequest {
            method: HttpMethod::POST,
            uri: url.to_string(),
            headers,
            body,
        };
        
        self.send_request(request).await
    }
    
    async fn send_request(&self, request: HttpRequest) -> Result<HttpResponse, NetworkError> {
        let (host, port) = self.parse_url(&request.uri)?;
        let addr = format!("{}:{}", host, port);
        
        let socket = tokio::time::timeout(
            self.timeout,
            TcpStream::connect(addr)
        ).await
            .map_err(|_| NetworkError::ConnectionTimeout)?
            .map_err(|_| NetworkError::ConnectionRefused)?;
        
        let request_str = self.format_request(&request);
        
        let (mut read, mut write) = socket.into_split();
        
        // 发送请求
        write.write_all(request_str.as_bytes()).await
            .map_err(|_| NetworkError::ConnectionReset)?;
        
        // 读取响应
        let mut response_data = Vec::new();
        let mut buffer = [0; 1024];
        
        loop {
            let n = tokio::time::timeout(
                self.timeout,
                read.read(&mut buffer)
            ).await
                .map_err(|_| NetworkError::ConnectionTimeout)?
                .map_err(|_| NetworkError::ConnectionReset)?;
            
            if n == 0 {
                break;
            }
            
            response_data.extend_from_slice(&buffer[..n]);
        }
        
        self.parse_response(&response_data)
    }
    
    fn format_request(&self, request: &HttpRequest) -> String {
        let mut request_str = format!(
            "{} {} HTTP/1.1\r\n",
            request.method.to_string(),
            request.uri
        );
        
        request_str.push_str(&format!("Host: {}\r\n", self.get_host(&request.uri)));
        request_str.push_str(&format!("User-Agent: {}\r\n", self.user_agent));
        
        for (key, value) in &request.headers {
            request_str.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        if !request.body.is_empty() {
            request_str.push_str(&format!("Content-Length: {}\r\n", request.body.len()));
        }
        
        request_str.push_str("\r\n");
        
        if !request.body.is_empty() {
            request_str.push_str(&String::from_utf8_lossy(&request.body));
        }
        
        request_str
    }
    
    fn parse_response(&self, data: &[u8]) -> Result<HttpResponse, NetworkError> {
        let response_str = String::from_utf8_lossy(data);
        let parts: Vec<&str> = response_str.split("\r\n\r\n").collect();
        
        if parts.len() < 2 {
            return Err(NetworkError::InvalidResponse);
        }
        
        let header_lines: Vec<&str> = parts[0].lines().collect();
        if header_lines.is_empty() {
            return Err(NetworkError::InvalidResponse);
        }
        
        let status_line: Vec<&str> = header_lines[0].split_whitespace().collect();
        if status_line.len() < 3 {
            return Err(NetworkError::InvalidResponse);
        }
        
        let status_code = status_line[1].parse().unwrap_or(500);
        let status_text = status_line[2..].join(" ");
        
        let mut headers = HashMap::new();
        for line in &header_lines[1..] {
            if let Some(colon_pos) = line.find(':') {
                let key = line[..colon_pos].trim();
                let value = line[colon_pos + 1..].trim();
                headers.insert(key.to_string(), value.to_string());
            }
        }
        
        let body = parts[1..].join("\r\n\r\n").into_bytes();
        
        Ok(HttpResponse {
            status_code,
            status_text,
            headers,
            body,
        })
    }
    
    fn parse_url(&self, url: &str) -> Result<(String, u16), NetworkError> {
        if url.starts_with("http://") {
            let host_port = &url[7..];
            if let Some(colon_pos) = host_port.find(':') {
                let host = host_port[..colon_pos].to_string();
                let port = host_port[colon_pos + 1..].parse().unwrap_or(80);
                Ok((host, port))
            } else {
                Ok((host_port.to_string(), 80))
            }
        } else {
            Err(NetworkError::InvalidAddress)
        }
    }
    
    fn get_host(&self, uri: &str) -> String {
        if uri.starts_with("http://") {
            let host_port = &uri[7..];
            if let Some(colon_pos) = host_port.find(':') {
                host_port[..colon_pos].to_string()
            } else {
                host_port.to_string()
            }
        } else {
            uri.to_string()
        }
    }
}
```

## 4. 优化策略

### 4.1 连接池优化

```rust
use tokio::sync::Mutex;
use std::collections::HashMap;

pub struct ConnectionPool {
    connections: Mutex<HashMap<String, VecDeque<TcpStream>>>,
    max_connections_per_host: usize,
    max_idle_time: Duration,
}

impl ConnectionPool {
    pub fn new(max_connections_per_host: usize, max_idle_time: Duration) -> Self {
        ConnectionPool {
            connections: Mutex::new(HashMap::new()),
            max_connections_per_host,
            max_idle_time,
        }
    }
    
    pub async fn get_connection(&self, host: &str, port: u16) -> Result<PooledConnection, NetworkError> {
        let key = format!("{}:{}", host, port);
        let mut connections = self.connections.lock().await;
        
        // 尝试从池中获取连接
        if let Some(host_connections) = connections.get_mut(&key) {
            while let Some(mut conn) = host_connections.pop_back() {
                // 检查连接是否仍然有效
                if self.is_connection_valid(&mut conn).await {
                    return Ok(PooledConnection {
                        stream: Some(conn),
                        pool: self,
                        key: key.clone(),
                    });
                }
            }
        }
        
        // 创建新连接
        let addr = format!("{}:{}", host, port);
        let stream = tokio::time::timeout(
            Duration::from_secs(5),
            TcpStream::connect(addr)
        ).await
            .map_err(|_| NetworkError::ConnectionTimeout)?
            .map_err(|_| NetworkError::ConnectionRefused)?;
        
        Ok(PooledConnection {
            stream: Some(stream),
            pool: self,
            key,
        })
    }
    
    async fn is_connection_valid(&self, stream: &mut TcpStream) -> bool {
        // 简化的连接有效性检查
        let mut buf = [0; 1];
        match stream.try_read(&mut buf) {
            Ok(0) => false, // 连接已关闭
            Ok(_) => true,   // 连接有效
            Err(_) => false, // 连接无效
        }
    }
    
    async fn return_connection(&self, key: String, stream: TcpStream) {
        let mut connections = self.connections.lock().await;
        
        let host_connections = connections.entry(key).or_insert_with(VecDeque::new);
        
        if host_connections.len() < self.max_connections_per_host {
            host_connections.push_back(stream);
        }
    }
}

pub struct PooledConnection<'a> {
    stream: Option<TcpStream>,
    pool: &'a ConnectionPool,
    key: String,
}

impl<'a> PooledConnection<'a> {
    pub async fn send(&mut self, data: &[u8]) -> Result<usize, NetworkError> {
        if let Some(ref mut stream) = self.stream {
            stream.write_all(data).await
                .map_err(|_| NetworkError::ConnectionReset)?;
            Ok(data.len())
        } else {
            Err(NetworkError::ConnectionReset)
        }
    }
    
    pub async fn receive(&mut self, buffer: &mut [u8]) -> Result<usize, NetworkError> {
        if let Some(ref mut stream) = self.stream {
            stream.read(buffer).await
                .map_err(|_| NetworkError::ConnectionReset)
        } else {
            Err(NetworkError::ConnectionReset)
        }
    }
}

impl<'a> Drop for PooledConnection<'a> {
    fn drop(&mut self) {
        if let Some(stream) = self.stream.take() {
            let pool = self.pool;
            let key = self.key.clone();
            tokio::spawn(async move {
                pool.return_connection(key, stream).await;
            });
        }
    }
}
```

### 4.2 异步I/O优化

```rust
use tokio::io::{AsyncRead, AsyncWrite};
use futures::stream::{Stream, StreamExt};

pub struct AsyncNetworkManager {
    event_loop: tokio::runtime::Runtime,
}

impl AsyncNetworkManager {
    pub fn new() -> Self {
        let event_loop = tokio::runtime::Runtime::new().unwrap();
        
        AsyncNetworkManager { event_loop }
    }
    
    pub async fn handle_multiple_connections<I>(&self, connections: I) -> Result<(), NetworkError>
    where
        I: IntoIterator<Item = TcpStream>,
    {
        let mut streams = futures::stream::select_all(
            connections.into_iter().map(|stream| {
                tokio::io::AsyncReadExt::bytes(stream)
            })
        );
        
        while let Some((data, index, remaining)) = streams.next().await {
            // 处理接收到的数据
            self.process_data(data.to_vec()).await?;
            
            // 继续监听剩余的流
            if !remaining.is_empty() {
                streams.push(tokio::io::AsyncReadExt::bytes(remaining));
            }
        }
        
        Ok(())
    }
    
    async fn process_data(&self, data: Vec<u8>) -> Result<(), NetworkError> {
        // 处理接收到的数据
        println!("Received {} bytes", data.len());
        Ok(())
    }
    
    pub async fn broadcast_message(&self, message: &[u8], connections: &[TcpStream]) -> Result<(), NetworkError> {
        let mut futures = Vec::new();
        
        for mut conn in connections.iter() {
            let message = message.to_vec();
            futures.push(async move {
                conn.write_all(&message).await
            });
        }
        
        let results = futures::future::join_all(futures).await;
        
        for result in results {
            if let Err(e) = result {
                eprintln!("Failed to send message: {}", e);
            }
        }
        
        Ok(())
    }
}
```

### 4.3 协议优化

```rust
pub struct ProtocolOptimizer {
    compression_enabled: bool,
    encryption_enabled: bool,
    compression_level: u32,
}

impl ProtocolOptimizer {
    pub fn new() -> Self {
        ProtocolOptimizer {
            compression_enabled: false,
            encryption_enabled: false,
            compression_level: 6,
        }
    }
    
    pub fn enable_compression(mut self, level: u32) -> Self {
        self.compression_enabled = true;
        self.compression_level = level;
        self
    }
    
    pub fn enable_encryption(mut self) -> Self {
        self.encryption_enabled = true;
        self
    }
    
    pub fn optimize_packet(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        let mut optimized = data.to_vec();
        
        // 压缩
        if self.compression_enabled {
            optimized = self.compress_data(&optimized)?;
        }
        
        // 加密
        if self.encryption_enabled {
            optimized = self.encrypt_data(&optimized)?;
        }
        
        Ok(optimized)
    }
    
    pub fn deoptimize_packet(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        let mut deoptimized = data.to_vec();
        
        // 解密
        if self.encryption_enabled {
            deoptimized = self.decrypt_data(&deoptimized)?;
        }
        
        // 解压
        if self.compression_enabled {
            deoptimized = self.decompress_data(&deoptimized)?;
        }
        
        Ok(deoptimized)
    }
    
    fn compress_data(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        use flate2::write::DeflateEncoder;
        use flate2::Compression;
        use std::io::Write;
        
        let mut encoder = DeflateEncoder::new(Vec::new(), Compression::new(self.compression_level));
        encoder.write_all(data)
            .map_err(|_| NetworkError::CompressionError)?;
        
        encoder.finish()
            .map_err(|_| NetworkError::CompressionError)
    }
    
    fn decompress_data(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        use flate2::read::DeflateDecoder;
        use std::io::Read;
        
        let mut decoder = DeflateDecoder::new(data);
        let mut decompressed = Vec::new();
        
        decoder.read_to_end(&mut decompressed)
            .map_err(|_| NetworkError::DecompressionError)?;
        
        Ok(decompressed)
    }
    
    fn encrypt_data(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 简化的加密实现
        let mut encrypted = Vec::new();
        for &byte in data {
            encrypted.push(byte ^ 0xAA); // 简单的XOR加密
        }
        Ok(encrypted)
    }
    
    fn decrypt_data(&self, data: &[u8]) -> Result<Vec<u8>, NetworkError> {
        // 简化的解密实现
        let mut decrypted = Vec::new();
        for &byte in data {
            decrypted.push(byte ^ 0xAA); // 简单的XOR解密
        }
        Ok(decrypted)
    }
}
```

## 5. 安全性分析

### 5.1 网络安全保证

网络编程必须考虑以下安全因素：

1. **数据完整性**: 确保数据在传输过程中不被篡改
2. **数据机密性**: 保护敏感数据不被窃听
3. **身份认证**: 验证通信双方的身份
4. **访问控制**: 限制对网络资源的访问

### 5.2 安全连接实现

```rust
use tokio_native_tls::{TlsConnector, TlsStream};
use native_tls::TlsConnector as NativeTlsConnector;

pub struct SecureConnection {
    tls_connector: TlsConnector,
}

impl SecureConnection {
    pub fn new() -> Result<Self, NetworkError> {
        let native_connector = NativeTlsConnector::new()
            .map_err(|_| NetworkError::TlsError)?;
        
        let tls_connector = TlsConnector::from(native_connector);
        
        Ok(SecureConnection { tls_connector })
    }
    
    pub async fn connect_secure(
        &self,
        host: &str,
        port: u16,
    ) -> Result<TlsStream<TcpStream>, NetworkError> {
        let addr = format!("{}:{}", host, port);
        let tcp_stream = TcpStream::connect(addr).await
            .map_err(|_| NetworkError::ConnectionRefused)?;
        
        self.tls_connector.connect(host, tcp_stream).await
            .map_err(|_| NetworkError::TlsError)
    }
    
    pub async fn send_secure_data(
        &self,
        stream: &mut TlsStream<TcpStream>,
        data: &[u8],
    ) -> Result<usize, NetworkError> {
        use tokio::io::AsyncWriteExt;
        
        stream.write_all(data).await
            .map_err(|_| NetworkError::ConnectionReset)?;
        
        Ok(data.len())
    }
    
    pub async fn receive_secure_data(
        &self,
        stream: &mut TlsStream<TcpStream>,
        buffer: &mut [u8],
    ) -> Result<usize, NetworkError> {
        use tokio::io::AsyncReadExt;
        
        stream.read(buffer).await
            .map_err(|_| NetworkError::ConnectionReset)
    }
}
```

### 5.3 防火墙规则

```rust
pub struct Firewall {
    rules: Vec<FirewallRule>,
}

pub struct FirewallRule {
    source_ip: Option<IpAddr>,
    dest_ip: Option<IpAddr>,
    source_port: Option<u16>,
    dest_port: Option<u16>,
    protocol: Option<Protocol>,
    action: FirewallAction,
}

pub enum FirewallAction {
    Allow,
    Deny,
    Log,
}

impl Firewall {
    pub fn new() -> Self {
        Firewall { rules: Vec::new() }
    }
    
    pub fn add_rule(&mut self, rule: FirewallRule) {
        self.rules.push(rule);
    }
    
    pub fn check_packet(&self, packet: &NetworkPacket) -> FirewallAction {
        for rule in &self.rules {
            if self.matches_rule(packet, rule) {
                return rule.action.clone();
            }
        }
        
        FirewallAction::Deny // 默认拒绝
    }
    
    fn matches_rule(&self, packet: &NetworkPacket, rule: &FirewallRule) -> bool {
        if let Some(source_ip) = rule.source_ip {
            if packet.source_ip != source_ip {
                return false;
            }
        }
        
        if let Some(dest_ip) = rule.dest_ip {
            if packet.dest_ip != dest_ip {
                return false;
            }
        }
        
        if let Some(source_port) = rule.source_port {
            if packet.source_port != source_port {
                return false;
            }
        }
        
        if let Some(dest_port) = rule.dest_port {
            if packet.dest_port != dest_port {
                return false;
            }
        }
        
        if let Some(protocol) = &rule.protocol {
            if packet.protocol != *protocol {
                return false;
            }
        }
        
        true
    }
}

pub struct NetworkPacket {
    source_ip: IpAddr,
    dest_ip: IpAddr,
    source_port: u16,
    dest_port: u16,
    protocol: Protocol,
    data: Vec<u8>,
}
```

## 6. 实际应用示例

### 6.1 聊天服务器

```rust
use tokio::sync::broadcast;
use std::collections::HashMap;

pub struct ChatServer {
    tx: broadcast::Sender<ChatMessage>,
    clients: HashMap<SocketAddr, String>,
}

#[derive(Debug, Clone)]
pub struct ChatMessage {
    sender: String,
    content: String,
    timestamp: SystemTime,
}

impl ChatServer {
    pub fn new() -> Self {
        let (tx, _) = broadcast::channel(100);
        
        ChatServer {
            tx,
            clients: HashMap::new(),
        }
    }
    
    pub async fn start(&mut self, addr: &str) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(addr).await?;
        println!("Chat server listening on {}", addr);
        
        let mut rx = self.tx.subscribe();
        
        loop {
            tokio::select! {
                accept_result = listener.accept() => {
                    let (socket, addr) = accept_result?;
                    let tx = self.tx.clone();
                    let mut rx = tx.subscribe();
                    
                    tokio::spawn(async move {
                        Self::handle_chat_client(socket, addr, tx, rx).await;
                    });
                }
                
                message = rx.recv() => {
                    if let Ok(chat_message) = message {
                        println!("[{}] {}: {}", 
                            chat_message.timestamp.duration_since(UNIX_EPOCH).unwrap().as_secs(),
                            chat_message.sender,
                            chat_message.content
                        );
                    }
                }
            }
        }
    }
    
    async fn handle_chat_client(
        mut socket: TcpStream,
        addr: SocketAddr,
        tx: broadcast::Sender<ChatMessage>,
        mut rx: broadcast::Receiver<ChatMessage>,
    ) {
        let mut buffer = [0; 1024];
        
        // 获取用户名
        let username = format!("User-{}", addr.port());
        
        // 发送欢迎消息
        let welcome = format!("Welcome {}! Type your messages.\n", username);
        let _ = socket.write_all(welcome.as_bytes()).await;
        
        loop {
            tokio::select! {
                read_result = socket.read(&mut buffer) => {
                    match read_result {
                        Ok(0) => {
                            println!("Client {} disconnected", addr);
                            break;
                        }
                        Ok(n) => {
                            let message = String::from_utf8_lossy(&buffer[..n]).trim().to_string();
                            
                            if !message.is_empty() {
                                let chat_message = ChatMessage {
                                    sender: username.clone(),
                                    content: message,
                                    timestamp: SystemTime::now(),
                                };
                                
                                let _ = tx.send(chat_message);
                            }
                        }
                        Err(e) => {
                            eprintln!("Error reading from client {}: {}", addr, e);
                            break;
                        }
                    }
                }
                
                message = rx.recv() => {
                    if let Ok(chat_message) = message {
                        let response = format!("[{}] {}: {}\n", 
                            chat_message.timestamp.duration_since(UNIX_EPOCH).unwrap().as_secs(),
                            chat_message.sender,
                            chat_message.content
                        );
                        
                        if let Err(e) = socket.write_all(response.as_bytes()).await {
                            eprintln!("Error writing to client {}: {}", addr, e);
                            break;
                        }
                    }
                }
            }
        }
    }
}
```

### 6.2 文件传输服务器

```rust
pub struct FileTransferServer {
    upload_dir: PathBuf,
}

impl FileTransferServer {
    pub fn new(upload_dir: PathBuf) -> Self {
        std::fs::create_dir_all(&upload_dir).unwrap();
        
        FileTransferServer { upload_dir }
    }
    
    pub async fn start(&self, addr: &str) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(addr).await?;
        println!("File transfer server listening on {}", addr);
        
        loop {
            let (socket, addr) = listener.accept().await?;
            println!("New file transfer connection from: {}", addr);
            
            let upload_dir = self.upload_dir.clone();
            tokio::spawn(async move {
                Self::handle_file_transfer(socket, addr, upload_dir).await;
            });
        }
    }
    
    async fn handle_file_transfer(
        mut socket: TcpStream,
        addr: SocketAddr,
        upload_dir: PathBuf,
    ) {
        let mut buffer = [0; 8192];
        
        // 接收文件名
        let filename = match Self::receive_string(&mut socket).await {
            Ok(name) => name,
            Err(e) => {
                eprintln!("Error receiving filename from {}: {}", addr, e);
                return;
            }
        };
        
        let file_path = upload_dir.join(&filename);
        let mut file = match File::create(&file_path).await {
            Ok(file) => file,
            Err(e) => {
                eprintln!("Error creating file {}: {}", filename, e);
                return;
            }
        };
        
        let mut total_bytes = 0;
        
        loop {
            match socket.read(&mut buffer).await {
                Ok(0) => {
                    println!("File '{}' received from {} ({} bytes)", filename, addr, total_bytes);
                    break;
                }
                Ok(n) => {
                    if let Err(e) = file.write_all(&buffer[..n]).await {
                        eprintln!("Error writing to file {}: {}", filename, e);
                        break;
                    }
                    total_bytes += n;
                }
                Err(e) => {
                    eprintln!("Error reading from client {}: {}", addr, e);
                    break;
                }
            }
        }
    }
    
    async fn receive_string(socket: &mut TcpStream) -> Result<String, std::io::Error> {
        let mut buffer = [0; 256];
        let n = socket.read(&mut buffer).await?;
        
        String::from_utf8_lossy(&buffer[..n])
            .trim()
            .to_string()
            .into()
    }
}
```

### 6.3 网络监控工具

```rust
pub struct NetworkMonitor {
    interfaces: Vec<NetworkInterface>,
}

impl NetworkMonitor {
    pub fn new() -> Self {
        NetworkMonitor {
            interfaces: Vec::new(),
        }
    }
    
    pub async fn start_monitoring(&mut self) -> Result<(), std::io::Error> {
        self.discover_interfaces().await?;
        
        loop {
            for interface in &mut self.interfaces {
                self.monitor_interface(interface).await?;
            }
            
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    }
    
    async fn discover_interfaces(&mut self) -> Result<(), std::io::Error> {
        // 简化的接口发现
        let interfaces = vec![
            NetworkInterface {
                name: "eth0".to_string(),
                ip_addresses: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 1, 100))],
                mac_address: Some(MacAddr::new([0x00, 0x11, 0x22, 0x33, 0x44, 0x55])),
                mtu: 1500,
            },
            NetworkInterface {
                name: "lo".to_string(),
                ip_addresses: vec![IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))],
                mac_address: None,
                mtu: 65536,
            },
        ];
        
        self.interfaces = interfaces;
        Ok(())
    }
    
    async fn monitor_interface(&self, interface: &NetworkInterface) -> Result<(), std::io::Error> {
        println!("Interface: {}", interface.name);
        println!("  IP Addresses: {:?}", interface.ip_addresses);
        println!("  MTU: {}", interface.mtu);
        
        // 这里可以添加更详细的监控逻辑
        // 如带宽使用、包统计等
        
        Ok(())
    }
    
    pub fn get_interface_stats(&self, interface_name: &str) -> Option<InterfaceStats> {
        // 简化的统计信息
        Some(InterfaceStats {
            bytes_received: 1024 * 1024,
            bytes_sent: 512 * 1024,
            packets_received: 1000,
            packets_sent: 500,
            errors: 0,
        })
    }
}

pub struct InterfaceStats {
    pub bytes_received: u64,
    pub bytes_sent: u64,
    pub packets_received: u64,
    pub packets_sent: u64,
    pub errors: u64,
}

pub struct MacAddr([u8; 6]);

impl MacAddr {
    pub fn new(bytes: [u8; 6]) -> Self {
        MacAddr(bytes)
    }
}
```

## 7. 总结

Rust网络编程为构建高性能、安全的网络应用提供了强大的工具和抽象。通过异步I/O、类型安全和内存安全，Rust网络应用能够处理高并发负载，同时保持代码的可靠性和可维护性。

网络编程需要深入理解网络协议、Socket编程和异步编程模型。Rust的生态系统提供了完整的网络编程解决方案，从底层的Socket操作到高级的网络框架，为开发者提供了构建企业级网络应用所需的所有工具。

现代网络应用需要综合考虑性能、安全性、可扩展性和可靠性。Rust的网络编程特性使得开发者能够构建既高效又安全的网络系统，满足各种复杂的网络应用需求。
