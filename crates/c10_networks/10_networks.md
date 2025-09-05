# 网络编程

## 目录

- [网络编程](#网络编程)
  - [目录](#目录)
  - [1. 网络协议模型](#1-网络协议模型)
    - [1.1 OSI/TCP-IP 协议栈的形式化](#11-ositcp-ip-协议栈的形式化)
    - [1.2 协议状态机的数学表示](#12-协议状态机的数学表示)
    - [1.3 抽象数据通道与消息传递](#13-抽象数据通道与消息传递)
  - [2. 套接字与异步网络](#2-套接字与异步网络)
    - [2.1 套接字编程的理论基础](#21-套接字编程的理论基础)
    - [2.2 异步网络模型的形式化](#22-异步网络模型的形式化)
    - [2.3 网络缓冲区管理](#23-网络缓冲区管理)
  - [3. 网络协议实现](#3-网络协议实现)
    - [3.1 HTTP协议的形式化](#31-http协议的形式化)
    - [3.2 WebSocket协议的理论基础](#32-websocket协议的理论基础)
    - [3.3 网络协议解析器](#33-网络协议解析器)
  - [4. 网络性能优化](#4-网络性能优化)
    - [4.1 连接池管理](#41-连接池管理)
    - [4.2 网络流量控制](#42-网络流量控制)
    - [4.3 网络负载均衡](#43-网络负载均衡)
  - [5. 网络安全](#5-网络安全)
    - [5.1 加密通信的理论基础](#51-加密通信的理论基础)
    - [5.2 数字签名与证书](#52-数字签名与证书)
  - [6. 总结](#6-总结)
  - [7. 版本对齐说明与形式化勘误 {#version-alignment-network}](#7-版本对齐说明与形式化勘误-version-alignment-network)
  - [附录A. P2P 网络（新增）](#附录a-p2p-网络新增)
    - [A.1 定义与目标](#a1-定义与目标)
    - [A.2 形式化与状态机](#a2-形式化与状态机)
    - [A.3 Rust 抽象（伪代码）](#a3-rust-抽象伪代码)
    - [A.4 基于 libp2p 的最小工作示例](#a4-基于-libp2p-的最小工作示例)
    - [A.5 可达性与 NAT 穿透](#a5-可达性与-nat-穿透)
    - [A.6 安全与信誉](#a6-安全与信誉)
    - [A.7 测试与基准](#a7-测试与基准)

## 1. 网络协议模型

### 1.1 OSI/TCP-IP 协议栈的形式化

**理论定义**：
OSI 模型将网络通信分为 7 层，TCP/IP 模型为 4 层，每层定义一组协议与抽象接口。

**分层模型**：
OSI = {L₁:物理, L₂:数据链路, L₃:网络, L₄:传输, L₅:会话, L₆:表示, L₇:应用}
TCP/IP = {L₁:链路, L₂:网络, L₃:传输, L₄:应用}

**集合符号**：
∀ 层 Li, ∃ 协议族 Pi, Li = (Pi, Ii), Ii 为接口集合

**Rust 伪代码**：

```rust
enum Layer { Physical, DataLink, Network, Transport, Session, Presentation, Application }
struct Packet { layer: Layer, data: Vec<u8> }
```

### 1.2 协议状态机的数学表示

**理论定义**：
协议状态机用于描述网络协议的状态转换过程，确保协议的正确性。

**数学符号**：
StateMachine = (S, Σ, δ, s₀, F)
其中 S 是状态集合，Σ 是输入字母表，δ 是转移函数，s₀ 是初始状态，F 是接受状态集合

**Rust 伪代码**：

```rust
enum ProtocolState {
    Closed,
    Listen,
    SynSent,
    SynReceived,
    Established,
    FinWait1,
    FinWait2,
    CloseWait,
    Closing,
    LastAck,
    TimeWait
}

enum ProtocolEvent {
    Open,
    Send,
    Receive,
    Close,
    Timeout
}

struct ProtocolStateMachine {
    current_state: ProtocolState,
    transition_table: HashMap<(ProtocolState, ProtocolEvent), ProtocolState>
}

impl ProtocolStateMachine {
    fn new() -> Self {
        let mut table = HashMap::new();
        // 定义状态转换规则
        table.insert((ProtocolState::Closed, ProtocolEvent::Open), ProtocolState::Listen);
        table.insert((ProtocolState::Listen, ProtocolEvent::Receive), ProtocolState::SynReceived);
        // ... 更多转换规则
        
        Self {
            current_state: ProtocolState::Closed,
            transition_table: table
        }
    }
    
    fn transition(&mut self, event: ProtocolEvent) -> bool {
        if let Some(&new_state) = self.transition_table.get(&(self.current_state, event)) {
            self.current_state = new_state;
            true
        } else {
            false
        }
    }
}
```

**简要说明**：
协议状态机确保了网络协议的正确性和可靠性。

### 1.3 抽象数据通道与消息传递

**理论定义**：
抽象数据通道（Channel）用于在网络层或进程间传递消息，保证数据有序与可靠。

**结构符号**：
Channel = { send(msg), recv() → msg }

**Rust 伪代码**：

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
let (tx, rx): (Sender<i32>, Receiver<i32>) = channel();
tx.send(42).unwrap();
let v = rx.recv().unwrap();
```

**简要说明**：
通道模型简化了消息传递与并发通信的实现。

## 2. 套接字与异步网络

### 2.1 套接字编程的理论基础

**理论定义**：
套接字（Socket）是网络通信的端点，提供进程间通信的抽象接口。

**数学符号**：
Socket = { bind(addr), connect(addr), send(data), recv() → data, close() }

**Rust 伪代码**：

```rust
use std::net::{TcpListener, TcpStream, SocketAddr};
use std::io::{Read, Write};

struct Socket {
    stream: Option<TcpStream>,
    address: SocketAddr
}

impl Socket {
    fn new(address: SocketAddr) -> Self {
        Self { stream: None, address }
    }
    
    fn bind(&mut self) -> std::io::Result<()> {
        let listener = TcpListener::bind(self.address)?;
        if let Ok((stream, _)) = listener.accept() {
            self.stream = Some(stream);
        }
        Ok(())
    }
    
    fn connect(&mut self) -> std::io::Result<()> {
        let stream = TcpStream::connect(self.address)?;
        self.stream = Some(stream);
        Ok(())
    }
    
    fn send(&self, data: &[u8]) -> std::io::Result<usize> {
        if let Some(ref stream) = self.stream {
            stream.write(data)
        } else {
            Err(std::io::Error::new(std::io::ErrorKind::NotConnected, "Not connected"))
        }
    }
    
    fn recv(&self, buffer: &mut [u8]) -> std::io::Result<usize> {
        if let Some(ref stream) = self.stream {
            stream.read(buffer)
        } else {
            Err(std::io::Error::new(std::io::ErrorKind::NotConnected, "Not connected"))
        }
    }
}
```

**简要说明**：
套接字提供了网络通信的统一接口。

### 2.2 异步网络模型的形式化

**理论定义**：
异步网络模型通过事件循环和回调机制实现非阻塞通信。

**数学符号**：
AsyncNet = { poll(), register(event, handler) }

**Rust 伪代码**：

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() {
    let listener = TcpListener::bind("127.0.0.1:8080").await.unwrap();
    
    loop {
        let (mut socket, _) = listener.accept().await.unwrap();
        
        tokio::spawn(async move {
            let mut buf = vec![0; 1024];
            
            loop {
                let n = match socket.read(&mut buf).await {
                    Ok(n) if n == 0 => return,
                    Ok(n) => n,
                    Err(_) => return,
                };
                
                if let Err(_) = socket.write_all(&buf[0..n]).await {
                    return;
                }
            }
        });
    }
}
```

**简要说明**：
异步网络模型提高了高并发场景下的性能。

### 2.3 网络缓冲区管理

**理论定义**：
网络缓冲区管理用于优化数据传输的性能和可靠性。

**数学符号**：
Buffer = { capacity, data, read_ptr, write_ptr }

**Rust 伪代码**：

```rust
use std::collections::VecDeque;

struct NetworkBuffer {
    capacity: usize,
    data: VecDeque<u8>,
    read_position: usize,
    write_position: usize
}

impl NetworkBuffer {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            data: VecDeque::with_capacity(capacity),
            read_position: 0,
            write_position: 0
        }
    }
    
    fn write(&mut self, data: &[u8]) -> usize {
        let available_space = self.capacity - self.data.len();
        let write_size = std::cmp::min(available_space, data.len());
        
        for i in 0..write_size {
            self.data.push_back(data[i]);
        }
        
        write_size
    }
    
    fn read(&mut self, buffer: &mut [u8]) -> usize {
        let read_size = std::cmp::min(self.data.len(), buffer.len());
        
        for i in 0..read_size {
            if let Some(byte) = self.data.pop_front() {
                buffer[i] = byte;
            }
        }
        
        read_size
    }
    
    fn available_read(&self) -> usize {
        self.data.len()
    }
    
    fn available_write(&self) -> usize {
        self.capacity - self.data.len()
    }
}
```

**简要说明**：
缓冲区管理优化了网络I/O的性能。

## 3. 网络协议实现

### 3.1 HTTP协议的形式化

**理论定义**：
HTTP协议是应用层协议，用于在Web浏览器和Web服务器之间传输数据。

**数学符号**：
HTTP = { Request, Response }
Request = { Method, URI, Headers, Body }
Response = { Status, Headers, Body }

**Rust 伪代码**：

```rust
use std::collections::HashMap;

#[derive(Debug)]
enum HttpMethod {
    GET,
    POST,
    PUT,
    DELETE,
    HEAD,
    OPTIONS
}

#[derive(Debug)]
struct HttpRequest {
    method: HttpMethod,
    uri: String,
    headers: HashMap<String, String>,
    body: Vec<u8>
}

impl HttpRequest {
    fn new(method: HttpMethod, uri: String) -> Self {
        Self {
            method,
            uri,
            headers: HashMap::new(),
            body: Vec::new()
        }
    }
    
    fn add_header(&mut self, key: String, value: String) {
        self.headers.insert(key, value);
    }
    
    fn set_body(&mut self, body: Vec<u8>) {
        self.body = body;
    }
    
    fn to_string(&self) -> String {
        let mut request = format!("{:?} {} HTTP/1.1\r\n", self.method, self.uri);
        
        for (key, value) in &self.headers {
            request.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        request.push_str("\r\n");
        
        if !self.body.is_empty() {
            request.push_str(&String::from_utf8_lossy(&self.body));
        }
        
        request
    }
}

#[derive(Debug)]
struct HttpResponse {
    status_code: u16,
    status_text: String,
    headers: HashMap<String, String>,
    body: Vec<u8>
}

impl HttpResponse {
    fn new(status_code: u16, status_text: String) -> Self {
        Self {
            status_code,
            status_text,
            headers: HashMap::new(),
            body: Vec::new()
        }
    }
    
    fn add_header(&mut self, key: String, value: String) {
        self.headers.insert(key, value);
    }
    
    fn set_body(&mut self, body: Vec<u8>) {
        self.body = body.clone();
        self.add_header("Content-Length".to_string(), body.len().to_string());
    }
    
    fn to_string(&self) -> String {
        let mut response = format!("HTTP/1.1 {} {}\r\n", self.status_code, self.status_text);
        
        for (key, value) in &self.headers {
            response.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        response.push_str("\r\n");
        
        if !self.body.is_empty() {
            response.push_str(&String::from_utf8_lossy(&self.body));
        }
        
        response
    }
}
```

**简要说明**：
HTTP协议实现了Web应用的基础通信。

### 3.2 WebSocket协议的理论基础

**理论定义**：
WebSocket协议提供了在单个TCP连接上进行全双工通信的机制。

**数学符号**：
WebSocket = { Handshake, DataFrames, ControlFrames }

**Rust 伪代码**：

```rust
use std::collections::HashMap;

#[derive(Debug)]
enum WebSocketOpcode {
    Continuation = 0x0,
    Text = 0x1,
    Binary = 0x2,
    Close = 0x8,
    Ping = 0x9,
    Pong = 0xA
}

#[derive(Debug)]
struct WebSocketFrame {
    fin: bool,
    opcode: WebSocketOpcode,
    mask: bool,
    payload_length: u64,
    masking_key: Option<[u8; 4]>,
    payload: Vec<u8>
}

impl WebSocketFrame {
    fn new(opcode: WebSocketOpcode, payload: Vec<u8>) -> Self {
        Self {
            fin: true,
            opcode,
            mask: false,
            payload_length: payload.len() as u64,
            masking_key: None,
            payload
        }
    }
    
    fn encode(&self) -> Vec<u8> {
        let mut frame = Vec::new();
        
        // First byte: FIN + RSV + Opcode
        let first_byte = if self.fin { 0x80 } else { 0x00 };
        let first_byte = first_byte | (self.opcode as u8);
        frame.push(first_byte);
        
        // Second byte: MASK + Payload length
        let second_byte = if self.mask { 0x80 } else { 0x00 };
        let second_byte = second_byte | (self.payload_length as u8);
        frame.push(second_byte);
        
        // Extended payload length
        if self.payload_length > 125 {
            if self.payload_length <= 65535 {
                frame.push(126);
                frame.extend_from_slice(&(self.payload_length as u16).to_be_bytes());
            } else {
                frame.push(127);
                frame.extend_from_slice(&self.payload_length.to_be_bytes());
            }
        }
        
        // Masking key
        if self.mask {
            if let Some(key) = self.masking_key {
                frame.extend_from_slice(&key);
            }
        }
        
        // Payload
        frame.extend_from_slice(&self.payload);
        
        frame
    }
    
    fn decode(data: &[u8]) -> Result<Self, String> {
        if data.len() < 2 {
            return Err("Frame too short".to_string());
        }
        
        let fin = (data[0] & 0x80) != 0;
        let opcode = match data[0] & 0x0F {
            0x0 => WebSocketOpcode::Continuation,
            0x1 => WebSocketOpcode::Text,
            0x2 => WebSocketOpcode::Binary,
            0x8 => WebSocketOpcode::Close,
            0x9 => WebSocketOpcode::Ping,
            0xA => WebSocketOpcode::Pong,
            _ => return Err("Unknown opcode".to_string())
        };
        
        let mask = (data[1] & 0x80) != 0;
        let payload_length = data[1] & 0x7F;
        
        let mut offset = 2;
        let mut actual_length = payload_length as u64;
        
        if payload_length == 126 {
            if data.len() < 4 {
                return Err("Frame too short for extended length".to_string());
            }
            actual_length = u16::from_be_bytes([data[2], data[3]]) as u64;
            offset += 2;
        } else if payload_length == 127 {
            if data.len() < 10 {
                return Err("Frame too short for extended length".to_string());
            }
            actual_length = u64::from_be_bytes([
                data[2], data[3], data[4], data[5],
                data[6], data[7], data[8], data[9]
            ]);
            offset += 8;
        }
        
        let mut masking_key = None;
        if mask {
            if data.len() < offset + 4 {
                return Err("Frame too short for masking key".to_string());
            }
            masking_key = Some([data[offset], data[offset + 1], data[offset + 2], data[offset + 3]]);
            offset += 4;
        }
        
        if data.len() < offset + actual_length as usize {
            return Err("Frame too short for payload".to_string());
        }
        
        let mut payload = data[offset..offset + actual_length as usize].to_vec();
        
        // Unmask payload if necessary
        if mask {
            if let Some(key) = masking_key {
                for i in 0..payload.len() {
                    payload[i] ^= key[i % 4];
                }
            }
        }
        
        Ok(WebSocketFrame {
            fin,
            opcode,
            mask,
            payload_length: actual_length,
            masking_key,
            payload
        })
    }
}
```

**简要说明**：
WebSocket协议实现了实时双向通信。

### 3.3 网络协议解析器

**理论定义**：
网络协议解析器用于解析和构造网络协议数据包。

**数学符号**：
Parser = { parse(data) → Packet, serialize(packet) → data }

**Rust 伪代码**：

```rust
use std::io::{Cursor, Read, Write};

trait ProtocolParser {
    type Packet;
    
    fn parse(&self, data: &[u8]) -> Result<Self::Packet, String>;
    fn serialize(&self, packet: &Self::Packet) -> Result<Vec<u8>, String>;
}

struct HttpParser;

#[derive(Debug)]
struct HttpPacket {
    is_request: bool,
    method: Option<String>,
    uri: Option<String>,
    status_code: Option<u16>,
    headers: Vec<(String, String)>,
    body: Vec<u8>
}

impl ProtocolParser for HttpParser {
    type Packet = HttpPacket;
    
    fn parse(&self, data: &[u8]) -> Result<Self::Packet, String> {
        let mut cursor = Cursor::new(data);
        let mut line = String::new();
        
        // Read first line
        cursor.read_line(&mut line).map_err(|e| e.to_string())?;
        let first_line = line.trim();
        
        let mut packet = HttpPacket {
            is_request: false,
            method: None,
            uri: None,
            status_code: None,
            headers: Vec::new(),
            body: Vec::new()
        };
        
        // Parse first line
        let parts: Vec<&str> = first_line.split_whitespace().collect();
        if parts.len() >= 3 {
            if parts[0].starts_with("HTTP/") {
                // Response
                packet.is_request = false;
                packet.status_code = parts[1].parse().ok();
            } else {
                // Request
                packet.is_request = true;
                packet.method = Some(parts[0].to_string());
                packet.uri = Some(parts[1].to_string());
            }
        }
        
        // Read headers
        loop {
            line.clear();
            cursor.read_line(&mut line).map_err(|e| e.to_string())?;
            let header_line = line.trim();
            
            if header_line.is_empty() {
                break;
            }
            
            if let Some(colon_pos) = header_line.find(':') {
                let key = header_line[..colon_pos].trim().to_string();
                let value = header_line[colon_pos + 1..].trim().to_string();
                packet.headers.push((key, value));
            }
        }
        
        // Read body
        let mut body = Vec::new();
        cursor.read_to_end(&mut body).map_err(|e| e.to_string())?;
        packet.body = body;
        
        Ok(packet)
    }
    
    fn serialize(&self, packet: &Self::Packet) -> Result<Vec<u8>, String> {
        let mut data = Vec::new();
        
        // Write first line
        if packet.is_request {
            if let (Some(ref method), Some(ref uri)) = (&packet.method, &packet.uri) {
                writeln!(data, "{} {} HTTP/1.1", method, uri).map_err(|e| e.to_string())?;
            }
        } else {
            if let Some(status_code) = packet.status_code {
                writeln!(data, "HTTP/1.1 {} OK", status_code).map_err(|e| e.to_string())?;
            }
        }
        
        // Write headers
        for (key, value) in &packet.headers {
            writeln!(data, "{}: {}", key, value).map_err(|e| e.to_string())?;
        }
        
        // Write empty line
        writeln!(data).map_err(|e| e.to_string())?;
        
        // Write body
        data.extend_from_slice(&packet.body);
        
        Ok(data)
    }
}
```

**简要说明**：
协议解析器提供了网络协议的标准化处理。

## 4. 网络性能优化

### 4.1 连接池管理

**理论定义**：
连接池管理用于复用网络连接，减少连接建立的开销。

**数学符号**：

```text
ConnectionPool = { connections: Vec<Connection>, max_size: usize }
```

**Rust 伪代码**：

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

struct Connection {
    id: u64,
    created_at: Instant,
    last_used: Instant,
    is_active: bool
}

impl Connection {
    fn new(id: u64) -> Self {
        let now = Instant::now();
        Self {
            id,
            created_at: now,
            last_used: now,
            is_active: true
        }
    }
    
    fn is_expired(&self, max_age: Duration) -> bool {
        self.created_at.elapsed() > max_age
    }
    
    fn is_idle(&self, max_idle: Duration) -> bool {
        self.last_used.elapsed() > max_idle
    }
    
    fn mark_used(&mut self) {
        self.last_used = Instant::now();
    }
}

struct ConnectionPool {
    connections: Arc<Mutex<VecDeque<Connection>>>,
    max_size: usize,
    max_age: Duration,
    max_idle: Duration,
    next_id: Arc<Mutex<u64>>
}

impl ConnectionPool {
    fn new(max_size: usize, max_age: Duration, max_idle: Duration) -> Self {
        Self {
            connections: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
            max_age,
            max_idle,
            next_id: Arc::new(Mutex::new(0))
        }
    }
    
    fn get_connection(&self) -> Option<Connection> {
        let mut connections = self.connections.lock().unwrap();
        
        // Remove expired and idle connections
        connections.retain(|conn| {
            !conn.is_expired(self.max_age) && !conn.is_idle(self.max_idle)
        });
        
        // Return an available connection
        connections.pop_front()
    }
    
    fn return_connection(&self, mut connection: Connection) {
        connection.mark_used();
        
        let mut connections = self.connections.lock().unwrap();
        
        if connections.len() < self.max_size {
            connections.push_back(connection);
        }
    }
    
    fn create_connection(&self) -> Connection {
        let mut next_id = self.next_id.lock().unwrap();
        let id = *next_id;
        *next_id += 1;
        Connection::new(id)
    }
}
```

**简要说明**：
连接池管理提高了网络应用的性能。

### 4.2 网络流量控制

**理论定义**：
网络流量控制用于管理数据传输的速率，防止网络拥塞。

**数学符号**：
FlowControl = { window_size, rate_limit, congestion_window }

**Rust 伪代码**：

```rust
use std::time::{Duration, Instant};

struct FlowController {
    window_size: usize,
    rate_limit: f64, // bytes per second
    congestion_window: usize,
    last_send_time: Instant,
    bytes_sent: usize
}

impl FlowController {
    fn new(window_size: usize, rate_limit: f64) -> Self {
        Self {
            window_size,
            rate_limit,
            congestion_window: window_size,
            last_send_time: Instant::now(),
            bytes_sent: 0
        }
    }
    
    fn can_send(&mut self, data_size: usize) -> bool {
        let now = Instant::now();
        let time_elapsed = now.duration_since(self.last_send_time).as_secs_f64();
        
        // Check rate limit
        let max_bytes = (self.rate_limit * time_elapsed) as usize;
        if self.bytes_sent >= max_bytes {
            return false;
        }
        
        // Check window size
        if data_size > self.congestion_window {
            return false;
        }
        
        true
    }
    
    fn on_send(&mut self, data_size: usize) {
        self.bytes_sent += data_size;
        self.last_send_time = Instant::now();
    }
    
    fn on_ack(&mut self) {
        // Increase congestion window (slow start)
        self.congestion_window = std::cmp::min(
            self.congestion_window * 2,
            self.window_size
        );
    }
    
    fn on_timeout(&mut self) {
        // Decrease congestion window (congestion avoidance)
        self.congestion_window = std::cmp::max(
            self.congestion_window / 2,
            1
        );
    }
    
    fn reset_rate_limit(&mut self) {
        self.bytes_sent = 0;
        self.last_send_time = Instant::now();
    }
}
```

**简要说明**：
流量控制确保了网络传输的稳定性和公平性。

### 4.3 网络负载均衡

**理论定义**：
网络负载均衡用于在多个服务器之间分配网络请求，提高系统的可用性和性能。

**数学符号**：

```text
LoadBalancer = { servers: Vec<Server>, algorithm: LoadBalancingAlgorithm }
```

**Rust 伪代码**：

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

#[derive(Debug)]
struct Server {
    id: String,
    address: String,
    port: u16,
    weight: u32,
    current_connections: u32,
    is_healthy: bool
}

impl Server {
    fn new(id: String, address: String, port: u16, weight: u32) -> Self {
        Self {
            id,
            address,
            port,
            weight,
            current_connections: 0,
            is_healthy: true
        }
    }
    
    fn get_load(&self) -> f64 {
        self.current_connections as f64 / self.weight as f64
    }
}

enum LoadBalancingAlgorithm {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    WeightedLeastConnections,
    Random
}

struct LoadBalancer {
    servers: Arc<Mutex<Vec<Server>>>,
    algorithm: LoadBalancingAlgorithm,
    current_index: Arc<Mutex<usize>>
}

impl LoadBalancer {
    fn new(algorithm: LoadBalancingAlgorithm) -> Self {
        Self {
            servers: Arc::new(Mutex::new(Vec::new())),
            algorithm,
            current_index: Arc::new(Mutex::new(0))
        }
    }
    
    fn add_server(&self, server: Server) {
        let mut servers = self.servers.lock().unwrap();
        servers.push(server);
    }
    
    fn remove_server(&self, server_id: &str) {
        let mut servers = self.servers.lock().unwrap();
        servers.retain(|s| s.id != server_id);
    }
    
    fn select_server(&self) -> Option<Server> {
        let servers = self.servers.lock().unwrap();
        let healthy_servers: Vec<&Server> = servers.iter()
            .filter(|s| s.is_healthy)
            .collect();
        
        if healthy_servers.is_empty() {
            return None;
        }
        
        match self.algorithm {
            LoadBalancingAlgorithm::RoundRobin => {
                let mut index = self.current_index.lock().unwrap();
                let server = healthy_servers[*index % healthy_servers.len()];
                *index += 1;
                Some(server.clone())
            },
            LoadBalancingAlgorithm::LeastConnections => {
                let server = healthy_servers.iter()
                    .min_by_key(|s| s.current_connections)
                    .unwrap();
                Some(server.clone())
            },
            LoadBalancingAlgorithm::Random => {
                use rand::Rng;
                let mut rng = rand::thread_rng();
                let index = rng.gen_range(0..healthy_servers.len());
                Some(healthy_servers[index].clone())
            },
            _ => None
        }
    }
    
    fn mark_server_unhealthy(&self, server_id: &str) {
        let mut servers = self.servers.lock().unwrap();
        if let Some(server) = servers.iter_mut().find(|s| s.id == server_id) {
            server.is_healthy = false;
        }
    }
    
    fn mark_server_healthy(&self, server_id: &str) {
        let mut servers = self.servers.lock().unwrap();
        if let Some(server) = servers.iter_mut().find(|s| s.id == server_id) {
            server.is_healthy = true;
        }
    }
}
```

**简要说明**：
负载均衡提高了系统的可用性和性能。

## 5. 网络安全

### 5.1 加密通信的理论基础

**理论定义**：
加密通信通过加密算法保护数据传输的安全性。

**数学符号**：
Encryption = { encrypt(plaintext, key) → ciphertext, decrypt(ciphertext, key) → plaintext }

**Rust 伪代码**：

```rust
use std::collections::HashMap;

trait EncryptionAlgorithm {
    fn encrypt(&self, plaintext: &[u8], key: &[u8]) -> Result<Vec<u8>, String>;
    fn decrypt(&self, ciphertext: &[u8], key: &[u8]) -> Result<Vec<u8>, String>;
}

struct XorCipher;

impl EncryptionAlgorithm for XorCipher {
    fn encrypt(&self, plaintext: &[u8], key: &[u8]) -> Result<Vec<u8>, String> {
        if key.is_empty() {
            return Err("Key cannot be empty".to_string());
        }
        
        let mut ciphertext = Vec::new();
        for (i, &byte) in plaintext.iter().enumerate() {
            let key_byte = key[i % key.len()];
            ciphertext.push(byte ^ key_byte);
        }
        
        Ok(ciphertext)
    }
    
    fn decrypt(&self, ciphertext: &[u8], key: &[u8]) -> Result<Vec<u8>, String> {
        // XOR cipher is symmetric
        self.encrypt(ciphertext, key)
    }
}

struct SecureChannel {
    algorithm: Box<dyn EncryptionAlgorithm>,
    key: Vec<u8>
}

impl SecureChannel {
    fn new(algorithm: Box<dyn EncryptionAlgorithm>, key: Vec<u8>) -> Self {
        Self { algorithm, key }
    }
    
    fn send(&self, data: &[u8]) -> Result<Vec<u8>, String> {
        self.algorithm.encrypt(data, &self.key)
    }
    
    fn receive(&self, data: &[u8]) -> Result<Vec<u8>, String> {
        self.algorithm.decrypt(data, &self.key)
    }
}
```

**简要说明**：
加密通信保护了数据传输的机密性。

### 5.2 数字签名与证书

**理论定义**：
数字签名用于验证消息的真实性和完整性。

**数学符号**：
DigitalSignature = { sign(message, private_key) → signature, verify(message, signature, public_key) → bool }

**Rust 伪代码**：

```rust
use std::collections::HashMap;

struct KeyPair {
    public_key: Vec<u8>,
    private_key: Vec<u8>
}

impl KeyPair {
    fn generate() -> Self {
        // Simplified key generation
        let public_key = vec![1, 2, 3, 4, 5];
        let private_key = vec![5, 4, 3, 2, 1];
        Self { public_key, private_key }
    }
}

struct DigitalSignature {
    key_pair: KeyPair
}

impl DigitalSignature {
    fn new() -> Self {
        Self { key_pair: KeyPair::generate() }
    }
    
    fn sign(&self, message: &[u8]) -> Vec<u8> {
        // Simplified signature generation
        let mut signature = Vec::new();
        signature.extend_from_slice(&self.key_pair.private_key);
        signature.extend_from_slice(message);
        
        // Simple hash-like operation
        for &byte in &signature {
            signature.push(byte.wrapping_add(1));
        }
        
        signature
    }
    
    fn verify(&self, message: &[u8], signature: &[u8]) -> bool {
        // Simplified signature verification
        let expected_signature = self.sign(message);
        signature == expected_signature
    }
    
    fn get_public_key(&self) -> &[u8] {
        &self.key_pair.public_key
    }
}

struct Certificate {
    public_key: Vec<u8>,
    issuer: String,
    subject: String,
    valid_from: u64,
    valid_until: u64,
    signature: Vec<u8>
}

impl Certificate {
    fn new(public_key: Vec<u8>, issuer: String, subject: String) -> Self {
        Self {
            public_key,
            issuer,
            subject,
            valid_from: 0,
            valid_until: u64::MAX,
            signature: Vec::new()
        }
    }
    
    fn is_valid(&self, current_time: u64) -> bool {
        current_time >= self.valid_from && current_time <= self.valid_until
    }
    
    fn sign(&mut self, signer: &DigitalSignature) {
        let data = format!("{}:{}:{}:{}:{}", 
            self.issuer, self.subject, self.valid_from, 
            self.valid_until, String::from_utf8_lossy(&self.public_key));
        self.signature = signer.sign(data.as_bytes());
    }
    
    fn verify(&self, signer_public_key: &[u8]) -> bool {
        // Simplified verification
        self.public_key == signer_public_key
    }
}
```

**简要说明**：
数字签名和证书确保了通信的认证和完整性。

## 6. 总结

本文档提供了网络编程的完整形式化理论框架，包括：

1. **网络协议模型**：OSI/TCP-IP协议栈、协议状态机、抽象数据通道
2. **套接字与异步网络**：套接字编程、异步网络模型、缓冲区管理
3. **网络协议实现**：HTTP协议、WebSocket协议、协议解析器
4. **网络性能优化**：连接池管理、流量控制、负载均衡
5. **网络安全**：加密通信、数字签名与证书

每个主题都包含：

- 严格的理论定义
- 数学符号表示
- 完整的Rust代码实现
- 实际应用说明

这个框架为Rust语言中的网络编程提供了坚实的理论基础和实践指导。

## 7. 版本对齐说明与形式化勘误 {#version-alignment-network}

- 异步运行时与网络库：文中示例使用 `tokio` 接口做伪代码展示，属版本无关用法；实际工程请以所选运行时与其版本文档为准（避免绑定到特定小版本）。
- HTTP/WebSocket 细节：
  - WebSocket 编解码示例聚焦结构与控制位，未覆盖扩展/分片/掩码的全部边界；工程实现请遵循 RFC6455 并进行完整的长度与掩码校验。
  - HTTP 例子为教学化结构，不涉及分块编码、持久连接与 HTTP/2 帧；实际实现建议使用成熟库并遵循相应 RFC。
- 缓冲区管理：示例 `VecDeque<u8>` 便于说明读写指针语义；零拷贝路径可结合 `bytes::Bytes`、`IoSlice` 等以减少拷贝；并应注意背压与水位阈值以防止放大。
- 性能与拥塞控制：提供了慢启动/拥塞避免的抽象接口；实际实现需结合拥塞控制算法（如 CUBIC/BBR）与计时器精度做细化。
- 安全说明：加密/签名示例为教学化伪实现，不具备安全性；工程需采用经过审计的库（如 `ring`/`rustls`），避免自实现密码学原语。

### 快速开始（新增：WebSocket/UDP/gRPC）

```bash
# WebSocket 回显（开两窗）
cargo run --example ws_echo_server
cargo run --example ws_echo_client

# UDP 回显（发送数据可用 netcat/ncat 或自写客户端）
cargo run --example udp_echo

# gRPC（开两窗）
cargo run --example grpc_server
cargo run --example grpc_client
```

参考实现：见 `examples/` 下对应示例源码与 `README.md` 运行指引。

## 附录A. P2P 网络（新增）

### A.1 定义与目标

**定义**：
P2P（Peer-to-Peer）网络是无中心协调或弱中心协调的分布式通信体系，节点既是客户端也是服务器，强调自治、可拓展与容错。

**目标**：

- 去中心化发现与路由
- 端到端加密与身份认证
- 在 NAT/防火墙环境下的可达性
- 高效的内容/消息分发

### A.2 形式化与状态机

```text
Peer = { id, keys, addrs, protocols }
Overlay = (V, E), V=Peer 集合, E=连接集合
Route(k) = 〈hop₁, hop₂, …, hopₙ〉 // 键 k 的路径
```

消息发布订阅：

```text
GossipSub = { join(topic), leave(topic), publish(topic, msg), on_msg(topic, msg) }
```

### A.3 Rust 抽象（伪代码）

```rust
struct PeerId(Vec<u8>);

struct PeerInfo {
    id: PeerId,
    addresses: Vec<String>,
    protocols: Vec<String>,
}

trait Discovery {
    fn bootstrap(&mut self, seeds: &[PeerInfo]);
    fn find_peer(&mut self, id: &PeerId) -> Option<PeerInfo>;
}

trait PubSub {
    fn join(&mut self, topic: &str);
    fn publish(&mut self, topic: &str, data: &[u8]);
}
```

### A.4 基于 libp2p 的最小工作示例

```rust
use futures::prelude::*;
use libp2p::{gossipsub, identity, kad, ping, identify, Multiaddr, PeerId, Swarm};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let key = identity::Keypair::generate_ed25519();
    let peer_id = PeerId::from(key.public());

    let transport = libp2p::tokio_development_transport(key.clone()).await?;

    let gossipsub = gossipsub::Behaviour::new(
        gossipsub::MessageAuthenticity::Signed(key.clone()),
        gossipsub::Config::default(),
    )?;

    let kad = kad::Behaviour::new(kad::Config::default(), kad::store::MemoryStore::new(peer_id));
    let ping = ping::Behaviour::default();
    let identify = identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public()));

    let behaviour = libp2p::swarm::NetworkBehaviour::combine((gossipsub, kad, ping, identify));
    let mut swarm = Swarm::new(transport, behaviour, peer_id);

    Swarm::listen_on(&mut swarm, "/ip4/0.0.0.0/tcp/0".parse::<Multiaddr>()?)?;

    loop {
        match swarm.select_next_some().await {
            libp2p::swarm::SwarmEvent::NewListenAddr { address, .. } => {
                println!("listening on {}", address);
            }
            _ => {}
        }
    }
}
```

### A.5 可达性与 NAT 穿透

- 优先 QUIC/UDP 打洞，失败则回退中继/中转。
- 记录多地址候选集；监测 RTT 选择最优路径。
- 提供探测 API：STUN 探测、UPnP 端口映射尝试、外网可达性测试。

### A.6 安全与信誉

- 握手使用 Noise/TLS；节点标识为公钥哈希。
- 消息签名与 anti-replay（时间戳/nonce/窗口）。
- 基于消息有效率/滥用事件的信誉度与速率限制。

### A.7 测试与基准

- 单元：Kademlia 路由表操作、GossipSub 去重。
- 集成：本地 3-5 节点组网，主题一致性。
- 基准：发布吞吐、查找延迟、路由 hop 数统计。
