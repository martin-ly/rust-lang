# C10 Networks - Tier 2: TCP/UDP 编程

> **文档版本**: v1.0.0  
> **最后更新**: 2025-10-23  
> **Rust 版本**: 1.90+  
> **预计阅读**: 35 分钟

---

## 📊 目录

- [C10 Networks - Tier 2: TCP/UDP 编程](#c10-networks---tier-2-tcpudp-编程)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. TCP 深入实践](#1-tcp-深入实践)
    - [1.1 TCP 套接字选项](#11-tcp-套接字选项)
    - [1.2 半关闭连接](#12-半关闭连接)
    - [1.3 TCP Keep-Alive](#13-tcp-keep-alive)
    - [1.4 TCP 粘包处理](#14-tcp-粘包处理)
  - [2. UDP 深入实践](#2-udp-深入实践)
    - [2.1 UDP 套接字选项](#21-udp-套接字选项)
    - [2.2 UDP 广播](#22-udp-广播)
    - [2.3 UDP 可靠传输](#23-udp-可靠传输)
  - [3. 协议设计](#3-协议设计)
    - [3.1 简单协议示例](#31-简单协议示例)
    - [3.2 分包与重组](#32-分包与重组)
  - [4. 流量控制](#4-流量控制)
    - [4.1 令牌桶算法](#41-令牌桶算法)
    - [4.2 滑动窗口](#42-滑动窗口)
  - [5. 性能优化](#5-性能优化)
    - [5.1 零拷贝技术](#51-零拷贝技术)
    - [5.2 连接池](#52-连接池)
  - [6. 实战案例](#6-实战案例)
    - [6.1 RPC 框架](#61-rpc-框架)
  - [7. 总结](#7-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

## 📋 目录

- [C10 Networks - Tier 2: TCP/UDP 编程](#c10-networks---tier-2-tcpudp-编程)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. TCP 深入实践](#1-tcp-深入实践)
    - [1.1 TCP 套接字选项](#11-tcp-套接字选项)
    - [1.2 半关闭连接](#12-半关闭连接)
    - [1.3 TCP Keep-Alive](#13-tcp-keep-alive)
    - [1.4 TCP 粘包处理](#14-tcp-粘包处理)
  - [2. UDP 深入实践](#2-udp-深入实践)
    - [2.1 UDP 套接字选项](#21-udp-套接字选项)
    - [2.2 UDP 广播](#22-udp-广播)
    - [2.3 UDP 可靠传输](#23-udp-可靠传输)
  - [3. 协议设计](#3-协议设计)
    - [3.1 简单协议示例](#31-简单协议示例)
    - [3.2 分包与重组](#32-分包与重组)
  - [4. 流量控制](#4-流量控制)
    - [4.1 令牌桶算法](#41-令牌桶算法)
    - [4.2 滑动窗口](#42-滑动窗口)
  - [5. 性能优化](#5-性能优化)
    - [5.1 零拷贝技术](#51-零拷贝技术)
    - [5.2 连接池](#52-连接池)
  - [6. 实战案例](#6-实战案例)
    - [6.1 RPC 框架](#61-rpc-框架)
  - [7. 总结](#7-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

---

## 1. TCP 深入实践

### 1.1 TCP 套接字选项

```rust
use tokio::net::TcpStream;
use std::time::Duration;

async fn configure_tcp_socket(stream: &TcpStream) -> std::io::Result<()> {
    // TCP_NODELAY: 禁用 Nagle 算法，减少延迟
    stream.set_nodelay(true)?;
    
    // 设置超时
    stream.set_linger(Some(Duration::from_secs(5)))?;
    
    println!("TCP 套接字配置完成");
    
    Ok(())
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let stream = TcpStream::connect("127.0.0.1:8080").await?;
    configure_tcp_socket(&stream).await?;
    Ok(())
}
```

### 1.2 半关闭连接

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
    
    // 发送数据
    stream.write_all(b"Request data\n").await?;
    
    // 关闭写端（半关闭）
    stream.shutdown().await?;
    println!("写端已关闭，但仍可读取");
    
    // 继续读取响应
    let mut buffer = Vec::new();
    stream.read_to_end(&mut buffer).await?;
    println!("收到响应: {} 字节", buffer.len());
    
    Ok(())
}
```

### 1.3 TCP Keep-Alive

```rust
use tokio::net::TcpListener;
use socket2::{Socket, Domain, Type, Protocol};
use std::time::Duration;

async fn tcp_keepalive_server() -> std::io::Result<()> {
    let socket = Socket::new(Domain::IPV4, Type::STREAM, Some(Protocol::TCP))?;
    
    // 启用 Keep-Alive
    socket.set_keepalive(Some(Duration::from_secs(60)))?;
    
    socket.set_reuse_address(true)?;
    socket.bind(&"127.0.0.1:8080".parse::<std::net::SocketAddr>().unwrap().into())?;
    socket.listen(128)?;
    
    let listener: std::net::TcpListener = socket.into();
    listener.set_nonblocking(true)?;
    let listener = TcpListener::from_std(listener)?;
    
    println!("TCP Keep-Alive 服务器启动");
    
    loop {
        let (stream, addr) = listener.accept().await?;
        println!("连接来自: {}", addr);
        
        // 处理连接...
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    tcp_keepalive_server().await
}
```

### 1.4 TCP 粘包处理

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader};
use bytes::{BytesMut, Buf};

// 消息格式: [长度 4 字节] [数据]
async fn send_frame(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    let len = data.len() as u32;
    stream.write_u32(len).await?;
    stream.write_all(data).await?;
    Ok(())
}

async fn recv_frame(stream: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let len = stream.read_u32().await? as usize;
    let mut buffer = vec![0u8; len];
    stream.read_exact(&mut buffer).await?;
    Ok(buffer)
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
    
    // 发送多个消息
    send_frame(&mut stream, b"Message 1").await?;
    send_frame(&mut stream, b"Message 2").await?;
    
    // 接收消息
    let msg1 = recv_frame(&mut stream).await?;
    let msg2 = recv_frame(&mut stream).await?;
    
    println!("收到: {:?}", String::from_utf8_lossy(&msg1));
    println!("收到: {:?}", String::from_utf8_lossy(&msg2));
    
    Ok(())
}
```

---

## 2. UDP 深入实践

### 2.1 UDP 套接字选项

```rust
use tokio::net::UdpSocket;

async fn configure_udp_socket() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0").await?;
    
    // 启用广播
    socket.set_broadcast(true)?;
    
    // 设置 TTL
    socket.set_ttl(64)?;
    
    println!("UDP 套接字配置完成");
    Ok(())
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    configure_udp_socket().await
}
```

### 2.2 UDP 广播

```rust
use tokio::net::UdpSocket;

// 发送广播
async fn udp_broadcast_sender() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0").await?;
    socket.set_broadcast(true)?;
    
    let broadcast_addr = "255.255.255.255:9999";
    let message = b"Broadcast message";
    
    socket.send_to(message, broadcast_addr).await?;
    println!("广播发送完成");
    
    Ok(())
}

// 接收广播
async fn udp_broadcast_receiver() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:9999").await?;
    socket.set_broadcast(true)?;
    
    println!("等待广播消息...");
    
    let mut buf = [0u8; 1024];
    loop {
        let (len, addr) = socket.recv_from(&mut buf).await?;
        println!("收到广播来自 {}: {}", addr, String::from_utf8_lossy(&buf[..len]));
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // udp_broadcast_sender().await
    udp_broadcast_receiver().await
}
```

### 2.3 UDP 可靠传输

```rust
use tokio::net::UdpSocket;
use tokio::time::{timeout, Duration};
use std::collections::HashMap;

struct ReliableUdp {
    socket: UdpSocket,
    seq_num: u32,
    ack_map: HashMap<u32, bool>,
}

impl ReliableUdp {
    async fn new(addr: &str) -> std::io::Result<Self> {
        Ok(Self {
            socket: UdpSocket::bind(addr).await?,
            seq_num: 0,
            ack_map: HashMap::new(),
        })
    }
    
    async fn send_reliable(&mut self, data: &[u8], dest: &str, max_retries: u32) -> std::io::Result<()> {
        let mut payload = Vec::with_capacity(data.len() + 4);
        payload.extend_from_slice(&self.seq_num.to_be_bytes());
        payload.extend_from_slice(data);
        
        for attempt in 0..=max_retries {
            self.socket.send_to(&payload, dest).await?;
            
            // 等待 ACK
            let mut ack_buf = [0u8; 4];
            match timeout(Duration::from_millis(500), self.socket.recv(&mut ack_buf)).await {
                Ok(Ok(_)) => {
                    let ack_seq = u32::from_be_bytes(ack_buf);
                    if ack_seq == self.seq_num {
                        self.seq_num += 1;
                        return Ok(());
                    }
                }
                _ => {
                    if attempt < max_retries {
                        println!("超时，重试 {}/{}", attempt + 1, max_retries);
                    }
                }
            }
        }
        
        Err(std::io::Error::new(std::io::ErrorKind::TimedOut, "发送失败"))
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let mut udp = ReliableUdp::new("0.0.0.0:0").await?;
    udp.send_reliable(b"Important message", "127.0.0.1:8080", 3).await?;
    Ok(())
}
```

---

## 3. 协议设计

### 3.1 简单协议示例

```rust
use bytes::{Buf, BufMut, BytesMut};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[derive(Debug, Clone)]
enum MessageType {
    Request = 0x01,
    Response = 0x02,
    Notification = 0x03,
}

#[derive(Debug)]
struct ProtocolMessage {
    msg_type: MessageType,
    request_id: u32,
    payload: Vec<u8>,
}

impl ProtocolMessage {
    fn encode(&self) -> Vec<u8> {
        let mut buffer = BytesMut::new();
        
        // 魔数 (2 字节)
        buffer.put_u16(0xABCD);
        
        // 消息类型 (1 字节)
        buffer.put_u8(self.msg_type.clone() as u8);
        
        // 请求 ID (4 字节)
        buffer.put_u32(self.request_id);
        
        // 负载长度 (4 字节)
        buffer.put_u32(self.payload.len() as u32);
        
        // 负载数据
        buffer.put_slice(&self.payload);
        
        buffer.to_vec()
    }
    
    fn decode(data: &[u8]) -> Result<Self, String> {
        if data.len() < 11 {
            return Err("数据太短".to_string());
        }
        
        let mut cursor = std::io::Cursor::new(data);
        
        // 检查魔数
        let magic = cursor.get_u16();
        if magic != 0xABCD {
            return Err("魔数错误".to_string());
        }
        
        // 消息类型
        let msg_type = match cursor.get_u8() {
            0x01 => MessageType::Request,
            0x02 => MessageType::Response,
            0x03 => MessageType::Notification,
            _ => return Err("未知消息类型".to_string()),
        };
        
        // 请求 ID
        let request_id = cursor.get_u32();
        
        // 负载长度
        let payload_len = cursor.get_u32() as usize;
        
        // 负载数据
        let position = cursor.position() as usize;
        if data.len() < position + payload_len {
            return Err("负载数据不完整".to_string());
        }
        let payload = data[position..position + payload_len].to_vec();
        
        Ok(Self {
            msg_type,
            request_id,
            payload,
        })
    }
}

fn main() {
    let msg = ProtocolMessage {
        msg_type: MessageType::Request,
        request_id: 123,
        payload: b"Hello Protocol".to_vec(),
    };
    
    let encoded = msg.encode();
    println!("编码: {} 字节", encoded.len());
    
    let decoded = ProtocolMessage::decode(&encoded).unwrap();
    println!("解码: {:?}", decoded);
}
```

### 3.2 分包与重组

```rust
use bytes::{BytesMut, BufMut};

const MAX_PACKET_SIZE: usize = 1024;

fn fragment_data(data: &[u8]) -> Vec<Vec<u8>> {
    let mut fragments = Vec::new();
    let total_fragments = (data.len() + MAX_PACKET_SIZE - 1) / MAX_PACKET_SIZE;
    
    for (i, chunk) in data.chunks(MAX_PACKET_SIZE).enumerate() {
        let mut fragment = BytesMut::new();
        fragment.put_u16(i as u16); // 分片索引
        fragment.put_u16(total_fragments as u16); // 总分片数
        fragment.put_slice(chunk);
        fragments.push(fragment.to_vec());
    }
    
    fragments
}

fn reassemble_data(fragments: Vec<Vec<u8>>) -> Result<Vec<u8>, String> {
    if fragments.is_empty() {
        return Err("无分片数据".to_string());
    }
    
    // 解析总分片数
    let total_fragments = u16::from_be_bytes([fragments[0][2], fragments[0][3]]) as usize;
    
    if fragments.len() != total_fragments {
        return Err("分片不完整".to_string());
    }
    
    let mut data = Vec::new();
    for fragment in fragments {
        data.extend_from_slice(&fragment[4..]); // 跳过头部
    }
    
    Ok(data)
}

fn main() {
    let original = vec![0u8; 3000];
    
    let fragments = fragment_data(&original);
    println!("分片数: {}", fragments.len());
    
    let reassembled = reassemble_data(fragments).unwrap();
    println!("重组数据: {} 字节", reassembled.len());
}
```

---

## 4. 流量控制

### 4.1 令牌桶算法

```rust
use tokio::time::{interval, Duration, Instant};
use std::sync::Arc;
use tokio::sync::Mutex;

struct TokenBucket {
    capacity: usize,
    tokens: usize,
    refill_rate: usize, // 每秒补充的令牌数
}

impl TokenBucket {
    fn new(capacity: usize, refill_rate: usize) -> Self {
        Self {
            capacity,
            tokens: capacity,
            refill_rate,
        }
    }
    
    fn try_consume(&mut self, count: usize) -> bool {
        if self.tokens >= count {
            self.tokens -= count;
            true
        } else {
            false
        }
    }
    
    fn refill(&mut self) {
        self.tokens = (self.tokens + self.refill_rate).min(self.capacity);
    }
}

#[tokio::main]
async fn main() {
    let bucket = Arc::new(Mutex::new(TokenBucket::new(100, 10)));
    
    // 定期补充令牌
    let bucket_clone = Arc::clone(&bucket);
    tokio::spawn(async move {
        let mut ticker = interval(Duration::from_secs(1));
        loop {
            ticker.tick().await;
            bucket_clone.lock().await.refill();
        }
    });
    
    // 消费令牌
    for i in 0..20 {
        let mut b = bucket.lock().await;
        if b.try_consume(5) {
            println!("请求 {} 通过", i);
        } else {
            println!("请求 {} 被限流", i);
        }
        drop(b);
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
}
```

### 4.2 滑动窗口

```rust
use std::collections::VecDeque;
use std::time::{Instant, Duration};

struct SlidingWindow {
    window_size: Duration,
    max_requests: usize,
    requests: VecDeque<Instant>,
}

impl SlidingWindow {
    fn new(window_size: Duration, max_requests: usize) -> Self {
        Self {
            window_size,
            max_requests,
            requests: VecDeque::new(),
        }
    }
    
    fn try_acquire(&mut self) -> bool {
        let now = Instant::now();
        
        // 清理过期请求
        while let Some(front) = self.requests.front() {
            if now.duration_since(*front) > self.window_size {
                self.requests.pop_front();
            } else {
                break;
            }
        }
        
        // 检查是否超过限制
        if self.requests.len() < self.max_requests {
            self.requests.push_back(now);
            true
        } else {
            false
        }
    }
}

#[tokio::main]
async fn main() {
    let mut window = SlidingWindow::new(Duration::from_secs(10), 5);
    
    for i in 0..10 {
        if window.try_acquire() {
            println!("请求 {} 通过", i);
        } else {
            println!("请求 {} 被限流", i);
        }
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}
```

---

## 5. 性能优化

### 5.1 零拷贝技术

```rust
use tokio::net::TcpStream;
use tokio::io::AsyncWriteExt;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
    
    // 使用 write_vectored 减少系统调用
    let bufs = [
        std::io::IoSlice::new(b"Header: "),
        std::io::IoSlice::new(b"Value\r\n"),
        std::io::IoSlice::new(b"Body content"),
    ];
    
    stream.write_vectored(&bufs).await?;
    
    Ok(())
}
```

### 5.2 连接池

```rust
use tokio::net::TcpStream;
use std::sync::Arc;
use tokio::sync::Semaphore;
use std::collections::VecDeque;

struct ConnectionPool {
    connections: Arc<tokio::sync::Mutex<VecDeque<TcpStream>>>,
    semaphore: Arc<Semaphore>,
    address: String,
}

impl ConnectionPool {
    fn new(address: String, max_size: usize) -> Self {
        Self {
            connections: Arc::new(tokio::sync::Mutex::new(VecDeque::new())),
            semaphore: Arc::new(Semaphore::new(max_size)),
            address,
        }
    }
    
    async fn acquire(&self) -> std::io::Result<TcpStream> {
        let _permit = self.semaphore.acquire().await.unwrap();
        
        let mut pool = self.connections.lock().await;
        if let Some(conn) = pool.pop_front() {
            Ok(conn)
        } else {
            TcpStream::connect(&self.address).await
        }
    }
    
    async fn release(&self, conn: TcpStream) {
        let mut pool = self.connections.lock().await;
        pool.push_back(conn);
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let pool = ConnectionPool::new("127.0.0.1:8080".to_string(), 10);
    
    let conn = pool.acquire().await?;
    // 使用连接...
    pool.release(conn).await;
    
    Ok(())
}
```

---

## 6. 实战案例

### 6.1 RPC 框架

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct RpcRequest {
    method: String,
    params: Vec<serde_json::Value>,
}

#[derive(Serialize, Deserialize, Debug)]
struct RpcResponse {
    result: serde_json::Value,
}

async fn handle_rpc_client(mut stream: TcpStream) -> std::io::Result<()> {
    let mut buffer = vec![0u8; 1024];
    
    loop {
        // 读取请求
        let n = stream.read(&mut buffer).await?;
        if n == 0 { break; }
        
        // 解析请求
        if let Ok(request) = serde_json::from_slice::<RpcRequest>(&buffer[..n]) {
            println!("RPC 调用: {}", request.method);
            
            // 处理请求
            let result = match request.method.as_str() {
                "add" => {
                    let a = request.params[0].as_i64().unwrap_or(0);
                    let b = request.params[1].as_i64().unwrap_or(0);
                    serde_json::json!(a + b)
                }
                "multiply" => {
                    let a = request.params[0].as_i64().unwrap_or(0);
                    let b = request.params[1].as_i64().unwrap_or(0);
                    serde_json::json!(a * b)
                }
                _ => serde_json::json!({"error": "未知方法"}),
            };
            
            // 发送响应
            let response = RpcResponse { result };
            let json = serde_json::to_vec(&response)?;
            stream.write_all(&json).await?;
        }
    }
    
    Ok(())
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:9001").await?;
    println!("RPC 服务器运行在 127.0.0.1:9001");
    
    loop {
        let (stream, _) = listener.accept().await?;
        tokio::spawn(handle_rpc_client(stream));
    }
}
```

---

## 7. 总结

### 核心要点

| 协议 | 特点 | 适用场景 |
|-----|------|---------|
| **TCP** | 可靠、有序、流式 | 文件传输、HTTP |
| **UDP** | 快速、无连接、数据报 | 视频流、游戏 |

### 最佳实践

1. **协议设计**: 定义清晰的消息格式
2. **粘包处理**: 使用长度前缀或分隔符
3. **流量控制**: 防止服务过载
4. **连接管理**: 使用连接池复用连接
5. **错误处理**: 妥善处理网络异常

---

## 📚 参考资源

- [TCP RFC 793](https://tools.ietf.org/html/rfc793)
- [UDP RFC 768](https://tools.ietf.org/html/rfc768)
- [Tokio Networking](https://tokio.rs/tokio/tutorial/io)

---

**下一步**: 学习 [性能与安全优化](05_性能与安全优化.md)，提升网络程序质量。
