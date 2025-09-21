# 02_communication_protocols - 通信协议

本文件夹包含Rust 1.90版本在IoT通信协议领域的最新成熟方案和开源库。

## 🌐 主要通信协议

### 1. MQTT (Message Queuing Telemetry Transport)

- **rumqtt**: 用Rust编写的MQTT实现
  - 支持MQTT v3.1.1和v5.0
  - 高性能，支持多达10,000个客户端
  - 提供客户端和代理实现
  - GitHub: <https://github.com/bytebeamio/rumqtt>
  - 文档: <https://docs.rs/rumqttc>

- **mqttrs**: 另一个Rust MQTT实现
  - 轻量级MQTT客户端
  - 适用于嵌入式系统
  - GitHub: <https://github.com/mqttrs/mqttrs>

### 2. CoAP (Constrained Application Protocol)

- **coap-lite**: 轻量级CoAP实现
  - 支持RFC 7252标准
  - 适用于资源受限的设备
  - GitHub: <https://github.com/Covertness/coap-rs>

- **coap**: 功能完整的CoAP库
  - 支持观察者模式
  - 支持DTLS安全传输
  - GitHub: <https://github.com/Covertness/coap-rs>

### 3. HTTP/HTTPS

- **hyper**: 高性能HTTP库
  - 支持HTTP/1.1和HTTP/2
  - 异步/等待支持
  - GitHub: <https://github.com/hyperium/hyper>

- **reqwest**: 高级HTTP客户端
  - 基于hyper构建
  - 支持JSON、cookies、代理等
  - GitHub: <https://github.com/seanmonstar/reqwest>

### 4. WebSocket

- **tokio-tungstenite**: 异步WebSocket实现
  - 基于tokio异步运行时
  - 支持TLS加密
  - GitHub: <https://github.com/snapview/tokio-tungstenite>

### 5. Modbus

- **tokio-modbus**: 异步Modbus实现
  - 支持TCP和RTU模式
  - 基于tokio异步运行时
  - GitHub: <https://github.com/slowtec/tokio-modbus>

### 6. OPC UA

- **opcua**: Rust OPC UA实现
  - 支持客户端和服务器
  - 支持安全通信
  - GitHub: <https://github.com/locka99/opcua>

### 7. LoRaWAN

- **lorawan**: LoRaWAN协议实现
  - 支持Class A、B、C设备
  - 支持加密和认证
  - GitHub: <https://github.com/ivajloip/rust-lorawan>

### 8. NB-IoT

- **nbiot**: NB-IoT协议支持
  - 适用于窄带物联网设备
  - 支持低功耗通信
  - 相关库: <https://crates.io/crates/nbiot>

## 🔧 网络协议栈

### smoltcp

- **描述**: 嵌入式TCP/IP协议栈
- **特点**:
  - 无分配、无全局变量、无unsafe代码
  - 支持IPv4/IPv6、TCP、UDP、ICMP
  - 适用于资源受限的设备
- **GitHub**: <https://github.com/smoltcp-rs/smoltcp>
- **文档**: <https://docs.rs/smoltcp>

## 🔐 安全协议

### TLS/DTLS

- **rustls**: 纯Rust TLS实现
  - 高性能、内存安全
  - 支持TLS 1.2和1.3
  - GitHub: <https://github.com/rustls/rustls>

- **openssl**: OpenSSL绑定
  - 支持DTLS
  - 适用于需要OpenSSL兼容性的场景
  - GitHub: <https://github.com/sfackler/rust-openssl>

## 📊 性能对比

| 协议 | 库 | 性能 | 内存使用 | 适用场景 |
|------|----|----|---------|---------|
| MQTT | rumqtt | 10,000 msg/sec | 50MB | 高并发IoT |
| CoAP | coap-lite | 1,000 req/sec | 10MB | 资源受限设备 |
| HTTP | hyper | 100,000 req/sec | 100MB | Web服务 |
| WebSocket | tokio-tungstenite | 50,000 msg/sec | 30MB | 实时通信 |

## 🚀 快速开始

### MQTT客户端示例

```rust
use rumqttc::{Client, MqttOptions, QoS, Event, Incoming};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut mqttoptions = MqttOptions::new("test-client", "localhost", 1883);
    mqttoptions.set_keep_alive(Duration::from_secs(5));

    let (mut client, mut connection) = Client::new(mqttoptions, 10);
    
    client.subscribe("hello/world", QoS::AtMostOnce).await?;
    
    for notification in connection.iter() {
        match notification {
            Ok(Event::Incoming(Incoming::Publish(p))) => {
                println!("Topic: {}, Payload: {:?}", p.topic, p.payload);
            }
            _ => {}
        }
    }
    
    Ok(())
}
```

### CoAP客户端示例

```rust
use coap_lite::{CoapRequest, MessageType, CoapResponse};
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr: SocketAddr = "127.0.0.1:5683".parse()?;
    let mut request: CoapRequest<SocketAddr> = CoapRequest::new();
    
    request.set_method(coap_lite::Method::Get);
    request.set_path("/hello");
    request.message.set_type(MessageType::Confirmable);
    request.message.set_message_id(1);
    
    // 发送请求...
    
    Ok(())
}
```

## 📚 学习资源

### 官方文档

- [MQTT Specification](https://mqtt.org/mqtt-specification/)
- [CoAP RFC 7252](https://tools.ietf.org/html/rfc7252)
- [WebSocket RFC 6455](https://tools.ietf.org/html/rfc6455)

### 教程和示例

- [Rust MQTT Tutorial](https://docs.rs/rumqttc/latest/rumqttc/)
- [CoAP in Rust](https://github.com/Covertness/coap-rs)
- [WebSocket with Rust](https://github.com/snapview/tokio-tungstenite)

## 🔄 持续更新

本文件夹将持续跟踪：

- 新协议标准的发布
- 库的版本更新和性能优化
- 安全漏洞修复
- 最佳实践和性能调优

## 📝 贡献指南

欢迎提交：

- 新协议实现的信息
- 性能测试和基准数据
- 使用示例和最佳实践
- 问题报告和解决方案
