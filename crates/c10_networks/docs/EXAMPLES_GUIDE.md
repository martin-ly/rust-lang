# 示例代码指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [示例代码指南](#示例代码指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [示例分类](#示例分类)
  - [🚀 快速开始](#-快速开始)
    - [运行所有示例](#运行所有示例)
    - [运行单个示例](#运行单个示例)
  - [📡 TCP 示例](#-tcp-示例)
    - [TCP Echo 服务器](#tcp-echo-服务器)
    - [TCP 客户端](#tcp-客户端)
    - [TCP 监控](#tcp-监控)
  - [📨 UDP 示例](#-udp-示例)
    - [UDP Echo](#udp-echo)
    - [UDP 自定义服务器](#udp-自定义服务器)
    - [UDP 自定义演示](#udp-自定义演示)
  - [🌐 HTTP 示例](#-http-示例)
    - [HTTP 客户端](#http-客户端)
  - [🔌 WebSocket 示例](#-websocket-示例)
    - [WebSocket 演示](#websocket-演示)
    - [WebSocket Echo 服务器](#websocket-echo-服务器)
    - [WebSocket Echo 客户端](#websocket-echo-客户端)
  - [🔗 P2P 示例](#-p2p-示例)
    - [P2P 最小示例](#p2p-最小示例)
  - [🔍 DNS 示例](#-dns-示例)
    - [DNS 查询](#dns-查询)
    - [统一 DNS](#统一-dns)
    - [DNS DoH/DoT](#dns-dohdot)
    - [DNS 自定义 NameServer](#dns-自定义-nameserver)
    - [DNS 记录查询](#dns-记录查询)
    - [DNS PTR 查询](#dns-ptr-查询)
    - [DNS 负缓存](#dns-负缓存)
  - [📦 gRPC 示例](#-grpc-示例)
    - [gRPC 服务器](#grpc-服务器)
    - [gRPC 客户端](#grpc-客户端)
  - [🔍 抓包示例](#-抓包示例)
    - [ARP 嗅探](#arp-嗅探)
    - [PCAP 离线分析](#pcap-离线分析)
    - [PCAP 实时 TCP](#pcap-实时-tcp)
  - [⚡ Rust 1.90 特性示例](#-rust-190-特性示例)
    - [异步特性演示](#异步特性演示)
    - [性能基准测试](#性能基准测试)
  - [🧪 语义验证示例](#-语义验证示例)
    - [语义验证演示](#语义验证演示)
  - [⚙️ 配置选项](#️-配置选项)
    - [环境变量配置](#环境变量配置)
  - [🔧 运行脚本](#-运行脚本)
    - [Windows PowerShell 脚本](#windows-powershell-脚本)
    - [Linux/macOS Bash 脚本](#linuxmacos-bash-脚本)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何运行需要特权的示例？](#q-如何运行需要特权的示例)
    - [Q: 如何跳过网络相关的测试？](#q-如何跳过网络相关的测试)
    - [Q: 如何配置示例的参数？](#q-如何配置示例的参数)
    - [Q: 示例运行失败怎么办？](#q-示例运行失败怎么办)
    - [Q: 如何添加新的示例？](#q-如何添加新的示例)

## 🎯 概述

C10 Networks 提供了丰富的示例代码，涵盖了网络编程的各个方面。这些示例展示了如何使用库的各种功能，从基础的 TCP/UDP 通信到高级的 P2P 网络和协议实现。

### 示例分类

- **基础网络**: TCP、UDP 套接字编程
- **应用协议**: HTTP、WebSocket、DNS
- **高级特性**: P2P 网络、gRPC、抓包分析
- **性能优化**: 基准测试、异步特性
- **安全验证**: 语义验证、形式化分析

## 🚀 快速开始

### 运行所有示例

```bash
# Windows PowerShell
.\scripts\run_examples.ps1

# Linux/macOS Bash
./scripts/run_examples.sh
```

### 运行单个示例

```bash
# TCP Echo 服务器
cargo run --example tcp_echo_server

# WebSocket 演示
cargo run --example websocket_demo

# P2P 网络
cargo run --example p2p_minimal
```

## 📡 TCP 示例

### TCP Echo 服务器

**文件**: `examples/tcp_echo_server.rs`

**功能特性**:

- ✅ 异步 TCP 服务器
- ✅ 多客户端并发处理
- ✅ 连接管理和错误处理
- ✅ 可配置的套接字选项
- ✅ 完整的日志记录

**运行方式**:

```bash
# 启动服务器
cargo run --example tcp_echo_server

# 在另一个终端测试连接
telnet 127.0.0.1 8080
```

**配置选项**:

- `C10_TCP_ADDRESS`: 监听地址 (默认: 127.0.0.1:8080)
- `C10_TCP_TIMEOUT`: 连接超时 (默认: 30秒)
- `C10_TCP_BUFFER_SIZE`: 缓冲区大小 (默认: 8192字节)
- `C10_TCP_KEEP_ALIVE`: 启用TCP Keep-Alive (默认: true)
- `C10_TCP_NODELAY`: 启用TCP_NODELAY (默认: true)

### TCP 客户端

**文件**: `examples/tcp_client.rs`

**功能特性**:

- ✅ 异步 TCP 客户端
- ✅ 连接重试机制
- ✅ 数据发送和接收
- ✅ 错误处理和超时

**运行方式**:

```bash
# 先启动服务器
cargo run --example tcp_echo_server

# 在另一个终端启动客户端
cargo run --example tcp_client
```

### TCP 监控

**文件**: `examples/tcp_monitor.rs`

**功能特性**:

- ✅ TCP 连接监控
- ✅ 流量统计
- ✅ 性能指标收集
- ✅ 实时数据展示

## 📨 UDP 示例

### UDP Echo

**文件**: `examples/udp_echo.rs`

**功能特性**:

- ✅ UDP 服务器和客户端
- ✅ 数据报处理
- ✅ 广播支持
- ✅ 多播支持

### UDP 自定义服务器

**文件**: `examples/udp_custom_server.rs`

**功能特性**:

- ✅ 自定义 UDP 协议
- ✅ 消息路由
- ✅ 状态管理
- ✅ 错误恢复

### UDP 自定义演示

**文件**: `examples/udp_custom_demo.rs`

**功能特性**:

- ✅ UDP 协议演示
- ✅ 消息序列化
- ✅ 协议验证
- ✅ 性能测试

## 🌐 HTTP 示例

### HTTP 客户端

**文件**: `examples/http_client.rs`

**功能特性**:

- ✅ HTTP/1.1 客户端
- ✅ GET/POST 请求
- ✅ 头部管理
- ✅ 响应处理
- ✅ 错误处理

**运行方式**:

```bash
cargo run --example http_client
```

## 🔌 WebSocket 示例

### WebSocket 演示

**文件**: `examples/websocket_demo.rs`

**功能特性**:

- ✅ WebSocket 帧创建和解析
- ✅ 握手请求和响应
- ✅ 密钥生成和验证
- ✅ 操作码特性演示
- ✅ 完整的协议支持

**运行方式**:

```bash
cargo run --example websocket_demo
```

**配置选项**:

- `C10_WS_DEMO_HOST`: 演示主机名 (默认: example.com)
- `C10_WS_DEMO_PATH`: 演示路径 (默认: /chat)
- `C10_WS_DEMO_KEY`: 自定义密钥 (可选)

### WebSocket Echo 服务器

**文件**: `examples/ws_echo_server.rs`

**功能特性**:

- ✅ WebSocket 服务器
- ✅ 多客户端支持
- ✅ 消息回显
- ✅ 连接管理

### WebSocket Echo 客户端

**文件**: `examples/ws_echo_client.rs`

**功能特性**:

- ✅ WebSocket 客户端
- ✅ 自动重连
- ✅ 消息发送
- ✅ 响应处理

## 🔗 P2P 示例

### P2P 最小示例

**文件**: `examples/p2p_minimal.rs`

**功能特性**:

- ✅ P2P 节点创建和身份管理
- ✅ TCP 传输层配置
- ✅ Noise 加密和 Yamux 多路复用
- ✅ GossipSub 消息传播
- ✅ Kademlia DHT 发现
- ✅ Ping 协议保活
- ✅ Identify 协议节点识别

**运行方式**:

```bash
# 启动第一个节点
cargo run --example p2p_minimal

# 在另一个终端启动第二个节点（会自动发现第一个节点）
cargo run --example p2p_minimal
```

**配置选项**:

- `C10_P2P_LISTEN_ADDR`: 监听地址 (默认: /ip4/0.0.0.0/tcp/0)
- `C10_P2P_TOPIC`: 订阅主题 (默认: c10-demo)
- `C10_P2P_PUBLISH_INTERVAL`: 发布间隔 (默认: 5秒)

## 🔍 DNS 示例

### DNS 查询

**文件**: `examples/dns_lookup.rs`

**功能特性**:

- ✅ 基础 DNS 查询
- ✅ A/AAAA 记录解析
- ✅ 系统 DNS 配置
- ✅ 错误处理

### 统一 DNS

**文件**: `examples/unified_dns.rs`

**功能特性**:

- ✅ 统一 DNS 接口
- ✅ 多后端支持
- ✅ 缓存机制
- ✅ 故障转移

### DNS DoH/DoT

**文件**: `examples/dns_doh_dot.rs`

**功能特性**:

- ✅ DNS over HTTPS (DoH)
- ✅ DNS over TLS (DoT)
- ✅ 加密 DNS 查询
- ✅ 隐私保护

### DNS 自定义 NameServer

**文件**: `examples/dns_custom_ns.rs`

**功能特性**:

- ✅ 自定义 NameServer 配置
- ✅ 内网 DNS 支持
- ✅ 负载均衡
- ✅ 故障检测

### DNS 记录查询

**文件**: `examples/dns_records.rs`

**功能特性**:

- ✅ MX 记录查询
- ✅ SRV 记录查询
- ✅ TXT 记录查询
- ✅ CNAME 记录查询

### DNS PTR 查询

**文件**: `examples/dns_ptr.rs`

**功能特性**:

- ✅ 逆向 DNS 查询
- ✅ IP 到域名解析
- ✅ PTR 记录处理

### DNS 负缓存

**文件**: `examples/dns_negative_cache.rs`

**功能特性**:

- ✅ 负缓存机制
- ✅ 失败查询缓存
- ✅ 缓存策略
- ✅ 性能优化

## 📦 gRPC 示例

### gRPC 服务器

**文件**: `examples/grpc_server.rs`

**功能特性**:

- ✅ gRPC 服务器实现
- ✅ Protobuf 消息处理
- ✅ HTTP/2 支持
- ✅ 服务发现

**运行方式**:

```bash
cargo run --example grpc_server
```

### gRPC 客户端

**文件**: `examples/grpc_client.rs`

**功能特性**:

- ✅ gRPC 客户端实现
- ✅ 服务调用
- ✅ 流式处理
- ✅ 错误处理

## 🔍 抓包示例

### ARP 嗅探

**文件**: `examples/arp_sniff.rs`

**功能特性**:

- ✅ ARP 包捕获
- ✅ 网络发现
- ✅ 实时监控
- ✅ 数据解析

**运行方式**:

```bash
# 需要管理员权限
cargo run --example arp_sniff
```

### PCAP 离线分析

**文件**: `examples/pcap_offline.rs`

**功能特性**:

- ✅ PCAP 文件解析
- ✅ 离线流量分析
- ✅ 协议识别
- ✅ 统计报告

**运行方式**:

```bash
cargo run --example pcap_offline --features offline
```

### PCAP 实时 TCP

**文件**: `examples/pcap_live_tcp.rs`

**功能特性**:

- ✅ 实时 TCP 流量捕获
- ✅ 连接跟踪
- ✅ 性能监控
- ✅ 数据统计

**运行方式**:

```bash
cargo run --example pcap_live_tcp --features pcap_live
```

## ⚡ Rust 1.90 特性示例

### 异步特性演示

**文件**: `examples/rust_190_async_features_demo.rs`

**功能特性**:

- ✅ Rust 1.90 异步特性
- ✅ 新的 async/await 语法
- ✅ 性能优化
- ✅ 内存管理

### 性能基准测试

**文件**: `examples/rust_190_performance_benchmark.rs`

**功能特性**:

- ✅ 性能基准测试
- ✅ 内存使用分析
- ✅ 并发性能测试
- ✅ 优化建议

## 🧪 语义验证示例

### 语义验证演示

**文件**: `examples/semantic_verification_demo.rs`

**功能特性**:

- ✅ 形式化验证
- ✅ 模型检查
- ✅ 定理证明
- ✅ 语义分析

## ⚙️ 配置选项

### 环境变量配置

所有示例都支持通过环境变量进行配置：

```bash
# TCP 配置
export C10_TCP_ADDRESS="127.0.0.1:8080"
export C10_TCP_TIMEOUT="30"
export C10_TCP_BUFFER_SIZE="8192"
export C10_TCP_KEEP_ALIVE="true"
export C10_TCP_NODELAY="true"

# WebSocket 配置
export C10_WS_DEMO_HOST="example.com"
export C10_WS_DEMO_PATH="/chat"
export C10_WS_DEMO_KEY="custom-key"

# P2P 配置
export C10_P2P_LISTEN_ADDR="/ip4/0.0.0.0/tcp/0"
export C10_P2P_TOPIC="c10-demo"
export C10_P2P_PUBLISH_INTERVAL="5"

# DNS 配置
export C10_DNS_BACKEND="system"
export C10_DNS_TIMEOUT_MS="5000"
export C10_DNS_ATTEMPTS="2"
export C10_DNS_CACHE_SIZE="512"
export C10_DNS_CACHE_TTL_MS="60000"
```

## 🔧 运行脚本

### Windows PowerShell 脚本

**文件**: `scripts/run_examples.ps1`

```powershell
# 运行所有示例
.\scripts\run_examples.ps1

# 运行特定示例
.\scripts\run_examples.ps1 -Example "tcp_echo_server"

# 跳过网络测试
.\scripts\run_examples.ps1 -SkipNetTests
```

### Linux/macOS Bash 脚本

**文件**: `scripts/run_examples.sh`

```bash
# 运行所有示例
./scripts/run_examples.sh

# 运行特定示例
./scripts/run_examples.sh tcp_echo_server

# 跳过网络测试
C10_SKIP_NETWORK_TESTS=1 ./scripts/run_examples.sh
```

## ❓ 常见问题

### Q: 如何运行需要特权的示例？

A: 某些示例（如抓包）需要管理员权限：

```bash
# Windows (以管理员身份运行 PowerShell)
.\scripts\run_examples.ps1

# Linux/macOS (使用 sudo)
sudo cargo run --example arp_sniff
```

### Q: 如何跳过网络相关的测试？

A: 设置环境变量：

```bash
export C10_SKIP_NETWORK_TESTS=1
```

### Q: 如何配置示例的参数？

A: 使用环境变量或修改示例代码中的默认值。

### Q: 示例运行失败怎么办？

A: 检查以下几点：

1. 网络连接是否正常
2. 端口是否被占用
3. 权限是否足够
4. 依赖是否正确安装

### Q: 如何添加新的示例？

A: 在 `examples/` 目录下创建新的 `.rs` 文件，并在 `Cargo.toml` 中添加相应的 `[[example]]` 配置。

---

**示例代码指南完成！** 🎉

现在您已经了解了 C10 Networks 的所有示例代码，可以开始探索网络编程的各个方面了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
