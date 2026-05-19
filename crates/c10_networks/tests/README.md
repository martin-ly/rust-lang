# C10 Networks 测试指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](../docs/STYLE.md)。

## 📋 目录

- [C10 Networks 测试指南](#c10-networks-测试指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [测试类型](#测试类型)
    - [测试结构](#测试结构)
  - [🚀 快速开始](#-快速开始)
    - [运行所有测试](#运行所有测试)
    - [运行特定测试](#运行特定测试)
    - [测试配置](#测试配置)
  - [📝 测试文件说明](#-测试文件说明)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [性能测试](#性能测试)
    - [安全测试](#安全测试)
    - [协议测试](#协议测试)
    - [DNS测试](#dns测试)
    - [测试运行器](#测试运行器)
  - [⚙️ 测试配置](#️-测试配置)
    - [环境变量](#环境变量)
    - [测试特性](#测试特性)
  - [🔧 测试工具](#-测试工具)
    - [测试运行器](#测试运行器-1)
    - [测试报告](#测试报告)
    - [性能基准](#性能基准)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何跳过网络测试？](#q-如何跳过网络测试)
    - [Q: 如何运行性能测试？](#q-如何运行性能测试)
    - [Q: 如何调试测试失败？](#q-如何调试测试失败)
    - [Q: 如何添加新测试？](#q-如何添加新测试)
    - [Q: 测试覆盖率如何查看？](#q-测试覆盖率如何查看)

## 🎯 概述

C10 Networks 提供了全面的测试套件，确保库的功能正确性、性能表现和安全性。测试覆盖了从基础的数据包处理到复杂的网络协议实现。

### 测试类型

- **单元测试**: 测试单个模块和函数的功能
- **集成测试**: 测试模块间的协作和整体功能
- **性能测试**: 验证性能指标和基准测试
- **安全测试**: 检查安全机制和防护措施
- **协议测试**: 验证网络协议的正确实现
- **DNS测试**: 测试DNS解析功能

### 测试结构

```
tests/
├── unit_tests.rs          # 单元测试
├── integration_tests.rs   # 集成测试
├── performance_tests.rs   # 性能测试
├── security_tests.rs      # 安全测试
├── protocol_tests.rs     # 协议测试
├── dns_tests.rs          # DNS测试
├── test_runner.rs        # 测试运行器
└── README.md             # 测试指南
```

## 🚀 快速开始

### 运行所有测试

```bash
# 运行所有测试
cargo test

# 运行所有测试（包括文档测试）
cargo test --all

# 运行测试并显示输出
cargo test -- --nocapture
```

### 运行特定测试

```bash
# 运行单元测试
cargo test --test unit_tests

# 运行集成测试
cargo test --test integration_tests

# 运行性能测试
cargo test --test performance_tests

# 运行安全测试
cargo test --test security_tests

# 运行协议测试
cargo test --test protocol_tests

# 运行DNS测试
cargo test --test dns_tests

# 运行测试运行器
cargo test --test test_runner
```

### 测试配置

```bash
# 跳过网络测试
C10_SKIP_NETWORK_TESTS=1 cargo test

# 启用DNS测试
C10_DNS_TESTS=1 cargo test --test dns_tests

# 运行特定测试函数
cargo test test_packet_creation

# 运行包含特定字符串的测试
cargo test -- packet
```

## 📝 测试文件说明

### 单元测试

**文件**: `unit_tests.rs`

测试各个模块的基本功能，包括：

- 错误处理模块测试
- 数据包创建和操作测试
- HTTP协议基本功能测试
- WebSocket协议基本功能测试
- 套接字配置测试
- 数据包序列化测试

**运行方式**:

```bash
cargo test --test unit_tests
```

### 集成测试

**文件**: `integration_tests.rs`

测试模块间的协作和整体功能，包括：

- TCP/UDP套接字集成测试
- HTTP/WebSocket协议集成测试
- TCP连接管理和连接池测试
- 数据包处理流水线测试
- 错误处理和恢复测试
- 并发处理测试
- 性能基准测试
- 超时处理测试
- 内存使用测试

**运行方式**:

```bash
cargo test --test integration_tests
```

### 性能测试

**文件**: `performance_tests.rs`

验证性能指标和基准测试，包括：

- 数据包创建性能测试
- 数据包构建器性能测试
- 数据包统计性能测试
- HTTP请求/响应创建性能测试
- WebSocket帧创建性能测试
- WebSocket握手请求性能测试
- 数据包序列化/反序列化性能测试
- 内存分配性能测试
- 并发数据包处理性能测试
- 大数据包处理性能测试
- 数据包过滤器性能测试
- 错误处理性能测试
- 数据包类型比较性能测试

**运行方式**:

```bash
cargo test --test performance_tests
```

### 安全测试

**文件**: `security_tests.rs`

检查安全机制和防护措施，包括：

- 恶意数据包检测测试
- HTTP安全头部验证测试
- WebSocket安全验证测试
- 输入验证和清理测试
- 数据包大小限制测试
- 序列号安全测试
- 错误处理安全测试
- 网络错误安全测试
- 数据包类型安全测试
- ACME管理器安全测试
- 数据包过滤安全测试
- 并发安全测试
- 内存安全测试
- 边界条件安全测试
- 协议安全测试

**运行方式**:

```bash
cargo test --test security_tests
```

### 协议测试

**文件**: `protocol_tests.rs`

验证网络协议的正确实现，包括：

- HTTP协议实现测试
- HTTP方法枚举测试
- HTTP状态码测试
- HTTP版本测试
- WebSocket协议实现测试
- WebSocket握手请求测试
- WebSocket操作码测试
- TCP协议实现测试
- TCP状态机测试
- TCP拥塞控制测试
- 套接字配置测试
- 协议数据包测试
- 协议错误处理测试
- 协议兼容性测试
- 协议性能测试
- 协议边界条件测试

**运行方式**:

```bash
cargo test --test protocol_tests
```

### DNS测试

**文件**: `dns_tests.rs`

测试DNS解析功能，包括：

- 系统DNS解析测试
- DNS IP查找测试
- DNS DoH/DoT测试

**运行方式**:

```bash
# 需要设置环境变量
C10_DNS_TESTS=1 cargo test --test dns_tests
```

### 测试运行器

**文件**: `test_runner.rs`

提供统一的测试运行接口，包括：

- 测试运行器配置
- 测试结果管理
- 测试套件结果统计
- 测试报告生成
- 测试配置验证

**运行方式**:

```bash
cargo test --test test_runner
```

## ⚙️ 测试配置

### 环境变量

| 环境变量                   | 描述               | 默认值               |
| :--- | :--- | :--- || `C10_SKIP_NETWORK_TESTS`   | 跳过网络相关测试   | `0`                  |
| `C10_DNS_TESTS`            | 启用DNS测试        | `0`                  |
| `C10_TCP_ADDRESS`          | TCP测试地址        | `127.0.0.1:8080`     |
| `C10_TCP_TIMEOUT`          | TCP超时时间        | `30秒`               |
| `C10_TCP_BUFFER_SIZE`      | TCP缓冲区大小      | `8192字节`           |
| `C10_TCP_KEEP_ALIVE`       | 启用TCP Keep-Alive | `true`               |
| `C10_TCP_NODELAY`          | 启用TCP_NODELAY    | `true`               |
| `C10_WS_DEMO_HOST`         | WebSocket测试主机  | `example.com`        |
| `C10_WS_DEMO_PATH`         | WebSocket测试路径  | `/chat`              |
| `C10_WS_DEMO_KEY`          | WebSocket测试密钥  | 自动生成             |
| `C10_P2P_LISTEN_ADDR`      | P2P监听地址        | `/ip4/0.0.0.0/tcp/0` |
| `C10_P2P_TOPIC`            | P2P订阅主题        | `c10-demo`           |
| `C10_P2P_PUBLISH_INTERVAL` | P2P发布间隔        | `5秒`                |

### 测试特性

| 特性        | 描述         | 测试文件               |
| :--- | :--- | :--- || `sniff`     | 抓包功能测试 | `integration_tests.rs` |
| `offline`   | 离线分析测试 | `integration_tests.rs` |
| `pcap_live` | 实时抓包测试 | `integration_tests.rs` |
| `tls`       | TLS功能测试  | `security_tests.rs`    |

## 🔧 测试工具

### 测试运行器

测试运行器提供了统一的测试执行接口：

```rust
use c10_networks::tests::test_runner::{TestRunner, TestRunnerConfig};

let config = TestRunnerConfig {
    run_unit_tests: true,
    run_integration_tests: true,
    run_performance_tests: true,
    run_security_tests: true,
    run_protocol_tests: true,
    run_dns_tests: true,
    skip_network_tests: false,
    verbose: false,
    timeout: Some(std::time::Duration::from_secs(300)),
};

let runner = TestRunner::new(config);
let results = runner.run_all_tests();
```

### 测试报告

测试报告生成器可以生成详细的测试报告：

```rust
use c10_networks::tests::test_runner::TestReportGenerator;

let report = TestReportGenerator::generate_report(&results);
println!("{}", report);
```

### 性能基准

性能测试提供了详细的性能指标：

```rust
// 性能测试结果示例
println!("数据包创建性能: {} ns/packet", avg_time);
println!("HTTP请求创建性能: {} ns/request", avg_time);
println!("WebSocket帧创建性能: {} ns/frame", avg_time);
```

## ❓ 常见问题

### Q: 如何跳过网络测试？

A: 设置环境变量：

```bash
C10_SKIP_NETWORK_TESTS=1 cargo test
```

### Q: 如何运行性能测试？

A: 运行性能测试套件：

```bash
cargo test --test performance_tests
```

### Q: 如何调试测试失败？

A: 使用以下方法调试：

1. **显示详细输出**:

   ```bash
   cargo test --test unit_tests -- --nocapture
   ```

2. **运行单个测试**:

   ```bash
   cargo test test_packet_creation -- --nocapture
   ```

3. **使用调试模式**:
   ```bash
   cargo test --test unit_tests -- --nocapture --test-threads=1
   ```

### Q: 如何添加新测试？

A: 在相应的测试文件中添加新的测试函数：

```rust
#[test]
fn test_new_functionality() {
    // 测试代码
    assert!(condition);
}
```

### Q: 测试覆盖率如何查看？

A: 使用 `tarpaulin` 工具查看测试覆盖率：

```bash
# 安装 tarpaulin
cargo install cargo-tarpaulin

# 运行覆盖率测试
cargo tarpaulin --out Html

# 查看覆盖率报告
open tarpaulin-report.html
```

---

**测试指南完成！** 🎉

现在您已经了解了 C10 Networks 的完整测试体系，可以开始编写和运行测试了。

_最后更新: 2025年1月_
_文档版本: v1.0_
_维护者: C10 Networks 开发团队_
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
