# 网络安全（Cybersecurity）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [网络安全（Cybersecurity）索引](#网络安全cybersecurity索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心概念](#-核心概念)
    - [1. 加密算法（Cryptographic Algorithms）](#1-加密算法cryptographic-algorithms)
    - [2. 安全协议（Security Protocols）](#2-安全协议security-protocols)
    - [3. 威胁检测（Threat Detection）](#3-威胁检测threat-detection)
    - [4. 安全工具（Security Tools）](#4-安全工具security-tools)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块介绍 Rust 在网络安全领域的应用与实践，提供安全工具、加密算法、威胁检测的技术指导。所有内容均基于 Rust 1.91.0 和当前最佳实践，特别关注 Rust 1.91 新增的悬空指针警告机制。

### 核心价值

- **网络安全**: 专注于 Rust 在网络安全领域的应用
- **最佳实践**: 基于 Rust 社区最新网络安全实践
- **完整覆盖**: 涵盖加密算法、安全协议、威胁检测、安全工具等核心主题
- **易于理解**: 提供详细的网络安全应用说明和代码示例

## 📚 核心概念

### 1. 加密算法（Cryptographic Algorithms）

**推荐库**: `ring`, `rustls`, `openssl`, `ed25519-dalek`, `aes-gcm`

- **对称加密**: AES、ChaCha20、Salsa20
- **非对称加密**: RSA、ECDSA、Ed25519
- **哈希函数**: SHA-256、SHA-512、Blake2
- **密钥管理**: 密钥生成、密钥存储、密钥轮换

**相关资源**:

- [ring 文档](https://docs.rs/ring/)
- [rustls 文档](https://docs.rs/rustls/)
- [OpenSSL Rust](https://docs.rs/openssl/)
- [ed25519-dalek 文档](https://docs.rs/ed25519-dalek/)

### 2. 安全协议（Security Protocols）

**推荐库**: `rustls`, `tokio-rustls`, `quinn`, `ssh2`

- **TLS/SSL**: TLS 1.3、SSL/TLS 实现、证书管理
- **IPSec**: IPSec 协议、VPN 实现、安全隧道
- **VPN**: VPN 协议、隧道协议、安全通信
- **SSH**: SSH 协议、安全远程访问、密钥认证

**相关资源**:

- [rustls 文档](https://docs.rs/rustls/)
- [tokio-rustls 文档](https://docs.rs/tokio-rustls/)
- [Quinn 文档](https://docs.rs/quinn/)
- [ssh2-rs 文档](https://docs.rs/ssh2/)

### 3. 威胁检测（Threat Detection）

**推荐库**: `snort`, `suricata`, `yara`, `clamav`

- **入侵检测**: 入侵检测系统、异常检测、规则引擎
- **恶意软件分析**: 恶意软件分析、行为分析、静态分析
- **漏洞扫描**: 漏洞扫描、安全审计、渗透测试
- **威胁情报**: 威胁情报、IOC 检测、威胁分析

**相关资源**:

- [Snort 文档](https://www.snort.org/)
- [Suricata 文档](https://suricata.io/)
- [YARA 文档](https://yara.readthedocs.io/)
- [ClamAV 文档](https://www.clamav.net/)

### 4. 安全工具（Security Tools）

**推荐库**: `cargo-audit`, `cargo-deny`, `cargo-geiger`, `cargo-crev`

- **安全扫描**: 代码扫描、依赖扫描、漏洞扫描
- **安全分析**: 静态分析、动态分析、交互分析
- **安全测试**: 渗透测试、安全测试、漏洞测试
- **安全监控**: 安全监控、威胁检测、安全告警

**相关资源**:

- [cargo-audit 文档](https://docs.rs/cargo-audit/)
- [cargo-deny 文档](https://docs.rs/cargo-deny/)
- [cargo-geiger 文档](https://docs.rs/cargo-geiger/)
- [cargo-crev 文档](https://github.com/crev-dev/cargo-crev)

## 💻 实践与样例

### 代码示例位置

- **网络安全**: [crates/c26_cybersecurity](../../../crates/c26_cybersecurity/)
- **加密算法**: [crates/c27_cryptography](../../../crates/c27_cryptography/)
- **安全工具**: [crates/c28_security_tools](../../../crates/c28_security_tools/)

### 快速开始示例

```rust
// 使用 ring 进行加密
use ring::rand::{SecureRandom, SystemRandom};

let rng = SystemRandom::new();
let mut key = [0u8; 32];
rng.fill(&mut key)?;
```

---

## 🔗 相关索引

- **理论基础（内存安全）**: [`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- **设计模式（安全模式）**: [`../../03_design_patterns/08_security/00_index.md`](../../03_design_patterns/08_security/00_index.md)
- **应用领域（金融科技）**: [`../01_fintech/00_index.md`](../01_fintech/00_index.md)

---

## 🧭 导航

- **返回应用领域**: [`../00_index.md`](../00_index.md)
- **大数据分析**: [`../07_big_data_analytics/00_index.md`](../07_big_data_analytics/00_index.md)
- **医疗健康**: [`../09_healthcare/00_index.md`](../09_healthcare/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
