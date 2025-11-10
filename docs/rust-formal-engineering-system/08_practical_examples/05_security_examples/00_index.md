# 安全示例（Security Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [安全示例（Security Examples）索引](#安全示例security-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 内存安全（Memory Safety）](#1-内存安全memory-safety)
    - [2. 并发安全（Concurrency Safety）](#2-并发安全concurrency-safety)
    - [3. 加密与安全（Cryptography \& Security）](#3-加密与安全cryptography--security)
    - [4. 输入验证（Input Validation）](#4-输入验证input-validation)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 🎯 目的

本模块提供 Rust 安全编程和最佳实践的实用示例，涵盖内存安全、并发安全、加密与安全和输入验证等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践，特别关注 Rust 1.91 新增的悬空指针警告机制。

### 核心价值

- **安全优先**: 专注于安全编程实践
- **最佳实践**: 基于 Rust 社区最新安全实践
- **完整覆盖**: 涵盖多个安全维度
- **易于理解**: 提供详细的安全说明和代码示例

## 📚 核心示例

### 1. 内存安全（Memory Safety）

**Rust 1.91 新特性**: 悬空原始指针警告机制

**推荐库**: `std::ptr`, `std::mem`, `std::alloc`

- **安全的内存管理**: 所有权和借用系统
- **防止缓冲区溢出**: 边界检查和安全的集合操作
- **防止悬垂指针**: Rust 1.91 新增悬空指针警告（⚠️）
- **安全的数据结构**: 使用标准库提供的安全数据结构

**相关资源**:

- [Rust Book - Memory Safety](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [悬空指针警告机制](../../01_theoretical_foundations/02_memory_safety/03_dangling_pointer_warnings_rust_1_91.md)
- [Rust 1.91 快速参考](../../RUST_1_91_QUICK_REFERENCE.md)

### 2. 并发安全（Concurrency Safety）

**推荐库**: `std::sync`, `std::thread`, `parking_lot`, `crossbeam`

- **线程安全的数据结构**: `Arc`, `Mutex`, `RwLock` 等
- **死锁预防**: 锁顺序、超时机制
- **竞态条件避免**: 原子操作、同步原语
- **安全的消息传递**: 通道、Actor 模式

**相关资源**:

- [Rust Book - Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [parking_lot 文档](https://docs.rs/parking_lot/)
- [crossbeam 文档](https://docs.rs/crossbeam/)

### 3. 加密与安全（Cryptography & Security）

**推荐库**: `ring`, `rustls`, `openssl`, `bcrypt`, `argon2`, `aes-gcm`

- **加密算法实现**: AES、ChaCha20、RSA 等
- **安全随机数生成**: `rand` crate、系统随机数
- **数字签名实现**: ECDSA、Ed25519 等
- **安全通信协议**: TLS、HTTPS 实现

**相关资源**:

- [ring 文档](https://docs.rs/ring/)
- [rustls 文档](https://docs.rs/rustls/)
- [RustCrypto 项目](https://github.com/RustCrypto)
- [Rust Security Book](https://anssi-fr.github.io/rust-guide/)

### 4. 输入验证（Input Validation）

**推荐库**: `validator`, `serde`, `regex`, `url`

- **输入数据验证**: 数据格式验证、类型检查
- **边界检查**: 数组边界、数值范围检查
- **类型安全转换**: 安全的类型转换和解析
- **错误处理**: 安全的错误处理和报告

**相关资源**:

- [validator 文档](https://docs.rs/validator/)
- [serde 文档](https://serde.rs/)
- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)

## 实践与样例

- 安全示例：参见 [crates/c10_networks](../../../crates/c10_networks/)
- 网络安全：[crates/c26_cybersecurity](../../../crates/c26_cybersecurity/)
- 应用领域（网络安全）：[`../../04_application_domains/08_cybersecurity/00_index.md`](../../04_application_domains/08_cybersecurity/00_index.md)

### 文件级清单（精选）

- `crates/c10_networks/src/security/`：
  - `secure_communication.rs`：安全通信示例
  - `input_validation.rs`：输入验证示例
  - `secure_data_structures.rs`：安全数据结构
- `crates/c26_cybersecurity/src/`：
  - `encryption_examples.rs`：加密示例
  - `security_tools.rs`：安全工具示例
  - `vulnerability_prevention.rs`：漏洞预防示例

## 相关索引

- 理论基础（内存安全）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- 设计模式（安全模式）：[`../../03_design_patterns/08_security/00_index.md`](../../03_design_patterns/08_security/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 性能示例：[`../04_performance_examples/00_index.md`](../04_performance_examples/00_index.md)
- 并发示例：[`../06_concurrent_examples/00_index.md`](../06_concurrent_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
