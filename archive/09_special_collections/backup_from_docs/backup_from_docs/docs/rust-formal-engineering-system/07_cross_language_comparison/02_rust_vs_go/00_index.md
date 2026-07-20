# Rust vs Go 比较

## 📊 目录

- [Rust vs Go 比较](#rust-vs-go-比较)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心对比维度](#核心对比维度)
    - [并发模型](#并发模型)
    - [内存管理](#内存管理)
    - [性能](#性能)
    - [类型系统](#类型系统)
    - [开发效率](#开发效率)
  - [适用场景对比](#适用场景对比)
    - [Rust 优势场景](#rust-优势场景)
    - [Go 优势场景](#go-优势场景)
  - [迁移指南](#迁移指南)
    - [从 Go 到 Rust](#从-go-到-rust)
    - [并发编程对比](#并发编程对比)
  - [实践与样例](#实践与样例)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 对比 Rust 与 Go 在并发编程、系统编程、开发效率等方面的差异。
- 提供从 Go 迁移到 Rust 的指导与最佳实践。

## 核心对比维度

### 并发模型

- **Rust**：基于所有权的并发安全，`async/await` 异步编程
- **Go**：goroutine 轻量级线程，channel 通信

### 内存管理

- **Rust**：编译时内存安全，所有权系统
- **Go**：垃圾回收器，自动内存管理

### 性能

- **Rust**：零成本抽象，无 GC 开销
- **Go**：GC 暂停，但并发性能优秀

### 类型系统

- **Rust**：强类型系统，模式匹配，泛型
- **Go**：简单类型系统，接口，无泛型（Go 1.18+ 支持）

### 开发效率

- **Rust**：编译时检查，学习曲线陡峭
- **Go**：简单语法，快速开发

## 适用场景对比

### Rust 优势场景

- 系统编程：操作系统、嵌入式系统
- 高性能应用：游戏引擎、数据库
- 安全关键应用：加密库、区块链
- 内存敏感应用：实时系统、IoT

### Go 优势场景

- 微服务：快速开发、部署简单
- 网络服务：高并发服务器
- DevOps 工具：容器、监控工具
- 原型开发：快速验证想法

## 迁移指南

### 从 Go 到 Rust

1. 理解所有权概念
2. 学习 Rust 的并发模型
3. 掌握错误处理模式
4. 熟悉 Cargo 包管理
5. 逐步迁移服务

### 并发编程对比

- Go goroutine → Rust async task
- Go channel → Rust mpsc channel
- Go select → Rust select! macro

## 实践与样例

- 对比实现：参见 [crates/c64_rust_vs_go](../../../crates/c64_rust_vs_go/)
- 并发编程：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 应用领域（微服务）：[`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)

## 导航

- 返回跨语言比较：[`../00_index.md`](../00_index.md)
- Rust vs C++：[`../01_rust_vs_cpp/00_index.md`](../01_rust_vs_cpp/00_index.md)
- Rust vs Python：[`../03_rust_vs_python/00_index.md`](../03_rust_vs_python/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
