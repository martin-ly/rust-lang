# Rust vs Kotlin 比较

## 目的

- 对比 Rust 与 Kotlin 在性能、内存管理、生态系统等方面的差异。
- 提供从 Kotlin 迁移到 Rust 的指导与最佳实践。

## 核心对比维度

### 性能

- **Rust**：编译型语言，零成本抽象，无 GC 开销
- **Kotlin**：编译型语言，JVM 优化，GC 暂停

### 内存管理

- **Rust**：编译时内存安全，所有权系统
- **Kotlin**：垃圾回收器，自动内存管理

### 并发模型

- **Rust**：基于所有权的并发安全，`async/await`
- **Kotlin**：协程，结构化并发

### 类型系统

- **Rust**：强类型系统，模式匹配，泛型
- **Kotlin**：强类型系统，空安全，泛型

### 生态系统

- **Rust**：现代包管理器 Cargo，快速增长的生态
- **Kotlin**：Maven/Gradle 生态，Android 开发

## 适用场景对比

### Rust 优势场景

- 系统编程：操作系统、嵌入式系统
- 高性能应用：游戏引擎、数据库
- 网络服务：高并发服务器
- 安全关键应用：加密库、区块链

### Kotlin 优势场景

- Android 开发：移动应用开发
- 后端开发：Spring Boot 集成
- 跨平台开发：Kotlin Multiplatform
- 脚本编程：Kotlin Script

## 迁移指南

### 从 Kotlin 到 Rust

1. 理解所有权概念
2. 学习 Rust 的并发模型
3. 掌握错误处理模式
4. 熟悉 Cargo 包管理
5. 逐步迁移核心模块

### 移动开发对比

- Kotlin Multiplatform → Rust 跨平台开发
- Maven/Gradle → Cargo
- Android 开发 → Rust 移动开发

## 实践与样例

- 对比实现：参见 [crates/c72_rust_vs_kotlin](../../../crates/c72_rust_vs_kotlin/)
- 移动开发：[crates/c47_mobile](../../../crates/c47_mobile/)
- 跨平台开发：[crates/c71_cross_platform](../../../crates/c71_cross_platform/)

## 相关索引

- 理论基础（内存安全）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 应用领域（移动）：[`../../04_application_domains/15_mobile/00_index.md`](../../04_application_domains/15_mobile/00_index.md)

## 导航

- 返回跨语言比较：[`../00_index.md`](../00_index.md)
- Rust vs Swift：[`../07_rust_vs_swift/00_index.md`](../07_rust_vs_swift/00_index.md)
- Rust vs Zig：[`../09_rust_vs_zig/00_index.md`](../09_rust_vs_zig/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
