# 安全示例（Security Examples）索引

## 目的

- 提供 Rust 安全编程和最佳实践的实用示例。
- 展示如何编写安全可靠的 Rust 代码。

## 核心示例

### 内存安全

- 安全的内存管理
- 防止缓冲区溢出
- 防止悬垂指针
- 安全的数据结构

### 并发安全

- 线程安全的数据结构
- 死锁预防
- 竞态条件避免
- 安全的消息传递

### 加密与安全

- 加密算法实现
- 安全随机数生成
- 数字签名实现
- 安全通信协议

### 输入验证

- 输入数据验证
- 边界检查
- 类型安全转换
- 错误处理

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
