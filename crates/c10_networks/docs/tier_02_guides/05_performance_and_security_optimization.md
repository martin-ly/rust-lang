> **EN**: Network Performance and Security Optimization
> **Summary**: Practical techniques for optimizing Rust network services: buffering, batching, connection limits, zero-copy I/O, input validation, IP filtering, rate limiting, TLS, and basic DDoS/slow-attack mitigations.
>
> **权威来源**: [concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md](../../../../concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md) · [concept/06_ecosystem/09_networking/02_network_security.md](../../../../concept/06_ecosystem/09_networking/02_network_security.md)

# C10 Networks - Tier 2: 性能与安全优化

> 本文档已由 `crates/*/docs/` 合规整改迁移。原始详细内容现已纳入 `concept/` 权威页；本页仅保留主题索引与入口链接。

---

## 主题索引

### 性能优化

- 缓冲区优化（`BufReader` / `BufWriter`）
- 批量写入减少系统调用
- 并发连接限制（`Semaphore`）
- 零拷贝文件发送（`tokio::io::copy` / `sendfile`）
- 连接统计与性能分析

### 网络安全

- 输入验证与长度/字符白名单
- IP 白名单/黑名单过滤
- 滑动窗口限流保护
- TLS 客户端/服务器配置（`tokio-rustls`）
- DDoS 防护（连接数 + 速率检查）
- 慢速攻击防护（读取超时）

### 实战案例

- 安全的 HTTP 代理（IP 过滤 + 限流 + 转发）

---

> **权威来源**: [concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md](../../../../concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md) · [concept/06_ecosystem/09_networking/02_network_security.md](../../../../concept/06_ecosystem/09_networking/02_network_security.md)
