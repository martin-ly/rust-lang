# 13 - 分布式系统

> **Rust中的分布式系统模式**

---

## 目录说明

本目录介绍使用Rust构建分布式系统的模式和最佳实践。

---

## 与actor-specialty的关系

- `actor-specialty`: Actor模型专题
- `13-distributed-systems`: 分布式系统通用模式

---

## 关键主题

| 主题 | 描述 |
|:---|:---|
| 一致性模型 | CAP定理、最终一致 |
| 服务发现 | Consul, etcd |
| 负载均衡 | 一致性哈希 |
| 熔断限流 | Circuit Breaker |

---

**维护者**: Rust Distributed Systems Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
