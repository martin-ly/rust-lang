# 消息传递模式

> **EN**: Message Passing Patterns
> **Summary**: Rust channel-based concurrency: std::sync::mpsc, Crossbeam, bounded/unbounded channels, select, and common messaging patterns. Migrated to the concurrency patterns authority.
>
> **适用 Rust 版本**: 1.97.0+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/03_advanced/00_concurrency/10_concurrency_patterns.md](../../../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md)

---

## 主题列表

- `std::sync::mpsc` 基础用法
- 多生产者单消费者（MPSC）
- 有界 vs 无界通道与背压
- `try_recv` / `recv_timeout` 非阻塞与超时接收
- Crossbeam channel（MPMC、有界/无界）
- `select!` 与多路复用
- 请求-响应、管道、扇出-扇入、发布-订阅模式
