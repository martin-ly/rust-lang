# Async Runtimes 目录

> **定位**: Rust 异步运行时生态的选型指南与深度分析。
> **Rust 版本**: 1.96.0+ (Edition 2024)

---

## 目录结构

```text
content/ecosystem/async_runtimes/
├── README.md            # 本文件
└── tokio_deep_dive.md   # Tokio 运行时深度解析
```
---

## 运行时概览

| 运行时 | 适用场景 | 特点 |
|---|---|---|
| **Tokio** | 通用异步 IO、Web 服务 | 生态最成熟，线程池、定时器、channel 一应俱全 |
| **async-std** | 已停止维护（2025-03） | 历史参考，不建议新项目使用 |
| **smol** | 轻量异步 | 小型应用、嵌入式 |
| **Embassy** | 嵌入式 `no_std` | 专为微控制器设计的异步运行时 |

---

## 选型建议

- 通用服务器/Web：Tokio
- 资源受限/微控制器：Embassy
- 极简场景：smol
