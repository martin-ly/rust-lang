# 性能优化指南

**EN**: Performance Optimization Guide
**Summary**: `content/` 专题入口：安全关键系统性能优化要点速查；通用 Rust 性能优化请见 concept/ 权威页。

> **权威来源**: 本文件为 `content/` 专题深度内容入口；通用 Rust 性能优化概念解释请见 [`concept/06_ecosystem/10_performance/01_performance_optimization.md`](../../../concept/06_ecosystem/10_performance/01_performance_optimization.md)。若 `concept/` 已覆盖相同主题，本文仅保留安全关键系统场景下的性能要点与决策树，不重复通用优化推导。

> **Bloom 层级**: L4-L6
>
> 本文内容迁移自历史归档，已按 `AGENTS.md` 规则保留为安全关键领域专题实践。

---

## 安全关键系统性能要点

在安全关键系统中，性能优化必须在**确定性、可验证性与最坏执行时间（WCET）**约束下进行：

- **避免动态分配**：关键路径尽量使用栈分配或固定大小的内存池，减少分配延迟与碎片化风险。
- **控制抖动**：优先使用 `current_thread` Tokio runtime 或裸机/RTOS 调度，降低调度不确定性。
- **WCET 分析**：对关键循环与分支保留上界估计，配合 `#[inline]`、`const` 与静态分支工具。
- **缓存可预测性**：在热路径中避免虚函数分发与动态装箱，使用单态化与 `enum` 替代 `dyn`。
- **编译时计算**：将查表、CRC、校准系数等移至 `const` 上下文或 `LazyLock` 初始化阶段。

## 决策树

```
性能瓶颈类型？
├── 延迟敏感（<100µs）
│   └── 消除堆分配 → 使用数组/arena + const 初始化
├── 吞吐量敏感
│   └── 数据并行/向量化 → 评估 SIMD 与 lock-free 通道
├── WCET 需认证
│   └── 禁用递归、动态分发、未绑定循环
└── 内存受限
    └── 使用 packed 结构体 + 静态链接 + strip 符号
```

## 延伸阅读

- 通用 Rust 性能优化：[concept/06_ecosystem/10_performance/01_performance_optimization.md](../../../concept/06_ecosystem/10_performance/01_performance_optimization.md)
- 零成本抽象：[concept/01_foundation/00_start/02_zero_cost_abstractions.md](../../../concept/01_foundation/00_start/02_zero_cost_abstractions.md)
- 所有权与性能：[concept/03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md](../../../concept/03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md)

---

**文档版本**: 2.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-14
**状态**: ✅ 已按 AGENTS.md §2 规范化为专题入口 stub
