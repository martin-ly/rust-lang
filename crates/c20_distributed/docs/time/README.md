# 时间与时钟（Time & Clocks）

- 物理时钟：NTP、PTP、时钟漂移与误差界
- 逻辑时钟：Lamport Clock、Vector Clock、DSV
- TrueTime 与外部一致性（Spanner）

## 物理时钟与误差

- NTP：网络时间同步，误差通常在毫秒级；对称路径与抖动影响测量。
- PTP：硬件时间戳，数据中心可达亚微秒级；部署成本更高。
- 误差界 ε：系统应保守估计 `now() ∈ [t-ε, t+ε]`，用于租约与安全读的上界分析。

## 逻辑时钟

- Lamport 时钟：提供事件的偏序；`LC(x) < LC(y)` ⇒ x→y，但非充要。
- Vector Clock：提供因果关系的必要充分条件；用于因果一致与冲突检测。
- DSV（Dependency/Version Vector）：跨分片跟踪依赖的紧凑表示。

## TrueTime/外部一致性

- TrueTime 提供 `TT.now()` 返回 `[earliest, latest]` 区间。
- 外部一致性：事务提交在真实时间上保持顺序；`commit wait` 等待到 `TT.after(commit_ts)` 才对外可见。

## 工程要点

- 租约（lease read）：需要安全时钟界和心跳；避免时钟回拨导致安全性破坏。
- 单调时钟：优先使用单调时间源（如 TSC/monotonic），避免墙钟回拨影响。
- 时钟异常：检测跃变，触发降级（禁用基于时间的乐观优化，转为多数派校验）。

## 进一步阅读

- Wiki：`NTP`, `PTP`, `Lamport timestamps`, `Vector clock`, `Google TrueTime`
- 课程：MIT 6.824（Time, Clocks）、UWash CSE452（Time & Sync）
- 论文：Spanner、Time, Clocks, and the Ordering of Events in a Distributed System（Lamport）
