# 缓存淘汰策略指南（LRU / LFU / ARC / CLOCK / W-TinyLFU） {#缓存淘汰策略指南lru-lfu-arc-clock-w-tinylfu}

> **概念族**: 算法 / 缓存策略
>
> **层级**: L3-L5
> **Bloom 层级**: L3-L5（应用 / 分析 / 评价）
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **权威来源**:
>
> [ARC: A Self-Tuning, Low Overhead Replacement Cache](https://www.usenix.org/legacy/events/fast03/tech/full_papers/megiddo/megiddo.pdf) |
> [TinyLFU: A Highly Efficient Cache Admission Policy](https://dl.acm.org/doi/10.1145/2674005.2674994) |
> [Caffeine – high performance caching library](https://github.com/ben-manes/caffeine) |
> [Wikipedia – Cache replacement policies](https://en.wikipedia.org/wiki/Cache_replacement_policies)

---

## 1. 为什么需要缓存淘汰策略 {#1-为什么需要缓存淘汰策略}

当缓存容量远小于工作集（working set）时，必须决定**在满载时驱逐哪一条数据**。
淘汰策略的目标是在有限空间内最大化命中率（hit ratio），从而降低对慢速后端存储的访问。

> **权威来源**: 操作系统/数据库教材中均将缓存淘汰视为资源受限下的经典权衡问题；
> 现代缓存库（如 Caffeine）则将其作为性能关键路径的核心优化。

---

## 2. 五种策略原理 {#2-五种策略原理}

### 2.1 LRU（Least Recently Used，最近最少使用） {#21-lruleast-recently-used最近最少使用}

- **核心假设**: 刚刚被访问的数据最可能再次被访问（recency bias）。
- **行为**: 维护访问时间顺序，驱逐最久未被访问的键。
- **实现要点**: 通常使用双向链表 + HashMap 达到 O(1) 的 get/put；本项目教学实现使用 `VecDeque` 简化。

**适用场景**: 工作集具有明显时间局部性，如用户会话、HTTP 响应缓存。

### 2.2 LFU（Least Frequently Used，最少使用） {#22-lfuleast-frequently-used最少使用}

- **核心假设**: 历史访问频次高的数据未来更可能被访问（frequency bias）。
- **行为**: 为每个键维护访问计数，优先淘汰计数最低的键；同频次时通常按最久未使用打破平局。
- **实现要点**: 可用最小堆、多个频次桶或 `BTreeMap<(freq, seq), K>` 维护淘汰顺序。

**适用场景**: 存在长期稳定热点的负载，如热门商品、静态资源 CDN。

### 2.3 ARC（Adaptive Replacement Cache） {#23-arcadaptive-replacement-cache}

- **核心思想**: 同时维护 **T1（最近缓存）** 与 **T2（频繁缓存）**，以及对应的幽灵队列 **B1/B2**。
  通过命中幽灵队列的历史反馈，动态调整 T1 的目标大小 `p`，在 recency 与 frequency 之间自适应切换。
- **行为**:
  - T1/T2 命中 → 移入 T2 MRU。
  - B1 命中 → 增加 `p`，说明最近被逐出的数据有价值，偏向 recency。
  - B2 命中 → 减小 `p`，说明频繁访问的数据更有价值，偏向 frequency。
- **实现要点**: 需要四条队列与 `p` 自适应逻辑；完整实现通常使用链表达到 O(1)。

**适用场景**: 工作负载特征未知或会随时间变化，如数据库缓冲池、通用进程内缓存。

### 2.4 CLOCK（Second Chance） {#24-clocksecond-chance}

- **核心思想**: 用环形缓冲区的**引用位（referenced bit）**近似 LRU，避免维护精确的时间戳。
- **行为**:
  - 命中时置引用位为 1。
  - 需要淘汰时，时钟指针顺时针扫描，若引用位为 1 则清零并放行，为 0 则驱逐。
- **实现要点**: `Vec<Slot>` + `HashMap<K, usize>` + 手型指针；平均 O(1)，最坏扫描一圈。

**适用场景**: 操作系统页置换、嵌入式缓存等对实现简单性与内存开销敏感的场景。

### 2.5 W-TinyLFU {#25-w-tinylfu}

- **核心思想**: 将缓存分为一个极小的**窗口 LRU（W）**和一个由 TinyLFU 准入过滤器保护的**主 LRU（M）**。
  新数据先进入窗口；窗口溢出时，候选者需通过 TinyLFU 频率估计击败主缓存中的受害者，才能晋升。
- **行为**:
  - 利用频率 sketch（如 Count-Min Sketch）估计访问频率，抵御扫描型噪声。
  - 窗口保留 recent data 的响应能力，主缓存保留 frequent data 的命中能力。
- **实现要点**: Count-Min Sketch + 两条 LRU 队列 + 准入比较逻辑。

**适用场景**: 存在扫描、突发访问的混合负载，如 Web 缓存、应用级对象缓存（Caffeine 默认策略）。

---

## 3. 命中率对比与直观解释 {#3-命中率对比与直观解释}

| 策略 | recency 负载 | frequency 负载 | 扫描型负载 | 实现复杂度 | 典型命中表现 |
|------|--------------|----------------|------------|------------|--------------|
| LRU  | 高           | 中             | 差         | 低         | 时间局部性强时优秀 |
| LFU  | 中           | 高             | 中         | 中         | 长期热点明显时优秀 |
| ARC  | 高           | 高（自适应）   | 较好       | 高         | 负载特征变化时稳健 |
| CLOCK| 接近 LRU     | 接近 LRU       | 较差       | 低         | LRU 的轻量近似 |
| W-TinyLFU | 高      | 高             | 优秀       | 高         | 综合场景表现均衡 |

> 注：具体命中率强烈依赖工作负载分布（zipf 参数、工作集大小、突发比例），
> 上述为常见定性结论，非绝对排序。

---

## 4. 适用场景与选型建议 {#4-适用场景与选型建议}

- **LRU**: 请求具有明显“最近使用则继续用”模式；实现最简单，适合快速原型与通用缓存。
- **LFU**: 已知存在长期稳定的热门键；需注意“历史噪声”问题（旧高频键长期占用空间）。
- **ARC**: 需要同时服务 recency 与 frequency 负载，且不希望手动调参；数据库/通用缓存常用。
- **CLOCK**: 内存或代码尺寸受限，需要近似 LRU；操作系统页表替换的经典选择。
- **W-TinyLFU**: 现代高并发应用缓存首选，尤其是扫描、突发与稳定热点并存的 Web/微服务场景。

---

## 5. 反例与边界 {#5-反例与边界}

### 5.1 LRU 的扫描型负载陷阱 {#51-lru-的扫描型负载陷阱}

负载：`1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, ...`，缓存容量 3。
LRU 会把一次性扫描键也缓存起来，挤出真正重复访问的键，命中率接近 0。
**W-TinyLFU / LFU / ARC 在此类场景更稳健**。

### 5.2 LFU 的“旧热点”问题 {#52-lfu-的旧热点问题}

键 A 在过去被访问 1000 次，但未来不再被访问；键 B 为新热点。
LFU 会长期保留 A，导致 B 被频繁淘汰。可通过**衰减计数器（aging）**缓解。

### 5.3 ARC 的幽灵队列内存开销 {#53-arc-的幽灵队列内存开销}

ARC 需要维护 B1/B2 幽灵队列，总元数据量可达 `2×capacity`。在容量极大或键很长的场景下，
需权衡元数据内存与命中率收益。

### 5.4 CLOCK 的最坏情况 {#54-clock-的最坏情况}

当所有槽位引用位均为 1 时，CLOCK 需要完整扫描一圈才能找到可驱逐槽位，
退化为 O(capacity)。可通过**多位引用计数**或**分段 CLOCK**改进。

### 5.5 W-TinyLFU 的参数敏感性 {#55-w-tinylfu-的参数敏感性}

窗口大小（window size）与 sketch 宽度直接影响对突发负载的响应速度；
过小则退化为 TinyLFU，过大则对扫描敏感。实际系统通常基于经验或自动调参确定。

---

## 6. 代码实现锚点 {#6-代码实现锚点}

本项目的实现位于 `crates/c08_algorithms`：

| 策略 | 实现文件 | 示例/对比 |
|------|----------|-----------|
| LRU | [crates/c08_algorithms/src/data_structure/lru_cache.rs](../../crates/c08_algorithms/src/data_structure/lru_cache.rs) | [cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |
| LFU | [crates/c08_algorithms/src/data_structure/lfu_cache.rs](../../crates/c08_algorithms/src/data_structure/lfu_cache.rs) | [cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |
| ARC | [crates/c08_algorithms/src/data_structure/arc_cache.rs](../../crates/c08_algorithms/src/data_structure/arc_cache.rs) | [cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |
| CLOCK | [crates/c08_algorithms/src/data_structure/clock_cache.rs](../../crates/c08_algorithms/src/data_structure/clock_cache.rs) | [cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |
| W-TinyLFU | [crates/c08_algorithms/src/data_structure/w_tinylfu_cache.rs](../../crates/c08_algorithms/src/data_structure/w_tinylfu_cache.rs) | [cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |

---

## 7. 权威来源分级（P0 / P1 / P2） {#7-权威来源分级p0-p1-p2}

- **P0（原始论文/官方实现）**:
  - [Megiddo & Modha, USENIX FAST 2003 – ARC](https://www.usenix.org/legacy/events/fast03/tech/full_papers/megiddo/megiddo.pdf)
  - [Einziger et al., EuroSys 2015 – TinyLFU / W-TinyLFU](https://dl.acm.org/doi/10.1145/2674005.2674994)
  - [Caffeine – high performance Java caching library](https://github.com/ben-manes/caffeine)

- **P1（经典教材/百科/权威博客）**:
  - [Wikipedia – Cache replacement policies](https://en.wikipedia.org/wiki/Cache_replacement_policies)
  - [Operating Systems: Three Easy Pieces – Page Replacement](http://pages.cs.wisc.edu/~remzi/OSTEP/vm-beyondphys-policy.pdf)
  - [Ben Manes – Designing a Concurrent Cache](https://highscalability.com/design-of-a-modern-cache/)

- **P2（社区实现/教学资料）**:
  - [Rust crates.io – lru crate](https://crates.io/crates/lru)
  - [Rust crates.io – cached crate](https://crates.io/crates/cached)
  - [System Design Primer – Caching](https://github.com/donnemartin/system-design-primer#caching)

---

## 8. 小结 {#8-小结}

缓存淘汰策略没有 universally best 的选择，关键在于理解**工作负载特征**与**策略假设**的匹配关系：

- recency 重要 → LRU / CLOCK
- frequency 重要 → LFU
- 负载混合或未知 → ARC / W-TinyLFU

本项目的五种实现统一实现了 `CachePolicy` trait，可通过 `crates/c08_algorithms/examples/cache_eviction_policies_demo.rs`
直接运行并对比命中率。

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**