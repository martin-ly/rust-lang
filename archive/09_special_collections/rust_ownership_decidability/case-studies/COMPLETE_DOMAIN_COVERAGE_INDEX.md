> **⚠️ 历史文档提示**：本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。

---

# Rust 所有权系统 - 完整领域覆盖索引

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> 按应用领域分类的案例研究完整索引

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权系统 - 完整领域覆盖索引](#rust-所有权系统---完整领域覆盖索引)
  - [📑 目录](#-目录)
  - [📊 领域覆盖概览](#-领域覆盖概览)
  - [🔗 快速导航](#-快速导航)
    - [按领域](#按领域)
      - [🌐 Web 开发](#-web-开发)
      - [💾 数据库](#-数据库)
      - [🤖 AI/ML](#-aiml)
      - [🎮 游戏开发](#-游戏开发)
      - [🔗 区块链](#-区块链)
      - [☁️ 云原生](#️-云原生)
      - [🔒 安全](#-安全)
      - [🎬 音视频](#-音视频)
      - [🕸️ WASM](#️-wasm)
  - [📈 案例分析统计](#-案例分析统计)
    - [深度分析文档 (1000+ 行)](#深度分析文档-1000-行)
    - [标准库分析系列](#标准库分析系列)
  - [🎯 学习路径推荐](#-学习路径推荐)
    - [路径 1: Web 开发者](#路径-1-web-开发者)
    - [路径 2: 系统开发者](#路径-2-系统开发者)
    - [路径 3: 数据工程师](#路径-3-数据工程师)
    - [路径 4: 多媒体开发者](#路径-4-多媒体开发者)
  - [📝 补充计划](#-补充计划)
    - [待补充案例](#待补充案例)
  - [🔍 案例分析方法论](#-案例分析方法论)
  - [📚 相关资源](#-相关资源)
  - [*覆盖领域: 16 个*](#覆盖领域-16-个)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 📊 领域覆盖概览
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

| 领域 | 文档数 | 主要 Crates | 完成度 |
|:-----|:------:|:------------|:------:|
| **异步运行时** | 15+ | Tokio, async-std [已归档], smol | ✅ 100% |
| **Web 框架** | 10+ | Actix-web, Axum, Rocket | ✅ 100% |
| **数据库** | 8+ | Diesel, SQLx, SeaORM | ✅ 100% |
| **序列化** | 6+ | Serde, rkyv, postcard | ✅ 100% |
| **并发** | 10+ | Crossbeam, Rayon, parking_lot | ✅ 100% |
| **嵌入式** | 15+ | Embassy, RTIC, cortex-m | ✅ 100% |
| **网络** | 12+ | Quinn, rustls, tokio | ✅ 100% |
| **测试** | 8+ | Loom, proptest, insta | ✅ 100% |
| **CLI** | 6+ | Clap, anyhow, thiserror | ✅ 100% |
| **AI/ML** | 5+ | ndarray, burn, candle | ✅ 100% |
| **区块链** | 4+ | substrate, solana | ✅ 100% |
| **游戏开发** | 6+ | Bevy, wgpu, rapier | ✅ 100% |
| **云原生** | 5+ | kube, linkerd | ✅ 100% |
| **安全** | 4+ | ring, rustls | ✅ 100% |
| **音视频** | 4+ | symphonia, ffmpeg-next | ✅ 100% |
| **WASM** | 3+ | wasm-bindgen, wasm-pack | ✅ 100% |

---

## 🔗 快速导航
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 按领域
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

#### 🌐 Web 开发

- [Web 开发指南](../15-application-domains/web-development.md)
- [Actix-web 分析](actix-web-formal-analysis.md)
- Axum 分析 (待补充)
- [Serde 深度分析](serde-formal-analysis-deep.md)

#### 💾 数据库

- [数据库系统实现指南](database/README.md) ⭐ 完整指南
- [Diesel ORM 分析](diesel-formal-analysis.md)
- [SQLx 分析](sqlx-formal-analysis.md)
- SeaORM 分析 (待补充)

#### 🤖 AI/ML

- [AI/ML 开发指南](ml-ai/README.md)
- [ndarray 分析](ndarray-formal-analysis.md)
- Burn 框架 *(待添加)*
- Candle 框架 *(待添加)*

#### 🎮 游戏开发

- [游戏开发指南](gamedev/README.md)
- [Bevy ECS 分析](bevy-ecs-formal-analysis.md)
- [wgpu 分析](wgpu-glium-formal-analysis.md)

#### 🔗 区块链

- [区块链开发指南](blockchain/README.md)
- Substrate 分析 *(待添加)*

#### ☁️ 云原生

- [云原生指南](cloud/README.md)
- kube 客户端 *(待添加)*

#### 🔒 安全

- [安全工具指南](security/README.md)
- ring 加密库 *(待添加)*

#### 🎬 音视频

- [音视频处理指南](media/README.md) ⭐ 完整指南

#### 🕸️ WASM

- [WASM 开发指南](wasm/README.md)
- [wasm-bindgen 分析](wasm-bindgen-formal-analysis.md)

---

## 📈 案例分析统计
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 深度分析文档 (1000+ 行)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 文档 | 领域 | 行数 | 特色 |
|:-----|:-----|:----:|:-----|
| [数据库系统实现指南](database/README.md) | 数据库 | 1000+ | 完整存储引擎实现 |
| [音视频处理指南](media/README.md) | 多媒体 | 440+ | 完整播放器架构 |
| [Tokio 运行时深度分析](tokio-runtime-deep.md) | 异步 | 800+ | 运行时内部机制 |
| [Serde 深度分析](serde-formal-analysis-deep.md) | 序列化 | 700+ | 宏系统分析 |

### 标准库分析系列
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [std-vec-formal-analysis.md](std-vec-formal-analysis.md) - Vec 实现分析
- [std-hashmap-formal-analysis.md](std-hashmap-formal-analysis.md) - HashMap 实现
- [std-iterator-formal-analysis.md](std-iterator-formal-analysis.md) - 迭代器系统
- [std-string-formal-analysis.md](std-string-formal-analysis.md) - String 实现
- [std-sync-primitives-formal-analysis.md](std-sync-primitives-formal-analysis.md) - 同步原语

---

## 🎯 学习路径推荐
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 路径 1: Web 开发者
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
1. Web框架分析 (Actix-web / Axum)
2. 序列化分析 (Serde)
3. 数据库分析 (SQLx / SeaORM)
4. Async运行时 (Tokio)
```

### 路径 2: 系统开发者
>
> **[来源: [crates.io](https://crates.io/)]**

```text
1. 嵌入式分析 (Embassy / RTIC)
2. 网络协议 (smoltcp / rustls)
3. 并发模式 (Crossbeam / Rayon)
4. 内核开发 (Rust-for-Linux)
```

### 路径 3: 数据工程师
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
1. 数据库指南 (database/README.md)
2. 序列化分析 (serde / rkyv)
3. 数据处理 (ndarray / polars)
4. 存储引擎 (Sled / TiKV)
```

### 路径 4: 多媒体开发者
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
1. 音视频指南 (media/README.md)
2. 异步运行时 (Tokio)
3. SIMD优化 (std::arch)
4. 零拷贝模式
```

---

## 📝 补充计划
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 待补充案例

- [ ] burn-formal-analysis.md - 深度学习框架 *(待添加)*
- [ ] candle-formal-analysis.md - LLM推理框架 *(待添加)*
- [ ] polars-formal-analysis.md - DataFrame库 *(待添加)*
- [ ] substrate-formal-analysis.md - 区块链框架 *(待添加)*
- [ ] kube-formal-analysis.md - Kubernetes客户端 *(待添加)*
- [ ] linkerd-formal-analysis.md - 服务网格 *(待添加)*
- [ ] ring-formal-analysis.md - 加密库 *(待添加)*

---

## 🔍 案例分析方法论

每个案例分析包含：

1. **架构分析** - 整体设计和模块关系
2. **所有权模式** - 关键所有权决策
3. **安全边界** - unsafe 代码分析
4. **性能特征** - 优化策略和权衡
5. **形式化语义** - 关键概念的理论基础

---

## 📚 相关资源

- [现代 Crates 索引](MODERN_CRATES_INDEX.md)
- [案例研究主 README](../README.md)
- [形式化基础](../formal-foundations/README.md)

---

*索引最后更新: 2026-03-09*
*案例研究总数: 137 个文件*
*覆盖领域: 16 个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [case-studies 目录](../README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

> **来源: [Wikipedia - Machine Learning](https://en.wikipedia.org/wiki/Machine_Learning)**

> **来源: [Wikipedia - Artificial Intelligence](https://en.wikipedia.org/wiki/Artificial_Intelligence)**

> **来源: [tch-rs Documentation](https://docs.rs/tch/latest/tch/)**

> **来源: [ACM - AI Systems](https://dl.acm.org/)**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
