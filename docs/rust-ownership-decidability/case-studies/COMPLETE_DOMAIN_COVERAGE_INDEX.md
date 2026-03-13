# Rust 所有权系统 - 完整领域覆盖索引

> 按应用领域分类的案例研究完整索引

---

## 📊 领域覆盖概览

| 领域 | 文档数 | 主要 Crates | 完成度 |
|:-----|:------:|:------------|:------:|
| **异步运行时** | 15+ | Tokio, async-std, smol | ✅ 100% |
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

### 按领域

#### 🌐 Web 开发

- [Web 开发指南](../15-application-domains/web-development.md)
- [Actix-web 分析](actix-web-formal-analysis.md)
- [Axum 分析](axum-formal-analysis.md)
- [Serde 深度分析](serde-formal-analysis-deep.md)

#### 💾 数据库

- [数据库系统实现指南](database/README.md) ⭐ 完整指南
- [Diesel ORM 分析](diesel-formal-analysis.md)
- [SQLx 分析](sqlx-formal-analysis.md)
- [SeaORM 分析](sea-orm-formal-analysis.md)

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

### 深度分析文档 (1000+ 行)

| 文档 | 领域 | 行数 | 特色 |
|:-----|:-----|:----:|:-----|
| [数据库系统实现指南](database/README.md) | 数据库 | 1000+ | 完整存储引擎实现 |
| [音视频处理指南](media/README.md) | 多媒体 | 440+ | 完整播放器架构 |
| [Tokio 运行时深度分析](tokio-runtime-deep.md) | 异步 | 800+ | 运行时内部机制 |
| [Serde 深度分析](serde-formal-analysis-deep.md) | 序列化 | 700+ | 宏系统分析 |

### 标准库分析系列

- [std-vec-formal-analysis.md](std-vec-formal-analysis.md) - Vec 实现分析
- [std-hashmap-formal-analysis.md](std-hashmap-formal-analysis.md) - HashMap 实现
- [std-iterator-formal-analysis.md](std-iterator-formal-analysis.md) - 迭代器系统
- [std-string-formal-analysis.md](std-string-formal-analysis.md) - String 实现
- [std-sync-primitives-formal-analysis.md](std-sync-primitives-formal-analysis.md) - 同步原语

---

## 🎯 学习路径推荐

### 路径 1: Web 开发者

```
1. Web框架分析 (Actix-web / Axum)
2. 序列化分析 (Serde)
3. 数据库分析 (SQLx / SeaORM)
4. Async运行时 (Tokio)
```

### 路径 2: 系统开发者

```
1. 嵌入式分析 (Embassy / RTIC)
2. 网络协议 (smoltcp / rustls)
3. 并发模式 (Crossbeam / Rayon)
4. 内核开发 (Rust-for-Linux)
```

### 路径 3: 数据工程师

```
1. 数据库指南 (database/README.md)
2. 序列化分析 (serde / rkyv)
3. 数据处理 (ndarray / polars)
4. 存储引擎 (Sled / TiKV)
```

### 路径 4: 多媒体开发者

```
1. 音视频指南 (media/README.md)
2. 异步运行时 (Tokio)
3. SIMD优化 (std::arch)
4. 零拷贝模式
```

---

## 📝 补充计划

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
- [案例研究主 README](README.md)
- [形式化基础](../formal-foundations/README.md)

---

*索引最后更新: 2026-03-09*
*案例研究总数: 137 个文件*
*覆盖领域: 16 个*
