# Rust 生态系统分析

## 包管理与供应链

- crates.io 信任链；`cargo-audit`/`supply-chain` 风险

## 关键领域生态

- 异步（tokio/async-std）；Web（axum/actix）；数据（polars/arrow）；
- 安全/验证（kani/creusot/prusti/loom）

## 风险与趋势

- 语义版本与破坏性变更；unsafe 面积；
- 稳定特性扩展（GAT、泛型特性专用化、宏2）

---

## 领域版图（扩展）

- 数据工程：Polars、Arrow、DataFusion、DeltaLake
- 可观测性：tracing、opentelemetry、prometheus-client
- 分布式：tonic、tower、etcd-client、quinn(QUIC)
- 区块链/Web3：ethers-rs、alloy、substrate
- 嵌入式/IoT：embassy、RTIC、no_std 生态

## 成熟度指标（建议）

- 维护活跃度（提交频率/发布节奏）
- 安全性（`RUSTSEC` 报告、`unsafe` 面积）
- 文档/示例密度（quickstart/教程/参考）
- 向后兼容/语义版本遵循度

## 供应链与合规

- SBOM 生成（`cargo auditable`）与依赖白名单
- 许可证扫描（`cargo-deny`）与盈余条款排查
- 可复现构建（锁定版本、vendor 源）
- 可信仓库与镜像：企业私有 crates 镜像、代理审核流程
- 依赖治理：临界依赖门禁、替代方案清单（RFC 记录）

## 选型建议（摘要）

- 服务端 IO 密集：tokio + axum + tower + tracing
- 高吞吐网络：quinn(QUIC) + zero-copy + io-uring（条件）
- 科学计算：ndarray + nalgebra + polars
- 形式化/验证：creusot/prusti/kani + loom
- 嵌入式：no_std + embassy + defmt + probe-rs

## 成熟度打分卡（模板）

| 指标 | 权重 | 说明 | 打分(1-5) |
|---|---:|---|---:|
| 维护活跃度 | 0.25 | 提交/发布节奏 |  |
| 安全性 | 0.25 | RUSTSEC/unsafe 面积 |  |
| 文档完整性 | 0.20 | 教程/参考/示例 |  |
| 兼容稳定性 | 0.15 | 语义版本/破坏变更 |  |
| 社区/治理 | 0.15 | issue 响应/维护者规模 |  |

### 治理与风险画像（补充）

- 单点维护者风险：Bus Factor < 2 的关键 crates 标红
- 资金与赞助：OpenCollective/企业支持状况
- 安全事件历史：RUSTSEC 记录与响应时间
- 依赖集中度：Top N 依赖权重分布与替代度

加权总分 = Σ(权重×打分)。≥4 建议生产可用，3-4 需审慎试点，<3 避免核心依赖。

## 供应链实践清单

1. 生成 SBOM（`cargo auditable`），纳入制品库；
2. `cargo deny` 启用许可证与漏洞门禁；
3. 关键依赖设白名单与镜像 vendor；
4. 采用可复现构建：锁定版本、禁用网络（CI）；
5. 定期 `cargo audit` 与变更周报。
6. 对高风险 crate 建立“替代路线卡”（迁移步骤/兼容垫片）。

## 领域蓝图（补充）

- 流处理：arroyo、fluvio、rdkafka、nats.rs
- 存储：tikv-client、sled、redb
- 图计算：raphtory-rs、graphlib
- 可视化/GUI：tauri、egui、slint
- 数据同步：capnpc/capnproto-rust、flatbuffers-rs
