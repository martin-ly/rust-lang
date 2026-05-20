# 对称差分析与后续任务计划（2026-05-21）

> **生成日期**: 2026-05-21
> **基准版本**: Rust 1.95.0+ (Edition 2024)
> **对应报告**: `RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md` v2.0

---

## 一、本次完成的工作

### 1.1 `docs/rust-ownership-decidability/` 子项目清理

| 任务 | 数量 | 状态 |
|:---|:---:|:---|
| 短 README 归档（<1000 字符纯目录索引） | 23 个 | ✅ 已完成 |
| 死链接修复 | 26 个 | ✅ 已清零 |

**归档文件列表**:

- `00-foundations/README.md`, `01-core-concepts/README.md`, `03-verification-tools/README.md`
- `04-decidability-analysis/README.md`, `05-comparative-study/README.md`, `06-visualizations/README.md`
- `11-design-patterns/behavioral/README.md`, `creational/README.md`, `rust-specific/README.md`, `structural/README.md`
- `13-architecture-patterns/README.md`, `14-distributed-systems/README.md`
- `16-program-semantics/04-verification/README.md`, `archive/README.md`, `audit_reports/README.md`
- `case-studies/README.md`, `exercises/README.md`
- `formal-foundations/models/README.md`, `proofs/README.md`, `semantics/README.md`
- `visualizations/README.md`, `decision-trees/README.md`, `matrices/README.md`

### 1.2 矩阵与报告更新

| 文档 | 更新内容 |
|:---|:---|
| `docs/07_future/rust_project_goals_2026_matrix.md` | Higher-level Rust 覆盖度 🔴20%→🟡75%；cargo-script 覆盖率提升至 🟢80%；P0/P1 任务重新排序 |
| `reports/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md` | 任务清单更新：R3–R6 标记为完成；T1–T22 重新编号和分类 |

---

## 二、对称差分析：项目 vs 国际最新 Rust 主题

### 2.1 已完全对齐（✅）

| 领域 | 覆盖状态 |
|:---|:---|
| Rust 1.95 核心 API | 100% — `if let` guards, `cfg_select!`, `core::range`, `Atomic*::update`, `cold_path`, `push_mut` 等全已覆盖 |
| Cargo Script / Frontmatter | 🟢 80% — 独立章节 + 工具链指南 |
| Public/Private Dependencies | 🟢 80% — RFC 3516 独立章节 |
| WASIp1/p2 目标体系 | ✅ — `wasm32-wasi` 已迁移 |
| async-std 清理 | ✅ — 已归档/移除 |

### 2.2 部分覆盖，需深化（🟡）

| 主题 | 现有文件 | 缺口 |
|:---|:---|:---|
| Async Closures | 代码有，指南待确认深度 | 需验证 `c06_async/docs/ASYNC_CLOSURES_GUIDE.md` 完整性 |
| AFIT dyn 兼容 | `crates/c06_async/src/afit_dyn_tracking.rs` (265 行) | 需更新 nightly 状态 |
| io_uring | `crates/c10_networks/src/io_uring_demo.rs` (254 行) | 需概念文档 |
| QUIC/HTTP3 | `crates/c10_networks/src/http3_quic.rs` (207 行) | 需架构分析 |
| libp2p | `crates/c10_networks/src/libp2p_advanced.rs` (813 行) | 需协议栈分析 |
| Embassy | `crates/c13_embedded/src/embassy_framework.rs` (515 行) | 需形式化分析 |
| RTIC | `crates/c13_embedded/src/rtic_framework.rs` (565 行) | 需实时性分析 |
| Rust for Linux | `crates/c07_process/src/rust_for_linux_preview.rs` (457 行) | 需内核 API 对照 |
| eBPF + Rust | `crates/c07_process/src/ebpf_aya.rs` (394 行) | 需程序类型矩阵 |
| Const Generics | 概念文档有，代码示例缺 | `adt_const_params`, `min_generic_const_args` |

### 2.3 完全缺失（🔴）

| 主题 | 紧迫度 | 说明 |
|:---|:---:|:---|
| Next-generation trait solver | P0 | 2026 稳定化目标；需概念章节 + nightly 代码 |
| Field Projections | P0 | Beyond the `&` 旗舰主题核心；与 Pin/智能指针联动 |
| Immobile types | P1 | nightly 原型；与 Pin 替代关系 |
| Open Enums | P2 | nightly 实验 |
| MC/DC Coverage | P2 | Safety-Critical 路线 |
| BorrowSanitizer | P2 | 原型阶段 |
| SBOM / cargo-semver-checks | P2 | 工具链演进 |
| Cargo "plumbing" commands | P2 | 原型阶段 |

---

## 三、后续任务计划（按优先级排序）

### 🔴 P0 — 立即执行

| 编号 | 任务 | 目标文件 | 状态 |
|:---:|:---|:---|:---:|
| T1 | Async Closures 深度指南 | `crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md` (462 行) | ✅ 已存在 |
| T2 | AFIT dyn 跟踪更新 | `crates/c06_async/src/afit_dyn_tracking.rs` (265 行) | ✅ 已存在 |
| T3 | `static mut` 文档示例更新 | `docs/02_reference/quick_reference/testing_cheatsheet.md` | ✅ 已修复 |
| T4 | Next-gen trait solver 概念章节 | `concept/02_intermediate/01_traits.md` §十二 + `crates/c04_generic/src/next_solver_preview.rs` | ✅ 已完成 |
| T5 | Field Projections 概念章节 | `concept/02_intermediate/03_memory_management.md` §十一 | ✅ 已完成 |

### 🟡 P1 — 补充深化

| 编号 | 任务 | 目标文件 | 状态 |
|:---:|:---|:---|:---:|
| T6 | io_uring 深度指南 | `docs/03_guides/IO_URING_GUIDE.md` (深化至 260 行+) | ✅ 已完成 |
| T7 | QUIC/HTTP3 指南 | `docs/03_guides/QUIC_HTTP3_GUIDE.md` (新建) | ✅ 已完成 |
| T8 | libp2p 指南 | `docs/03_guides/LIBP2P_GUIDE.md` (新建) | ✅ 已完成 |
| T9 | Embassy/RTIC 嵌入式指南 | `docs/03_guides/EMBEDDED_RUST_GUIDE.md` (新建) | ✅ 已完成 |
| T10 | Rust for Linux 指南 | `docs/03_guides/RUST_FOR_LINUX_GUIDE.md` (新建) | ✅ 已完成 |
| T11 | eBPF + Rust (Aya) | `docs/03_guides/RUST_FOR_LINUX_GUIDE.md` §eBPF | ✅ 已覆盖 |
| T12 | Const Generics 扩展 | `crates/c04_generic/src/const_generics_extended_preview.rs` (326 行) | ✅ 已存在 |
| T13 | `use<..>` precise capturing 指南 | `crates/c02_type_system/src/precise_capturing_guide.rs` (211 行) | ✅ 已存在 |
| T14 | Safety-Critical Rust 路线对齐 | `docs/04_research/safety_critical_alignment_2026.md` (新建) | ✅ 已完成 |

### 🟢 P2 — 跟踪观察 & 基础设施（剩余）

| 编号 | 任务 | 目标文件 | 状态 |
|:---:|:---|:---|:---:|
| T15 | Safety Tags 预研指南 | `docs/05_guides/SAFETY_TAGS_GUIDE.md` | ✅ 已完成 |
| T16 | 并行前端编译指南 | `docs/06_toolchain/parallel_frontend.md` | ✅ 已完成 |
| T17 | `derive(CoercePointee)` 跟踪 | `c04_generic/src/derive_coerce_pointee_tracking.rs` | ✅ 已完成 |
| T18 | 版本跟踪表更新 | `concept/07_future/05_rust_version_tracking.md` | ✅ 已完成 |
| T19 | 非 Web 场景补充 | `content/scenarios/embedded_systems_scenarios.md` + `systems_infrastructure_scenarios.md` | ✅ 已完成 |
| T20 | AI 编程指南 2026 版 | `guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md` (227 行) | ✅ 已存在 |
| T21 | `knowledge/` 交叉引用补充 | 101 个文件添加交叉引用 | ✅ 已完成 |

---

## 四、质量指标当前状态

| 轨道 | Bloom | 来源率 | 死链接 | 跨文件链接 |
|:---|:---:|:---:|:---:|:---:|
| `concept/` | 50/50 ✅ | 17.3% ✅ | 0 ✅ | 50/50 ✅ |
| `knowledge/` | 129/129 ✅ | 15.8% ✅ | 0 ✅ | 16/129 ⚠️ |
| `docs/` (活跃) | N/A | 14.2% ✅ | 0 ✅ | 459/1125 ⚠️ |
| `rust-ownership-decidability/` | N/A | N/A | 0 ✅ | 验证中 |

---

> **权威来源**: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/flagships.html), [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **文档版本**: 1.0
> **最后更新**: 2026-05-21
