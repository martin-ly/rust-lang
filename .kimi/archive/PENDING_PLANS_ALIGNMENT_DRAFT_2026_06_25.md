# 本项目未完成计划与任务全面梳理（在线对齐草案）

> 生成时间：2026-06-25
> 主控文件：`.kimi/EXECUTION_CHECKLIST_2026_06_22.md`
> 唯一硬截止：**2026-07-09** Rust 1.97.0 发布日

---

## 一、当前执行主控状态

根据 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`（4 周执行清单，2026-06-23 ~ 2026-07-20）：

- **Week 1/2/4**：已完成
- **Week 3**：剩余 7 项待完成，全部围绕 **2026-07-09 Rust 1.97.0 发布日**

### P0 — 硬截止 2026-07-09 的 8 项任务

| 编号 | 任务 | 依赖/风险 |
|---|---|---|
| A3.1 | 执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 上游实际发布日期 |
| A3.2 | 更新 `rust-toolchain.toml` 到 `1.97.0` | 依赖 A3.1 |
| A3.3 | 激活 `crates/c08_algorithms/src/rust_197_features.rs` 占位代码 | `retain_back` 可能推迟 |
| A3.4 | 运行 `cargo test --workspace` | 依赖 A3.2/A3.3 |
| A3.5 | 更新 `concept/07_future/rust_1_97_preview.md` 状态并迁移 | 依赖 A3.1 |
| A3.6 | 完善 `CHANGELOG.md [3.1.0]` 条目 | 依赖 A3.1/A3.3 |
| A3.7 | 更新术语表中 1.97 术语状态 | 依赖上游实际稳定内容 |
| — | 补充 1.97 特性相关练习 | 依赖特性稳定性 |

### 在线对齐发现（Rust 1.97）

- **release.rs** 确认 Rust 1.97.0 目标发布日为 **2026-07-09**（距今日 14 天）。
- **PR #151973** `VecDeque::truncate_front` / `retain_back` 当前标签为 `finished-final-comment-period` / `disposition-merge`，即 **已走完 FCP，等待合并**，进入 1.97 的概率较高。
- 但 `retain_back` 在部分 nightly 快照中不可见，**存在推迟到 1.98 的风险**。
- 其他占位特性（`float_algebraic`、`RandomSource`、`box_vec_non_null`、`int_format_into`、C-variadic）需根据发布日实际稳定列表逐一核对。

---

## 二、未完成内容分类汇总

### A. 版本特性与权威来源修正（P0-P1）

| 主题 | 当前问题 | 在线事实 | 建议动作 |
|---|---|---|---|
| **async closures** | `content/emerging/async_closures.md` 仍标 nightly-only；多处标注未更新 | **Rust 1.85.0（2025-02-20）已 stable** async closures / `AsyncFn*` traits | 全局修正为 1.85.0 stable，更新示例 |
| **Rust 2024 Edition** | `knowledge/06_ecosystem/02_edition_2024.md` 写为 1.82.0+；混淆 `gen` 关键字与 `gen {}` | **Rust 2024 Edition 在 1.85.0 stable**；`gen` 是保留关键字，`gen {}` blocks 仍为 nightly | 修正 Edition 版本号为 1.85.0+；区分 `gen` 关键字 vs `gen blocks` |
| **`&raw const`** | 全局存在非官方术语 `&const` | 官方术语为 `&raw const` / `&raw mut` | 全局替换并统一 |
| **never type `!`** | 标注状态可能滞后 | PR #155697 仍在推进，**未完全 stable** | 保持跟踪，勿提前标 stable |
| **gen blocks / async gen** | 可能标为即将稳定 | `gen {}` 仍为 nightly；async gen 更远 | 稳定度标注统一为 nightly/preview |
| **RTN** | 部分文档可能暗示接近稳定 | 2025-05 Project Goals Update：**RTN 因下一代 trait solver 顾虑被 block** | 更新为长期跟踪 |
| **AFIDT / `dyn async Trait`** | `async_trait` → AFIDT 迁移计划可能过于乐观 | async fn in dyn trait 仍需更多实验和初始 RFC；`dynosaur` 仍为实验性 | 文档侧先更新，代码侧保留 `async_trait` 直到稳定 |
| **async drop** | 可能标为即将稳定 | 2025 仍为实验性原型 | 标注为实验性 |

### B. Rust 1.96 覆盖缺口（P1）

根据 release.rs / 官方 release notes，1.96.0（2026-05-28）已 stable 以下内容，但项目尚未完整覆盖：

- `assert_matches!` / `debug_assert_matches!`
- `core::range::{Range, RangeIter, RangeFrom, RangeFromIter, RangeToInclusive, RangeToInclusiveIter}`
- `NonZero` 整数范围迭代
- `From<T> for AssertUnwindSafe<T>`
- `From<T> for LazyCell<T, F>` / `LazyLock<T, F>`
- s390x vector registers inline assembly
- `valid for read/write` 定义重构
- Cargo CVE-2026-5222 / 5223 修复
- rustdoc 1.96 改进（`missing_doc_code_examples` lint、sidebar 分离等）

### C. 内容清理、去重与价值审计（P1）

| 问题 | 数量/范围 | 状态 |
|---|---|---|
| `docs/` A/B/C 价值审计 | 861 个 C 类文件，883 个问题 | 进行中 |
| 高相似文件合并 | 109 对潜在相似，需关注 ≥0.90 且 Jaccard ≥0.5 | 下季度复测 |
| `docs/` 死链 | 915 个本地死链（历史数据） | 待修复 |
| `concept/` 编号冲突 | 如 `10_numerics.md` vs `10_error_handling_basics.md` | 待解决 |
| 双元数据系统 | 统一元数据模板 | 待解决 |
| `rust-ownership-decidability/` 迁移 | 核心结论迁到 `concept/04_formal/`，原目录归档 | 阶段 3 待执行 |
| `docs/content/` 重复目录 | 与顶层 `content/` 重复，多为迁移 stub | 待清理 |
| 季度僵尸文件 | 3 个（`docs/02_reference/README.md` 等） | 待审查 |

### D. 结构性内容缺口

#### 1. 索引引用缺失文件（~13 个）

- `concept/07_future/19_rust_edition_preview.md`（`concept/SUMMARY.md` 引用）
- `docs/07_project/07_task_index.md`
- `content/emerging/generic_const_items.md`
- `content/emerging/coroutines.md`
- `content/academic/rustbelt_formal_verification.md`
- `content/academic/tree_borrows_pldi_2025.md`
- `content/scenarios/distributed_system.md`
- 以及 `CONTENT_CRATES_MAPPING.md` 中多处路径不一致

#### 2. 占位/待补充主题

- `io_uring`、`QUIC`、`libp2p`：🔴 占位
- `Embassy`、`RTIC`、`Rust for Linux`、`eBPF + Aya`：⚠️ 待深化
- `Return Type Notation`：10% 完成
- `Coroutine Trait`：15% 完成
- `Impl Trait in Assoc Type`：40% 完成
- 9 个 `docs/02_reference/quick_reference/*.md` 中 “Rust 1.91/1.92 特性演示（代码示例待补充）”

#### 3. 形式化/安全关键

- `docs/rust-ownership-decidability/` 中 5 个 Coq 证明仍 `admit` 待完成
- AutoVerus、ESBMC、TrustInSoft 未覆盖
- Safety Tags、BorrowSanitizer、Tree Borrows、AutoVerus/Verus 概念页与可编译示例缺失
- Safety-Critical 工作组未落地（负责人/预算/认证体系）

### E. 生态迁移与依赖安全

| 项目 | 当前状态 | 阻塞/风险 |
|---|---|---|
| **Sea-ORM 2.0** | workspace 仍用 `2.0.0-rc.41` | 等待上游 `2.0.0` stable |
| **async-std** | 代码层已清零，活跃文档已标注 | 中优先级 7 个文档文件待清理 |
| **`async_trait` → AFIDT/dynosaur** | 文档侧待更新 | AFIDT 未 stable，代码侧不能移除 |
| **`hickory-proto 0.25.2`** | RUSTSEC-2026-0118/0119 | 等待 `libp2p 0.57+` 升级 |
| **`rsa 0.9.10`** | RUSTSEC-2023-0071 Marvin Attack | MySQL 后端未启用，代码路径不可达，持续跟踪 |
| **`cargo-vet`** | Windows 编译失败（LockFileEx） | 等待上游修复 |
| **大量传递依赖版本落后** | 899 个唯一包 | 定期评估升级 |

### F. 教学增强与国际化（P2-P3）

- `LEARNING_MVP_PATH.md` 精化与英文版
- TRPL 3rd Ed 逐章对照 + Brown Book 所有权 Inventory 映射
- Google Comprehensive Rust 课程映射
- Aquascope 可视化集成被工具链阻塞，需 Mermaid/自定义 SVG 替代方案
- `concept/` 273 个英文骨架
- 3 零基础 + 2 有经验可用性测试
- 教师/讲师反馈
- Rust 中文社区对接

### G. 编译器/Cargo/工具链深度内容（P2）

- rustc query system / new trait solver
- MIR / codegen / LLVM backend
- Cargo resolver v3 / public-private deps / build scripts / registries
- Cranelift backend / parallel frontend / build-std
- Pin ergonomics / RTN / Field Projections
- `cargo-script` 实战

### H. 通用 PL 基座与 Effect System（P3-长期）

- 变量模型、求值策略（CBV/CBN/CBR）、副作用与纯度
- 控制流理论（结构化程序定理、Continuation、CFG）
- 数据抽象谱系、C/C++ ABI 与对象模型对比
- `const_trait_impl_preview.md` 深度重写（`~const` 方向已废弃）
- Effect System 独立章节（可选）

---

## 三、关键阻塞与风险

| 阻塞项 | 影响 | 在线事实/缓解 |
|---|---|---|
| Rust 1.97.0 正式发布 | A3.x 全部任务 | release.rs 确认 07-09；保留等效实现，标注“推迟至 1.98” |
| `VecDeque::retain_back` 稳定性 | A3.3 / A3.5 / A3.7 | PR #151973 已 FCP 完成，等待合并；仍存在推迟风险 |
| `cargo audit` 无法联网 | 依赖安全审计 | 本地脚本 `scripts/supply_chain_audit.py` 兜底 |
| Sea-ORM 2.0 stable | 生态迁移 | 上游未发布，记录阻塞 |
| AFIDT / `dyn async Trait` | `async_trait` 移除 | 2025H1 Project Goals：仍需 RFC 和实验；短期不可移除 |
| RTN 稳定 | async trait 完整故事 | 因下一代 trait solver 顾虑被 block |
| 形式化/安全关键专家缺失 | L4 可信度、认证落地 | 标注“教学类比”，先补 Verus/Kani 可运行示例 |
| 多版 roadmap 口径不一致 | 执行混乱 | 已统一主控为 `EXECUTION_CHECKLIST_2026_06_22.md` |

---

## 四、建议确认事项

1. **2026-07-09 发布日执行**：是否按现有 `EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 执行？若 `retain_back` 未稳定，是否保留等效实现并标注 1.98？
2. **权威来源修正优先级**：是否将 async closures / Edition 2024 / `&raw const` 修正列为 07-09 前最高优先级 P1？
3. **内容瘦身力度**：`docs/` A/B/C 审计与 109 对相似文件合并，是否继续按当前节奏推进，还是优先处理 ≥0.90 高相似对？
4. **AFIDT / `async_trait` 策略**：文档侧先行更新为“实验性/跟踪中”，代码侧保持 `async_trait` 直到 AFIDT stable，是否同意？
5. **形式化/安全关键定位**：是否继续以“教学类比 + 可运行示例”方式推进，暂不设真实工作组？
6. **国际化/社区验证**：英文骨架、TRPL 对照、可用性测试，是否纳入 2026 Q4 计划？

---

## 五、下一步建议

1. **立即**：等待 2026-07-09，执行 1.97 发布日清单（不可提前）。
2. **本周**：完成 async closures / Edition 2024 / `&raw const` 全局修正（P1）。
3. **下周**：补充 Rust 1.96 覆盖缺口（assert_matches、core::range、NonZero、s390x inline asm）。
4. **7 月下旬**：启动 `docs/` A/B/C 审计与重复文件合并。
5. **持续**：跟踪 AFIDT、RTN、gen blocks、async drop、Polonius 上游进展。
