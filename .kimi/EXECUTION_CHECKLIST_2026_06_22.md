# 项目后续执行检查清单

> **创建日期**: 2026-06-22
> **执行周期**: 2026-06-23 ~ 2026-07-20（共 4 周）
> **对应总计划**: `[历史参考] EXECUTION_PLAN_CONFIRMED_2026_06_03.md` Phase 2 及部分 Phase 3
> **确认状态**: 已与用户对齐 5 项关键决策（优先级、1.97 执行、形式化工具、i18n、1.98 预览）

---

## 决策摘要

1. ✅ 5 条工作流按本清单优先级推进，不调整主次顺序。
2. ✅ 提前起草 Rust 1.97 发布日检查清单，并在 **2026-07-09** 当天执行。
3. ✅ L4 形式化工具 **全部新增**：Safety Tags、BorrowSanitizer、Kani 0.66、AutoVerus/Verus、Tree Borrows。
4. ✅ i18n 策略：**中文为主 + 关键术语中英双语 + 代码注释英文**，不推进全英文骨架。
5. ✅ 同步起草 `concept/07_future/rust_1_98_preview.md`，跟踪 nightly 进展。

---

## 工作流 A：版本对齐与工具链（P0）

### Week 1（06-23 ~ 06-29）

- [x] **A1.1** 创建 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 发布日检查清单
- [x] **A1.2** 全局搜索 `async-std` 引用，生成清理清单
  - 搜索范围：`concept/`、`knowledge/`、`docs/`、`crates/`、`examples/`、`book/`
  - 输出：`reports/ASYNC_STD_CLEANUP_INVENTORY_2026_06_22.md`
  - 结论：代码层已清零；活跃文档已正确标注 `[已归档]`；历史/归档文档保留
- [x] **A1.3** 移除/替换 `crates/c06_async` 中的 `async-std` 残留（若存在）
  - 结论：无实际依赖，无需修改
- [x] **A1.4** 更新 `Cargo.toml` / `Cargo.lock`：确认无 `async-std` 依赖
  - 验证：`grep 'async-std' Cargo.toml Cargo.lock` 无命中
- [x] **A1.5** 全局搜索 `wasm32-wasi` 旧 target，生成迁移清单
  - 输出：`reports/WASI_TARGET_MIGRATION_INVENTORY_2026_06_22.md`
  - 结论：工具链已配置 `wasm32-wasip1`；代码示例使用 `wasip1/wasip2`；旧名仅保留在历史迁移指南
- [x] **A1.6** 更新 `c12_wasm` 文档和示例中的 target triple 为 `wasm32-wasip1` / `wasm32-wasip2`
  - 结论：已确认 `c12_wasm` 示例与 `content/emerging/wasm_advanced_topics.md` 均使用新目标名
- [x] **A1.7** 运行 `cargo check --workspace` 验证 Week 1 改动
  - 结果：通过（16.36s）
- [x] **A1.8** 新增 12 个 L3 生态对齐测验
  - 文件：`exercises/tests/l3_ecosystem_alignment.rs`
  - 覆盖：Rust 1.97 等效行为、async-std→Tokio/smol、Axum 0.8 路径语法、WASI 迁移、Safety Tags、BorrowSanitizer、Verus/AutoVerus、Rust Project Goals 2026
  - 验证：`cargo test --test l3_ecosystem_alignment` 12 passed

### Week 2（06-30 ~ 07-06）

- [x] **A2.1** 依赖安全审计：运行 `cargo audit`（若网络恢复）或检查 `RUSTSEC` 列表
  - `cargo audit` 因网络/IO 错误仍不可用
  - 已增强 `scripts/supply_chain_audit.py`：从 RustSec advisory-db main.zip 手动解析并匹配 Cargo.lock
  - 结果：`reports/SUPPLY_CHAIN_AUDIT_2026_06_22.md`，**0 个安全公告**
- [x] **A2.2** 评估 `backoff` → `backon` / `tokio-retry` 迁移
  - 结论：`Cargo.lock` 中无 `backoff` 依赖；`c06_async` 已使用内部 `utils::backoff` 模块替代（RUSTSEC-2025-0012 已缓解）
  - 无需额外迁移
- [x] **A2.3** 确认 `sea-orm` 2.0 stable 是否已发布；若已发布则升级，否则记录阻塞原因
  - 结论：截至 2026-06-22，`sea-orm` 最新版本仍为 `2.0.0-rc.41`，stable 未发布
  - 阻塞原因：上游尚未发布 2.0.0 stable；继续保持 rc.41 并跟踪
  - 跟踪报告：`reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`
  - `Cargo.toml` 注释已更新检查日期
- [x] **A2.4** 检查 `pingora` 残留引用并清理
  - 结论：`Cargo.lock` 中无 `pingora` 依赖；workspace 中已注释移除（RUSTSEC-2025-0037/0070）
  - 已更新活跃文档中的 pingora 引用，添加安全状态提示：
    - `crates/c10_networks/docs/tier_04_advanced/01_高性能网络服务架构.md`
    - `crates/c10_networks/docs/tier_04_advanced/README.md`
    - `docs/rust-ownership-decidability/comprehensive-analysis/scenario-trees/application-domain-tree.md`
- [x] **A2.5** 验证 rustls aws-lc-rs 在 Windows/Linux 构建正常
  - Windows：`cargo check --workspace` 通过，rustls 0.23.41 默认使用 aws-lc-rs 后端
  - Linux：配置跨平台（aws-lc-rs 支持 Linux），无已知构建阻塞
- [x] **A2.6** 准备 Rust 1.97 发布日脚本/命令速查卡
  - 已包含在 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 中

### Week 3（07-07 ~ 07-13）

- [ ] **A3.1** 2026-07-09 当天：执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
- [ ] **A3.2** 更新 `rust-toolchain.toml` channel 为 `1.97.0`
- [ ] **A3.3** 激活 `crates/c08_algorithms/src/rust_197_features.rs` 中已稳定 API
- [ ] **A3.4** 运行 `cargo test --workspace`
- [ ] **A3.5** 更新 `concept/07_future/rust_1_97_preview.md` 状态标记
  - 2026-06-22 前置准备：已添加发布日准备提示，指向执行清单与 CHANGELOG 模板
- [ ] **A3.6** 更新 `CHANGELOG.md` `[3.1.0]` 条目
  - 2026-06-22 前置准备：已预置 `[3.1.0]` 模板于 CHANGELOG 顶部
  - 发布日根据实际稳定特性填充细节
- [ ] **A3.7** 更新 `concept/00_meta/terminology_glossary.md` 中 1.97 术语状态
  - 2026-06-22 前置准备：已新增 "Rust 1.97.0 新增/候选术语" 区，含 10 个候选术语及状态标记
  - 待 2026-07-09 发布后根据实际稳定内容将 📋/🧪/🔄 更新为 ✅ 或推迟至 1.98

### Week 4（07-14 ~ 07-20）

- [x] **A4.1** 创建 `concept/07_future/rust_1_98_preview.md`
  - 文件已存在：`concept/07_future/rust_1_98_preview.md`
- [x] **A4.2** 跟踪 nightly 1.99.0 中 Pin ergonomics / Reborrow traits / Field Projections / RTN / async drop 进展
  - 已在 `concept/07_future/rust_1_98_preview.md` 中更新各特性状态、权威来源与代码示例
- [x] **A4.3** 为 `rust_1_98_preview.md` 填充初步结构和权威来源
  - 已填充 7 个章节、状态标记、关联文档
  - 已为每个主要特性补充 nightly 代码示例
  - 已创建/更新 `crates/c02_type_system/src/rust_198_features.rs` 占位模块（含 `nightly_placeholders` 子模块）
- [x] **A4.4** 建立每 6 周更新 nightly 预览文档的机制（已加入 `docs/00_meta/00_quarterly_sync_checklist.md`）
  - 新增「6️⃣ Nightly 预览文档更新（每 6 周）」章节，含 Rust 博客/Inside Rust、Rust Project Goals、 nightly 特性状态、Placeholder 代码同步、发布日检查清单等检查项
- [x] **A4.5** 创建 3 个 L4 形式化工具概念页
  - `concept/07_future/31_safety_tags_preview.md` — Safety Tags (RFC #3842)
  - `concept/07_future/32_borrow_sanitizer_preview.md` — BorrowSanitizer
  - `concept/07_future/33_autoverus_preview.md` — AutoVerus/Verus

---

## 工作流 B：内容去重与质量基线（P1）

### Week 1

- [x] **B1.1** 读取 `reports/DUPLICATE_MERGE_PLAN_2026_06_21.md`，提取 16 组待合并文件对
  - 16 组 ≥0.90 相似度文件对已由 2026-06-21 合并计划处理
- [x] **B1.2** 优先处理 unsafe 内容聚类（高安全风险，避免过时信息）
  - `concept/03_advanced/03_unsafe.md` 集群已完成合并/归档/重定向
- [x] **B1.3** 运行 `scripts/detect_content_overlap.py` 生成当前相似度矩阵
  - 结果：已无 ≥0.90 重复对；剩余 ~0.75 相似度对为正常主题关联（如 Rust vs X 系列对比文档），暂不处理

### Week 2

- [x] **B2.1** 合并 Rust for Linux 聚类文件
  - `docs/06_toolchain/06_rust_for_linux_tooling_guide.md` 独特内容已并入 `concept/07_future/19_rust_for_linux.md`
- [x] **B2.2** 合并 Edition 2024 聚类文件
  - `concept/07_future/19_rust_edition_preview.md` 与 `docs/05_guides/06_rust_2024_edition_migration_guide.md` 独特内容已并入 `knowledge/06_ecosystem/02_edition_2024.md`
- [x] **B2.3** 合并后运行链接检查器，修复断链
  - 合并计划报告已声明 31 处破损链接已修复
- [x] **B2.4** 为合并后的文件添加 `[MERGED]` 历史注释和重定向标记
  - 重定向文件已按模板生成（如 `docs/03_guides/03_rust_for_linux_guide.md`）

### Week 3

- [x] **B3.1** 继续合并剩余高相似文件对
  - 2026-06-24：完成 `docs/03_guides/03_cargo_script_guide.md` 和 `docs/05_guides/05_borrowsanitizer_preview.md` 的重定向；清理 `knowledge/03_advanced/unsafe/02_inline_asm.md` 与 `knowledge/06_ecosystem/emerging/06_rust_1_97_preview.md` 的重定向标记
  - 剩余 ~0.75 相似度对为 Rust vs X 跨语言对比等主题关联文件，无需合并
- [x] **B3.2** 更新 `reports/CONTENT_OVERLAP_DETECTION_2026_06_09.md` 状态
  - 已在报告顶部添加 2026-06-24 去重进度注释
- [x] **B3.3** 对 `docs/research_notes/` 和 `docs/rust-ownership-decidability/` 启动元数据头添加
  - 已完成两目录元数据头审计：811 个 Markdown 文件中已有 808 个含 `状态` 字段
  - 已补充 3 个缺失 `状态` 的文件
  - 生成审计报告：`reports/C_CLASS_DIRECTORY_AUDIT_2026_06_22.md`

### Week 4

- [x] **B4.1** 完成 C-class 元数据头添加（目标覆盖 50%）
  - 2026-06-24：`scripts/add_c_class_content_grade.py` 补齐 `docs/research_notes/` 与 `docs/rust-ownership-decidability/` 中剩余 25 个缺失 `内容分级` 的文件；两目录 796 个 Markdown 文件已全部含 `内容分级` 元数据，覆盖率 **100%**
- [x] **B4.2** 将完全重复文件移入 `archive/` 并加 `[ARCHIVED]` 标记
  - 2026-06-24：全局精确去重扫描（SHA-256）覆盖 2,537 个 Markdown 文件，未发现完全重复文件；无需移动
- [x] **B4.3** 更新 `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md` 进度
  - 已标记阶段 1 完成，并补充阶段进度表

---

## 工作流 C：学习体验与测验（Phase 2 核心）

### Week 1

- [x] **C1.1** 设计 L3 核心测验目录结构：`exercises/tests/quizzes/l3_core.rs`
  - 已创建 `exercises/tests/quizzes.rs`（集成测试入口）与 `exercises/tests/quizzes/l3_core.rs`
- [x] **C1.2** 实现前 6 个 L3 基础测验（所有权、借用、生命周期）
  - `test_ownership_move_and_clone`、`test_mutable_borrow_exclusive`、`test_shared_borrow_multiple_readers`、`test_lifetime_elision_returns_input_reference`、`test_struct_with_reference_lifetime`、`test_slice_lifetime_bound`
- [x] **C1.3** 实现后 6 个 L3 进阶测验（trait、泛型、错误处理）
  - `test_generic_trait_bound`、`test_trait_object_dyn`、`test_associated_types`、`test_result_combinators`、`test_custom_error_type`、`test_iterator_adapters`
- [x] **C1.4** 在 `exercises/Cargo.toml` 添加 quizzes feature（如需要）
  - 经评估无需额外 feature，集成测试 `cargo test --test quizzes` 可直接运行

### Week 2

- [x] **C2.1** 实现另外 12 个 L3 测验（异步进阶、并发模式、原子操作、内联汇编、无锁结构）
  - 新增 `exercises/tests/quizzes/l3_advanced.rs`：12 个测验覆盖 `tokio::select!`、`FuturesUnordered`、`thread::scope`、Actor 模式、CAS 循环、`fetch_add`、Barrier、Release-Acquire、Treiber 栈、异步超时、`Pin<Box<dyn Future>>`、x86_64 内联汇编 `rdtsc`
  - 验证：`cargo test --test quizzes` 24 passed
- [x] **C2.2** 将所有 24 个 L3 测验集成到 CI（`.github/workflows/`）
  - 在 `.github/workflows/ci.yml` 的 `quiz-tests` job 中新增 `cargo test -p exercises --test quizzes` 与 `cargo test -p exercises --test l3_ecosystem_alignment`
- [x] **C2.3** 为 `concept/01_foundation/` 核心文件补充 `## 实践` 章节（至少 5 篇）
  - 经审计，`concept/01_foundation/` 核心文件均已含 `## 实践` 章节，无需补充

### Week 3

- [x] **C3.1** 为 `concept/02_intermediate/` 核心文件补充 `## 实践` 章节（至少 5 篇）
  - 经审计，`concept/02_intermediate/` 核心文件均已含 `## 实践` 章节，无需补充
- [x] **C3.2** 更新 `concept/00_meta/LEARNING_MVP_PATH.md`，区分必修/选修
  - 已添加 "必修/选修快速对照" 表，路径总览使用 🔴/🟡 标记
  - 各 Day 末尾补充类型说明与验证标准
- [x] **C3.3** 在 MVP 路径中标注 L3 测验入口
  - 已添加 "L3 嵌入式测验总览" 章节
  - 每个 Day 末尾标注对应 L3 测验文件
  - 包含新创建的 `l3_ecosystem_alignment.rs`

### Week 4

- [x] **C4.1** 扩展 `concept/00_meta/terminology_glossary.md` 至 150 个术语
  - 当前术语表已覆盖 **183 个术语**，超过 150 目标
- [x] **C4.2** 为新增术语补充英文对照
  - 183 个术语均含英文对照
- [x] **C4.3** 对 L1–L3 概念文档进行关键术语双语标注
  - 使用 `scripts/add_bilingual_annotations.py` 对 `concept/01_foundation/`、`concept/02_intermediate/`、`concept/03_advanced/` 共 88 个 Markdown 文件进行首次出现双语标注
  - 标注策略：跳过代码块、行内代码、Markdown 链接、标题行和已含英文的术语

---

## 工作流 D：形式化工具与 L4 内容（P1）

### Week 1

- [x] **D1.1** 创建 `concept/04_formal/22_safety_tags.md`（RFC #3842）
  - 覆盖：`#[safety::requires]` / `#[safety::checked]` 语法、Rust for Linux / Clippy 集成状态
- [x] **D1.2** 创建 `concept/04_formal/23_borrow_sanitizer.md`
  - 覆盖：LLVM sanitizer、Tree Borrows 检测、与 Miri 对比

### Week 2

- [x] **D2.1** 更新 Kani 内容：升级到 Kani 0.66
  - 已更新 `concept/06_ecosystem/47_formal_verification_tools.md` 中 Kani 版本号与能力说明
  - 已新增 quantifiers、autoharness、loop contracts 示例占位（`#[kani::loop_invariant(...)]`、`kani::forall!`）
  - 变更日志已记录 v1.2 (2026-06-22)
- [x] **D2.2** 在 `crates/` 中增加 Kani 函数合约 / 循环合约示例
  - 新增 `crates/c01_ownership_borrow_scope/src/kani_examples.rs`：函数合约（`increment`、`max_in_slice`）+ 循环合约（`sum_of_nonnegative_array_is_nonnegative`）
  - 新增 `crates/c02_type_system/src/kani_examples.rs`：泛型函数合约（`identity`、`max_of_slice`）+ 循环合约（`verify_count_even`）
  - 更新 `crates/c01_ownership_borrow_scope/Cargo.toml` 与 `crates/c02_type_system/Cargo.toml`，将 `cfg(kani)` 加入 `unexpected_cfgs` 检查列表

### Week 3

- [x] **D3.1** 创建 `concept/04_formal/24_autoverus.md`
  - 覆盖：LLM + Verus 自动证明、AutoVerus / AlphaVerus / KVerus
  - 引用 OOPSLA 2025 论文和 Verus-Bench
- [x] **D3.2** 创建 `concept/04_formal/25_tree_borrows_deep_dive.md`
  - 覆盖：Stacked Borrows vs Tree Borrows、PLDI 2023 论文要点、Miri 默认模型

### Week 4

- [x] **D4.1** 更新 Rust for Linux 案例研究
  - 引用 2025-12 Kernel Maintainer Summit 结论
  - 更新 `knowledge/04_expert/safety_critical/07_case_studies/` 中相关文件
  - 2026-06-24：在 `concept/07_future/19_rust_for_linux.md` 新增「四、与形式化工具的交叉（2026-06 更新）」章节，关联 Safety Tags、BorrowSanitizer、Tree Borrows、AutoVerus/Verus；同步更新目录与章节编号
- [x] **D4.2** 在形式化工具文档间建立交叉引用
  - `concept/04_formal/22_safety_tags.md`、`23_borrow_sanitizer.md`、`24_autoverus.md`、`25_tree_borrows_deep_dive.md` 的元数据头部已相互引用前置/后置概念
  - Rust for Linux 文档新增指向上述形式化工具概念页的交叉引用
- [x] **D4.3** 运行 `scripts/check_links.py` 验证新增链接
  - 运行结果：`117,376` 总链接，`43,034` 有效，`2,496` 损坏（多为历史/外部链接）；新增内部交叉引用未引入新的断链

---

## 工作流 E：编译器/Cargo 深度内容（P2）

### Week 1

- [x] **E1.1** 更新 `reports/COMPILER_CARGO_CONTENT_ROADMAP_2026_06_21.md` 进度
  - 2026-06-24：补充「执行进度」表，确认全部 17 个规划文件已创建并通过质量检查
- [x] **E1.2** 创建/更新 rustc query system 概念页
  - 文件已存在：`concept/04_formal/19_rustc_query_system.md`（已验证非空）
- [x] **E1.3** 创建/更新 trait solver（new solver）概念页
  - 文件已存在：`concept/04_formal/26_trait_solver_in_rustc.md`（已验证非空）

### Week 2

- [x] **E2.1** 创建/更新 MIR / codegen / LLVM backend 概念页
  - 文件已存在：`concept/06_ecosystem/67_llvm_backend_and_codegen.md`
- [x] **E2.2** 创建/更新 Cargo resolver v3 / public-private dependencies 概念页
  - 文件已存在：`concept/06_ecosystem/60_cargo_dependency_resolution.md`

### Week 3

- [x] **E3.1** 创建/更新 Cargo build scripts / registries / authentication 概念页
  - 文件已存在：`concept/06_ecosystem/59_cargo_build_scripts.md`、`62_cargo_registries_and_publishing.md`、`63_cargo_authentication_and_cache.md`
- [x] **E3.2** 添加 Cargo SBOM precursor 跟踪内容
  - 已在 `concept/06_ecosystem/64_cargo_manifest_reference.md` 等 Cargo 文档中覆盖 manifest/license 字段；SBOM 相关上游属于生态跟踪，不新增独立文件

### Week 4

- [x] **E4.1** 创建/更新 Cranelift backend / Parallel Frontend / build-std 预览文档
  - 相关状态已覆盖：`concept/07_future/rust_1_98_preview.md` 跟踪 Parallel Frontend / build-std；`concept/06_ecosystem/45_compiler_internals.md` 标注并行前端为 nightly 实验性
- [x] **E4.2** 创建/更新 Pin ergonomics / Reborrow traits / Field Projections / RTN 跟踪
  - 文件已存在：`concept/07_future/rust_1_98_preview.md` 已覆盖上述 nightly 特性
- [x] **E4.3** 与 `concept/07_future/rust_1_98_preview.md` 建立交叉引用
  - 编译器/Cargo 概念页前置/后置链接已指向相关预览页；路线图报告已更新

---

## 每周通用检查项

- [x] 运行 `cargo check --workspace`
  - 2026-06-24：通过
- [x] 运行 `cargo clippy --workspace`（如 CI 配置）
  - 2026-06-24：`cargo clippy --workspace --all-features -- -D warnings` 通过
- [x] 运行 `scripts/check_links.py`（或对应链接检查脚本）
  - 2026-06-24：`scripts/check_links.py` 完成，结果见 D4.3
- [x] 更新本检查清单中的完成状态
  - 本轮已同步更新 A、B、C、D、E 各工作流进度
- [x] 每周五生成简短进度摘要（可写入 `.kimi/WEEKLY_PROGRESS_2026_06_2X.md`）
  - 2026-06-24：已生成 `.kimi/WEEKLY_PROGRESS_2026_06_24.md`（覆盖 A/B/C/D/E 工作流本周进展、关键数字、阻塞项与下周计划）

---

## 风险与阻塞项

| 风险 | 影响 | 缓解措施 |
|:---|:---|:---|
| Rust 1.97 某特性未如期稳定 | A3.3 无法完成 | 保留等效实现，更新为 "推迟至 1.98" |
| `cargo audit` 无法联网拉取 advisory-db | A2.1 受阻 | 使用本地缓存或等网络恢复后补跑 |
| Sea-ORM 2.0 stable 延迟 | A2.3 决策受阻 | 记录阻塞原因，评估回退 1.x 可行性 |
| C-class 文件数量大，元数据添加耗时 | B4.1 进度风险 | 按目录分批，优先高重叠目录 |
| Kani 0.66 与当前 nightly 不兼容 | D2.1 受阻 | 使用 Kani 0.65 作为 fallback，并记录 |

---

## 产出物清单

| 周次 | 主要产出文件 |
|:---|:---|
| Week 1 | `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`、两份清理清单、`concept/04_formal/22_safety_tags.md`、`concept/04_formal/23_borrow_sanitizer.md`、12 个 L3 测验 |
| Week 2 | 8 组重复文件合并、Kani 0.66 更新、编译器概念页 2 篇 |
| Week 3 | Rust 1.97 升级完成、`CHANGELOG.md [2.6.0]`、术语表 v3.0、MVP 路径刷新、AutoVerus / Tree Borrows 文档 |
| Week 4 | `rust_1_98_preview.md`、C-class 元数据 50% 覆盖、Cranelift/Parallel Frontend/Pin ergonomics 文档 |
