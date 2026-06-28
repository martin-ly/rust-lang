# 项目未完成计划与任务全面梳理（2026-06-28 版）

> **扫描范围**：`e:\_src\rust-lang` 全仓库（`.kimi/`、`reports/`、`docs/`、`concept/`、`book/`、`knowledge/`、`crates/`、`exercises/`、`examples/`、`scripts/`、`content/` 等）
> **网络对齐**：Rust 1.97.0 草案发布说明（2026-07-09）、mdbook-i18n-helpers 0.3.6、TRPL 3rd Edition（2026-03 出版）、Brown University Interactive Book、Google Comprehensive Rust
> **状态**：待确认 — 请审阅优先级与范围后批准执行

---

## 一、总体判断

1. **主控锚点**：项目以 `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` 为当前主控，硬截止为 **2026-07-09 Rust 1.97.0 发布日**。
2. **国际化策略**：当前是“中文深度内容为主体 + 英文元数据骨架为杠杆”，`concept/` 已完成 338 个文件的 `**EN**` 标题与 `**Summary**` 英文摘要 100% 覆盖，但无完整英文/其他语言版本。
3. **内容债务**：`book/` 仅为 HTML 构建产物；`exercises/` 仅 30/100+ 上线；`crates/integration_tests/` 为空壳；`concept/` 存在编号缺号、重复文件、未链接 preview 草稿。
4. **外部对齐**：506 条外部链接失效/异常；6 对 KG 术语漂移低于阈值；TRPL 3rd 已新增 Ch17 async 章节，需更新学习路径映射。

---

## 二、P0 — 硬截止 2026-07-09（Rust 1.97.0 发布日）

| 编号 | 任务 | 来源 | 关键动作 | 验收标准 |
|------|------|------|----------|----------|
| **P0-1** | 确认并执行 Rust 1.97.0 发布日清单 | `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 监控官方 release， checklist 逐条执行 | 发布日清单全部勾选 |
| **P0-2** | 切换 `rust-toolchain.toml` 到 `1.97.0` | `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` A3.2 | 修改 channel，验证 rustup | `rustc --version` 输出 1.97.0 |
| **P0-3** | 激活 `crates/c08_algorithms/src/rust_197_features.rs` 真实 API | A3.3 | 根据最终 release notes 替换 `cfg` / placeholder：• `VecDeque::truncate_front`（大概率稳定）• `NonZero/isolate_highest_one/lowest_one`（已确认）• `integer::isolate_highest_one/lowest_one/bit_width`（已确认）• `Default for RepeatN`、`Copy for ffi::FromBytesUntilNulError`（已确认） | 该文件可通过 `cargo test` |
| **P0-4** | 全 workspace 验证 | A3.4 | `cargo check`、`cargo test`、`cargo clippy` 全通过 | CI/本地均绿 |
| **P0-5** | 刷新 1.97 预览文档并迁移 | A3.5 | 更新 `concept/07_future/rust_1_97_preview.md`，迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md` | 内容与新 stable API 一致 |
| **P0-6** | 回填 `CHANGELOG.md [3.1.0]` | A3.6 / CHANGELOG | 写入 1.97 真实变更条目 | CHANGELOG 3.1.0 段落完整 |
| **P0-7** | 更新术语表 1.97 术语状态 | A3.7 | 在 `concept/00_meta/terminology_glossary.md` 中标记新稳定 API | 术语表与新 release 对齐 |

**网络对齐要点（Rust 1.97.0）**：

- 已确认稳定 API：`isolate_highest_one/lowest_one`、`bit_width`、`NonZero` 系列、`Default for RepeatN`、`Copy for ffi::FromBytesUntilNulError`。
- 语言级：`cfg(target_has_atomic_primitive_alignment)`、`div32` 等 target features。
- Cargo：`resolver.lockfile-path`、`build.warnings`、`-m` shorthand。
- Rustdoc：`--emit`、`--remap-path-prefix`。
- _compiler_：v0 symbol mangling 默认启用（需确认对学习路径影响）。

---

## 三、P1 — 发布日后稳定化（2026-07-10 ~ 2026-07-20）

| 编号 | 任务 | 来源 | 关键动作 | 验收标准 |
|------|------|------|----------|----------|
| **P1-1** | 最终回填 CHANGELOG | A4.1 | 对未进入 1.97 的条目标注“推迟至 1.98” | CHANGELOG 发布 |
| **P1-2** | 归档发布日清单 | A4.2 | 将 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 归档到 `archive/project_reports/` | 归档完成 |
| **P1-3** | 全 workspace 回归 + 供应链审计 | A4.3 / SUPPLY_CHAIN_AUDIT | `cargo check/test/clippy`、`cargo audit --no-fetch` | 全绿 |
| **P1-4** | 启动 P2 深度内容 | A4.4 | 至少新增/完善 2 个实践章节 | 2 个文件合并 |
| **P1-5** | 提交当前工作区未提交改动 | git 状态 | `README.md`、`CHANGELOG.md`、`CONTRIBUTING.md`、`concept/07_future/rust_1_97_preview.md`、`exercises/tests/l3_rust_197_alignment.rs` | 提交并推送 |
| **P1-6** | 关闭权威来源差异任务批次 | `reports/COMPREHENSIVE_AUTHORITATIVE_ALIGNMENT_DIFF_2026_06_23.md` | 按 TASK-1.x ~ TASK-4.x 优先级关闭 | 至少 70% 完成 |

---

## 四、P2 — 2026 Q3 滚动任务（内容深化与对齐）

### 4.1 编译器 / Cargo 深度内容

| 编号 | 任务 | 来源 | 关键动作 |
|------|------|------|----------|
| **P2-1** | rustc query system 实践 | `.kimi/PROJECT_PENDING_PLANS_FINAL_ALIGNMENT_2026_06_26.md` | 新增/完善 `concept/04_formal/19_rustc_query_system.md` 并链接到 SUMMARY |
| **P2-2** | new trait solver 对比 | 同上 | 新增 `concept/04_formal/26_trait_solver_in_rustc.md` 实践示例 |
| **P2-3** | Cargo resolver v3 / `public = true` | 同上 | 在 `concept/06_ecosystem/01_toolchain.md` 或新增 `cargo_resolver_v3.md` 中补充 |
| **P2-4** | MIR / codegen / LLVM 入门 | 同上 | 补齐 `concept/04_formal/` 相关缺失编号 |

### 4.2 形式化工具示例

| 编号 | 任务 | 来源 | 关键动作 |
|------|------|------|----------|
| **P2-5** | Kani 函数/循环合约扩展到 c03/c04 | 同上 | 在 c03_control_fn / c04_generic crates 中新增示例 |
| **P2-6** | Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 概念页交叉引用 | 同上 | 完善 `concept/07_future/31_safety_tags_preview.md`、`32_borrow_sanitizer_preview.md`、`33_autoverus_preview.md` 并加入 SUMMARY |

### 4.3 生态迁移与跟踪

| 编号 | 任务 | 来源 | 关键动作 |
|------|------|------|----------|
| **P2-7** | Sea-ORM 2.0 stable 迁移评估 | `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md` | 上游发布 stable 后 7 天内完成迁移文档 |
| **P2-8** | AFIDT / dynosaur / WASI 目标再次确认 | 同上 | 更新 `concept/07_future/` 相关 preview |

### 4.4 权威教材对齐

| 编号 | 任务 | 来源 | 关键动作 |
|------|------|------|----------|
| **P2-9** | TRPL 3rd Ed 逐章对照表 | `reports/TRPL_3RD_ED_BROWN_BOOK_ALIGNMENT_AUDIT_2026_06_19.md` | 更新 `concept/00_meta/learning_mvp_path.md`，标注 Ch17 async 等新内容 |
| **P2-10** | Brown Book 所有权研究引用 | 同上 | 在所有权文档中显式引用 Brown Book 可视化方法 |
| **P2-11** | async.md 标注 TRPL Ch17 | 同上 | 在 `concept/03_advanced/03_async.md` 顶部添加“对应 TRPL 3rd Ch17” |

---

## 五、P3 — 长期 / 2026 Q4（国际化与社区验证）

基于 `.kimi/I18N_Q4_2026_PLAN.md` 与最新网络最佳实践对齐：

### 5.1 i18n 工程化（建议采用 mdbook-i18n-helpers 路线）

| 编号 | 任务 | 关键动作 | 验收标准 |
|------|------|----------|----------|
| **P3-1** | 评估引入 `mdbook-i18n-helpers` | 研究 gettext/PO 工作流；对比当前“英文元数据骨架”与完整翻译路线 | 产出决策文档 |
| **P3-2** | 修复 506 条失效/异常外部链接 | 按官方 > 学术 > 社区优先级修复 | 失效率 < 1% |
| **P3-3** | 更新 225 条重定向链接为最终 URL | 运行 `scripts/i18n/fix_*_links.py` | 重定向清零 |
| **P3-4** | CI 集成 i18n 检查 | 将 `check_concept_headers.py`、`check_terminology_consistency.py` 接入 `.github/workflows/ci.yml` | CI 失败时阻断合并 |
| **P3-5** | 完成 6 对 KG 术语漂移审校 | 参考 `reports/MULTILINGUAL_ALIGNMENT_DRIFT_2026_06_27.md` | 全部 ≥ 0.7 或人工确认 |
| **P3-6** | 扩展双语术语标注到全 `concept/` | 对 `04_formal/`、`05_comparative/`、`06_ecosystem/`、`07_future/` 首次出现术语强制标注 | `add_bilingual_annotations.py` 强制模式通过 |
| **P3-7** | 生成完整英文版 `README_EN.md` | 翻译根 README 核心内容 | README_EN.md 上线 |
| **P3-8** | 为 `knowledge/` / `docs/` 核心文件添加 EN/Summary 元数据 | 优先 `knowledge/01_fundamentals/` ~ `03_advanced/` | 覆盖率 ≥ 50% |

### 5.2 学习资源国际化

| 编号 | 任务 | 关键动作 |
|------|------|----------|
| **P3-9** | 完成 TRPL 3rd Ed 逐章对照表 | 在 `LEARNING_MVP_PATH.md` 中列出 22 章映射 |
| **P3-10** | Brown Inventory 练习英文说明 | 为 8 个 `inventory_*.rs` 补充英文题干/注释 |
| **P3-11** | 本地化 5-10 个 Google Comprehensive Rust 练习 | 新建或补充 `concept/06_ecosystem/55_api_design_guide.md` |

### 5.3 社区验证

| 编号 | 任务 | 计划时间 | 来源 |
|------|------|----------|------|
| **P3-12** | 可用性测试（3+2 组） | 2026-11 | `reports/I18N_USABILITY_TEST_PLAN_Q4_2026.md` |
| **P3-13** | 收集教师/讲师反馈 ≥5 份 | 2026-11 | `reports/I18N_EDUCATOR_FEEDBACK_QUESTIONNAIRE_Q4_2026.md` |
| **P3-14** | 国内外社区发布英文骨架预览帖 | 2026-11~12 | `reports/I18N_COMMUNITY_ENGAGEMENT_DRAFTS_Q4_2026.md` |
| **P3-15** | 汇总验证报告并更新 README/CONTRIBUTING | 2026-12 | — |

---

## 六、结构性 / 内容完整性 Backlog

按模块列出需补齐的“骨架”问题，建议在 P1-P2 间逐步消化：

### 6.1 `book/`（mdBook 产物）

- [ ] 新增 `book/README.md`，说明“源码在 `concept/`，此处为构建产物”。
- [ ] 清理空目录：`book/00_meta/placeholders/`、`book/07_future/archive/`、`book/archive/`、`book/sources/`。
- [ ] 评估是否将 `book/` 改为独立构建输出目录（如 `book/html/`），避免与源码混淆。

### 6.2 `concept/`

- [ ] 修复编号缺号：`04_formal/07_separation_logic.md`（SUMMARY 缺号，实际有 `11_separation_logic.md`）。
- [ ] 将未链接文件加入 `SUMMARY.md`：`19_rustc_query_system.md`、`25_name_resolution_and_hir.md`、`26_trait_solver_in_rustc.md`、`27_type_checking_and_inference.md`、`28_borrow_checking_decidability.md`、`29_type_inference_complexity.md`、`30_aeneas_symbolic_semantics.md`、`31_miri.md`、`32_kani.md`、`rust_1_98_preview.md`、`31_safety_tags_preview.md`、`32_borrow_sanitizer_preview.md`、`33_autoverus_preview.md`。
- [ ] 处理重复文件：`01_foundation/10_numerics.md` vs `11_numeric_types.md` 等 6 组。
- [ ] 补充或标记草稿文件：`06_ecosystem/39_os_kernel.md`、`45_compiler_internals.md`、`48_industrial_case_studies.md`、`51_quantum_computing_rust.md`、`53_embedded_graphics.md`、`54_webassembly_advanced.md`、`55_rust_for_data_science.md`。

### 6.3 `content/`

- [ ] 新增 `content/representations/README.md`、`content/scenarios/README.md`。
- [ ] 同步 `content/README.md` 快速导航，补充缺失的 9 个文件链接。
- [ ] 为 `content/ecosystem/async_runtimes/`、`error_handling/`、`serialization/` 增加 README。

### 6.4 `crates/`

- [ ] 决策：`crates/integration_tests/` 空壳 — 补充集成测试或移除。
- [ ] `crates/c11_macro_system_proc/` 补充 example（当前仅 `.gitkeep`）。
- [ ] `crates/common/` 补充 examples/、tests/。
- [ ] 更新 `crates/README.md`，列出 c13_embedded、c14_semantic_web、common、integration_tests、c11_macro_system_proc。
- [ ] 清理空 `.gitkeep`、空 `.rs` 模块文件。
- [ ] 修复 `c02_type_system/src/advanced_macros.rs:392` 文档 TODO。

### 6.5 `exercises/`

- [ ] 补齐 46 处 TODO，优先：
  - `exercises/src/rust_195_feature_exercises.rs`（16 处）
  - `exercises/src/rust_196_feature_exercises.rs`（2 处）
  - `exercises/src/type_system/ex06_if_let_guards.rs`（3 处）
  - `exercises/src/ownership_borrowing/brown_inventories/inventory_01.rs` ~ `inventory_08.rs`（25 处）
- [ ] 实现 `unsafe_rust/` 主题：`src/unsafe_rust/` 目录、docs/unsafe_rust/ 题目、tests/unsafe_rust/ 测试。
- [ ] 将新增未跟踪文件 `exercises/tests/l3_rust_197_alignment.rs` 纳入 `RUSTLINGS_MAPPING.md` 与测试入口。
- [ ] 清理 `exercises/tests/` 下 8 个空主题子目录或填充测试。
- [ ] 更新 `exercises/RUSTLINGS_MAPPING.md` 与真实文件同步。

### 6.6 `knowledge/`

- [ ] 修复 `knowledge/INDEX.md` 中指向不存在的裸文件名路径（约 6 处）。
- [ ] 补齐 `knowledge/03_advanced/concurrency/01_atomics.md` 3 处代码 TODO。
- [ ] 补齐 `knowledge/04_expert/safety_critical/08_training/03_hands_on_lab_exercises.md` 等 5 处代码 TODO。
- [ ] 模板占位：RUSTSEC-XXXX、SSRS-XXX、负责人 XXX 等 8 处低优先级占位。

### 6.7 `docs/`

- [ ] 完成 `docs/rust-ownership-decidability/exercises/ADVANCED_OWNERSHIP_WORKSHOP.md` 中 31 处代码 TODO。
- [ ] 新增 `docs/04_research/README.md`。
- [ ] 决策并清理 `docs/07_future/` 空目录。
- [ ] 清理 `docs/research_notes/`、`docs/rust-ownership-decidability/` 下的空目录。

### 6.8 `examples/`

- [ ] 为 3 个子项目新增 README：`build_script_practice/`、`incremental_practice/`、`resolver_v3_practice/`。
- [ ] 在 `examples/README.md` 中索引顶层 11 个 `.rs` 示例。

---

## 七、Blocker / 待确认项

| 编号 | 问题 | 当前状态 | 建议 |
|------|------|----------|------|
| **B-1** | Aquascope 集成 | 方案 A/B 均阻塞 | 短期维持 Brown Book 可视化 + Mermaid/ASCII 替代；Q3 再评估 |
| **B-2** | `#[optimize]`、`ptr::try_cast_aligned`、ATPIT 等 | 上游未稳定 | 持续跟踪，不纳入 P0 |
| **B-3** | `cargo audit` / `cargo-vet` Windows 兼容 | 网络/平台阻塞 | 使用 `scripts/supply_chain_audit.py` fallback |
| **B-4** | Sea-ORM 2.0 stable | 上游 2.0.0-rc.41 | 发布后再迁移 |
| **B-5** | AFIDT / dyn async Trait | 实验性 | 年内稳定概率低，仅跟踪 |
| **B-6** | ManuallyDrop 常量模式、expr metavariable to cfg、AI 辅助警告强调顺序 | 待确认 | 需要权威来源二次确认后决策 |
| **B-7** | `book/` 是否引入 `mdbook-i18n-helpers` 做完整翻译 | 待决策 | Q4 先做 POC，对比成本后决策 |

---

## 八、建议的执行节奏

| 阶段 | 时间 | 重点任务 |
|------|------|----------|
| **发布日前** | 06-28 ~ 07-08 | 完成 P0-1 ~ P0-7 准备；确认 1.97 最终稳定 API |
| **发布日** | 07-09 | 执行发布日清单；切换 toolchain；全 workspace 验证 |
| **发布后 2 周** | 07-10 ~ 07-20 | P1-1 ~ P1-6；提交未提交改动；归档 |
| **Q3 滚动** | 07-21 ~ 09-30 | P2-1 ~ P2-11；消化 6.1 ~ 6.8 结构性 backlog 中 P1-P2 级别项 |
| **Q4 国际化** | 10-01 ~ 12-31 | P3-1 ~ P3-15；社区验证；2027 Q1 维护机制落地 |

---

## 九、已确认决策

| 问题 | 决策 | 影响 |
|------|------|------|
| **Q3 结构性债务优先级** | **全部修复并提升到 P1 并行处理** | 经复核：`crates/integration_tests/` 并非空壳（已有 11 个通过测试）; exercises 中 46 处 TODO 多数为注释/起始代码示例，实际函数已实现且测试通过；仅 `docs/rust-ownership-decidability/exercises/ADVANCED_OWNERSHIP_WORKSHOP.md` 中存在真实待填 `todo!()`。实际修复范围缩窄为工作坊 + 清理误导性 TODO 注释。 |
| **Q5 重复文件处理** | **合并/删除重复文件** | `concept/` 中真正内容重叠的 2 组合并；其余 3 组为不同主题抢占同一编号，将重命名/重新编号并修复 SUMMARY 链接。 |

## 十、仍待确认的关键问题

1. **P0 范围**：是否批准在 2026-07-09 按本计划执行 Rust 1.97.0 切换？是否需要增加对 v0 symbol mangling、Cargo `build.warnings` 等编译器/Cargo 特性的覆盖？
2. **i18n 路线**：Q4 是否优先试点 `mdbook-i18n-helpers`（gettext/PO 工作流）做英文版 `book/`？还是继续当前“英文元数据骨架”策略？
3. **外部链接修复**：506 条失效/异常链接是否按“官方 > 学术 > 社区”优先级由脚本批量修复，还是人工逐条审校？

---

_本文件由 Kimi Code CLI 基于 2026-06-28 全仓库扫描与网络最新内容对齐生成，待用户确认后生效。_
