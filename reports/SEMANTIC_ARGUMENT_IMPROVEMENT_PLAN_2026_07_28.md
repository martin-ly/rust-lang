# 语义分析论证完善计划（Rust 1.97.1 基线）

> **EN**: Semantic Argument Completeness Improvement Plan (Rust 1.97.1 Baseline)
> **Summary**: A concrete, prioritized plan to eliminate semantic argument defects in `concept/` against the Rust 1.97.1 stable semantics and Edition 2024 model, based on automated gate failures and targeted manual review.
> **日期**: 2026-07-28
> **基线 Rust 版本**: 1.97.1 (Edition 2024)
> **检查范围**: `concept/` 权威概念页 + crates 示例代码

---

## 一、执行摘要

本次审计以 **Rust 1.97.1 stable / Edition 2024** 为单一语义基线，结合已有 23 个阻断质量门 + 5 个观察门 + 专项语义检查器，对项目语义论证完善度进行全面扫描。

**当前整体状态**：
- 语义健康分 **99.7/100**，概念一致性、去重、KG 完整性均达基线。
- 交叉语义域覆盖、决策树 rustc error code 映射、版本语义注入、权威来源新鲜度均 100% 通过。
- **剩余可量化缺陷共 25 处**，集中在代码示例腐烂、版本标注不一致、思维表征/反例缺失三类。

**优先级分布**：
- **P0（阻断性语义错误）**：6 处 `concept/` 代码块在当前 rustc 1.97.1 下编译失败，直接削弱论证可信度。
- **P1（显著论证缺口）**：15 处 crates 版本标签不一致 + 4 处缺失 mindmap + 数处真反例缺失 + 3 处空父章节。
- **P2（深度提升）**：形式化层语义模型补充、跨语言对比论证强化、Rust 1.97.1 补丁语义追踪。

---

## 二、检查方法论

| 维度 | 工具/手段 | 用途 |
|---|---|---|
| 代码示例语义正确性 | `scripts/check_concept_code_blocks.py --strict --sample 0` | 验证 `concept/` 中所有 ```rust 块在 rustc 1.97.1 下可编译 |
| 版本语义注入 | `scripts/check_version_semantic_injection.py --strict` | 确认 1.90–1.97 特性双向链接完整 |
| 版本一致性 | `scripts/check_rust_feature_versioning.py --strict` | 发现 crates 中文件名与内容版本标注不一致 |
| MSRV 一致性 | `scripts/check_msrv_consistency.py --strict` | 确认 Cargo.toml `rust-version = 1.97.1` 为唯一事实源 |
| 思维表征/反例 | `scripts/check_mindmap_coverage.py --strict` | 统计 mindmap 与反例节覆盖率 |
| 内容完整性 | `scripts/audit_content_completeness.py` | 发现空章节、占位标记 |
| 权威来源新鲜度 | `scripts/check_authority_freshness.py` | 对比上游 stable 与库内基线 |
| 人工抽样审查 | 逐页阅读 L1–L7 核心权威页 | 识别自动化工具无法度量的论证深度问题 |

---

## 三、当前基线（已验证）

```text
semantic_health.py --strict     → 99.7 / OK
concept_consistency_auditor.py  → 0 错误 / 0 警告 / 0 提示
cross_domain_coverage.py        → 16/16 覆盖（100%）
decision_trees.py --strict      → Top30 100% 覆盖，0 节点歧义
version_semantic_injection.py   → 74/74 映射（100%）
authority_freshness.py          → 1.97.1 同步，0 WARN
msrv_consistency.py --strict    → 0 ERROR / 0 WARN
stub_purity.py --strict         → 0 伪 stub / 0 空壳页 / 0 高重复
```

**唯一失败的专项门**：`check_concept_code_blocks.py --strict` 报出 6 块腐烂代码，详见 §四。

---

## 四、P0 阻断性语义缺陷（立即修复）

### 4.1 `concept/` 腐烂代码块（6 处）

以下代码块在 rustc 1.97.1 / Edition 2024 下**应过但失败**，属于语义标准解释与当前编译器行为不一致，必须修复。

| # | 文件 | 行 | 失败原因 | 修复动作 | 验收标准 |
|---:|---|---:|---|---|---|
| 1 | `concept/01_foundation/04_control_flow/03_let_chains.md` | 173 | `match x` 中 `x` 未定义（脚本自动包 `fn main()` 后缺失上下文） | 在块首补 `let x = Some(1);` 或改为 `rust,ignore` | `check_concept_code_blocks.py --strict` pass |
| 2 | `concept/01_foundation/04_control_flow/05_let_else.md` | 310 | `let first = contents.lines().next() else { ... };` 后 `first.to_string()` 触发 `Option<&str>` trait bound 错误 | 确认 let-else 语法在 Edition 2024 下行为；修正为 `if let Some(first) = ...` 或调整类型标注 | 同上 |
| 3 | `concept/02_intermediate/00_traits/08_negative_impls.md` | 341 | `fn assert_not_send_sync<T: !Send + !Sync>()` 使用 nightly `negative_bounds` 特性，未标注 nightly | 将块标记为 `rust,nightly` 或 `rust,ignore`；或在正文中明确说明需 nightly | 同上 |
| 4 | `concept/03_advanced/01_async/15_state_machine_semantics.md` | 52 | `step1`/`step2` 未定义 | 改为 `rust,ignore` 或补全辅助函数 | 同上 |
| 5 | `concept/03_advanced/02_unsafe/08_async_in_unsafe_contexts.md` | 113 | `let raw: *const u8 = /* 某个有效指针 */;` 不是有效表达式 | 改为 `rust,ignore` 并保留注释说明 | 同上 |
| 6 | `concept/05_comparative/02_managed_languages/10_rust_vs_ocaml.md` | 386 | 多文件 crate 结构被单一代码块包裹后报错 | 改为 `rust,ignore` 或拆分为独立文件结构说明 | 同上 |

### 4.2 crates 版本标注不一致（15 处）

`scripts/check_rust_feature_versioning.py --strict` 发现以下文件**文件名含 `194` 但内容多次出现 `1.97.0+`**，易造成学习者对“引入版本 / 稳定版本 / 当前 MSRV”的语义混淆：

- `crates/c01_ownership_borrow_scope/src/rust_194_features.rs`
- `crates/c02_type_system/src/rust_194_features.rs`
- `crates/c04_generic/src/rust_194_features.rs`
- `crates/c06_async/src/rust_194_features.rs`
- `crates/c07_process/src/rust_194_features.rs`
- `crates/c08_algorithms/src/rust_194_features.rs`
- `crates/c09_design_pattern/src/rust_194_features.rs`
- `crates/c10_networks/src/rust_194_features.rs`
- `crates/c11_macro_system_proc/src/rust_194_features.rs`
- `crates/c12_wasm/src/rust_194_features.rs`

**修复动作**：
1. 统一注释模板，明确区分：
   - `引入版本`：特性首次出现的 Rust 版本（如 1.94.0）
   - `稳定版本`：特性进入 stable 的版本（如 1.94.0 本身或后续）
   - `当前 MSRV`：本 crate/workspace 的 `rust-version`（1.97.1）
2. 若文件实际展示的是 1.97 特性，应重命名为 `rust_197_features.rs`；若确为 1.94 特性，则注释应改为“1.94 引入，1.97.1 验证可用”。

---

## 五、P1 显著论证缺口

### 5.1 缺失 mindmap 的内容页（4 处）

`check_mindmap_coverage.py` 显示以下文件缺少 `mindmap` 图（但已有其他结构）：

- `concept/03_advanced/01_async/16_structured_concurrency.md`
- `concept/07_future/00_version_tracking/rust_1_100_preview.md`
- `concept/07_future/00_version_tracking/rust_1_99_preview.md`
- `concept/07_future/02_preview_features/39_async_ioring_preview.md`

**修复动作**：为每页补充五件套（定义-属性-关系-示例-反例）的 mindmap。

### 5.2 真反例缺失（排除 glossary/knowledge map/version tracking 后）

以下文件既无“反例”章节标题，也无 `compile_fail` 代码块，且不属于可豁免的 glossary/版本跟踪/知识图类型：

- `concept/03_advanced/01_async/16_structured_concurrency.md`
- `concept/03_advanced/02_unsafe/09_sanitizers.md`
- `concept/06_ecosystem/00_toolchain/16_rustdoc_internals.md`
- `concept/07_future/02_preview_features/39_async_ioring_preview.md`

**修复动作**：
- `16_structured_concurrency.md`：补充“孤儿任务泄漏”“取消传播失败”反例。
- `09_sanitizers.md`：补充 ASan/TSan 误报与漏报场景、`#[sanitize(...)]` 与 `no_mangle` 冲突。
- `16_rustdoc_internals.md`：补充 intra-doc link 解析失败、doc test error code 漂移。
- `39_async_ioring_preview.md`：补充 uring submit-and-wait 与 Rust Future 模型不匹配的反例。

### 5.3 空父章节（3 文件）

`audit_content_completeness.py` 检测到以下文件存在 TOC 中父章节缺少引导语：

- `concept/03_advanced/02_unsafe/09_sanitizers.md`（5 处空父章节）
- `concept/06_ecosystem/00_toolchain/16_rustdoc_internals.md`（6 处空父章节）
- `concept/07_future/00_version_tracking/rust_1_100_preview.md`（1 处空父章节）

**修复动作**：在每个父章节标题后增加 1–2 段过渡性说明，明确该节要回答的语义问题。

---

## 六、P2 深度提升项

### 6.1 形式化语义模型补充

部分 L4 形式化页仍有描述性文字重于形式化论证的迹象。建议重点强化：

- `concept/04_formal/00_type_theory/`：补充类型判断规则（typing judgment）的标准记法。
- `concept/04_formal/01_ownership_logic/`：将 RustBelt 的 Iris 规则与 `unsafe` 合约映射到具体代码模式。
- `concept/04_formal/05_rustc_internals/`：对 borrow checker/NLL/_polonius_ 的算法语义给出不变量说明。

### 6.2 跨语言对比论证强化

`05_comparative/` 层部分页面仅罗列差异表格，缺少“为什么 Rust 选择此语义”的机制解释。建议：

- 对 `rust_vs_cpp`、`rust_vs_ada_spark`、`rust_vs_haskell` 等核心对比页，每页增加一节“语义等价性/不可等价性论证”。
- 用形式化或操作语义说明所有权/借用/生命周期在不同语言中的表达能力差异。

### 6.3 Rust 1.97.1 补丁语义追踪

Rust 1.97.1 为 1.97.0 的补丁版本，主要修复编译器 bug。建议：

- 建立 `concept/07_future/00_version_tracking/rust_1_97_1.md` 补丁页（当前存在但需确认是否完整覆盖 1.97.1 release notes）。
- 若 1.97.1 修复了影响 `unsafe`/FFI/ borrow check 的语义边界，应在对应权威页增加“1.97.1 语义修正”小节。

### 6.4 新增语义监控门

为预防语义论证腐烂，建议新增以下质量门或观察项：

| 门 | 检查内容 | 频率 | 当前状态 |
|---|---|---|---|
| `concept-code-blocks --strict` | 所有 ```rust 块编译性 | 每次 PR | ❌ 当前未通过，修复后转阻断 |
| `rust-feature-versioning --strict` | crates 文件名与内容版本一致 | 每次 PR | ❌ 当前未通过 |
| `mindmap-coverage --strict` | 内容页 mindmap ≥ 95% / 反例 ≥ 95% | 每周 | ⚠️ 当前为观察门 |
| 形式化深度抽样审查 | 每季度人工审查 10 篇 L4 页 | 季度 | 无脚本 |

---

## 七、任务清单（与用户确认版）

### 第一轮：P0 立即修复（1–2 天）

- [ ] 修复 6 处 `concept/` 腐烂代码块（详见 §4.1）。
- [ ] 修复后重跑 `python scripts/check_concept_code_blocks.py --strict --sample 0`，确认 rot=0。
- [ ] 审查并统一 15 个 `rust_194_features.rs` 的版本注释（详见 §4.2）。
- [ ] 重跑 `python scripts/check_rust_feature_versioning.py --strict`，确认通过。

### 第二轮：P1 论证结构补全（1 周）

- [ ] 为 4 个缺失 mindmap 的页面补充 mindmap。
- [ ] 为 4 个真反例缺失页面补充反例节或 `compile_fail` 块。
- [ ] 为 3 个有空父章节的页面补充引导语。
- [ ] 重跑 `python scripts/check_mindmap_coverage.py --strict` 与 `python scripts/audit_content_completeness.py`，确认改善。

### 第三轮：P2 深度提升（2–4 周）

- [ ] 对 `04_formal/` 核心页进行形式化深度抽样审查，补充 typing judgment / 不变量。
- [ ] 对 `05_comparative/` 核心页补充语义等价/不可等价论证。
- [ ] 复核 `concept/07_future/00_version_tracking/rust_1_97_1.md` 与官方 1.97.1 release notes 的语义对齐。
- [ ] 将 `check_concept_code_blocks.py --strict` 与 `check_rust_feature_versioning.py --strict` 纳入 `run_quality_gates.sh` 阻断段。

---

## 八、需要用户确认的事项

1. **P0 修复范围**：是否同意先集中修复 §4.1 的 6 处代码块腐烂 + §4.2 的 15 处版本标注不一致？
2. **质量门升级**：是否同意将 `check_concept_code_blocks.py --strict` 与 `check_rust_feature_versioning.py --strict` 升级为阻断门？
3. **P2 深度项优先级**：形式化语义、跨语言论证、1.97.1 补丁追踪三项中，希望优先推进哪一项？
4. **资源投入**：P2 任务涉及人工审查与重写，是否需要先输出一份更详细的“形式化页深度审计报告”再开始修改？

---

## 九、相关报告与证据

- `tmp/cb_2026-07-28.json` — 代码块编译实测原始结果
- `reports/SEMANTIC_HEALTH_2026-07-28.md` — 语义健康基线
- `reports/TOPOLOGY_QUALITY_2026-07-28.md` — 拓扑实质度基线
- `reports/CONTENT_OVERLAP_V2_2026-07-28.md` — 去重健康基线
- `concept/00_meta/02_sources/06_external_authority_topic_index.md` — 外部权威来源主题映射与缺口清单
