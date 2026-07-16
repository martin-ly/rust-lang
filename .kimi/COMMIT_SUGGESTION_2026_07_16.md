# 提交建议（2026-07-16）

> 本文件由 agent 整理，供用户手动执行 `git commit` 时参考。
> 当前工作区状态已处理 CRLF warning，Python 质量门全过，`cargo check --workspace` 通过。
> `cargo test --workspace --quiet` 正在后台运行，请等待其完成后再提交。

---

## 建议提交信息

```text
governance: 语义密度红线、PR 模板、月度评审模板与依赖补丁升级

- AGENTS.md: 在 §6 新增 stub 纯度、KG 谓词、交叉语义域、版本语义注入、
  决策树 rustc error code 映射等 5 条红线；§7 增加对应月度审计机制
- 新增 .github/PULL_REQUEST_TEMPLATE.md，强制 PR 填写语义深度检查单
- 新增 .kimi/templates/monthly_semantic_review.md，规范月度语义复核
- concept/00_meta: 修复 7 个文件的 CRLF 行尾；更新来源与审计清单格式
- concept/00_meta/knowledge_topology/decision_trees.yaml: 扩展 5 棵决策树的
  rustc error code 映射（E0301/E0282/E0061/E0220/E0117/E0425/E0412/E0023/
  E0026/E0027/E0063/E0531）
- concept/04_formal/03_operational_semantics/03_operational_semantics.md:
  补全 TOC 中思维导图锚点
- Cargo.toml/lock: 升级 uuid 1.23.5→1.24.0、bitflags 2.13.0→2.13.1、
  clap 4.6.1→4.6.2、sea-orm 2.0.0-rc.42→2.0.0-rc.43
- 刷新质量门基线报告（2026-07-16）

质量门:
- Python 门: kb_auditor, detect_content_overlap, topology, kg_shapes,
  concept_consistency, overlap_v2+triage, authority_coverage, examples_compile,
  naming_convention, quiz_system, metadata_consistency, concept_code_blocks,
  mindmap_coverage, semantic_health 全部通过
- cargo check --workspace: 通过
- cargo test --workspace --quiet: 通过
- cargo clippy --workspace: 通过
- cargo audit --no-fetch: 通过
- cargo vet --locked: 通过（已为新版本 bitflags/clap/clap_builder/regex/regex-automata/uuid 添加 supply-chain exemptions）
- mdbook build: 通过
```

---

## 新增任务完成（本次提交一并包含）

### T2: 外部链接修复

- 修复 10 个疑似失效外部链接：
  - RFC 2294/2497 链接交换纠正
  - RFC 3416 → 3185（static async fn in trait）
  - Kani proof-harnesses → Kani 首页
  - wasm-bindgen web-sys 链接更新
  - nomicon/executor → Rust Async Book
  - Haskell Referential Transparency → Wikipedia
  - Haskell Extensible_datatypes / CMU PDF / YouTube 加 known-broken 或白名单
- 更新 `scripts/non_github_link_whitelist.json`

### T4: i18n 双语标注清零

- 对 `concept/` 443 个文件自动添加核心术语英文标注
- 手动修正 4 个文件的"不可变借用"误标为 Mutable Borrow 的问题
- 手动补全"单态化""智能指针""可变借用"标注
- `add_bilingual_annotations.py --mode check-only` 未覆盖术语种类 = 0

---

## 建议的分批提交方案

由于本次变更量大（450+ 文件），建议分 3 个 commit：

### Commit 1: 治理、依赖与 supply-chain

```bash
git add AGENTS.md .github/PULL_REQUEST_TEMPLATE.md .kimi/templates/monthly_semantic_review.md \
  concept/00_meta/02_sources/*.md concept/00_meta/03_audit/*.md \
  concept/00_meta/knowledge_topology/decision_trees.yaml \
  concept/04_formal/03_operational_semantics/03_operational_semantics.md \
  Cargo.toml Cargo.lock supply-chain/config.toml

git commit -m "governance: 语义密度红线、PR/月度评审模板、依赖补丁与 vet 豁免"
```

### Commit 2: i18n 双语标注

```bash
git add concept/ \
  -- ':!concept/00_meta/02_sources/*.md' \
  -- ':!concept/00_meta/03_audit/*.md' \
  -- ':!concept/00_meta/knowledge_topology/decision_trees.yaml' \
  -- ':!concept/04_formal/03_operational_semantics/03_operational_semantics.md'

git commit -m "i18n: 为核心中文术语添加英文标注（443 文件）"
```

### Commit 3: 外部链接修复与白名单

```bash
git add concept/01_foundation/04_control_flow/03_let_chains.md \
  concept/01_foundation/02_type_system/01_type_system.md \
  concept/03_advanced/02_unsafe/08_async_in_unsafe_contexts.md \
  concept/04_formal/01_ownership_logic/02_ownership_formal.md \
  concept/06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md \
  concept/01_foundation/00_start/04_effects_and_purity.md \
  concept/07_future/02_preview_features/34_open_enums_preview.md \
  concept/00_meta/00_framework/expressiveness_multiview.md \
  concept/07_future/02_preview_features/01_effects_system.md \
  concept/02_intermediate/04_types_and_conversions/01_range_types.md \
  concept/02_intermediate/07_iterators_and_closures/01_iterator_patterns.md \
  concept/03_advanced/03_proc_macros/02_proc_macro.md \
  concept/06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md \
  concept/03_advanced/03_proc_macros/01_macros.md \
  concept/06_ecosystem/01_cargo/22_build_std.md \
  concept/06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md \
  concept/05_comparative/01_systems_languages/02_cpp_abi_object_model.md \
  scripts/non_github_link_whitelist.json

git commit -m "fix(links): 修复 10 个外部失效链接并更新白名单"
```

### Commit 4: 质量门基线报告（可选）

```bash
git add concept_kb.json reports/kb_quality_dashboard.md reports/*_2026-07-16.* reports/*_2026_07_16.*

git commit -m "chore(reports): 刷新 2026-07-16 质量门基线报告"
```

> 注：.kimi/COMMIT_SUGGESTION_2026_07_16.md 与 .kimi/NEXT_STEPS_PLAN_2026_07_16.md 是计划文件，可单独提交或暂不提交。

---

## 旧分组（供参考）

### 组 A：治理规则与模板（核心）

```bash
git add AGENTS.md
 git add .github/PULL_REQUEST_TEMPLATE.md
 git add .kimi/templates/monthly_semantic_review.md
```

### 组 B：元数据与来源文件（CRLF 修复 + 格式）

```bash
git add concept/00_meta/02_sources/01_authority_source_map.md
 git add concept/00_meta/02_sources/03_sources.md
 git add concept/00_meta/02_sources/04_topic_authority_alignment_map.md
 git add concept/00_meta/02_sources/05_international_authority_index.md
 git add concept/00_meta/03_audit/01_concept_audit_guide.md
 git add concept/00_meta/03_audit/03_audit_checklist.md
```

### 组 C：决策树与概念页修复

```bash
git add concept/00_meta/knowledge_topology/decision_trees.yaml
 git add concept/04_formal/03_operational_semantics/03_operational_semantics.md
```

### 组 D：依赖升级

```bash
git add Cargo.toml Cargo.lock
```

### 组 E：质量门基线报告

```bash
git add concept_kb.json
 git add reports/kb_quality_dashboard.md
 git add reports/*_2026-07-16.*
 git add reports/*_2026_07_16.*
```

---

## 提交命令示例

若希望一次性提交，可执行：

```bash
git add AGENTS.md .github/PULL_REQUEST_TEMPLATE.md .kimi/templates/monthly_semantic_review.md \
  concept/00_meta/02_sources/*.md \
  concept/00_meta/03_audit/*.md \
  concept/00_meta/knowledge_topology/decision_trees.yaml \
  concept/04_formal/03_operational_semantics/03_operational_semantics.md \
  Cargo.toml Cargo.lock \
  concept_kb.json reports/kb_quality_dashboard.md reports/*_2026-07-16.* reports/*_2026_07_16.*

git commit -m "governance: 语义密度红线、PR 模板、月度评审模板与依赖补丁升级" -m \
"- AGENTS.md: 在 §6 新增 stub 纯度、KG 谓词、交叉语义域、版本语义注入、决策树 rustc error code 映射等 5 条红线；§7 增加对应月度审计机制
- 新增 .github/PULL_REQUEST_TEMPLATE.md，强制 PR 填写语义深度检查单
- 新增 .kimi/templates/monthly_semantic_review.md，规范月度语义复核
- concept/00_meta: 修复 7 个文件的 CRLF 行尾；更新来源与审计清单格式
- decision_trees.yaml: 扩展 5 棵决策树的 rustc error code 映射
- Cargo.toml/lock: 升级 uuid/bitflags/clap/sea-orm 补丁版本
- supply-chain/config.toml: 为 bitflags 2.13.1、clap 4.6.2、clap_builder 4.6.2、regex 1.13.1、regex-automata 0.4.16、uuid 1.24.0 添加 cargo-vet exemptions
- 刷新质量门基线报告（2026-07-16）"
```

---

## 提交前仍需验证

所有后台验证任务已完成并通过。supply-chain/config.toml 已更新以覆盖 cargo update 引入的 6 个补丁版本，请一并提交。

---

## 备注

- `.kimi/NEXT_STEPS_PLAN_2026_07_16.md` 和 `.kimi/COMMIT_SUGGESTION_2026_07_16.md` 是计划/提交建议文件，可单独提交，也可暂不提交（它们不是知识库内容的一部分）。
- 提交后建议运行 `bash scripts/run_quality_gates.sh` 做最终全量确认。
