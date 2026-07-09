# 项目全面对齐完成报告

**日期**: 2026-07-10
**范围**: Cargo 配置统一、`knowledge/` 规范化为重定向 stub、`docs/` 权威链接补齐、`concept/` 版本元数据清理
**目标**: 建立单一、可维护的一致性基线

---

## 1. 关键决策（已与用户确认）

| 决策项 | 选择 |
|---|---|
| MSRV / `rust-version` | 保持 `1.96.1`（本地可构建） |
| crate 版本号 | 全部继承 workspace `3.1.0` |
| `knowledge/` 长篇内容 | 全部改为 ≤12 行 stub，指向 `concept/` 权威页 |

---

## 2. Phase A：Cargo 配置统一

### 2.1 完成内容

- 根 `Cargo.toml` 新增统一 workspace 元数据：
  - `authors = ["Rust Learning Community"]`
  - `repository = "https://github.com/martin-ly/rust-lang"`
  - `homepage = "https://github.com/martin-ly/rust-lang"`
- 全部 workspace member（24 个 crate + `exercises`）改用 workspace 继承：
  - `version.workspace = true`
  - `edition.workspace = true`
  - `rust-version.workspace = true`
  - `authors.workspace = true`
  - `license.workspace = true`
  - `repository.workspace = true`
  - `homepage.workspace = true`
- 修正了错误/不一致的仓库 URL（原 `rust-lang/rust-lang-learning` → `martin-ly/rust-lang`）。
- 修复 `c08_algorithms` 中 `eframe` dev-dependency 的 contradictory feature 配置。
- `c14_semantic_web` 本地硬编码依赖改为 workspace 继承。
- Feature 命名规范化：
  - `c05_threads`: `custom_ring_buffers` → `custom-ring-buffers`，`work_stealing_examples` → `work-stealing-examples`
  - `c07_process`: `async` → `async-support`，`futures` → `futures-support`
  - `c10_networks`: `pcap_live` → `pcap-live`
- 同步更新了所有引用上述 feature 的源码、示例与文档中的 `cfg(feature = ...)` 与命令行说明。

### 2.2 受影响文件数

约 80+ 个文件（Cargo.toml、源码、README/docs）。

---

## 3. Phase B：`knowledge/` 全部 stub 化

### 3.1 完成内容

- 扫描 `knowledge/**/*.md`（排除 `README.md`、`INDEX.md` 及已含 `权威来源` 的 stub）。
- 对 68 个仍含长篇正文的文件，使用标题/EN/摘要/路径与 `concept/` 做相似度匹配，生成重定向 stub。
- 保留原 H1、EN/Summary（如有），顶部添加 `> **权威来源**: [concept/...](...)` 链接。
- 其余 51 个文件此前已是 stub 或索引页，保持不变。

### 3.2 结果

- `knowledge/` 下所有活跃 Markdown 现在均为学习入口 stub 或索引页。
- 无内容重复（`detect_content_overlap.py` 0 对潜在重复）。
- 无死链（`kb_auditor.py --link-check` 0 死链）。

---

## 4. Phase C/D：`docs/` 权威链接 + `concept/` 元数据清理

### 4.1 `docs/` 权威链接

- 根据 `reports/CANONICAL_ALIGNMENT_AUDIT_2026_07_09.md` 第 3.1、3.2、5 节：
  - 31 个已列出的 `docs/` 文件已全部自带 `权威来源` 链接。
  - 为 `docs/05_guides/05_kani_practical_guide.md` 补全了指向 `concept/04_formal/04_model_checking/32_kani.md` 的权威链接。

### 4.2 `concept/` 版本元数据

- 修正以下文件的 `1.96.1+` 为 `1.97.0+`（保留 nightly 标注）：
  - `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md`
  - `concept/04_formal/05_rustc_internals/19_rustc_query_system.md`
  - `concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md`
- 修正 `docs/01_core/01_ownership_borrowing_lifetimes.md` 同一文件内顶部 `1.97.0+` 与头部 `1.96.1+` 不一致的问题。
- 更新 `concept/07_future/01_edition_roadmap/44_edition_guide.md` 的 overlap 提示，说明 `knowledge/` 对应文件已转为 stub 并指向本文。

---

## 5. 全部门禁结果

| 门禁 | 命令 | 结果 |
|---|---|---|
| Cargo check | `cargo check --workspace` | ✅ 通过 |
| Cargo test | `cargo test --workspace --quiet` | ✅ 通过 |
| Cargo clippy | `cargo clippy --workspace -- -D warnings` | ✅ 通过 |
| Cargo audit | `cargo audit --no-fetch` | ✅ 0 漏洞 |
| Cargo vet | `cargo vet --locked` | ✅ Vetting Succeeded |
| mdbook build | `mdbook build` | ✅ 成功 |
| 死链检查 | `python scripts/kb_auditor.py --link-check` | ✅ 0 死链 / 0 跨层问题 |
| 内容重叠 | `python scripts/detect_content_overlap.py` | ✅ 0 潜在重复 |
| i18n 术语 | `python scripts/add_bilingual_annotations.py --mode check-only` | ✅ 0 未覆盖 |

---

## 6. 提交记录

- `09521cb16` — align(Phase A): unify Cargo manifests, version inheritance, feature naming, metadata
- `1a645f45d` — align(Phase B): stubify knowledge/ non-archive Markdown files to concept/ canonical links
- `bf8b94bbb` — align(Phase C/D): docs canonical links + concept version/metadata cleanup

---

## 7. 后续建议

1. **继续修剪 `docs/` 中重复的理论正文**：当前已补齐权威链接，但部分 guide 仍保留大段与 `concept/` 重复的概念推导。建议后续按文件逐步删除重复段落，保留操作步骤、决策树、示例代码。
2. **迁移 `content/safety_critical/` 与 `content/ecosystem/deep_dives/`**：虽已 stub 化，但这些报告套房更适合放到 `docs/` 或 `content/`。
3. **统一 `concept/` 元数据模板**：可在 `AGENTS.md` 中明确 EN/Summary 位置、Rust 版本字段格式，作为新增文件的模板。
4. **CI 固化**：建议将上述 9 个门禁加入 CI，防止一致性回退。

---

*报告生成完毕，工作区已 clean。*
