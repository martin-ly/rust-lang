# crates/*/docs 对齐 concept/ 权威层审计（2026-07-11）

**EN**: crates docs → concept Authority Alignment
**Summary**: 审计 crates/*/docs 是否按 AGENTS.md §2/§3.4 把通用 Rust 概念解释链接到 concept/ 权威层（不复制）。只读，不改正文。

> 扫描 crates/*/docs md: **563** · 含 concept/ 链接: **550** (97.7%) · 疑似复述待人工: **0**

## 口径
- `has_concept_link` = 正文含 `concept/` 子串（相对链接到权威层）。
- `suspect` = 无 concept 链接 且 >80 行 且 通用概念关键词命中 ≥3（**仅提示**，crate 特定 API/示例/实战含概念词属正常，需人工判断是否真复述通用概念）。

## 疑似复述清单（前 60，按关键词命中降序）
| 文件 | 行数 | 概念词命中 |
|:---|---:|---:|
✅ 无疑似复述（所有 >80 行且多概念词的 crates docs 已含 concept/ 链接）。

## 诚信
- 本审计只读；`suspect` 是启发式提示，不自动判定违规、不自动改文件。
- crates/*/docs 允许保留 crate 直接相关独特内容（API/示例/构建/实战）；仅当确为『复制通用概念解释』时才需改为链 concept/（AGENTS.md §3.4）。

*由 `scripts/check_crates_docs_alignment.py` 生成*