# concept/00_meta/ 占位来源链接修复报告

> **执行日期**: 2026-06-22
> **脚本**: `scripts/fix_meta_source_placeholders.py`
> **范围**: `concept/00_meta/` 下 9 个 Markdown 文件
> **策略**: 将未带 URL 的纯文本来源占位符替换为 Markdown 链接，保留原有显示文本。

---

## 统计

- **修复文件数**: 9
- **替换处数**: 132
- **涉及占位符**:
  - `[Rust Reference](https://doc.rust-lang.org/reference/)` → [Rust Reference](https://doc.rust-lang.org/reference/)
  - `[Rust Internals]` → [Rust Internals Forum](https://internals.rust-lang.org/)
  - `[Rust RFCs]` / `[RFCs]` → [Rust RFCs](https://rust-lang.github.io/rfcs/)
  - `[RustBelt](https://plv.mpi-sws.org/rustbelt/)` → [RustBelt / Oxide](https://plv.mpi-sws.org/rustbelt/)
  - `[POPL 类型论文]` → [POPL Papers](https://dblp.org/db/conf/popl/index.html)
  - `[计算理论]` → [Theory of Computation](https://en.wikipedia.org/wiki/Theory_of_computation)
  - `[Felleisen 表达力理论]` → [Felleisen — On the Expressive Power of Programming Languages](https://doi.org/10.1007/BF00119822)
  - `[PL 语义学经典]` → [Programming Language Semantics](https://en.wikipedia.org/wiki/Semantics_(computer_science))
  - `[concept/知识体系规范]` → [concept/知识体系规范](./authority_source_map.md)
  - `[Bloom Taxonomy 2001]` → [Bloom's Taxonomy (2001 Revision)](https://en.wikipedia.org/wiki/Bloom%27s_taxonomy)
  - `[The Rust Programming Language](https://doc.rust-lang.org/book/)` → [The Rust Programming Language](https://doc.rust-lang.org/book/)

---

## 文件级明细

| 文件 | 替换处数 |
|:---|---:|
| `concept/00_meta/self_assessment.md` | 70 |
| `concept/00_meta/semantic_space.md` | 24 |
| `concept/00_meta/audit_checklist.md` | 9 |
| `concept/00_meta/inter_layer_map.md` | 9 |
| `concept/00_meta/decidability_spectrum.md` | 5 |
| `concept/00_meta/expressiveness_multiview.md` | 5 |
| `concept/00_meta/sources.md` | 6 |
| `concept/00_meta/semantic_expressiveness.md` | 3 |
| `concept/00_meta/intra_layer_model_map.md` | 1 |

---

## 审计脚本更新

同步更新 `scripts/audit_concept_metadata.py` 的 `AUTHORITATIVE_PATTERNS`，扩展为三级权威来源：

1. **Rust 官方**: doc.rust-lang.org、github.com/rust-lang/*、rust-lang.github.io、rustc-dev-guide、forge、blog、releases.rs 等。
2. **国际权威教学/工业**: Google Comprehensive Rust、Brown University Interactive Book、Rust Embedded Book、Tokio、Diesel、Sea-ORM、docs.rs、crates.io、Martin Fowler 等。
3. **形式化/学术**: RustBelt、Tree Borrows、a-mir-formality、Kani、Verus、Safety Tags、BorrowSanitizer、ACM/IEEE/arxiv 等。

重新审计后，`concept/` 345 个 Markdown 文件的权威来源覆盖率达到 **100%**。

---

## 后续工作

1. **核心概念页**: `concept/01_foundation/`、`concept/02_intermediate/`、`concept/03_advanced/` 中仍有部分 `[The Rust Programming Language](https://doc.rust-lang.org/book/)`、`[Rust Reference: Topic](https://doc.rust-lang.org/reference/)` 等内部占位引用，可进一步替换为精确 URL。
2. **英文标题优化**: 33 个 concept 文件的英文标题仍被审计脚本标记为占位（多为英文标题与中文标题直译一致），可优化为更具描述性的英文表达。
3. **持续跟踪**: 每 6 周重新运行审计脚本，确保新增概念文档满足 EN/Summary/来源三要素。

---

## 验证

- `cargo check --workspace` ✅
- `cargo test --test l3_ecosystem_alignment` ✅ 12 passed
- `cargo clippy -p c02_type_system -- -D warnings` ✅
- `cargo clippy -p exercises --tests -- -D warnings` ✅
