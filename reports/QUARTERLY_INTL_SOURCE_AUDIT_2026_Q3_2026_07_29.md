# Quarterly International Source Semantic Audit — 2026 Q3

**Audit quarter**: 2026 Q3
**Auditor**: Kimi Code CLI
**Scope**: Sample 8 core `concept/` pages and compare them against the corresponding international authority sources (Rust Reference, Rustonomicon, The Rust Programming Language, Async Book, std docs, RFCs). Goal: detect semantic drift, missing boundary conditions, and outdated version annotations.

---

## 1. Sample Selection

| Priority | Page path | Authority source to compare | Reason for selection |
|---:|---|---|---|
| P0 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | [TRPL Ch04](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | Core L1 concept; frequent drift risk |
| P0 | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | [TRPL Ch04](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) | Core L1 concept |
| P0 | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | [Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/lifetime-rules.html) | Complex boundary semantics |
| P0 | `concept/03_advanced/01_async/08_pin_unpin.md` | [std::pin](https://doc.rust-lang.org/std/pin/index.html), [Async Book — Pin](https://rust-lang.github.io/async-book/04_pinning/01_chapter.html) | Cross-domain (async × unsafe) |
| P0 | `concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | [Rust Reference — BCU](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | Normative source; anchors must stay valid |
| P1 | `concept/02_intermediate/00_traits/01_traits.md` | [TRPL Ch10](https://doc.rust-lang.org/book/ch10-02-traits.html), [RFC 255](https://rust-lang.github.io/rfcs/0255-object-safety.html) | L2 core |
| P1 | `concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md` | [Rustonomicon — Send/Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | Cross-domain boundary |
| P1 | `concept/03_advanced/02_unsafe/01_unsafe.md` | [Rust Reference — unsafe keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) | L3 expert |

---

## 2. Comparison Dimensions

For each sampled page, check the following against the authority source:

| Dimension | Question to answer | Pass criterion |
|---|---|---|
| **Definition drift** | Does the page's definition match the authority source? | No contradiction; any project-specific extension is explicitly marked `project-specific` |
| **Boundary completeness** | Are all exceptions, preconditions, and UB triggers listed? | Matches or exceeds authority source coverage |
| **Version alignment** | Does the rust-version annotation match current stable? | ≤ current stable patch version |
| **Anchor validity** | Do external links to Reference/Nomicon still resolve? | All links HTTP 200 |
| **Code block freshness** | Do code examples compile under current stable with the declared edition? | `check_concept_code_blocks.py` sample pass |
| **Cross-link health** | Does the page link to related `concept/` authority pages? | No dead internal links |

---

## 3. Audit Findings

| # | Page path | Authority source | Dimension | Finding | Severity (P0/P1/P2) | Action item |
|---:|---|---|---|---|---|---|
| 1 | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | TRPL Ch04.2, Rust Reference — References | Definition drift / Anchor validity | 定理链编号段落中误插了「不可达」非正文文本，影响阅读；外部链接本身有效。 | P2 | 已删除误插文本（commit 待用户提交）。 |
| 2 | `concept/03_advanced/01_async/08_pin_unpin.md` | Rustonomicon — Pin, std::pin | Anchor validity | 原引用 Rustonomicon Pin 的链接指向 `std/pin/index.html`，与权威来源 `nomicon/pin.html` 不一致。 | P2 | 已修正为 `https://doc.rust-lang.org/nomicon/pin.html`，并保留 std::pin 模块链接。 |
| 3 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | TRPL Ch04, Brown Interactive Book | Definition drift / Version alignment | 定义与 TRPL/Brown 一致；rust-version 1.97.0+ 对齐当前 stable 1.97.1；无新增边界条件。 | — | 无行动项。 |
| 4 | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | Rust Reference — Lifetimes, TRPL Ch10.3 | Definition drift / Boundary completeness | 已覆盖 elision 规则（含 trait object、`const`/`static`、函数指针/闭包、`'_` placeholder）；`'static ⊑ 'a` 方向说明与 Reference 一致；外部链接有效。 | — | 无行动项。 |
| 5 | `concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | Rust Reference — BCU | Boundary completeness / Anchor validity | 11 项 UB 清单逐条链接到 Reference `r-undefined.*` 锚点；1.97.1+ 版本标注与 Reference 当前稳定版一致；未发现遗漏。 | — | 无行动项。 |
| 6 | `concept/02_intermediate/00_traits/01_traits.md` | TRPL Ch10.2, RFC 255 | Definition drift / Version alignment | Trait 定义、object safety、orphan rule、coherence 与 RFC 255 / RFC 1023 一致；rust-version 1.97.0+ 对齐；含 nightly 特性提示。 | — | 无行动项。 |
| 7 | `concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md` | Rustonomicon — Send/Sync, std::marker | Definition drift | Send/Sync 契约、auto trait 推导、negative impl、PhantomData opt-out 与权威来源一致；未发现漂移。 | — | 无行动项。 |
| 8 | `concept/03_advanced/02_unsafe/01_unsafe.md` | Rust Reference, Rustonomicon, Edition Guide 2024 | Boundary completeness / Version alignment | 已覆盖 unsafe blocks、unsafe extern blocks（RFC 3484）、unsafe attributes（RFC 3325）、unsafe_op_in_unsafe_fn；rust-version 1.97.1+ 对齐；链接有效。 | — | 无行动项。 |

---

## 4. Mandatory Commands

Run before sign-off:

```bash
# External link validity for sampled pages
python scripts/kb_auditor.py --link-check

# Authority semantic keyword coverage
python scripts/authority_semantic_diff.py --strict

# Cross-domain coverage (no P0 gaps)
python scripts/check_cross_domain_coverage.py --strict

# Concept code blocks for sampled pages (manual extraction if needed)
python scripts/check_concept_code_blocks.py --strict
```

---

## 5. Summary and Action Items

| Priority | Action | Owner | Due date |
|---|---|---|---|
| P2 | 完成 `borrowing.md` 定理链编号段落的清理并提交。 | Maintainer | 2026-07-29 |
| P2 | 完成 `pin_unpin.md` Rustonomicon 链接修正并提交。 | Maintainer | 2026-07-29 |
| — | 其余 6 个抽样页与国际来源一致，无需行动。 | — | — |
| — | 运行 KG 刷新序列（`generate_kg_index.py` → `generate_kg_v3.py` → `apply_kg_semantic_predicates.py` → `fallback_kg_generic_to_related.py` → `compress_kg_relatedto.py`）并校验 `check_kg_shapes.py --strict` 与 `check_kg_relation_precision.py --strict`。 | Kimi Code CLI | 2026-07-29 |
| — | 运行全质量门回归 `bash scripts/run_quality_gates.sh` 确认无回归。 | Kimi Code CLI | 2026-07-29 |

**Overall audit conclusion**: [x] Minor drift remediated / [ ] No drift / [ ] Major drift requires follow-up sprint

**Sign-off**: Kimi Code CLI, 2026-07-29
