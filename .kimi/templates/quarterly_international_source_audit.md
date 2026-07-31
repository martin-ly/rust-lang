# Quarterly International Source Semantic Audit

**Audit quarter**: QX YYYY
**Auditor**: @username
**Scope**: Sample 5–8 core `concept/` pages and compare them against the corresponding international authority sources (Rust Reference, Rustonomicon, The Rust Programming Language, Async Book, std docs, RFCs). Goal: detect semantic drift, missing boundary conditions, and outdated version annotations.

---

## 1. Sample Selection

Select 5–8 pages from the priority list below, ensuring coverage across L1–L4 and at least one cross-domain boundary page:

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
| P1 | `concept/04_formal/03_operational_semantics/10_minirust.md` | [MiniRust GitHub](https://github.com/RalfJung/minirust), [Tree Borrows paper](https://perso.crans.org/vanile/treebor/) | L4 formal baseline |
| P1 | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` | [Tree Borrows paper](https://perso.crans.org/vanile/treebor/), [Miri borrow tracker](https://github.com/rust-lang/miri/blob/master/src/borrow_tracker/mod.rs) | L4 memory model |
| P2 | `concept/06_ecosystem/08_formal_verification/02_formal_verification_tools.md` | [Kani](https://model-checking.github.io/kani/), [Verus](https://verus-lang.github.io/verus/guide/), [Creusot](https://creusot-rs.github.io/) | L5-L6 ecosystem |

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
| 1 | | | | | | |
| 2 | | | | | | |
| 3 | | | | | | |
| 4 | | | | | | |
| 5 | | | | | | |

---

## 4. Mandatory Commands

Run before sign-off:

```bash
# External link validity for sampled pages
python scripts/kb_auditor.py --link-check

# Authority semantic keyword coverage
python scripts/authority_semantic_diff.py --strict

# Concept authority coverage (P0/P1/P2 + crates docs)
python scripts/check_concept_authority_coverage.py --strict --include-crates

# Cross-domain coverage (no P0 gaps)
python scripts/check_cross_domain_coverage.py --strict

# Concept code blocks for sampled pages (manual extraction if needed)
python scripts/check_concept_code_blocks.py --strict
```

---

## 5. Summary and Action Items

| Priority | Action | Owner | Due date |
|---|---|---|---|
| | | | |

**Overall audit conclusion**: [ ] No drift / [ ] Minor drift remediated / [ ] Major drift requires follow-up sprint

**Sign-off**: _________________
