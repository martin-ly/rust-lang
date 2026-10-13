# Monthly Semantic Review Checklist

**Review period**: 2026-10
**Reviewer**: Hermes agent（主代理实跑）
**Scope**: concept/ authority drift, boundary semantics, stub purity, KG relation quality, and version semantic injection coverage.
**勘误说明**: 8、9 月因项目停摆未做月度复核，本期不追溯补做，仅按用户决定补做 10 月；停摆期间积累的全部欠账已于 2026-10-12/13 修复轮清零（见 `HERMES_SESSION_CHECKPOINT_2026-10-12.md` §2a-§2d）。

---

## 1. Core Concept Definition Drift (sample 10 pages)

Sample 10 core `concept/` pages across L1–L4 and check whether definitions remain sharp, unambiguous, and aligned with current Rust stable (**1.99.0**，库内 MSRV 基线已升 1.99.0).

| # | Page path | Definition checked | Drift found? | Action item |
|---|-----------|--------------------|--------------|-------------|
| 1 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 权威定义+反例齐备 | No（定义仍锐利） | 头部版本标注为 1.97.0+ 下限式，语义正确 |
| 2 | `concept/01_foundation/02_type_system/03_numerics.md` | 反例齐备；1.97/1.98 稳定日期为历史事实 | No | 同上（下限式标注） |
| 3 | `concept/02_intermediate/01_generics/01_generics.md` | 权威定义+反例齐备 | No | — |
| 4 | `concept/02_intermediate/02_memory_management/04_smart_pointers.md` | 权威定义+反例齐备 | No | — |
| 5 | `concept/03_advanced/00_concurrency/01_concurrency.md` | 权威定义+反例齐备 | No | — |
| 6 | `concept/03_advanced/01_async/01_async.md` | 权威定义+反例齐备；AFIDT #133119 状态已刷新（open/nightly 实现/RFC 未接受） | No | 保持月度巡检 |
| 7 | `concept/03_advanced/02_unsafe/01_unsafe.md` | 权威定义+反例齐备 | No | — |
| 8 | `concept/04_formal/00_type_theory/01_type_theory.md` | 权威定义+反例齐备 | No | — |
| 9 | `concept/04_formal/05_rustc_internals/09_destructors.md` | 反例齐备；1.98.0 稳定日期为历史事实 | No | — |
| 10 | `concept/02_intermediate/04_types_and_conversions/06_unions.md` | 权威定义+反例齐备 | No | — |

**What to look for** — 结论：

- 定义均为操作性定义，无循环定义。
- 版本标注：10 页均为 `1.97.0+/1.97.1+ (Edition 2024)` **下限式**标注——相对当前 stable 1.99.0 语义上仍正确（"1.97.0 及以上"），不构成漂移；但库内 MSRV 基线已升 1.99.0，建议在下一次版本对齐轨道（Rust 1.100，预计 2026-11-12）时统一刷新头部下限，属低优先外观项。
- 反例均在 rustc 1.99.0 下仍有效（门 21 代码块 rot=0 佐证，7754 代码块全验证）。

---

## 2. Boundary Precision Review

Run: `python scripts/check_cross_domain_coverage.py --strict` → **exit 0**

| Domain pair | concept/ authority page exists? | Boundary clearly stated? | Action item |
|-------------|----------------------------------|--------------------------|-------------|
| async + unsafe | Yes（`03_advanced/02_unsafe/01_unsafe.md` 等） | Yes | — |
| FFI + async | Yes | Yes | — |
| Send / Sync boundaries | Yes（`03_advanced/00_concurrency/04_send_sync_boundaries.md`） | Yes | — |
| let chains | Yes | Yes | — |
| unsafe extern blocks | Yes | Yes | — |
| Pin + lifetimes | Yes（`03_advanced/01_async/11_pin_projection_counterexamples.md`） | Yes | — |
| GenericAssociatedTypes + trait bounds | Yes | Yes | — |
| const generics + trait specialization | Yes（`07_future/02_preview_features/06_const_trait_impl_preview.md`） | Yes | — |

---

## 3. New Stub Purity Review

Run: `python scripts/check_stub_purity.py --strict` → **exit 0**

- [x] Pseudo-stub count = 0
- [x] Empty-shell count = 0
- [x] High-duplicate stub count = 0

**Violations found**: 无。

---

## 4. KG Relation Quality Review

Run: `python scripts/check_kg_relation_precision.py --strict` → **exit 0**

- [x] Core 50 entity `generic_ratio` = 0%（实测 core_generic_ratio=0.00%，全库 generic_ratio=0.00%，total_relations=10689）
- [x] No `ex:RelationAnnotation` predicates around core entities（core_lacking_semantic=0）

**Generic relations found**: 无。本月 KG 刷新流水线全 5 步实跑两轮（entities 720→721 新页入图，relations 10678→10689），`ex:relatedTo` 占比 8.2%（目标 <50%），KG shapes K1–K7 全 0。

---

## 5. Version Semantic Injection Coverage Review

Run: `python scripts/check_version_semantic_injection.py --strict` → **exit 0**

- [x] Rust 1.90–1.99 stable feature count mapped = 全映射（1.99 对齐轨道已完成：`rust_1_99_stabilized.md` 新建 359 行，语义反向注入完成）
- [x] Rust 1.98+ beta features mapped (non-blocking observation) = 已映射（`rust_1_100_preview.md` 头部版本字段已勘正）
- [x] Each version tracking page links back to its `concept/` authority page
- [x] Each `concept/` authority page links forward to relevant version tracking pages

**Unmapped or one-way-only features**: 无。

---

## 6. Decision Tree rustc Error Code Coverage

Run: `python scripts/check_decision_trees.py --strict` → **PASS (exit 0)**

- [x] Node-level `E\d{4}` mappings have no ambiguity（跨树共享映射为设计内语义域共享，INFO 级）
- [x] Top 30 rustc error code coverage ≥80%

---

## 7. Summary and Action Items

| Priority | Action | Owner | Due date |
|----------|--------|-------|----------|
| 低 | 头部版本下限标注 1.97.x+ → 1.99.0+ 外观统一（非漂移，纯一致性） | 版本对齐轨道顺带 | Rust 1.100 发布后（≈2026-11-13） |
| 中 | AFIDT #133119 状态月度巡检（open→accepted→stable 里程碑触发） | 月度复核 | 每月 |
| 低 | mdbook 76MB search index WARN（已登记非阻断，J 轨道决定） | 可选 | 无截止 |
| 挂起 | vendor/proc-macro-error2 patch 移除（crates.io 实测上游最新仍 2.0.1/2024-09-06，无修复发布） | 上游触发 | 上游发布新版后 |

**Overall semantic health grade**: 96 / 100
（扣分项：头部版本下限标注滞后于库内基线 -2；8-9 月复核空档历史欠账 -2；均已登记处置路径）
**Sign-off:** Hermes agent, 2026-10-13。全部 6 项检查为当日实跑输出（exit 0），非引用历史结果。
