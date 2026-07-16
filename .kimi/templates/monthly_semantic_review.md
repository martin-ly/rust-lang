# Monthly Semantic Review Checklist

**Review period**: YYYY-MM
**Reviewer**: @username
**Scope**: concept/ authority drift, boundary semantics, stub purity, KG relation quality, and version semantic injection coverage.

---

## 1. Core Concept Definition Drift (sample 10 pages)

Sample 10 core `concept/` pages across L1–L4 and check whether definitions remain sharp, unambiguous, and aligned with current Rust stable (1.97.0).

| # | Page path | Definition checked | Drift found? | Action item |
|---|-----------|--------------------|--------------|-------------|
| 1 | `concept/01_foundation/xx_xx/xx_xx.md` |                    | [ ] Yes [ ] No |             |
| 2 | `concept/01_foundation/xx_xx/xx_xx.md` |                    | [ ] Yes [ ] No |             |
| 3 | `concept/02_intermediate/xx_xx/xx_xx.md` |                  | [ ] Yes [ ] No |             |
| 4 | `concept/02_intermediate/xx_xx/xx_xx.md` |                  | [ ] Yes [ ] No |             |
| 5 | `concept/03_advanced/xx_xx/xx_xx.md` |                      | [ ] Yes [ ] No |             |
| 6 | `concept/03_advanced/xx_xx/xx_xx.md` |                      | [ ] Yes [ ] No |             |
| 7 | `concept/04_formal/xx_xx/xx_xx.md` |                        | [ ] Yes [ ] No |             |
| 8 | `concept/04_formal/xx_xx/xx_xx.md` |                        | [ ] Yes [ ] No |             |
| 9 | `concept/02_intermediate/xx_xx/xx_xx.md` |                  | [ ] Yes [ ] No |             |
| 10 | `concept/03_advanced/xx_xx/xx_xx.md` |                     | [ ] Yes [ ] No |             |

**What to look for**:

- Definitions are operational (can be turned into a decision procedure).
- No circular definitions.
- Rust version annotations match current stable or are explicitly marked as nightly/preview.
- Counterexamples exist and are still valid under latest rustc.

---

## 2. Boundary Precision Review

Check key cross-domain / boundary semantics. Each should have a non-stub `concept/` authority page.

Run: `python scripts/check_cross_domain_coverage.py --strict`

| Domain pair | concept/ authority page exists? | Boundary clearly stated? | Action item |
|-------------|----------------------------------|--------------------------|-------------|
| async + unsafe | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| FFI + async | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| Send / Sync boundaries | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| let chains | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| unsafe extern blocks | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| Pin + lifetimes | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| GenericAssociatedTypes + trait bounds | [ ] Yes [ ] No | [ ] Yes [ ] No |             |
| const generics + trait specialization | [ ] Yes [ ] No | [ ] Yes [ ] No |             |

**Notes / additional boundary topics**:

---

## 3. New Stub Purity Review

Run: `python scripts/check_stub_purity.py --strict`

- [ ] Pseudo-stub count = 0
- [ ] Empty-shell count = 0
- [ ] High-duplicate stub count = 0

**Violations found**:

| File path | Lines | Bytes | Issue | Remediation |
|-----------|-------|-------|-------|-------------|
|           |       |       |       |             |

**Policy reminder**: Stub/redirect files must remain pure (≤25 lines / ≤2000 bytes). Content beyond a one-sentence description + canonical link must be moved to the `concept/` authority page.

---

## 4. KG Relation Quality Review

Run: `python scripts/check_kg_relation_precision.py --strict`

- [ ] Core 50 entity `generic_ratio` = 0%
- [ ] No `ex:RelationAnnotation` predicates around core entities

**Generic relations found**:

| Subject | Predicate | Object | Suggested concrete predicate |
|---------|-----------|--------|------------------------------|
|         |           |        |                              |

**Policy reminder**: KG relations must use semantic predicates (`dependsOn`, `entails`, `mutexWith`, `refines`, `equivalentTo`, `counterExample`). Generic `ex:RelationAnnotation` is not allowed for core entities.

---

## 5. Version Semantic Injection Coverage Review

Run: `python scripts/check_version_semantic_injection.py --strict`

- [ ] Rust 1.90–1.97 stable feature count mapped = _**/**_
- [ ] Each version tracking page links back to its `concept/` authority page
- [ ] Each `concept/` authority page links forward to relevant version tracking pages

**Unmapped or one-way-only features**:

| Feature | Version page | concept/ authority page | Issue | Action |
|---------|--------------|-------------------------|-------|--------|
|         |              |                         |       |        |

**Policy reminder**: Version features must map back to `concept/` authority pages; isolated release notes are not sufficient.

---

## 6. Decision Tree rustc Error Code Coverage (optional but recommended)

Run: `python scripts/check_decision_trees.py --strict`

- [ ] Node-level `E\d{4}` mappings have no ambiguity
- [ ] Top 30 rustc error code coverage ≥80%

**Gaps**:

| Error code | Decision tree node | Action |
|------------|--------------------|--------|
|            |                    |        |

---

## 7. Summary and Action Items

| Priority | Action | Owner | Due date |
|----------|--------|-------|----------|
|          |        |       |          |

**Overall semantic health grade**: _**/ 100
**Sign-off**:**_
