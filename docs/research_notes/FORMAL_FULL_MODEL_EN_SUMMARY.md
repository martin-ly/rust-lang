# Rust Formal Full Model — English Summary

> **Source**: [FORMAL_FULL_MODEL_OVERVIEW.md](./FORMAL_FULL_MODEL_OVERVIEW.md) (Chinese)
> **Rust version**: 1.93.0+ (Edition 2024)
> **Last updated**: 2026-02-20

---

## Overview

A unified formal system covering **ownership + borrow + lifetime + type + trait + async + pin**, with axiom lists, theorem dependency DAG, and mappings to sub-documents.

---

## Core Mechanisms and Axiom Layer

| Mechanism | Axioms/Definitions | Sub-document |
| :--- | :--- | :--- |
| **Ownership** | Rules 1–3: unique owner, move transfer, scope-end drop | ownership_model |
| **Borrow** | Rules 5–8: shared/mutable borrow, mutual exclusion, scope | borrow_checker_proof |
| **Lifetime** | Axiom LF1–LF2, Def 1.4, $\ell \subseteq \text{lft}$ | lifetime_formalization |
| **Type system** | Progress, preservation, typing rules | type_system_foundations |
| **Variance** | Def 1.1–3.1 (covariant, contravariant, invariant) | variance_theory |
| **Trait** | Axiom COH1/COH2, object safety, impl resolution | trait_system_formalization |
| **Async** | Def 4.1–5.2 (Future, Poll, Ready/Pending) | async_state_machine |
| **Pin** | Def 1.1–2.2 (location stability, self-reference) | pin_self_referential |
| **Control flow** | A-CF1: reduction preserves type and ownership | formal_methods README |
| **Variables** | Def 1.4 binding, Def 1.5 shadowing | ownership_model |

---

## Theorem Dependency DAG (Simplified)

```text
[ axioms ]
     │
[ ownership ] [ borrow ] [ type ]
     │            │         │
     └────────────┼─────────┘
                  │
           [ lifetime LF-T1–T3 ]
                  │
     [ variance | async | pin ]
                  │
           [ CE-T1–T3 composition ]
                  │
           [ CSO-T1, USF-T1 ]
```

---

## Axiom → Composition Theorem DAG (Pillars 1+3)

- **CE-T1** (memory safety) ← ownership T3
- **CE-T2** (data-race freedom) ← borrow T1 + type T3
- **CE-T3** (type safety) ← type T3

---

## Key Axioms (Unified Numbering)

| ID | Content |
| :--- | :--- |
| A-OW1 | Each value has at most one owner |
| A-OW2 | Move transfers ownership |
| A-OW3 | Scope end releases |
| A-BR1 | Shared borrows may coexist |
| A-BR2 | Mutable borrow is exclusive |
| A-BR3 | Shared and mutable are mutually exclusive |
| A-BR4 | Borrow scope constraints |
| A-CF1 | Control-flow reduction preserves type and ownership |
| A-BIND1 | Variable binding establishes/updates $\Gamma$ |
| A-SHADOW1 | Shadowing makes old binding inaccessible; implicit drop |

---

## Formal Language and Proofs

- [FORMAL_LANGUAGE_AND_PROOFS](./FORMAL_LANGUAGE_AND_PROOFS.md) — Inference rules, operational semantics, judgment forms, formal proof derivations (mathematical level; complements Coq skeletons)

## Related Documents

- [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) — Full proofs for T-OW2, T-BR1, T-TY3 (L2)
- [PROOF_INDEX](./PROOF_INDEX.md) — 105+ proof index
- [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) — International alignment
