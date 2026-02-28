# Core Theorems — English Summary

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **Source**: [CORE_THEOREMS_FULL_PROOFS.md](./CORE_THEOREMS_FULL_PROOFS.md) (Chinese)
> **Proof depth**: L2 (full proofs; L3 machine-checkable scaffolding in progress)

---

## Overview

L2-level full proofs for **ownership T2**, **borrow T1**, and **type T3**, with induction base/step, auxiliary lemmas, and proof dependency DAG.

---

## Theorem Summary

| Theorem | Statement | Proof |
| :--- | :--- | :--- |
| **T-OW2** | Ownership uniqueness: at any time, at most one variable owns each value | Induction on state; L-OW1 base; move/copy/scope-end steps |
| **T-BR1** | Borrow checker ⇒ data-race freedom | L-BR1 (write mutual exclusion), L-BR2 (read-write exclusion); contradiction |
| **T-TY3** | Well-typed programs never reach type errors | T-TY2 preservation + L-TY1 (type errors rejected); contradiction |
| **SEND-T1 / SYNC-T1** | Send ⇒ safe cross-thread transfer; Sync ⇒ safe cross-thread shared reference | Def SEND1/SYNC1, SYNC-L1 ($T:\text{Sync} \Leftrightarrow \&T:\text{Send}$); [send_sync_formalization](formal_methods/send_sync_formalization.md) |

---

## Auxiliary Lemmas

| Lemma | Content |
| :--- | :--- |
| L-OW1 | Initial uniqueness |
| L-OW2 | No dangling (ownership T3 property 1) |
| L-OW3 | No double free (ownership T3 property 2) |
| L-BR1 | Write operations mutually exclusive |
| L-BR2 | Read and write cannot coexist |
| L-TY1 | Type errors rejected at type-check time |
| SYNC-L1 | $T : \text{Sync} \Leftrightarrow \&T : \text{Send}$ (Rust std; [send_sync_formalization](formal_methods/send_sync_formalization.md)) |

---

## L3 Machine-Checkable Scaffolding

| Theorem | L3 skeleton | Status |
| :--- | :--- | :--- |
| T-OW2 | coq_skeleton/OWNERSHIP_UNIQUENESS.v | Statement defined; proof Admitted |
| T-BR1 | coq_skeleton/BORROW_DATARACE_FREE.v | Statement + L-BR1/L-BR2 placeholders; proof Admitted |
| T-TY3 | coq_skeleton/TYPE_SAFETY.v | Statement + L-TY1 placeholder; proof Admitted |
| SEND-T1 / SYNC-T1 | [send_sync_formalization](formal_methods/send_sync_formalization.md) | L2 proofs in doc; no Coq skeleton yet |

**Extension path**: Aeneas, coq-of-rust integration for auto-generated Coq.

---

## Formal Language and Proofs

- [FORMAL_LANGUAGE_AND_PROOFS](./FORMAL_LANGUAGE_AND_PROOFS.md) — Formal language (inference rules, operational semantics, judgment forms) and mathematical proofs; complements Coq skeletons.

## Related Documents

- [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md) — Unified formal system (incl. Send/Sync)
- [send_sync_formalization](./formal_methods/send_sync_formalization.md) — Send/Sync Def SEND1/SYNC1, SEND-T1/SYNC-T1, SEND-SYNC-T1
- [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](./SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) — Safe decidable mechanisms (per-mechanism sections + 4-dim tables)
- [PROOF_INDEX](./PROOF_INDEX.md) — 105+ proof index
- [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md) — Safe Rust → proof assistant
