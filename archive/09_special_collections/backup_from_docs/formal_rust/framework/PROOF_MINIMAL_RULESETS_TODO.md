# Proof Convergence Plan (Minimal Rulesets → 100%)


## 📊 目录

- [Milestones](#milestones)
- [Workstreams & Tasks](#workstreams-tasks)
- [KPIs](#kpis)
- [Ownership](#ownership)
- [References](#references)


Status: Active  
Scope: Rust ≤ 1.89 (syntax/semantics, type system, borrowing/lifetimes, generics/traits/associated types)

## Milestones

- M1 (Week 1): Minimal rulesets compile
  - λ-core (Abs/App), eval (β), ADT (construct/project), basic contexts
  - Files: Coq/Lean progress-preservation modules
- M2 (Week 2): Progress/Preservation core branches proved
  - Cases: Abs/App/Proj; substitution/weakening/strengthening realized
- M3 (Week 3): HM unify sound/complete mainline
  - unify_sound, unify_complete + principal_types scaffold integration
- M4 (Week 4): Ownership invariants stitched
  - O-OB-UNI/O-OB-IMM/O-OB-LIF with MVE and doc ↔ proof alignment
- M5 (Week 5): AT projection consistency + trait bounds mapping
  - O-AT-PROJ/O-TR-BND first pass; back-links zero missing
- M6 (Week 6): >80% de-admit/sorry, optional CI syntax checks green

## Workstreams & Tasks

- WS1: Minimal Rulesets
  - [x] Define Expr/Ty/Ctx, typing (T-Var/Abs/App), eval (E-App/E-AppAbs)
  - [x] ADT typing (product/sum) and projections (T-Project), eval proj
  - [x] Context extension/lookup lemmas
- WS2: Type Safety Proofs
  - [x] Substitution lemma (typed substitution) - 基础结构已实现
  - [x] Weakening, Strengthening - 基础结构已实现
- [ ] Progress proof (Abs/App/ADT) - 草案进行中
- [ ] Preservation proof (β, proj) - 草案进行中
- WS3: HM Inference
  - [ ] Constraint syntax, Subst, apply  
  - [ ] unify_sound  
  - [ ] unify_complete  
  - [ ] principal_types interfaces + examples
- WS4: Ownership & Borrowing
  - [ ] Formal invariant skeleton (mut unique / imm aliasing)  
  - [ ] Lifetimes no-escape check hook to safety
  - [ ] MVEs synced with docs/tests
- WS5: Traits & Associated Types
  - [ ] AT projection well-formedness and consistency obligations  
  - [ ] Trait bound → constraint mapping to HM layer
- WS6: Navigation & Back-links
  - [ ] All “映射” sections have reverse links  
  - [ ] SSOT mapping finalized (no duplicate sources)

## KPIs

- Admit/sorry ratio: 100% → 20% (M6)  
- Back-link coverage: 100%  
- Examples passing: ≥ 1 per topic  
- Crossref errors: 0  

## Ownership

- WS1/WS2: (owner: core-proofs)  
- WS3: (owner: inference)  
- WS4: (owner: memory)  
- WS5: (owner: generics)  
- WS6: (owner: docs)

## References

- Progress/Preservation: `framework/proofs/coq/type_system_progress_preservation.v`, `lean/TypeSystem/ProgressPreservation.lean`  
- HM: `coq/hm_inference_soundness_completeness.v`, `lean/TypeSystem/HMInference.lean`  
- Docs: `language/02_type_system/22_formal_type_system_proofs.md`
