# Documentation Master Index

> Auto-generated cross-reference index for the Rust Ownership Decidability documentation.

## Table of Contents

- [Documentation Master Index](#documentation-master-index)
  - [Table of Contents](#table-of-contents)
  - [Documentation Structure](#documentation-structure)
    - [Core Documentation](#core-documentation)
    - [Core Concepts](#core-concepts)
    - [Formal Foundations](#formal-foundations)
    - [Case Studies](#case-studies)
  - [Core Concept Links](#core-concept-links)
    - [Ownership System](#ownership-system)
    - [Borrowing System](#borrowing-system)
    - [Lifetimes](#lifetimes)
    - [Type System](#type-system)
  - [Formal Verification Links](#formal-verification-links)
    - [Key Theorems](#key-theorems)
    - [Coq File Organization](#coq-file-organization)
  - [Case Study Links](#case-study-links)
    - [Standard Library Case Studies](#standard-library-case-studies)
    - [Async Ecosystem](#async-ecosystem)
  - [Cross-Reference Map](#cross-reference-map)
    - [Files Referenced By](#files-referenced-by)

---

## Documentation Structure

### Core Documentation

| Document | Description |
|----------|-------------|
| [README.md](README.md) | Project overview and navigation |
| [READING_GUIDE.md](READING_GUIDE.md) | How to read this documentation |
| [FINAL_MASTER_INDEX.md](FINAL_MASTER_INDEX.md) | Manual master index |
| [MASTER_COMPREHENSIVE_ANALYSIS.md](MASTER_COMPREHENSIVE_ANALYSIS.md) | Comprehensive analysis |

### Core Concepts

| Topic | Detailed Guide | Quick Reference |
|-------|---------------|-----------------|
| Ownership | [ownership-deep-dive.md](01-core-concepts/detailed-concepts/ownership-deep-dive.md) | [ownership-concept-card.md](01-core-concepts/short-concepts/ownership-concept-card.md) |
| Borrowing | [borrowing-in-depth.md](01-core-concepts/detailed-concepts/borrowing-in-depth.md) | [borrowing-concept-card.md](01-core-concepts/short-concepts/borrowing-concept-card.md) |
| Lifetimes | [lifetimes-mastery.md](01-core-concepts/detailed-concepts/lifetimes-mastery.md) | [lifetime-concept-card.md](01-core-concepts/short-concepts/lifetime-concept-card.md) |

### Formal Foundations

| Area | Entry Point |
|------|-------------|
| Formal Models | [formal-foundations/models/](formal-foundations/models/) |
| Semantics | [formal-foundations/semantics/](formal-foundations/semantics/) |
| Proofs | [formal-foundations/proofs/](formal-foundations/proofs/) |
| Coq Formalization | [coq-formalization/](coq-formalization/) |

### Case Studies

| Category | Index |
|----------|-------|
| All Case Studies | [case-studies/README.md](case-studies/README.md) |
| Embedded | [case-studies/embedded/README.md](case-studies/embedded/README.md) |
| Blockchain | [case-studies/blockchain/README.md](case-studies/blockchain/README.md) |
| Web Development | [case-studies/wasm/README.md](case-studies/wasm/README.md) |

---

## Core Concept Links

### Ownership System

- **Theory**: [ownership-types.md](formal-foundations/models/ownership-types.md)
- **Practice**: [ownership-deep-dive.md](01-core-concepts/detailed-concepts/ownership-deep-dive.md)
- **Examples**: See examples in [COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md](COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md)

### Borrowing System

- **Theory**: [borrow-semantics.md](formal-foundations/models/borrow-semantics.md)
- **Practice**: [borrowing-in-depth.md](01-core-concepts/detailed-concepts/borrowing-in-depth.md)
- **Coq Proof**: [ReborrowComplete.v](coq-formalization/theories/Advanced/ReborrowComplete.v)

### Lifetimes

- **Theory**: [lifetime-logic.md](formal-foundations/models/lifetime-logic.md)
- **Practice**: [lifetimes-mastery.md](01-core-concepts/detailed-concepts/lifetimes-mastery.md)
- **Coq Proof**: [MetatheoryTermination.v](coq-formalization/theories/Advanced/MetatheoryTermination.v)

### Type System

- **Theory**: [type-system-formalization.md](formal-foundations/semantics/type-system-formalization.md)
- **Coq**: [TypeSystem.v](coq-formalization/theories/Typing/TypeSystem.v)

---

## Formal Verification Links

### Key Theorems

| Theorem | Natural Language | Coq Formalization |
|---------|-----------------|-------------------|
| Termination | [THEOREM_INTUITIONS.md](THEOREM_INTUITIONS.md) | [MetatheoryTermination.v](coq-formalization/theories/Advanced/MetatheoryTermination.v) |
| Decidability | [decidability_theorems.md](theorems/decidability_theorems.md) | [MetatheoryDecidability.v](coq-formalization/theories/Advanced/MetatheoryDecidability.v) |
| Type Safety | [memory-safety-proof.md](formal-foundations/proofs/memory-safety-proof.md) | [MetatheoryKeyProofs.v](coq-formalization/theories/Advanced/MetatheoryKeyProofs.v) |

### Coq File Organization

```text
coq-formalization/
├── Syntax/           # Type and expression definitions
├── Typing/           # Type system rules
├── Semantics/        # Operational semantics
├── Metatheory/       # Key theorems and proofs
└── Advanced/         # Rust 1.94+ features
```

---

## Case Study Links

### Standard Library Case Studies

| Crate | Formal Analysis |
|-------|-----------------|
| Vec | [std-vec-formal-analysis.md](case-studies/std-vec-formal-analysis.md) |
| String | [std-string-formal-analysis.md](case-studies/std-string-formal-analysis.md) |
| HashMap | [std-hashmap-formal-analysis.md](case-studies/std-hashmap-formal-analysis.md) |
| Iterator | [std-iterator-formal-analysis.md](case-studies/std-iterator-formal-analysis.md) |
| Smart Pointers | [std-smart-pointers-formal-analysis.md](case-studies/std-smart-pointers-formal-analysis.md) |

### Async Ecosystem

| Crate | Formal Analysis |
|-------|-----------------|
| Tokio Runtime | [tokio-runtime-formal-analysis.md](case-studies/tokio-runtime-formal-analysis.md) |
| Async-std | [async-std-formal-analysis.md](case-studies/async-std-formal-analysis.md) |
| Futures | [futures-crate-formal-analysis.md](case-studies/futures-crate-formal-analysis.md) |

---

## Cross-Reference Map

### Files Referenced By

**docs/research_notes/formal_methods/ownership_model.md** (referenced 301 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_model..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_model..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_model..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_model..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_model..."
- ... and 296 more

**docs/research_notes/formal_methods/borrow_checker_proof.md** (referenced 265 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "borrow_checker_proof..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "borrow_checker_proof..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "borrow_checker_proof..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "borrow_checker_proof..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "borrow_checker_proof..."
- ... and 260 more

**docs/research_notes/type_theory/type_system_foundations.md** (referenced 226 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system_foundations..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system_foundations..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system_foundations..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system_foundations..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system_foundations..."
- ... and 221 more

**docs/research_notes/formal_methods/async_state_machine.md** (referenced 179 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "async_state_machine..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "async_state_machine..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "async_state_machine..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "async_state_machine..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "async_state_machine..."
- ... and 174 more

**docs/research_notes/formal_methods/README.md** (referenced 130 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/formal_methods..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/formal_methods..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "formal_methods..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "formal_methods/README..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/formal_methods..."
- ... and 125 more

**docs/research_notes/formal_methods/lifetime_formalization.md** (referenced 125 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "lifetime_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "lifetime_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "formal_methods/lifetime_formalization..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "lifetime_formalization..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "生命周期形式化..."
- ... and 120 more

**docs/research_notes/PROOF_INDEX.md** (referenced 124 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "PROOF_INDEX..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "PROOF_INDEX..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "PROOF_INDEX..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/PROOF_INDEX.md..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "PROOF_INDEX..."
- ... and 119 more

**docs/research_notes/type_theory/trait_system_formalization.md** (referenced 123 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "trait_system_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "trait_system_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "trait_system_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "trait_system_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "trait_system_formalization..."
- ... and 118 more

**docs/research_notes/formal_methods/send_sync_formalization.md** (referenced 117 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "send_sync_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "send_sync_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "send_sync_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "send_sync_formalization..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "send_sync_formalization..."
- ... and 112 more

**docs/research_notes/type_theory/variance_theory.md** (referenced 93 times)

- [crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md](crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md): "variance_theory..."
- [crates/c04_generic/docs/ONE_PAGE_SUMMARY.md](crates/c04_generic/docs/ONE_PAGE_SUMMARY.md): "variance_theory..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "variance_theory..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "variance_theory..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "variance_theory..."
- ... and 88 more

**docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md** (referenced 89 times)

- [docs/rust-ownership-decidability/CROSS_REFERENCE_VERIFICATION_SUMMARY.md](docs/rust-ownership-decidability/CROSS_REFERENCE_VERIFICATION_SUMMARY.md): "MASTER_INDEX_AUTO.md..."
- [docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md](docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md): "MASTER_INDEX_AUTO.md..."
- [docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md](docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md): "MASTER_INDEX_AUTO.md..."
- [docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md](docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md): "MASTER_INDEX_AUTO.md..."
- [docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md](docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md): "MASTER_INDEX_AUTO.md..."
- ... and 84 more

**docs/research_notes/software_design_theory/01_design_patterns_formal/README.md** (referenced 85 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "01_design_patterns_formal..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "01_design_patterns..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "01_design_patterns_formal/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "01_design_patterns..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "01_design_patterns..."
- ... and 80 more

**docs/research_notes/formal_methods/pin_self_referential.md** (referenced 83 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "pin_self_referential..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "pin_self_referential..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "pin_self_referential..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "pin_self_referential..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "pin_self_referential..."
- ... and 78 more

**docs/research_notes/CORE_THEOREMS_FULL_PROOFS.md** (referenced 78 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "CORE_THEOREMS_FULL_PROOFS..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "CORE_THEOREMS_FULL_PROOFS..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "CORE_THEOREMS_FULL_PROOFS..."
- [docs/COMPREHENSIVE_COMPLETION_STATUS_2026_02_23.md](docs/COMPREHENSIVE_COMPLETION_STATUS_2026_02_23.md): "CORE_THEOREMS_FULL_PROOFS..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "CORE_THEOREMS_FULL_PROOFS..."
- ... and 73 more

**docs/research_notes/TOOLS_GUIDE.md** (referenced 73 times)

- [README.en.md](README.en.md): "View Guide..."
- [README.en.md](README.en.md): "research_notes/TOOLS_GUIDE..."
- [README.en.md](README.en.md): "Formal Verification Tools Guide..."
- [crates/c07_process/docs/tier_01_foundations/02_主索引导航.md](crates/c07_process/docs/tier_01_foundations/02_主索引导航.md): "形式化验证工具..."
- [crates/c09_design_pattern/README.md](crates/c09_design_pattern/README.md): "形式化验证理论..."
- ... and 68 more

**docs/research_notes/type_theory/advanced_types.md** (referenced 72 times)

- [BROKEN_LINKS_REPORT.md](BROKEN_LINKS_REPORT.md): "类型理论 - 高级类型..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "advanced_types..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "advanced_types..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "advanced_types..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "advanced_types..."
- ... and 67 more

**docs/02_reference/quick_reference/type_system.md** (referenced 72 times)

- [crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_内存布局优化.md](crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_内存布局优化.md): "type_system 速查卡..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.en.md](crates/c02_type_system/docs/00_MASTER_INDEX.en.md): "type_system..."
- [crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md](crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md): "type_system..."
- [crates/c02_type_system/docs/tier_04_advanced/README.md](crates/c02_type_system/docs/tier_04_advanced/README.md): "类型系统指南..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "type_system..."
- ... and 67 more

**docs/research_notes/README.md** (referenced 69 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "research_notes/..."
- ... and 64 more

**crates/c01_ownership_borrow_scope/docs/tier_04_advanced/06_类型系统理论.md** (referenced 59 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "Tier 4: 类型系统理论..."
- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "4.1 类型系统理论..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "类型系统理论..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "所有权理论..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用理论..."
- ... and 54 more

**docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md** (referenced 59 times)

- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "多维概念矩阵..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "多维概念矩阵..."
- [crates/c03_control_fn/README.md](crates/c03_control_fn/README.md): "多维概念矩阵..."
- [crates/c04_generic/README.md](crates/c04_generic/README.md): "知识图谱与概念关系增强版..."
- [crates/c04_generic/README.md](crates/c04_generic/README.md): "多维矩阵对比分析..."
- ... and 54 more

**docs/research_notes/experiments/performance_benchmarks.md** (referenced 58 times)

- [crates/c01_ownership_borrow_scope/docs/README.md](crates/c01_ownership_borrow_scope/docs/README.md): "性能基准测试..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "performance_benchmarks..."
- [docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md](docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md): "experiments/performance_benchmarks.md..."
- [docs/research_notes/FAQ.md](docs/research_notes/FAQ.md): "性能基准测试..."
- [docs/research_notes/GETTING_STARTED.md](docs/research_notes/GETTING_STARTED.md): "性能基准测试..."
- ... and 53 more

**docs/02_reference/quick_reference/ownership_cheatsheet.md** (referenced 56 times)

- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md): "ownership_cheatsheet..."
- [crates/c01_ownership_borrow_scope/docs/ONE_PAGE_SUMMARY.md](crates/c01_ownership_borrow_scope/docs/ONE_PAGE_SUMMARY.md): "ownership_cheatsheet..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "quick_reference/ownership_cheatsheet..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_cheatsheet..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "ownership_cheatsheet..."
- ... and 51 more

**docs/research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md** (referenced 56 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "FORMAL_PROOF_SYSTEM_GUIDE..."
- [docs/FINAL_LINK_REPAIR_REPORT.md](docs/FINAL_LINK_REPAIR_REPORT.md): "形式化分析..."
- [docs/LINK_REPAIR_STRATEGY.md](docs/LINK_REPAIR_STRATEGY.md): "形式化分析..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "形式化证明系统指南..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "形式化证明系统指南..."
- ... and 51 more

**docs/research_notes/software_design_theory/03_execution_models/06_boundary_analysis.md** (referenced 52 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "06_boundary_analysis..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "06_boundary_analysis..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "06_boundary_analysis..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "06_boundary_analysis..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "06_boundary_analysis..."
- ... and 47 more

**docs/04_thinking/DECISION_GRAPH_NETWORK.md** (referenced 50 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "决策图网..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "决策图网..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "决策图网..."
- [crates/c05_threads/README.md](crates/c05_threads/README.md): "决策图网..."
- [crates/c05_threads/docs/00_MASTER_INDEX.md](crates/c05_threads/docs/00_MASTER_INDEX.md): "决策图网..."
- ... and 45 more

**docs/research_notes/QUALITY_CHECKLIST.md** (referenced 50 times)

- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "QUALITY_CHECKLIST..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "QUALITY_CHECKLIST..."
- [docs/README.md](docs/README.md): "./research_notes/QUALITY_CHECKLIST.md..."
- [docs/archive/process_reports/2026_02/CONTENT_IMPROVEMENT_PLAN.md](docs/archive/process_reports/2026_02/CONTENT_IMPROVEMENT_PLAN.md): "QUALITY_CHECKLIST..."
- [docs/archive/process_reports/2026_02/DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md](docs/archive/process_reports/2026_02/DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md): "QUALITY_CHECKLIST..."
- ... and 45 more

**docs/04_thinking/PROOF_GRAPH_NETWORK.md** (referenced 48 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "证明图网..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "证明图网..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "证明图网..."
- [crates/c05_threads/README.md](crates/c05_threads/README.md): "证明图网..."
- [crates/c05_threads/docs/00_MASTER_INDEX.md](crates/c05_threads/docs/00_MASTER_INDEX.md): "证明图网..."
- ... and 43 more

**docs/research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md** (referenced 47 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "INTERNATIONAL_FORMAL_VERIFICATION_INDEX..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "国际对标索引..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "国际对标索引..."
- [docs/01_learning/LEARNING_PATH_PLANNING.md](docs/01_learning/LEARNING_PATH_PLANNING.md): "国际对标索引..."
- [docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md](docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md): "INTERNATIONAL_FORMAL_VERIFICATION_INDEX..."
- ... and 42 more

**docs/research_notes/RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md** (referenced 47 times)

- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS..."
- [docs/06_toolchain/README.md](docs/06_toolchain/README.md): "Rust 1.93 语言特性全面分析（92 项设计论证）..."
- [docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md](docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md): "RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS..."
- [docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md](docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md): "RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS..."
- [docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md](docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md): "RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS..."
- ... and 42 more

**crates/c01_ownership_borrow_scope/docs/tier_02_guides/01_所有权快速入门.md** (referenced 46 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "Tier 2: 所有权快速入门..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md): "Ownership Guide..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "所有权系统详解..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "所有权系统基础..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "所有权基础..."
- ... and 41 more

**docs/research_notes/research_methodology.md** (referenced 46 times)

- [docs/research_notes/CONTENT_ENHANCEMENT.md](docs/research_notes/CONTENT_ENHANCEMENT.md): "研究方法论..."
- [docs/research_notes/FAQ.md](docs/research_notes/FAQ.md): "研究方法论..."
- [docs/research_notes/FAQ.md](docs/research_notes/FAQ.md): "研究方法论..."
- [docs/research_notes/FAQ.md](docs/research_notes/FAQ.md): "研究方法论..."
- [docs/research_notes/FAQ.md](docs/research_notes/FAQ.md): "研究方法论..."
- ... and 41 more

**crates/c02_type_system/docs/tier_02_guides/01_基础类型指南.md** (referenced 44 times)

- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "基础类型指南..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "基础类型指南..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.en.md](crates/c02_type_system/docs/00_MASTER_INDEX.en.md): "Basic Types Guide..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.md](crates/c02_type_system/docs/00_MASTER_INDEX.md): "基础类型指南..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "Tier 2 - 基础类型指南..."
- ... and 39 more

**docs/research_notes/experiments/memory_analysis.md** (referenced 44 times)

- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "memory_analysis..."
- [docs/02_reference/ALIGNMENT_GUIDE.md](docs/02_reference/ALIGNMENT_GUIDE.md): "memory_analysis..."
- [docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md](docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md): "experiments/memory_analysis.md..."
- [docs/research_notes/GLOSSARY.md](docs/research_notes/GLOSSARY.md): "内存分析..."
- [docs/research_notes/GLOSSARY.md](docs/research_notes/GLOSSARY.md): "内存分析..."
- ... and 39 more

**crates/c02_type_system/docs/tier_02_guides/04_Trait系统指南.md** (referenced 43 times)

- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "Trait系统指南..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.en.md](crates/c02_type_system/docs/00_MASTER_INDEX.en.md): "Trait System Guide..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.md](crates/c02_type_system/docs/00_MASTER_INDEX.md): "Trait 系统指南..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "Tier 2 - Trait 系统指南..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "Trait 系统指南..."
- ... and 38 more

**docs/research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md** (referenced 43 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "SAFE_UNSAFE_ANALYSIS..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "SAFE_UNSAFE_ANALYSIS..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "SAFE_UNSAFE_ANALYSIS..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "SAFE_UNSAFE_ANALYSIS..."
- [docs/04_thinking/APPLICATIONS_ANALYSIS_VIEW.md](docs/04_thinking/APPLICATIONS_ANALYSIS_VIEW.md): "SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS..."
- ... and 38 more

**docs/research_notes/software_design_theory/04_compositional_engineering/README.md** (referenced 43 times)

- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "04_compositional_engineering..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "04_compositional_engineering..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "04_compositional_engineering..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "04_compositional_engineering/..."
- [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md): "04_compositional_engineering..."
- ... and 38 more

**docs/research_notes/experiments/compiler_optimizations.md** (referenced 42 times)

- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "compiler_optimizations..."
- [docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md](docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md): "experiments/compiler_optimizations.md..."
- [docs/research_notes/GLOSSARY.md](docs/research_notes/GLOSSARY.md): "编译器优化..."
- [docs/research_notes/INDEX.md](docs/research_notes/INDEX.md): "compiler_optimizations.md..."
- [docs/research_notes/INDEX.md](docs/research_notes/INDEX.md): "编译器优化..."
- ... and 37 more

**docs/research_notes/DESIGN_MECHANISM_RATIONALE.md** (referenced 42 times)

- [docs/04_thinking/DECISION_GRAPH_NETWORK.md](docs/04_thinking/DECISION_GRAPH_NETWORK.md): "DESIGN_MECHANISM_RATIONALE..."
- [docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md](docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md): "DESIGN_MECHANISM_RATIONALE..."
- [docs/04_thinking/README.md](docs/04_thinking/README.md): "../research_notes/DESIGN_MECHANISM_RATIONALE.md..."
- [docs/research_notes/ARGUMENTATION_GAP_INDEX.md](docs/research_notes/ARGUMENTATION_GAP_INDEX.md): "DESIGN_MECHANISM_RATIONALE..."
- [docs/research_notes/ARGUMENTATION_GAP_INDEX.md](docs/research_notes/ARGUMENTATION_GAP_INDEX.md): "DESIGN_MECHANISM_RATIONALE..."
- ... and 37 more

**crates/c12_wasm/docs/RUST_192_WASM_IMPROVEMENTS.md** (referenced 41 times)

- [BROKEN_LINKS_REPORT.md](BROKEN_LINKS_REPORT.md): "c12_wasm/docs/RUST_192_WASM_IMPROVEMENTS.md..."
- [crates/c12_wasm/README.md](crates/c12_wasm/README.md): "Rust 1.92.0 WASM 改进文档..."
- [crates/c12_wasm/README.md](crates/c12_wasm/README.md): "Rust 1.92.0 WASM 改进文档..."
- [crates/c12_wasm/RUST_192_UPDATE_SUMMARY.md](crates/c12_wasm/RUST_192_UPDATE_SUMMARY.md): "Rust 1.92.0 WASM 改进文档..."
- [crates/c12_wasm/docs/RUST_192_BEST_PRACTICES.md](crates/c12_wasm/docs/RUST_192_BEST_PRACTICES.md): "Rust 1.92.0 WASM 改进文档..."
- ... and 36 more

**crates/c02_type_system/docs/tier_02_guides/03_泛型编程指南.md** (referenced 41 times)

- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "泛型编程指南..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.en.md](crates/c02_type_system/docs/00_MASTER_INDEX.en.md): "Generics Guide..."
- [crates/c02_type_system/docs/00_MASTER_INDEX.md](crates/c02_type_system/docs/00_MASTER_INDEX.md): "泛型编程指南..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "Tier 2 - 泛型编程指南..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "泛型编程指南..."
- ... and 36 more

**docs/research_notes/type_theory/README.md** (referenced 41 times)

- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "类型理论研究..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "类型理论研究..."
- [crates/c02_type_system/README.md](crates/c02_type_system/README.md): "类型理论研究..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "类型理论研究..."
- [crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md](crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md): "类型理论研究..."
- ... and 36 more

**docs/04_thinking/MIND_MAP_COLLECTION.md** (referenced 41 times)

- [crates/c04_generic/README.md](crates/c04_generic/README.md): "`docs/04_thinking/MIND_MAP_COLLECTION.md`..."
- [crates/c04_generic/docs/tier_01_foundations/01_项目概览.md](crates/c04_generic/docs/tier_01_foundations/01_项目概览.md): "`docs/04_thinking/MIND_MAP_COLLECTION`..."
- [crates/c04_generic/docs/tier_01_foundations/01_项目概览.md](crates/c04_generic/docs/tier_01_foundations/01_项目概览.md): "`docs/04_thinking/MIND_MAP_COLLECTION`..."
- [crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md](crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md): "`docs/04_thinking/MIND_MAP_COLLECTION`..."
- [crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md](crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md): "`MIND_MAP_COLLECTION`..."
- ... and 36 more

**docs/rust-formal-engineering-system/00_master_index.md** (referenced 41 times)

- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "00_master_index..."
- [docs/DOCS_STRUCTURE_OVERVIEW.md](docs/DOCS_STRUCTURE_OVERVIEW.md): "链接..."
- [docs/README.md](docs/README.md): "形式化工程系统..."
- [docs/README.md](docs/README.md): "./rust-formal-engineering-system/00_master_index.m..."
- [docs/archive/temp/FORMAL_AND_PRACTICAL_NAVIGATION.md](docs/archive/temp/FORMAL_AND_PRACTICAL_NAVIGATION.md): "主索引..."
- ... and 36 more

**crates/c01_ownership_borrow_scope/docs/tier_03_references/08_内存安全参考.md** (referenced 38 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "3.3 内存安全最佳实践..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "内存安全理论..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "内存安全保证..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "错误处理..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "内存安全理论..."
- ... and 33 more

**crates/c03_control_fn/docs/tier_01_foundations/02_主索引导航.md** (referenced 37 times)

- [README.md](README.md): "📖 主索引..."
- [crates/c03_control_fn/README.md](crates/c03_control_fn/README.md): "主索引导航..."
- [crates/c03_control_fn/docs/00_MASTER_INDEX.md](crates/c03_control_fn/docs/00_MASTER_INDEX.md): "主索引导航..."
- [crates/c03_control_fn/docs/DOCUMENTATION_INDEX.md](crates/c03_control_fn/docs/DOCUMENTATION_INDEX.md): "主索引导航..."
- [crates/c03_control_fn/docs/tier_01_foundations/01_项目概览.md](crates/c03_control_fn/docs/tier_01_foundations/01_项目概览.md): "主索引导航..."
- ... and 32 more

**crates/c01_ownership_borrow_scope/docs/tier_03_references/09_性能优化参考.md** (referenced 37 times)

- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "3.4 性能优化..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "性能优化..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "性能优化..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "性能调优..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "性能优化..."
- ... and 32 more

**crates/c01_ownership_borrow_scope/docs/tier_02_guides/02_借用实践指南.md** (referenced 37 times)

- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用系统详解..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用系统..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用系统..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用系统..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "借用系统..."
- ... and 32 more

**crates/c04_generic/docs/tier_02_guides/01_泛型基础指南.md** (referenced 37 times)

- [crates/c04_generic/docs/00_MASTER_INDEX.en.md](crates/c04_generic/docs/00_MASTER_INDEX.en.md): "Generics Basics Guide..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "泛型基础指南..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "泛型基础指南..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "泛型基础指南..."
- [crates/c04_generic/docs/00_MASTER_INDEX.md](crates/c04_generic/docs/00_MASTER_INDEX.md): "泛型基础指南..."
- ... and 32 more

**docs/research_notes/type_theory/00_completeness_gaps.md** (referenced 37 times)

- [docs/02_reference/quick_reference/generics_cheatsheet.md](docs/02_reference/quick_reference/generics_cheatsheet.md): "类型系统完备性缺口..."
- [docs/02_reference/quick_reference/modules_cheatsheet.md](docs/02_reference/quick_reference/modules_cheatsheet.md): "类型系统完备性缺口..."
- [docs/02_reference/quick_reference/type_system.md](docs/02_reference/quick_reference/type_system.md): "类型理论完备性缺口..."
- [docs/archive/process_reports/2026_02/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md](docs/archive/process_reports/2026_02/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md): "type_theory/00_completeness_gaps.md..."
- [docs/research_notes/ARGUMENTATION_GAP_INDEX.md](docs/research_notes/ARGUMENTATION_GAP_INDEX.md): "type_theory/00_completeness_gaps..."
- ... and 32 more

**crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md** (referenced 36 times)

- [README.en.md](README.en.md): "📖 Master Index..."
- [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md): "主索引..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md): "00_MASTER_INDEX.md..."
- [crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md](crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md): "Rust 版本特性索引..."
- [crates/c01_ownership_borrow_scope/docs/FAQ.md](crates/c01_ownership_borrow_scope/docs/FAQ.md): "主索引..."
- ... and 31 more

---

*This index was auto-generated. Last updated: 2026-03-07T12:52:15.411743*
