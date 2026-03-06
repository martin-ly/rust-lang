# Cross-Reference Verification Report

**Generated**: 2026-03-06T11:41:17.918883

## Executive Summary

This report documents the cross-reference verification for the rust-ownership-decidability documentation.

| Metric | Count |
|--------|-------|
| Total Markdown Files | 385 |
| Total Coq Files | 32 |
| Total Files | 431 |
| Total Links Checked | 616 |
| Broken Links Found | 10 |
| Missing Cross-References | 381 |

## Broken Links

### List of Broken Links

| Source File | Broken Link | Line | Context |
|-------------|-------------|------|---------|
| MASTER_INDEX_AUTO.md | `formal-foundations/models/` | 53 | \| Formal Models \| [formal-foundations/models/](formal-foun... |
| MASTER_INDEX_AUTO.md | `formal-foundations/semantics/` | 54 | \| Semantics \| [formal-foundations/semantics/](formal-found... |
| MASTER_INDEX_AUTO.md | `formal-foundations/proofs/` | 55 | \| Proofs \| [formal-foundations/proofs/](formal-foundations... |
| MASTER_INDEX_AUTO.md | `coq-formalization/` | 56 | \| Coq Formalization \| [coq-formalization/](coq-formalizati... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/ownership-types.md` | 73 | - **Theory**: [ownership-types.md](formal-foundations/models... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/borrow-semantics.md` | 79 | - **Theory**: [borrow-semantics.md](formal-foundations/model... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/lifetime-logic.md` | 85 | - **Theory**: [lifetime-logic.md](formal-foundations/models/... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 56 | \| [CROSS_REFERENCE_VERIFICATION_REPORT.md](CROSS_REFERENCE_... |
| README.md | `formal-foundations/README.md` | 65 | \| 形式化理论 \| [形式化基础](formal-foundations/README.md) / [Coq代码](... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 243 | - [x] 完整的交叉引用 ([验证报告](CROSS_REFERENCE_VERIFICATION_REPORT.md... |

## Missing Cross-References

Files that mention key concepts but don't link to them:

| Source File | Concept | Suggested Link |
|-------------|---------|----------------|
| 00-foundations/00-03-separation-logic.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 00-foundations/00-04-theory-connections.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 00-foundations/README.md | formal | formal-foundations/README.md |
| 01-core-concepts/01-01-ownership-rules.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 01-core-concepts/01-02-borrowing-system.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 01-core-concepts/01-02-borrowing-system.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 01-core-concepts/01-03-lifetimes.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 01-core-concepts/01-04-runtime-vs-compile-time.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 01-core-concepts/README.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 01-core-concepts/README.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 01-core-concepts/README.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 01-core-concepts/detailed-concepts/borrowing-in-depth.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 01-core-concepts/ownership-counterexamples.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 01-core-concepts/ownership-counterexamples.md | examples | COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md |
| 01-core-concepts/short-concepts/borrowing-concept-card.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 03-verification-tools/03-01-verification-overview.md | formal | formal-foundations/README.md |
| 03-verification-tools/03-01-verification-overview.md | coq | coq-formalization/README.md |
| 03-verification-tools/03-02-creusot-deep-dive.md | formal | formal-foundations/README.md |
| 04-decidability-analysis/04-01-type-inference.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 04-decidability-analysis/04-01-type-inference.md | formal | formal-foundations/README.md |
| 04-decidability-analysis/04-02-borrow-checking.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 04-decidability-analysis/04-02-borrow-checking.md | formal | formal-foundations/README.md |
| 06-visualizations/06-01-concept-matrix.md | coq | coq-formalization/README.md |
| 06-visualizations/06-03-architecture-diagrams.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 06-visualizations/06-03-architecture-diagrams.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 06-visualizations/06-03-architecture-diagrams.md | coq | coq-formalization/README.md |
| 07-references/README.md | formal | formal-foundations/README.md |
| 07-references/academic-papers.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 07-references/academic-papers.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 07-references/academic-papers.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 07-references/academic-papers.md | formal | formal-foundations/README.md |
| 07-references/bibliography.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 07-references/bibliography.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 07-references/bibliography.md | formal | formal-foundations/README.md |
| 07-references/books-resources.md | formal | formal-foundations/README.md |
| 07-references/books-resources.md | coq | coq-formalization/README.md |
| 07-references/online-courses.md | formal | formal-foundations/README.md |
| 07-references/online-courses.md | coq | coq-formalization/README.md |
| 07-references/tools-libraries.md | coq | coq-formalization/README.md |
| 08-advanced-topics/08-04-proc-macros.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 08-advanced-topics/RUST_1.94_UPDATE_REPORT.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 10-research-frontiers/10-01-future-directions.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 10-research-frontiers/10-01-future-directions.md | borrowing | 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md |
| 10-research-frontiers/10-01-future-directions.md | formal | formal-foundations/README.md |
| 10-research-frontiers/10-01-future-directions.md | coq | coq-formalization/README.md |
| 10-research-frontiers/10-02-type-system-extensions.md | coq | coq-formalization/README.md |
| 10-research-frontiers/10-03-verification-advancements.md | coq | coq-formalization/README.md |
| 10-research-frontiers/10-04-ownership-variations.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |
| 10-research-frontiers/10-04-ownership-variations.md | lifetimes | 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md |
| 10-research-frontiers/10-05-ai-integration.md | ownership | 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md |

## Recommendations

### For Improving Navigation

1. **Add 'See Also' sections** to key documents linking related concepts
2. **Create topic hubs** for major themes (ownership, borrowing, lifetimes)
3. **Add breadcrumbs** at the top of each file showing its place in the hierarchy
4. **Link case studies to theory** - each case study should link to relevant formal foundations
5. **Link examples to proofs** - practical examples should reference Coq proofs

### For Maintaining Cross-References

1. Run this verification script regularly
2. Add link checking to CI/CD pipeline
3. Use relative paths for internal links
4. Avoid hardcoding file paths in multiple places

## Appendix: File Statistics

### Markdown Files by Directory

- **case-studies**: 135 files
- **root**: 44 files
- **comprehensive-analysis**: 21 files
- **formal-foundations**: 20 files
- **01-core-concepts**: 15 files
- **actor-specialty**: 15 files
- **archive**: 15 files
- **progress**: 12 files
- **visualizations**: 10 files
- **async-specialty**: 9 files
- **12-concurrency-patterns**: 8 files
- **10-research-frontiers**: 7 files
- **audit_reports**: 7 files
- **comparative-analysis**: 7 files
- **07-references**: 6 files
- **08-advanced-topics**: 6 files
- **extensions**: 6 files
- **00-foundations**: 5 files
- **15-application-domains**: 5 files
- **meta-model**: 5 files
- **06-visualizations**: 4 files
- **11-design-patterns**: 4 files
- **13-architecture-patterns**: 4 files
- **03-verification-tools**: 3 files
- **04-decidability-analysis**: 3 files
- **05-comparative-study**: 2 files
- **14-distributed-systems**: 2 files
- **coq-formalization**: 2 files
- **exercises**: 2 files
- **theorems**: 1 files

### Coq Files by Directory

- **coq-formalization/theories/Advanced**: 18 files
- **coq-formalization/theories/Metatheory**: 5 files
- **coq-formalization/examples**: 3 files
- **coq-formalization/theories/Syntax**: 2 files
- **coq-formalization/theories/Decidability**: 1 files
- **coq-formalization/theories/Semantics**: 1 files
- **coq-formalization/theories/Typing**: 1 files
- **coq-formalization/theories/Utils**: 1 files

---

*Report generated by check_cross_references.py*:
