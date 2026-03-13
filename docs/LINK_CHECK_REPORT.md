# Markdown 内部链接检查报告

**扫描时间:** 2026-03-13 16:40:51

## 统计信息

- **总检查文件数:** 1295
- **总检查链接数:** 7932
- **有效链接数:** 7927
- **断链数量:** 5

## 断链详情（按文件分组）

### `07_project/README.md`

- **链接文本:** `{}`
  - **链接目标:** `./{}.md`
  - **解析路径:** `E:\_src\rust-lang\docs\07_project\{}.md`
  - **修复建议:**
    - 文件不存在，请检查路径是否正确或创建该文件

### `Rust所有权与可判定性/rust_vs_go_comprehensive_analysis.md`

- **链接文本:** `T Drawable`
  - **链接目标:** `item T`
  - **解析路径:** `E:\_src\rust-lang\docs\Rust所有权与可判定性\item T`
  - **修复建议:**
    - 文件不存在，请检查路径是否正确或创建该文件

### `archive/process_reports/2026_02/project/ONE_PAGE_SUMMARY_TEMPLATE.md`

- **链接文本:** `{}`
  - **链接目标:** `{}`
  - **解析路径:** `E:\_src\rust-lang\docs\archive\process_reports\2026_02\project\{}`
  - **修复建议:**
    - 文件不存在，请检查路径是否正确或创建该文件

### `rust-ownership-decidability/CROSS_REFERENCE_VERIFICATION_REPORT.md`

- **链接文本:** `formal-foundations/models/`
  - **链接目标:** `formal-foun... |
| MASTER_INDEX_AUTO.md | `formal-foundations/semantics/` | 54 | \| Semantics \| [formal-foundations/semantics/](formal-found... |
| MASTER_INDEX_AUTO.md | `formal-foundations/proofs/` | 55 | \| Proofs \| [formal-foundations/proofs/](formal-foundations... |
| MASTER_INDEX_AUTO.md | `coq-formalization/` | 56 | \| Coq Formalization \| [coq-formalization/](coq-formalizati... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/ownership-types.md` | 73 | - **Theory**: [ownership-types.md](formal-foundations/models... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/borrow-semantics.md` | 79 | - **Theory**: [borrow-semantics.md](formal-foundations/model... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/lifetime-logic.md` | 85 | - **Theory**: [lifetime-logic.md](formal-foundations/models/... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 56 | \| [CROSS_REFERENCE_VERIFICATION_REPORT.md](CROSS_REFERENCE_... |
| README.md | `formal-foundations/README.md` | 65 | \| 形式化理论 \| [形式化基础](formal-foundations/README.md`
  - **解析路径:** `E:\_src\rust-lang\docs\rust-ownership-decidability\formal-foun... |
| MASTER_INDEX_AUTO.md | `formal-foundations\semantics\` | 54 | \| Semantics \| [formal-foundations\semantics\](formal-found... |
| MASTER_INDEX_AUTO.md | `formal-foundations\proofs\` | 55 | \| Proofs \| [formal-foundations\proofs\](formal-foundations... |
| MASTER_INDEX_AUTO.md | `coq-formalization\` | 56 | \| Coq Formalization \| [coq-formalization\](coq-formalizati... |
| MASTER_INDEX_AUTO.md | `formal-foundations\models\ownership-types.md` | 73 | - **Theory**: [ownership-types.md](formal-foundations\models... |
| MASTER_INDEX_AUTO.md | `formal-foundations\models\borrow-semantics.md` | 79 | - **Theory**: [borrow-semantics.md](formal-foundations\model... |
| MASTER_INDEX_AUTO.md | `formal-foundations\models\lifetime-logic.md` | 85 | - **Theory**: [lifetime-logic.md](formal-foundations\models\... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 56 | \| [CROSS_REFERENCE_VERIFICATION_REPORT.md](CROSS_REFERENCE_... |
| README.md | `formal-foundations\README.md` | 65 | \| 形式化理论 \| [形式化基础](formal-foundations\README.md`
  - **修复建议:**
    - 相似文件:
    -   - `README.md`
    -   - `01_learning/README.md`
    -   - `02_reference/README.md`

- **链接文本:** `Coq代码`
  - **链接目标:** `... |
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
2. **Create topic hubs** for major themes (ownership, borrowing, lifetimes`
  - **解析路径:** `E:\_src\rust-lang\docs\rust-ownership-decidability\... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 243 | - [x] 完整的交叉引用 ([验证报告](CROSS_REFERENCE_VERIFICATION_REPORT.md... |

`
  - **修复建议:**
    - 文件不存在，请检查路径是否正确或创建该文件

## 修复建议汇总

### 常见修复方案

1. **添加 .md 扩展名**
   - 如果链接指向一个 Markdown 文件但没有扩展名，添加 `.md`

2. **修正相对路径**
   - `./file.md` - 同一目录下的文件
   - `../file.md` - 上级目录的文件
   - `subdir/file.md` - 子目录的文件

3. **使用绝对路径**
   - `/path/to/file.md` - 相对于 docs 目录的绝对路径

4. **创建缺失的文件**
   - 如果文件确实不存在，需要创建它或更新链接指向正确的文件
