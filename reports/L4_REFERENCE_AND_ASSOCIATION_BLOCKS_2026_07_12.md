# L4 Reference 摘译页定位裁决 + 关联区块模板统一报告

> **EN**: L4 Reference-Excerpt Positioning Ruling & Association Block Template Unification
> **Summary**: P3-2/P3-3 execution report (2026-07-12): classification and positioning ruling for Rust Reference excerpt pages in `concept/04_formal/05_rustc_internals/`, plus concept/ association-block heading unification, core-30 upper/lower-concept enrichment, and the new `check_association_blocks.py` semantic-observation gate.
> **任务**: P3-2（任务 A）+ P3-3 部分（任务 B）
> **日期**: 2026-07-12
> **状态**: ✅ 完成（未执行 git commit；工作区改动由用户自行提交）

---

## 一、任务 A：L4 Reference 摘译页定位裁决（P3-2）

### 1.1 盘点与分类（`concept/04_formal/05_rustc_internals/` 全部 17 个内容页）

| 文件 | Bloom | A/S/P | 判定 | 处置 |
|:---|:---|:---|:---|:---|
| 19_rustc_query_system.md | L2-L4 | F | ① 编译器原理（查询系统/增量编译） | 保留 L4，无改动 |
| 20_mir_codegen_llvm_primer.md | L2-L4 | F | ① 编译器原理（MIR/codegen/LLVM） | 保留 L4，无改动 |
| 26_trait_solver_in_rustc.md | L2-L4 | F | ① 形式化（trait 求解/归纳） | 保留 L4，无改动 |
| 35_name_resolution_and_hir.md | L2-L4 | F | ① 编译器前端原理（名称解析/HIR） | 保留 L4，无改动 |
| 53_generics_compiler_behavior.md | L4-L5 | S | ① 编译器行为分析（单态化/分发/类型擦除） | 保留 L4，无改动 |
| 38_application_binary_interface.md | L2-L3 | S | ② Reference 摘译（ABI 属性规范） | 保留 + 定位声明 |
| 40_names_and_resolution.md | L2-L4 | S | ② Reference 摘译（Names 章） | 保留 + 定位声明 |
| 41_special_types_and_traits.md | L2-L4 | S | ② Reference 摘译（Special Types and Traits 章） | 保留 + 定位声明 |
| 42_type_layout.md | L2-L4 | S | ② Reference 摘译（Type Layout 章） | 保留 + 定位声明 |
| 43_destructors.md | L2-L4 | S | ② Reference 摘译（Destructors 章） | 保留 + 定位声明 |
| 45_lexical_structure.md | L2-L4 | S | ② Reference 摘译（Lexical Structure 章） | 保留 + 定位声明 |
| 46_items_reference.md | L2-L4 | S | ② Reference 摘译（Items 章） | 保留 + 定位声明 |
| 47_attributes.md | L2-L3 | S | ② Reference 摘译（Attributes 章） | 保留 + 定位声明 |
| 48_statements_and_expressions_reference.md | L2-L4 | S | ② Reference 摘译（Statements/Expressions 章） | 保留 + 定位声明 |
| 49_patterns_reference.md | L2-L4 | S | ② Reference 摘译（Patterns 章） | 保留 + 定位声明 |
| 51_names_reference.md | L2-L4 | S | ② Reference 摘译（Names/路径/可见性） | 保留 + 定位声明 |
| 52_reference_appendices.md | L2-L4 | S | ② Reference 摘译（Appendices 章） | 保留 + 定位声明 |

判定依据：② 类文件正文均为 Rust Reference 对应章节的条文摘译 + 示例 + 交叉引用（头部「来源」直接指向 doc.rust-lang.org/reference 对应章节），不含形式化推导/证明；① 类文件讲解编译器内部机制原理（查询系统、MIR、trait solver、HIR lowering、单态化）。

### 1.2 迁移成本评估与裁定

对 12 个 ② 类文件统计外部引用（`concept/`、`knowledge/`、`docs/`、`content/`、`crates/`、`exercises/`）与同目录互引：

| 文件 | 外部引用 | 同目录互引 |
|:---|:---:|:---:|
| 38_application_binary_interface | 13 | 1 |
| 40_names_and_resolution | 5 | 4 |
| 41_special_types_and_traits | 3 | 2 |
| 42_type_layout | 10 | 1 |
| 43_destructors | 5 | 2 |
| 45_lexical_structure | 6 | 1 |
| 46_items_reference | 4 | 4 |
| 47_attributes | 4 | 1 |
| 48_statements_and_expressions_reference | 5 | 2 |
| 49_patterns_reference | 5 | 3 |
| 51_names_reference | 4 | 1 |
| 52_reference_appendices | 4 | 0 |

**裁定：保留原位 + 定位声明（低成本正确方案），不迁移。** 理由：

1. **引用成本高**：12 页合计外部引用 68 处 + 同目录互引 23 处（前置/后置概念链），迁移到 `01_foundation/` 需改动约 90 处链接，且迁移后与 L1 同名主题页（如 `01_foundation/04_control_flow/40_patterns.md`）形成新的重复/竞态，违背 canonical 规则。
2. **规范依据**：`concept/00_meta/03_audit/asp_marking_guide.md` §2.2「层级递增原则：L4 形式化层以 S/P 为主」——S（Specification）规范分析类内容本就属于 L4 合法组成；§3.4 亦有 L4 层 S 标记先例。
3. **D1 规则不要求 Bloom 与目录层级一致**：`scripts/check_metadata_consistency.py` 的 D1 仅检查**文件内**「Bloom 层级」与「层次定位/层级」字段交集，与目录位置无关。② 类页面现有 L2-L3/L2-L4 标注与内容（理解/分析层规范摘译）相符，**无需改标**，维持原值。

### 1.3 已执行改动

- 12 个 ② 类文件头部（`权威来源` 行之后）插入统一「定位声明」：标明本页为 Rust Reference 对应章节的**规范摘译与注解**、非形式化推导，并按主题指向同层形式化内容（如 40/46/51 → 35_name_resolution_and_hir；48/43 → 17_operational_semantics；49 → 27_type_checking_and_inference；45/52 → 44_notation；38/47 → 20_mir_codegen_llvm_primer；41 → 26_trait_solver_in_rustc + 02_type_theory；42 → 21_type_semantics）。
- `concept/04_formal/README.md` 新增「### 4.1 `05_rustc_internals/` 子目录的混合定位（P3-2 裁决）」小节，记录①/②分类表与裁定理由。

---

## 二、任务 B：关联区块模板统一（P3-3 部分）

### 2.1 现有变体统计（改动前，concept/ 全量）

| 变体 | 出现次数（标题行） |
|:---|:---:|
| `相关概念文件`（含 `###` 与编号前缀形式） | 140 |
| `关联概念`（含编号前缀形式，如「七、关联概念」） | 37 |
| `相关概念`（已合规） | 14+ |
| `相关概念链接`（含编号前缀形式） | ~30 文件（本次未改，见 2.5） |
| 纯 `延伸阅读` / `📚 延伸阅读` | 4（均不与相关概念节相邻，按规则保留） |

**标准模板**：

```markdown
## 相关概念

- **上层概念**: ...（前置依赖/前置概念）
- **下层概念**: ...（后置概念/后置延伸）
- **对比概念**: ...（可选）
- **应用场景**: ...（可选）
```

### 2.2 批量统一（`scripts/unify_association_headings.py`，仅改标题行）

- 「相关概念文件」「关联概念」→「相关概念」，保留标题层级（##/###）与编号前缀（「七、」「10.」）：**177 处 / 177 文件**。
- 行内含额外内容的标题（如 `## 相关概念文件 [链接…]`，1 处）按规则不改。
- **TOC 锚点联动修复**：重命名使 125 个文件的目录锚点 `#相关概念文件`/`#关联概念`/`#六相关概念文件` 失效，已同步修正为 `#相关概念`（显示文本同步更新），修复后 `grep` 残留为 0。
- 纯「延伸阅读」4 处（template_deduplication_guide、39_type_level_programming、39_future_and_executor_mechanisms、39_high_performance_network_service_architecture）经核查均不与「相关概念」节相邻，按「若两节相邻则合并去重」规则**不合并，保留原样**。

### 2.3 核心 30 页上层/下层概念补全

对 L1-L3 旗舰 30 页（ownership/borrowing/lifetimes/lifetimes_advanced/move_semantics/type_system/reference_semantics/control_flow/patterns/statements_and_expressions/collections/modules_and_paths/error_handling_basics/attributes_and_macros/traits/generics/memory_management/smart_pointers/interior_mutability/error_handling/module_system/macro_patterns/iterator_patterns/advanced_traits/const_generics/concurrency/async/unsafe/macros/atomics_and_memory_ordering）：

- 从文件元数据 `前置概念/前置依赖` → `- **上层概念**:`，`后置概念/后置延伸` → `- **下层概念**:`，提取 markdown 链接补全。
- 26 页插入现有关联区块；4 页（03_lifetimes、23_move_semantics、32_const_generics、01_concurrency）无关联区块，新建 `## 相关概念` 节（插入尾部参考区块之前）。
- 结果：上层概念覆盖 30/30，下层概念覆盖 26/30（4 页元数据后置为空或仅为非链接占位 `[FFI]` 形式，如实跳过）。
- 入口概念（如 01_ownership，前置依赖为「无」）标注 `- **上层概念**: 无（入口概念，无前置依赖）`。

### 2.4 新检查脚本 `scripts/check_association_blocks.py`

- A1 命名合规（阻断）：弃用变体「相关概念文件」「关联概念」出现即不合规；
- A2 存在性（阻断）：内容页（排除 `00_meta/`、`README.md`、重定向 stub）须有关联区块或前置/后置元数据；
- A3（观察，不阻断）：「相关概念链接」待归并变体计数、上层/下层概念子项覆盖率。
- 默认 exit 0；`--strict` 时 A1/A2 不合规 exit 1。已登记 `scripts/README.md`。
- 当前结果：扫描 402 内容页（跳过 6 stub），A1=0、A2=0、合规标题 191 处，`--strict` 通过。

### 2.5 遗留观察（后续批次）

- 「相关概念链接」变体约 30 文件：任务 B2 明确映射仅含两个变体，故本次未动；已在 checker A3 中持续观察，建议下一批次裁决是否归并。
- 4 页核心页缺下层概念子项（元数据后置为空/非链接占位），待元数据补全后重跑 `--enrich-core`（脚本幂等）。

---

## 三、验证（B5）

| 检查 | 结果 |
|:---|:---|
| `python scripts/check_metadata_consistency.py` | 与改动前基线完全一致：scanned=483，flagged=30，D1=0/D2=1/D3=0/D4=0/D5=17/D6=13 — **无新增标记** |
| 新增链接死链定点检查（152 条：30 核心页上层/下层概念行 + 12 页定位声明行） | 0 死链 |
| 同文件锚点（`scripts/check_active_anchors.py`） | 19 处 broken 均为**改动前已存在**（quizzes/引理类，与本次无关）；本次重命名引入的 125 处 TOC 锚点已全部修复，残留 0 |
| `python scripts/check_template_cliches.py --strict` | ✅ 通过（exit 0，无命中） |
| `python scripts/check_association_blocks.py --strict` | ✅ 通过（exit 0） |

## 四、改动清单

- 内容：`concept/04_formal/05_rustc_internals/` 12 页定位声明；`concept/04_formal/README.md` 新增 §4.1；concept/ 177 文件标题统一；125 文件 TOC 锚点修复；30 核心页上层/下层概念补全。
- 脚本：`scripts/unify_association_headings.py`（标题统一 + `--enrich-core` 补全）、`scripts/check_association_blocks.py`（新检查门）；`scripts/README.md` 登记。
- 一次性脚本：`tmp/p3_2_add_reference_translation_declaration.py`（定位声明插入，幂等，tmp/ 不提交）。
- 未执行 git commit（注：会话期间用户于 05:53 自行提交了主体改动；剩余未提交改动为 125+ 文件的 TOC 锚点修复，均为单行替换）。
