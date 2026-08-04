# WS-F 形式语义与计算等价语义对齐表

**EN**: WS-F Formal Semantics Authority Alignment Report
**Summary**: Symmetric-difference analysis and remediation actions for Rust formal semantics topics in P7, covering computational equivalence, operational semantics foundations, and algorithm-level observational equivalence.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **工作流**: WS-F formal semantics
> **日期**: 2026-08-04
> **治理依据**: AGENTS.md §2 Canonical、§3 去重、§4 元数据与命名、§5 质量门

---

## 一、本次新增/增强文件

| 路径 | 类型 | 说明 |
|:---|:---:|:---|
| `concept/04_formal/11_computational_models/06_computational_equivalence_in_rust.md` | 新增权威页 | Rust 图灵完备性、类型系统图灵完备性、停机问题、safe vs unsafe 表达力差异、多维矩阵、决策树、思维导图 |
| `concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md` | 增强 | 新增 1.9 观察等价与上下文等价、1.10 结构化操作语义基础（含 Rust 小步解释器） |
| `concept/04_formal/08_algorithm_semantics/05_algorithm_equivalence.md` | 增强 | 新增 2.4 迭代 vs 递归观察等价、2.5 尾递归优化语义、2.6 并行前缀和语义、2.7 互换决策树 |
| `concept/SUMMARY.md` | 更新 | 在「计算模型与可计算性子层导览」下新增 `06_computational_equivalence_in_rust.md` 导航条目 |

> **命名调整说明**：原 P7 计划建议文件名为 `01_computational_equivalence_in_rust.md`，但 `concept/04_formal/11_computational_models/` 已存在 `01_computational_semantics_framework.md`。根据 AGENTS.md §4.0「同目录禁同号」，本次实际使用 `06_computational_equivalence_in_rust.md`，并在 SUMMARY 中保持连续序号。

---

## 二、语义对齐表

| 维度 | 本地状态（P7 前） | 国际化权威来源状态 | 对称差 | 修复动作 | 修复后状态 |
|:---|:---|:---|:---|:---|:---|
| **Rust 图灵完备性** | 在 `02_computability_theory.md` 有理论描述，但缺少「用安全 Rust 代码直接构造图灵完备解释器」的完整可编译示例 | Sipser 2013、Cutland 1980 使用通用图灵机/λ 演算定义；工程社区常用 Brainfuck/UTM 解释器演示 | 缺一个能证明安全 Rust 图灵完备的、可运行的代码级权威页 | 新建 `06_computational_equivalence_in_rust.md`，实现完整 Brainfuck 解释器（`run_bf` + `bracket_map`）并给出 `fn main()` 断言 | ✅ 新增权威页，代码可编译 |
| **类型系统图灵完备性** | `02_computability_theory.md` 提及 trait 求解边界；`04_mathematical_functions_of_computation.md` 有 Curry-Howard | Pierce 2002、TAPL 指出类型系统可在理论上图灵完备；Jones 1993 讨论类型化 λ 演算 | 缺 Peano 类型级编码 + 递归深度限制（E0275）的对照示例 | 新增类型级 `Add` / `NatVal` Peano 实现，并配 `compile_fail,E0275` 反例说明可判定片段截断 | ✅ 新增示例 |
| **停机问题不可判定性** | 已有 Rice 定理、E0080 示例 | Sipser、Hopcroft & Ullman 给出经典对角化证明 | 缺用 Rust 伪代码演示对角化论证的结构 | 新增 `halts` / `diagonal` 伪代码 + E0080 CTFE 截断示例 | ✅ 新增 |
| **safe vs unsafe 表达力差异** | `02_computability_theory.md` 2.5 节有观察等价不可判定；`unsafe` 权威页单独存在 | RustBelt、Rust Reference 区分 safe invariant 与 unsafe 能力 | 缺一张把「计算能力等价 / 可表达行为不同」映射到 Rust 代码的多维矩阵 | 新增安全/unsafe 多维矩阵 + `safe_tape_read` / `unsafe_tape_read` 对照示例 | ✅ 新增 |
| **Felleisen 表达力框架** | `05_equivalence_of_computational_models.md` 已有完整框架 | Felleisen 1991、Weiss et al. 2018 | 框架与 Rust 构造映射已完整，但缺决策树工具 | 在 `06_computational_equivalence_in_rust.md` 新增「判定构造是否提升表达力」决策树 | ✅ 新增 |
| **观察等价 / 上下文等价** | `04_mathematical_functions_of_computation.md` 1.9 已触及；`05_algorithm_equivalence.md` 是算法层应用 | Pitts 1997、Pierce 2002 给出形式定义 | `05_equivalence_of_computational_models.md` 作为模型等价权威页，缺少等价形式化基础 | 增强 `05_equivalence_of_computational_models.md`：新增观察等价/上下文等价定义 + `factorial_iter/rec` 示例 | ✅ 增强 |
| **结构化操作语义 SOS** | `03_operational_semantics/03_operational_semantics.md` 为专门权威页 | Plotkin 1981 SOS | 模型等价页缺少 SOS 与 Rust 解释器的桥梁 | 增强 `05_equivalence_of_computational_models.md`：新增命令式语言小步语义规则 + Rust AST 解释器（可运行 5!） | ✅ 增强 |
| **迭代 vs 递归观察等价** | `05_algorithm_equivalence.md` 已有二分查找迭代/递归实例 | Knuth TAOCP、算法教材 | 缺更通用示例（如求和）与显式等价声明 | 新增 `sum_iter` / `sum_rec` 示例 | ✅ 增强 |
| **尾递归优化语义** | 未专门讨论 Rust 不保证 TCO 对等价的限制 | Rust Reference / rustc 后端实现 | 缺 TCO 与观察等价关系的说明 | 新增 `sum_tail_rec` vs `sum_loop`，强调输出等价但栈消耗不等价 | ✅ 增强 |
| **并行前缀和语义** | 未覆盖并行 scan 的观察等价 | Blelloch 1990 prefix sums、rayon 文档 | 缺并行前缀和的 Rust 示例 | 新增 `prefix_sum_seq` / `prefix_sum_par`（基于 `std::thread::scope`） | ✅ 增强 |
| **算法实现互换决策** | 有反命题树与常见陷阱 | 软件工程/形式化方法 | 缺一个可直接用于代码审查的决策树 | 新增 mermaid flowchart「判定两个 Rust 算法实现是否可互换」 | ✅ 增强 |

---

## 三、内容去重检查

- 新增前运行 `python scripts/detect_content_overlap.py`，发现 2 对潜在重复（均与本次修改无关，见 `reports/CONTENT_OVERLAP_DETECTION_2026_08_04.md`）。
- 新建页 `06_computational_equivalence_in_rust.md` 与现有 `02_computability_theory.md`、`05_equivalence_of_computational_models.md`、`04_mathematical_functions_of_computation.md` 做了明确职责切分：
  - 重复主题（图灵完备、Rice、Felleisen）仅保留结论性摘要与链接；
  - 新增内容为 Rust-specific 可编译示例、多维矩阵、决策树、safe/unsafe 表达力边界。

---

## 四、质量门自检

| 检查项 | 命令 / 方法 | 结果 |
|:---|:---|:---|
| 内容去重 | `python scripts/detect_content_overlap.py` | 通过（仅 2 对历史潜在重复，与本次无关） |
| 代码块编译 | `python scripts/check_concept_code_blocks.py --sample 0 --strict` | 本次新增/修改文件无失败；仓库整体存在 19 个历史 candidate 失败 + 1 个 compile_fail 标注腐烂（与本次无关），见 `reports/CB_CHECK_WS_F_2026_08_04.md` |
| 命名规范 | `python scripts/check_naming_convention.py --strict` | ✅ 通过（ERROR=0） |
| 死链 / SUMMARY | `python scripts/kb_auditor.py` | ✅ 死链 0；发现 1 个无关跨层引用问题（`49_gof_patterns_in_rust.md` 缺少 L5 向下引用） |
| 元数据一致性 | `python scripts/check_metadata_consistency.py --strict` | ✅ 通过（本次文件未被 flag） |
| Workspace 构建 | `cargo check --workspace` | ✅ 通过 |
| Workspace 测试 | `cargo test --workspace --quiet` | ✅ 通过 |

---

## 五、发现的问题与后续行动

1. **文件名序号冲突**：P7 计划原建议 `01_computational_equivalence_in_rust.md`，但目录已存在 `01_computational_semantics_framework.md`。已按 AGENTS.md 调整为 `06_computational_equivalence_in_rust.md` 并在 SUMMARY 中同步。
2. **P7 计划中的其他 WS-F 文件**：`concept/04_formal/00_type_theory/11_formal_design_pattern_theory.md` 与 `concept/04_formal/10_architecture_semantics/02_architecture_pattern_semantics.md` 的增强未在本次用户指定的 WS-F 工作包内要求（用户仅要求了三个文件 + 对齐表）。如需推进，请单独指派。
3. **代码块验证**：已运行 `check_concept_code_blocks.py --sample 0 --strict`。本次新增/修改文件的所有代码块均编译通过；仓库整体 rot 来自其他工作流的历史遗留问题。

---

## 六、引用路径

- 新增权威页：`concept/04_formal/11_computational_models/06_computational_equivalence_in_rust.md`
- 增强模型等价页：`concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md`
- 增强算法等价页：`concept/04_formal/08_algorithm_semantics/05_algorithm_equivalence.md`
- 导航更新：`concept/SUMMARY.md`
- 去重检测报告：`reports/CONTENT_OVERLAP_DETECTION_2026_08_04.md`
