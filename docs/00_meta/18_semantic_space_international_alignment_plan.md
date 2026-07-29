# Rust 语义空间国际权威来源对齐计划

**EN**: International Authoritative Source Alignment Plan for Rust Semantic Space  
**Summary**: 本计划系统推进 `e:/_src/rust-lang` 知识库在语义空间、计算语义、系统/软件/企业架构、AI 语义工程等领域与国际权威来源的全面对齐，确保概念权威页唯一、可验证、可持续演进。

> **Rust 版本**: 1.97.1+ (Edition 2024)  
> **计划波次**: Wave 0 – Wave 5  
> **决策前提**: 仅对齐英文权威来源；非英文社区暂不覆盖；不引入阻碍未来扩展的刚性结构；用户自行提交，本计划负责持续执行与质量门回归。

---

## 一、背景与目标

用户指出本项目需要补齐对 Rust **表征空间 / 语义空间** 的系统分析，并与网络上关于 Rust 1.97.1、计算语义模型、形式语言、数学函数等价、并行/并发/异步/分布式、系统架构、企业架构、软件工程、AI 本体论与语义工程等方面的最新最全面国际权威内容进行对齐。

本计划遵循 AGENTS.md 的 Canonical 规则：通用 Rust 概念解释统一维护在 `concept/`；`docs/` 与 `reports/` 只保留计划、分析与状态报告；禁止在多处维护相同正文。

## 二、理论框架与权威来源

| 维度 | 权威来源 | 对齐章节/文件 |
|---|---|---|
| 表达力理论 | Felleisen (1991) *On the Expressive Power of Programming Languages* | `concept/00_meta/15_semantic_space.md` §3 |
| 类型系统图灵完备 | Leffler (2017) *Rust's Type System is Turing-Complete* | `concept/00_meta/15_semantic_space.md` §2 |
| 所有权形式化 | Jung et al. (2018) *RustBelt: Securing the Foundations of the Rust Programming Language* (POPL) | `concept/04_formal/02_separation_logic/01_rustbelt.md` |
| 内存模型 | Jung et al. (2020) *Stacked Borrows*；Villani et al. (2025) *Tree Borrows* | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` |
| 观察等价 | Wadler (1989) *Theorems for Free!*；Plotkin 操作语义 | `concept/04_formal/03_operational_semantics/06_observational_equivalence.md` |
| 并发表达力 | Herlihy & Shavit (2011) *The Art of Multiprocessor Programming* | `concept/04_formal/12_concurrency_models/` |
| 计算语义 | Winskel (1993) *The Formal Semantics of Programming Languages*；Pierce *Types and Programming Languages* | `concept/04_formal/11_computational_models/` |
| 架构形式化 | ISO/IEC/IEEE 42010；Bass, Clements & Kazman (2021) *Software Architecture in Practice* | `concept/04_formal/10_architecture_semantics/` |
| 系统工程 | INCOSE 系统工程手册；ISO/IEC/IEEE 15288 | `concept/04_formal/09_system_semantics/` |
| 语义工程 / 本体 | OWL 2 Primer；W3C SHACL； RDF 1.1 Concepts | `concept/04_formal/13_semantic_engineering/` |
| AI 模型服务 | MLCommons；Hugging Face Inference API；NVIDIA Triton；Seldon Core | `concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md` |
| Rust 1.97.1 | [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)；[Rust 1.97.0 Blog](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/) | `concept/07_future/00_version_tracking/rust_1_97_1.md` |

## 三、当前状态速览

- `archive/01_governance/02_project_plans/PLAN_Semantic_Space_Wave.md` 提出创建 `00_meta/semantic_space.md` 并增强 5 个现有文件，但该计划已归档。
- 当前项目已演化出完整的 `concept/04_formal/` 体系：计算模型、形式语言、数学函数、并发模型、系统语义、架构语义、算法语义、语义工程等。
- 顶层元权威页已存在：`concept/00_meta/00_framework/semantic_space.md`（1371 行），覆盖归档计划中的表征空间定义、语义封闭性、三维边界、等价表达谱系、机制组合代数、跨语言对比等全部要求。本计划不再新建同名文件，而是对齐并增强该页。
- Rust 1.97.1 特性已通过 `check_version_semantic_injection.py` 100% 映射，但补丁版本的**语义论证深度**（LLVM 误编译对 unsafe/优化语义的影响）仍不足。
- 企业架构与 AI 模型服务权威页刚创建，需要与国际来源对齐、补充反例与决策树。

详见配套报告：`reports/SEMANTIC_SPACE_INTL_GAP_2026_07_29.md`。

## 四、执行波次

### Wave 0：基线与对称差（本轮启动）

- [ ] W0-1 盘点 `concept/04_formal/`、`concept/00_meta/`、`concept/06_ecosystem/14_enterprise_architecture/`、`concept/07_future/04_research_and_experimental/` 中语义空间相关页的覆盖度、Bloom 层级、权威来源行、代码块、反例节、mindmap。
- [ ] W0-2 抓取/整理 Rust 1.97.1、Felleisen、Leffler、RustBelt、Tree Borrows、ISO/IEC/IEEE 42010、OWL 2/SHACL 等权威来源的关键论断。
- [ ] W0-3 生成对称差矩阵：归档计划 vs 当前实现 vs 国际来源。
- [ ] W0-4 输出 `reports/SEMANTIC_SPACE_INTL_GAP_2026_07_29.md` 更新版。

**验证**: `python scripts/kb_auditor.py` 死链 0；`python scripts/check_canonical_uniqueness.py --strict` 通过。

### Wave 1：对齐并增强现有 `concept/00_meta/00_framework/semantic_space.md`

- [ ] W1-1 审查现有 1371 行内容，确认与归档计划 `PLAN_Semantic_Space_Wave.md` 的覆盖映射。
- [ ] W1-2 将 Felleisen、Leffler、Wadler、RustBelt、Tree Borrows 等引用从“首页/Wikipedia”级提升到具体论文/标准/预印本链接。
- [ ] W1-3 为“能/不能/痛苦能”边界表补充 Rust 1.97.1 相关案例（如 `must_use` 对 `Result<T, !>`、`dead_code_pub_in_binary`、v0 mangling 对 FFI 链接语义的影响）。
- [ ] W1-4 增加可编译反例：非法组合（E0502、E0382、E0597）与等价表达对比块。
- [ ] W1-5 刷新与 `concept/04_formal/` 子页、`concept/06_ecosystem/14_enterprise_architecture/`、`concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md` 的双向链接。
- [ ] W1-6 检查该页所有 `rust` 代码块，确保 `--strict` 下无 rotted。

**验证**: `python scripts/check_concept_code_blocks.py --strict`；`python scripts/check_mindmap_coverage.py --strict`。

### Wave 2：形式化子领域国际来源对齐

- [ ] W2-1 `concept/04_formal/11_computational_models/`：补充 Church-Turing 论题、lambda 演算、图灵机、符号执行与 Rust const 求值的等价性说明。
- [ ] W2-2 `concept/04_formal/12_concurrency_models/`：补充 process calculus、actor、session types、algebraic effects 与 async/await 的表达能力对比。
- [ ] W2-3 `concept/04_formal/10_architecture_semantics/`：引入 ISO/IEC/IEEE 42010 视图与视点、架构决策记录 (ADR)、架构权衡分析方法 (ATAM)。
- [ ] W2-4 `concept/04_formal/09_system_semantics/`：引入反应式系统（Reactive Manifesto）、分布式一致性模型、系统生命周期标准。
- [ ] W2-5 `concept/04_formal/08_algorithm_semantics/`：补充 Hoare 逻辑、细化演算、迭代器正确性、unsafe 算法不变量的可验证示例。
- [ ] W2-6 `concept/04_formal/13_semantic_engineering/`：对齐 OWL 2 DL/QL/RL、SHACL shapes、RDF*、知识图谱嵌入、LLM 本体工程实践。

**验证**: `python scripts/check_concept_authority_coverage.py --strict --include-crates`；`python scripts/check_kg_relation_precision.py --strict`。

### Wave 3：企业架构 / 软件工程模式深化

- [ ] W3-1 扩展 `concept/06_ecosystem/14_enterprise_architecture/04_domain_driven_design_in_rust.md`：战略模式（限界上下文、上下文映射、防腐层、共享内核）与战术模式（实体、值对象、聚合、领域事件、仓储、领域服务）。
- [ ] W3-2 创建/对齐架构模式页：Clean Architecture、Hexagonal / Ports & Adapters、Onion、Layered、Microkernel、Event-Driven、CQRS/ES（已存在则链接，避免重复）。
- [ ] W3-3 创建/对齐软件工程实践页：SOLID、GRASP、测试金字塔、持续交付、DevEx、平台工程。
- [ ] W3-4 所有模式页给出 Rust 实现样例、决策树、反例。

**验证**: `python scripts/detect_content_overlap_v2.py --budget 999999` + `python scripts/triage_overlap.py` 可处理项 0。

### Wave 4：Rust 1.97.1 语义深度论证

- [ ] W4-1 在 `concept/07_future/00_version_tracking/rust_1_97_1.md` 中补充 LLVM 误编译修复的语义影响分析：触发条件、对 unsafe/内联汇编/优化边界的影响、如何验证代码是否受影响。
- [ ] W4-2 对 1.97.0 的每项语言特性补充“语义等价 / 观察行为变化 / 迁移注意”小节。
- [ ] W4-3 检查并修复 `concept/` 中所有 1.97 相关代码块是否 rotted。

**验证**: `python scripts/check_version_semantic_injection.py --strict` 维持 100%；`python scripts/check_concept_code_blocks.py --strict`。

### Wave 5：KG / Quiz / 交叉链接与全质量门回归

- [ ] W5-1 为 Wave 1–4 新增/修改页生成或更新 KG 实体与语义谓词（`dependsOn`/`entails`/`refines`/`counterExample`）。
- [ ] W5-2 在 `concept/00_meta/knowledge_topology/quiz_registry.yaml` 注册新 quiz（若新增概念页）。
- [ ] W5-3 更新 `concept/SUMMARY.md`、相关 README、stub/重定向页。
- [ ] W5-4 运行 `bash scripts/run_quality_gates.sh`，确保 23 阻断 + 5 观察门全绿。

**验证**: `bash scripts/run_quality_gates.sh` 输出 `All 23 quality gates passed`。

## 五、目录与文件规划

```text
docs/00_meta/
  18_semantic_space_international_alignment_plan.md   # 本计划
  analysis/semantic_space_alignment/
    00_inventory.md                                   # 现有覆盖盘点
    01_formal_sources_baseline.md                     # 国际来源基线
    02_gap_matrix.md                                  # 对称差矩阵
    03_wave1_outline.md                               # semantic_space.md 大纲
    04_wave2_subdomain_notes.md                       # 子领域对齐笔记
    05_wave3_architecture_patterns.md                 # 架构模式对齐笔记
    06_wave4_1971_semantics.md                        # 1.97.1 语义笔记

concept/00_meta/
  15_semantic_space.md                                # Wave 1 权威页（新建）

reports/
  SEMANTIC_SPACE_INTL_GAP_2026_07_29.md               # 对称差与批判性分析
  SEMANTIC_SPACE_WAVE_X_COMPLETION_YYYY_MM_DD.md      # 每波完成后报告
```

## 六、时间线（建议）

| 波次 | 预计耗时 | 依赖 |
|---|---|---|
| Wave 0 | 1 轮会话 | 无 |
| Wave 1 | 1–2 轮会话 | Wave 0 |
| Wave 2 | 2–3 轮会话 | Wave 1 |
| Wave 3 | 1–2 轮会话 | Wave 1 |
| Wave 4 | 0.5–1 轮会话 | Wave 1 |
| Wave 5 | 0.5 轮会话 | Wave 2–4 |

## 七、成功标准

1. 全部 23 个阻断质量门 + 5 个语义观察门通过。
2. `concept/00_meta/15_semantic_space.md` 创建且不与现有权威页重复。
3. 对称差报告中识别的高优先级缺口（P0/P1）清零或明确列入下轮计划。
4. KG 核心实体 generic relation 比例保持 0%。
5. 新增/修改概念页均包含 EN 标题、Summary、Bloom 层级、权威来源、反例节、mindmap。

## 八、风险与缓解

| 风险 | 缓解 |
|---|---|
| 国际来源抓取受限 | 优先使用官方文档、已知的 arXiv/ACM DOI、作者博客等可公开访问链接；无法获取全文时引用摘要/关键结论。 |
| 内容重复触发 overlap-v2 阻断门 | 新增内容先查重；跨目录使用重定向 stub；所有正文只在 `concept/` 维护。 |
| 子领域过多导致单轮无法完成 | 分波次并行推进；每波次结束即回归质量门，保持主干始终可发布。 |
| AI/本体论来源快速变化 | 以 W3C/ISO 标准为锚点，社区工具仅作为示例；版本页单独维护。 |

## 九、下一步动作（待确认后立即执行）

1. 确认本计划总体方向与波次优先级（是否按 Wave 0→1→2/3 并行→4→5 推进）。
2. 确认是否立即创建 `docs/00_meta/analysis/semantic_space_alignment/` 工作目录与 `concept/00_meta/15_semantic_space.md` 大纲。
3. 确认 Wave 2 与 Wave 3 是否可并行启动（二者依赖 Wave 1 的框架，但可共享大纲后并行填充）。

---

> **关联文件**
> - `archive/01_governance/02_project_plans/PLAN_Semantic_Space_Wave.md`
> - `reports/SEMANTIC_SPACE_INTL_GAP_2026_07_29.md`
> - `AGENTS.md` §2 Canonical 规则、§5 质量门、§6 红线
