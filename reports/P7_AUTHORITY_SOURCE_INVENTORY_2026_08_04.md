# P7 国际化权威来源清单与本地映射表

**EN**: P7 International Authority Source Inventory and Local Mapping
**Summary**: Systematic inventory of authoritative international Rust sources and their mapping to local `concept/` pages, identifying subject and semantic symmetric differences for P7 alignment sprint.

> **Rust 版本**: 1.97.0+ / 1.98 beta (Edition 2024)
> **日期**: 2026-08-04
> **治理**: AGENTS.md §2 Canonical / §3 去重 / §5 质量门

---

## 一、清单方法论

1. **主题对称差** = 权威来源目录主题 ⊖ 本地 `concept/SUMMARY.md` 主题。
2. **语义对称差** = 同一主题下，权威来源与本地页在定义、示例、版本、形式化深度上的差异。
3. **优先级**：P0（本地完全缺口）> P1（本地浅覆盖）> P2（本地覆盖但版本/形式化落后）。
4. **状态标记**：
   - ✅ 已对齐
   - ⚠️ P1/P2 差距
   - ❌ P0 缺口
   - 🔄 待 P7 更新

---

## 二、核心语言与参考文档

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| The Rust Programming Language (2024 ed.) | https://doc.rust-lang.org/book/ | `concept/01_foundation/`~`03_advanced/` | ⚠️ P1 | 本地覆盖极全；1.98 新特性（async closures, `str::strip_circumfix`, `NonZero*::from_str_radix` 等）需持续注入 |
| The Rust Reference | https://doc.rust-lang.org/reference/ | 分散于各权威页 | ✅ | 引用充分，edition 2024 规则基本覆盖 |
| The Rustonomicon | https://doc.rust-lang.org/nomicon/ | `concept/03_advanced/02_unsafe/` | ⚠️ P1 | 内存模型、validity、aliasing、Stacked Borrows/Tree Borrows 最新文档需更新 |
| Rust By Example | https://doc.rust-lang.org/rust-by-example/ | `concept/` 各示例 | ✅ | 示例风格一致 |
| Rust Style Guide | https://doc.rust-lang.org/style/ | `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` | ⚠️ P2 | 部分 style 规则未显式对齐 |
| Rust RFCs Book | https://rust-lang.github.io/rfcs/ | `concept/00_meta/` / `07_future/` | ✅ | RFC 引用较全 |

---

## 三、惯用法与设计模式

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| Rust API Guidelines | https://rust-lang.github.io/api-guidelines/ | `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md` | ⚠️ P1 | 本地已覆盖主要惯用法，但 API Guidelines 的 30 条核心建议未逐条显式映射；建议新增 `48_api_guidelines_idioms.md` |
| Rust Design Patterns (unofficial) | https://rust-unofficial.github.io/patterns/ | `concept/06_ecosystem/03_design_patterns/` | ⚠️ P1 | 本地 GoF/架构模式覆盖全，但 unofficial book 的 `ffi/ffi_idioms.md`、`patterns/behavioural/` 等细分页可进一步对齐 |
| design-patterns-rust (GoF) | https://github.com/fadeevab/design-patterns-rust | `concept/06_ecosystem/03_design_patterns/47_rust_design_and_architecture_patterns_semantic_atlas.md` | ⚠️ P1 | 23 GoF 模式已覆盖，但部分模式缺少「Rust 实现变体 + 反例 + 决策树」 |
| Refactoring Guru Rust | https://refactoring.guru/design-patterns/rust | 同上 | ⚠️ P2 | UML 与 Rust 实现对应可补强 |

**P7 动作**：
- WS-A：增强 `02_idioms_spectrum.md`，新增 API Guidelines 逐条映射。
- WS-C：将 23 GoF 模式逐一核对，补全变体与反例。

---

## 四、算法与数据结构

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| Rust Algorithm Club | https://github.com/weihanglo/rust-algorithm-club | `concept/06_ecosystem/16_algorithm_patterns/` | ⚠️ P1 | 本地算法模式覆盖广；可补「数据结构」专题页（链表/堆/并查集/线段树）与竞赛编程惯用法 |
| CLRS | — | 同上 | ⚠️ P2 | 复杂度证明可更形式化 |
| Sedgewick | — | 同上 | ⚠️ P2 | 图算法、字符串算法可补复杂度下界分析 |
| CP-Algorithms | https://cp-algorithms.com/ | 无直接映射 | ❌ P0 | 竞赛算法领域本地无独立权威页；建议新增 `18_competitive_programming_idioms.md` |

**P7 动作**：
- WS-B：新增 `02_data_structures_in_rust.md`、`18_competitive_programming_idioms.md`。

---

## 五、异步与并发

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| Asynchronous Programming in Rust | https://rust-lang.github.io/async-book/ | `concept/03_advanced/01_async/` | ⚠️ P1 | async fn 精确捕获、async 闭包（1.85/1.86 稳定）已覆盖；需持续跟踪 1.98+ async drop |
| Rust Atomics and Locks (Mara Bos) | https://marabos.nl/atomics/ | `concept/03_advanced/00_concurrency/06_atomics_and_memory_ordering.md` | ✅ | 引用充分 |
| Herlihy & Shavit, The Art of Multiprocessor Programming | — | `concept/03_advanced/00_concurrency/` | ⚠️ P2 | 并发算法正确性证明可补强 |

**P7 动作**：
- 跟踪 async drop / gen blocks 在 1.99/1.100 的进展。
- 补强并发算法的形式化不变量证明。

---

## 六、嵌入式 / no_std

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| The Embedded Rust Book | https://docs.rust-embedded.org/book/ | `concept/06_ecosystem/05_systems_and_embedded/` | ⚠️ P1 | 本地 P6 已新增 38/41/42/43/44/34/36；可补硬件验证实测 |
| Embassy Book | https://embassy.dev/book/ | `concept/06_ecosystem/05_systems_and_embedded/34_embassy_framework_deep_dive.md` | ⚠️ P1 | Embassy 内容已创建，但可补更多端到端示例 |
| Knurling Books (defmt/probe-rs) | https://knurling-books.org/ | `concept/06_ecosystem/05_systems_and_embedded/36_defmt_probe_rs_architecture.md` | ⚠️ P1 | 已覆盖，可补 QEMU/真实硬件验证 |
| RTIC Book | https://rtic-rs.github.io/book/ | 无直接映射 | ❌ P0 | RTIC 框架本地无独立权威页 |
| Tock OS Book | https://book.tockos.org/ | 无直接映射 | ❌ P0 | Tock 本地无独立权威页 |
| Hubris Docs | https://hubris.oxide.computer/ | 无直接映射 | ❌ P0 | Hubris 本地无独立权威页 |

**P7 动作**：
- WS-E：新增 `45_embedded_hardware_validation.md`、`46_rtos_and_scheduling_in_rust.md`。

---

## 七、Cargo / 工具链 / FFI

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| The Cargo Book | https://doc.rust-lang.org/cargo/ | `concept/06_ecosystem/01_cargo/` | ✅ | 覆盖全面 |
| Rust FFI Omnibus | https://jakegoulding.com/rust-ffi-omnibus/ | `concept/03_advanced/04_ffi/` | ⚠️ P1 | 可补更多 FFI 惯用示例 |
| Rustc Dev Guide | https://rustc-dev-guide.rust-lang.org/ | `concept/04_formal/05_rustc_internals/` | ⚠️ P2 | 编译器内部部分主题本地覆盖较浅 |

**P7 动作**：
- 跟踪 Cargo `resolver.lockfile-path`、`build.warnings` 等 1.97 特性语义注入。
- 补 FFI 反例（repr(transparent) 1.98 严格规则）。

---

## 八、形式语义与计算理论

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| RustBelt (Jung et al., POPL 2018) | https://plv.mpi-sws.org/rustbelt/popl18/ | `concept/04_formal/` | ✅ | 引用充分 |
| Aeneas (Ho & Protzenko) | https://aeneas-verif.org/ | `concept/04_formal/` | ⚠️ P2 | 可补 Aeneas 验证流程示例 |
| Patina / Oxide / MiniRust | 学术论文 | `concept/04_formal/` | ⚠️ P2 | 可补形式化语义对比 |
| Kani / Prusti / Gillian | 工具文档 | `concept/04_formal/` | ⚠️ P1 | 形式化验证工具链案例可扩展 |
| Pierce TAPL | — | `concept/04_formal/00_type_theory/` | ✅ | 引用充分 |
| Felleisen 1991 | https://www.cs.tufts.edu/comp/150FP/archive/matthias-felleisen/expressive-as-published.pdf | `concept/00_meta/00_framework/semantic_space.md` | ✅ | 已对齐 |

**P7 动作**：
- WS-F：增强 `semantic_space.md`、新增/增强计算等价页。
- 补全 Kani/Prusti/Gillian 案例库。

---

## 九、企业架构 / 云原生 / SRE

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| Azure Architecture Center | https://learn.microsoft.com/azure/architecture/ | `concept/06_ecosystem/14_enterprise_architecture/` | ⚠️ P1 | 已覆盖可观测性、微服务；可补事件驱动/CQRS/云原生 |
| AWS Well-Architected | https://docs.aws.amazon.com/wellarchitected/ | 同上 | ⚠️ P1 | 可补可靠性、安全、成本优化支柱 |
| DDD Reference | https://domainlanguage.com/ddd/reference/ | `concept/06_ecosystem/14_enterprise_architecture/04_domain_driven_design_in_rust.md` | ✅ | 已覆盖 |
| Google SRE Book | https://sre.google/sre-book/ | `concept/06_ecosystem/14_enterprise_architecture/09_observability_and_sre_patterns.md` | ⚠️ P1 | SLO/错误预算/事故响应可补强 |

**P7 动作**：
- WS-D：新增事件驱动/CQRS、云原生/Serverless 权威页。

---

## 十、AI / LLM / 语义工程 / 本体论

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| W3C OWL2 / SKOS / SHACL | https://www.w3.org/ | `tools/kg_shacl/` / `concept/00_meta/` | ⚠️ P1 | KG SHACL 已全绿；可补 LLM 语义检索对齐 |
| GraphRAG papers | arXiv | `tools/kg_rag/` | ⚠️ P1 | 可补 KG+LLM RAG 架构 |
| LLM+KG Surveys | arXiv | `concept/00_meta/00_framework/kg_ontology_v2.md` | ⚠️ P1 | 已部分扩展，可继续深化 |

**P7 动作**：
- WS-G：增强 `kg_ontology_v2.md`，补充 LLM 语义检索与本体对齐。

---

## 十一、版本发布说明

| 权威来源 | URL | 本地映射 | 状态 | 对称差说明 |
|---|---|---|---|---|
| Rust release notes | https://github.com/rust-lang/rust/releases | `concept/07_future/00_version_tracking/` | ✅ | 1.90–1.97 稳定特性 100% 映射 |
| releases.rs | https://releases.rs/ | `rust_1_98_preview.md` / `rust_1_99_preview.md` / `rust_1_100_preview.md` | 🔄 | 需每两周巡检更新 |
| rust-lang/blog | https://blog.rust-lang.org/ | 同上 | 🔄 | 需跟踪 stabilization reports |

**P7 动作**：
- WS-H：更新 1.99/1.100 跟踪页，注入最新 nightly 特性语义链接。

---

## 十二、对称差汇总

### 主题对称差（本地缺口）

1. RTIC 框架
2. Tock OS
3. Hubris
4. 竞赛编程算法惯用法
5. 事件驱动/CQRS/Serverless 架构模式
6. 嵌入式硬件验证流程

### 语义对称差（本地覆盖但需增强）

1. API Guidelines 逐条语义映射
2. GoF 23 模式 Rust 变体与反例
3. 内存模型/validity/Tree Borrows 最新文档
4. async drop / gen blocks / safety tags 进展
5. Kani/Prusti/Gillian 案例库
6. LLM+KG 语义检索架构
7. SLO/错误预算/混沌工程

---

## 十三、P7 任务优先级矩阵

| 任务 | 影响 | 工作量 | 风险 | P7 批次 |
|---|---|---|---|---|
| 增强惯用法 API Guidelines | 高 | 中 | 低 | 第 1 批 |
| 创建 semantic_space.md（已存在，增强） | 高 | 低 | 低 | 第 1 批 |
| 增强计算等价/形式语义 | 高 | 中 | 中 | 第 1 批 |
| 更新 1.99/1.100 版本跟踪 | 中 | 低 | 低 | 第 1 批 |
| 新增事件驱动/CQRS/Serverless | 中 | 高 | 中 | 第 2 批 |
| 新增 RTOS/嵌入式硬件验证 | 高 | 高 | 高（硬件依赖） | 第 2 批 |
| 新增竞赛编程惯用法 | 中 | 中 | 低 | 第 2 批 |
| 增强 AI/KG/LLM 语义工程 | 高 | 中 | 低 | 第 2 批 |
| 每轮 KG/SUMMARY/质量门刷新 | 高 | 中 | 低 | 每轮 |

---

## 十四、参考

- AGENTS.md §2 Canonical / §3 去重 / §5 质量门
- `reports/PLAN_P7_Semantic_International_Alignment_2026_08_04.md`
