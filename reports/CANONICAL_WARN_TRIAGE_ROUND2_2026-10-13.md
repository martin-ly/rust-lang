# CANONICAL WARN 第二轮只读梳理报告（2026-10-13, Round 2）

- 数据源：`python scripts/check_canonical_uniqueness.py --json` 实测输出（提交 208ac7548 之后）
- 规模：**121 条 WARN**（`same_dir_topic_duplicate` 117 + `dual_canonical` 4），分布于 **36 个目录簇**
- 本轮性质：**严格只读**——未修改任何 concept/ 文件、未改门脚本、无 git 操作；仅新建本报告
- 上一轮报告：`reports/CANONICAL_WARN_TRIAGE_2026-10-13.md`（§6.2 处置建议）

## 0. 簇分布总览

| 目录簇 | WARN 数 |
|---|---|
| concept/00_meta/00_framework | 2 |
| concept/00_meta/02_sources | 2 |
| concept/00_meta/04_navigation | 2 |
| concept/01_foundation/06_strings_and_text | 1 |
| concept/01_foundation/07_modules_and_items | 1 |
| concept/01_foundation/08_error_handling | 1 |
| concept/02_intermediate/00_traits | 3 |
| concept/02_intermediate/01_generics | 2 |
| concept/02_intermediate/03_error_handling | 1 |
| concept/03_advanced/00_concurrency | 2 |
| concept/03_advanced/01_async | 2 |
| concept/03_advanced/02_unsafe | 2 |
| concept/03_advanced/03_proc_macros | 1 |
| concept/03_advanced/05_inline_assembly | 1 |
| concept/03_advanced/08_process_ipc | 5 |
| concept/04_formal/00_type_theory | 4 |
| concept/04_formal/01_ownership_logic | 1 |
| concept/04_formal/03_operational_semantics | 1 |
| concept/04_formal/04_model_checking | 1 |
| concept/04_formal/05_rustc_internals | 4 |
| concept/04_formal/10_architecture_semantics | 4 |
| concept/04_formal/11_computational_models | 1 |
| concept/04_formal/13_semantic_engineering | 1 |
| concept/04_formal/15_language_specification | 1 |
| concept/06_ecosystem/00_toolchain | 3 |
| concept/06_ecosystem/01_cargo | 13 |
| concept/06_ecosystem/03_design_patterns | 6 |
| concept/06_ecosystem/05_systems_and_embedded | 29 |
| concept/06_ecosystem/06_data_and_distributed | 3 |
| concept/06_ecosystem/07_security_and_cryptography | 2 |
| concept/06_ecosystem/11_domain_applications | 1 |
| concept/06_ecosystem/12_networking | 2 |
| concept/06_ecosystem/14_enterprise_architecture | 4 |
| concept/06_ecosystem/16_algorithm_patterns | 6 |
| concept/07_future/00_version_tracking | 4 |
| concept/07_future/01_edition_roadmap | 2 |

最大簇：`06_ecosystem/05_systems_and_embedded`（29）、`06_ecosystem/01_cargo`（13）、`06_ecosystem/03_design_patterns`（6）、`03_advanced/08_process_ipc`（5）。

## 1. (a) 真重复候选 2 对：逐节裁决

### A1. `23_no_std_and_bare_metal_idioms.md` vs `38_no_std_bare_metal_rust.md`（05_systems_and_embedded）

**证据（H2 节清单对比）**

| 23（1340 行，25 节） | 38（1994 行，22 节） |
|---|---|
| 权威定义 / 最小可启动 crate / 关键属性矩阵 / panic handler 与运行时入口 / 自定义分配器与 heapless / critical-section 与内存屏障 / static vs static mut / build-std 与 target JSON / 链接脚本约定 / Embassy 执行器 / 反模式 / 反例与失效模式 / 边界测试 / 决策树 / 构建-运行-测试工作流 / probe-rs 实测 / 惯用法扩展 / SHACL 衔接 / 权威来源×2 | 权威定义 / no_std 语义边界 / 最小可编译 crate / 裸机启动流程 / 内存布局 / 异常与 panic / target spec 可移植性 / 属性关系表 / 正例 / 反例与失效模式 / 决策树 / 边界测试 / 权威来源补充 / 迁移检查清单 / RTOS 关系 / 版本兼容 / 快速参考卡 / P7 附录 |

- 精确重叠节名仅 7 个，且 4 个是样板骨架（知识结构图/目录/思维导图/相关概念）；实质重叠 3 个：权威定义、反例与失效模式、边界测试。
- 语义近似节对 2 组：「最小可启动 crate」~「最小可编译 crate」、「build-std 与 target JSON」~「target spec 可移植性」。
- 代码块互抄检测：51×59 块两两相似度 >0.85 的对 **0 个**；正文段落近重复 **0 个** → 无正文互抄，属主题重叠而非复制。
- 权威声明冲突：23 头部「本文件为 concept/ 权威页」（L13）；38 Summary 自称 "A canonical reference"（L8）且 L1476 显式「本文件…是 no_std 与裸机 Rust 的 concept/ 权威概念页」——**38 的权威声明更具体、带子主题让渡说明**（链接脚本/启动流程等指向专题页）。

**裁决建议（一句话）**：以 **38 为 canonical**（声明更完整、行数更多、自称 canonical reference 且已有子主题让渡机制）；23 收敛为「惯用法/工作流专题页」——头部加「权威来源指向 38_no_std_bare_metal_rust」注记、删除或改写「权威定义」节为指向 38，保留 Embassy/probe-rs/构建工作流等 38 没有的独有节；随后将 23~38 登记进 IGNORE_PAIRS（分层互补）。不建议物理合并（两文件独有节各占 ~60%，合并收益低、破坏锚点）。

### A2. `04_compiler_internals.md` vs `05_compiler_infrastructure.md`（00_toolchain）

**证据**

- **Summary 行逐字符相同**：两文件 L8/L9 均为 `Compiler Internals: Rust ecosystem tools, crates, and engineering practices.` ——该句式与 `06_event_driven_architecture`、`04_database_systems`、`04_category_theory` 等多页一致，属**泛化样板注入**（模板默认值未定制），不是内容互抄证据。
- 权威声明：两文件头部都有「本文件为 concept/ 权威页」样板行（L10/L11），但 05 另有真实来源对齐记录（L191 rustc-dev-guide/Cranelift，L193 创建变更日志 2026-06-01）。
- H2 节清单：04（918 行，17 节）= 前端 AST/HIR/类型系统/MIR/借用检查/后端codegen/查询系统——**rustc 编译管线内部**；05（334 行，12 节）= 并行前端摘要/Cranelift 摘要/build-std/Sanitizer 生态——**编译器基础设施选型**。实质重叠节 **0 个**（重叠仅样板骨架：测验/认知路径/国际权威参考/思维导图）。代码块与段落近重复 **0 个**。
- 体量悬殊（918 vs 334 行），05 明显是 04 的「基础设施补充页」。

**裁决建议（一句话）**：判定为**互补分层而非真重复**——04 为 canonical（编译管线内部权威页），05 头部 Summary 应定制改写（消除样板注入痕迹）并加「本页为 04 的基础设施补充」定位句，随后 04~05 登记 IGNORE_PAIRS；同样不建议合并（05 的 Cranelift/build-std/Sanitizer 内容 04 完全没有）。

> 两对共同点：均无正文互抄证据；「真重复」表象来自样板 Summary/权威声明行 + 词干相似。处置方向都是「头部权威定位收敛 + 登记豁免」，不是移动/删除文件（符合 AGENTS.md 文件规则）。

## 2. (b) 合法分层 → 建议登记 IGNORE_PAIRS（16 对，可直接粘贴）

其余 119 条中，103 条可由 §3 正则豁免覆盖；正则覆盖不到的 16 条逐对判定全部为 (b) 互补/误报，登记清单如下（追加进 `IGNORE_PAIRS = { ... }` 尾部）：

```python
    # 08 中文版 MVP 学习路径 vs 14 英文版（EN 标题/受众独立成页），同一路径的双语版本，非重复权威页
    frozenset({
        "concept/00_meta/04_navigation/08_learning_mvp_path.md",
        "concept/00_meta/04_navigation/14_learning_mvp_path_en.md",
    }),
    # use 声明 vs 枚举：主题完全不同，仅共享复数泛词干，纯词干误报
    frozenset({
        "concept/01_foundation/07_modules_and_items/03_use_declarations.md",
        "concept/01_foundation/07_modules_and_items/05_enumerations.md",
    }),
    # 01 基础 asm! 语法 vs 02 no_std/内核向扩展：基础+进阶合法分层
    frozenset({
        "concept/03_advanced/05_inline_assembly/01_inline_assembly.md",
        "concept/03_advanced/05_inline_assembly/02_inline_assembly_extended.md",
    }),
    # 操作语义规则 vs 观察等价概念：形式语义两个不同子主题
    frozenset({
        "concept/04_formal/03_operational_semantics/03_operational_semantics.md",
        "concept/04_formal/03_operational_semantics/06_observational_equivalence.md",
    }),
    # rustc 两阶段名称解析实现(HIR lowering) vs Rust Reference 名称系统规范：实现层 vs 规范层互补
    frozenset({
        "concept/04_formal/05_rustc_internals/04_name_resolution_and_hir.md",
        "concept/04_formal/05_rustc_internals/06_names_and_resolution.md",
    }),
    # rustc 内部架构(AST/HIR/MIR) vs rustc 测试基础设施(compiletest/Crater)：不同主题
    frozenset({
        "concept/06_ecosystem/00_toolchain/04_compiler_internals.md",
        "concept/06_ecosystem/00_toolchain/13_compiler_testing.md",
    }),
    # 01 设计模式总览 vs 33 反模式：正/反模式互补（33 头部已声明互补）
    frozenset({
        "concept/06_ecosystem/03_design_patterns/01_patterns.md",
        "concept/06_ecosystem/03_design_patterns/33_anti_patterns.md",
    }),
    # 架构模式总览 vs 拒绝类型领域验证模式：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/08_architecture_patterns.md",
        "concept/06_ecosystem/03_design_patterns/43_rejection_type_pattern.md",
    }),
    # 设计模式 FAQ 页 vs API 设计模式总览：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md",
        "concept/06_ecosystem/03_design_patterns/18_api_design_patterns.md",
    }),
    # 设计模式 FAQ 页 vs 反模式总览：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md",
        "concept/06_ecosystem/03_design_patterns/33_anti_patterns.md",
    }),
    # API/SemVer 演进惯用法 vs 测试/Mock 惯用法：同目录两个不同惯用法专题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/39_api_design_and_semver_idioms.md",
        "concept/06_ecosystem/03_design_patterns/40_testing_and_mocking_idioms.md",
    }),
    # 23 惯用法页 vs 39 硬件测量技术：不同子主题（与 (a) 对 23~38 无关）
    frozenset({
        "concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md",
        "concept/06_ecosystem/05_systems_and_embedded/39_no_std_hardware_measurement_and_validation.md",
    }),
    # 42 中断/抢占并发 vs 53 临界区/同步原语：裸机并发两个子主题
    frozenset({
        "concept/06_ecosystem/05_systems_and_embedded/42_interrupts_and_concurrency_on_bare_metal.md",
        "concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md",
    }),
    # 数据库生态工具 vs 数据密集系统设计(B-tree/LSM)：不同主题
    frozenset({
        "concept/06_ecosystem/06_data_and_distributed/04_database_systems.md",
        "concept/06_ecosystem/06_data_and_distributed/10_data_intensive_systems_design.md",
    }),
    # 字符串算法 vs 在线/流式算法：算法目录内共享 _algorithms 泛词干的不同主题
    frozenset({
        "concept/06_ecosystem/16_algorithm_patterns/07_string_algorithms_in_rust.md",
        "concept/06_ecosystem/16_algorithm_patterns/11_online_and_streaming_algorithms.md",
    }),
    # 数据结构总览 vs 持久化数据结构专题：总览+专题合法分层
    frozenset({
        "concept/06_ecosystem/16_algorithm_patterns/08_data_structures_in_rust.md",
        "concept/06_ecosystem/16_algorithm_patterns/16_persistent_data_structures.md",
    }),
```

（注：`no_std_and_bare_metal_idioms ~ no_std_hardware_measurement_and_validation` 一对与 (a) 对 23~38 无关——39 是硬件测量专题，23 是惯用法页，主题不同，可安全登记。）

## 3. (c) 词干误报 → 建议扩充 STEM_PATTERN_EXEMPTIONS（46 条正则）

设计原则：与既有 5 条模式同级；每条要求**两词干同时命中**才豁免（沿用 `stem_pattern_exempt` 语义）；已逐条校验**没有任何一条会同时命中 (a) 两对的词干**（`.*bare_metal_rust$` 刻意收紧结尾以保留 23~38 的 WARN；`.*no_std.*` 因会豁免 23~38 而被弃用）。追加条目：

```python
    (re.compile(r".*_reference$"), "目录内共享 _reference 后缀的规范参考页（Rust Reference 各章规范页 vs 实现页），词干相似属后缀惯例（round-2 复核 2026-10-13）"),
    (re.compile(r".*_theory$"), "目录内共享 _theory 后缀的不同理论主题页（type_theory/category_theory、formal_design_pattern_theory/formal_algorithm_theory）（round-2）"),
    (re.compile(r".*_and_rust$"), "『X 与 Rust』映射系列页（type_theory_and_rust/category_theory_and_rust），主题不同（round-2）"),
    (re.compile(r".*architecture.*"), "架构主题族页（architecture_pattern_semantics/architecture_refinement/clean_architecture_in_rust 等），同目录多子主题（round-2）"),
    (re.compile(r".*_in_rust$"), "『X in Rust』领域应用系列页（graph/string_algorithms_in_rust、DDD 战术/战略页），主题不同（round-2）"),
    (re.compile(r".*_data_structures.*"), "数据结构族页（ownership_aware/probabilistic/persistent_data_structures），共享泛后缀的不同专题（round-2）"),
    (re.compile(r".*generics.*"), "泛型族页（generics/const_generics/const_generics_and_trait_objects），基础+进阶合法分层（round-2）"),
    (re.compile(r".*traits$"), "trait 族页（traits/derive_traits/advanced_traits），泛词干相似（round-2）"),
    (re.compile(r".*associated_type.*"), "关联类型族页（generic_associated_types/associated_type_defaults），不同特性页（round-2）"),
    (re.compile(r".*concurrency.*"), "并发族页（concurrency/concurrency_patterns/interrupts_and_concurrency_on_bare_metal），主题族内不同子页（round-2）"),
    (re.compile(r".*send_sync.*"), "Send/Sync 族页（auto_traits 语义 vs 边界判定），互补分层（round-2）"),
    (re.compile(r".*async.*"), "async 族页（cancellation_safety/trait_object_safety/boundary_panorama/gat_async_boundary），不同子主题（round-2）"),
    (re.compile(r".*linear_logic.*"), "线性逻辑族页（理论页 vs 应用页），基础+应用合法分层（round-2）"),
    (re.compile(r".*knowledge_graph.*"), "知识图谱族页（construction vs reasoning），不同子主题（round-2）"),
    (re.compile(r".*language_specification.*"), "语言规范族页（overview vs Ferrocene 规范），总览+专题（round-2）"),
    (re.compile(r".*database.*"), "数据库族页（database_access vs database_systems），泛词干相似（round-2）"),
    (re.compile(r".*distributed.*"), "分布式族页（consensus vs protocols），不同子主题（round-2）"),
    (re.compile(r".*security.*"), "安全族页（practices/cryptography/architecture/network_security），同目录多子主题（round-2）"),
    (re.compile(r".*network.*"), "网络族页（advanced_network_protocols/formal_network_protocol_theory/networking_basics），不同子主题（round-2）"),
    (re.compile(r".*rust_in_.*"), "『Rust in X』行业应用系列页（financial_services/iot_and_edge），主题不同（round-2）"),
    (re.compile(r".*safety_critical.*"), "功能安全族页（misra 指南/safety_critical_systems/topic_index），同主题族多子页（round-2）"),
    (re.compile(r".*interrupt.*"), "中断族页（exception_model vs interrupts_and_concurrency_on_bare_metal），不同子主题（round-2）"),
    (re.compile(r"^embedded_"), "embedded_* 前缀族页（graphics/hal/memory/debugging 等），嵌入式目录命名惯例（round-2）"),
    (re.compile(r".*hardware.*"), "硬件验证族页（hardware_validation/hardware_test_matrix/hardware_measurement），不同子主题（round-2）"),
    (re.compile(r".*_deep_dive$"), "共享 _deep_dive 后缀的框架专题页（embassy/rtic），主题不同（round-2）"),
    (re.compile(r".*_internals$"), "共享 _internals 后缀的实现剖析页（compiler_internals/rustdoc_internals），工具不同（round-2）"),
    (re.compile(r".*_map$"), "meta 导航族页（authority_source_map/inter_layer_map 等），共享泛后缀 _map（round-2）"),
    (re.compile(r".*_index$"), "meta 索引族页（authority_index/topic_index/semantic_space_index），共享泛后缀 _index（round-2）"),
    (re.compile(r".*_1\d\d.*"), "版本号系列页（cargo_196/197_features、feature_domain_matrix_197/198、migration_197/198），独立版本跟踪页（round-2；与既有 rust_1_\d+ 模式互补，覆盖 _NNN 中缀形态）"),
    (re.compile(r".*cargo.*"), "cargo 族页（script/build_scripts/manifest/registries/workspaces 等），Cargo 目录命名惯例（round-2）"),
    (re.compile(r".*edition.*"), "edition 族页（edition_preview/edition_guide），版本路线图内不同页（round-2）"),
    (re.compile(r".*_faq$"), "共享 _faq 后缀的 FAQ 页（macro_faq/design_patterns_faq），FAQ 与主题页词干相似属误报（round-2）"),
    (re.compile(r".*_guide$"), "共享 _guide 后缀的指南页（rust_edition_guide 等），指南与主题页词干相似属误报（round-2）"),
    (re.compile(r".*macro.*"), "宏族页（macros/macro_faq），泛词干相似（round-2）"),
    (re.compile(r".*error.*"), "错误处理族页（error_handling_basics/control_flow/idioms），基础+进阶合法分层（round-2）"),
    (re.compile(r".*type.*"), "类型族页（type_theory/type_inference/type_system_reference/subtype_variance），同目录多子主题（round-2）"),
    (re.compile(r".*memory.*"), "内存族页（memory_allocators/memory_layout_and_heap_safety），不同子主题（round-2）"),
    (re.compile(r".*unsafe.*"), "unsafe 族页（unsafe_reference/std_unsafe_internals），规范页 vs 生态剖析页互补（round-2）"),
    (re.compile(r".*process.*"), "进程族页（process_security_and_sandboxing/process_testing_and_benchmarking），不同子主题（round-2）"),
    (re.compile(r".*semantic.*"), "语义族页（semantic_space/pattern_semantic_space_index），索引页与主题页词干相似属误报（round-2）"),
    (re.compile(r".*theorem.*"), "定理族页（theorem_inference_forest/theorem_registry），不同 meta 页（round-2）"),
    (re.compile(r".*strings_and.*"), "字符串族页（strings_and_text/strings_and_encoding），不同子主题（round-2）"),
    (re.compile(r".*_safety$"), "共享 _safety 后缀的专题页（cancellation_safety/heap_safety），主题不同（round-2）"),
    (re.compile(r".*verification.*"), "验证工具族页（verification_toolchain/modern_verification_tools），工具族命名相似（round-2）"),
    (re.compile(r".*debugging.*"), "调试族页（embedded_debugging_logging/probe_rs_and_embedded_debugging），工具专题互补（round-2）"),
    (re.compile(r".*bare_metal_rust$"), "bare_metal_rust 命名系列（no_std_bare_metal_rust/bare_metal_rust），注意：刻意不匹配 no_std_and_bare_metal_idioms，保留 (a) 对 23~38 的 WARN（round-2）"),
```

覆盖簇举例：cargo 版本系列（`_196/_197` 中缀版本号，补既有 `rust_1_\d+` 未覆盖的形态）、embedded_* 前缀族、architecture/type/security/network/database/distributed 泛主题族、meta 导航 `_map/_index` 族、`_reference/_theory/_guide/_faq/_deep_dive` 泛后缀族。

## 4. 预期效果

| 处置 | 数量 |
|---|---|
| (c) 46 条新正则豁免 | 103 条 WARN |
| (b) 16 对 IGNORE_PAIRS 登记 | 16 条 WARN |
| (a) 故意保留（23~38 的 same_dir 1 条 + 04~05 的 same_dir 1 条） | 2 条 WARN |
| **预期残留** | **2 条**（即 (a) 两对本身，直至头部权威定位收敛完成后按 §1 建议登记豁免，残留归 0） |

模拟校验：121 = 103(正则) + 16(登记对) + 2((a) 保留)，无遗漏、无重叠计数。

## 5. 执行顺序建议（下一轮，非本轮）

1. 先做 (a) 两对的头部收敛（23 加权威指向注记、05 定制 Summary），不动正文主体、不移动不删除文件。
2. 一次性追加 46 条正则 + 16 对登记到门脚本，跑 `--json` 复测确认残留 = 2。
3. (a) 头部收敛完成后再登记 23~38、04~05 两对，残留归 0，WARN 清零。

*报告生成：2026-10-13；方法：门脚本 --json 全量解析 + 逐文件头部 Summary/权威声明抽取（167 文件）+ 逐对 H2 节清单/代码块/段落相似度比对（difflib >0.85 阈值）+ 豁免方案全量模拟。*
