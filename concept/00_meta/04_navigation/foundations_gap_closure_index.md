# 基础知识缺口补全总索引
>
> **EN**: Foundations Gap Closure Index
> **Summary**: A completion index tracking the closure of foundational knowledge gaps identified in SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md across Phase A, B, and C.
>
> **受众**: [进阶]
> **层级**: L0 元信息
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**: [PL Foundations Roadmap](../00_framework/pl_foundations_roadmap.md) · [C/C++ Engineering Roadmap](../00_framework/cpp_rust_engineering_roadmap.md) · [Pattern Semantic Space Index](../00_framework/pattern_semantic_space_index.md)
> **后置概念**: [Concept Audit Guide](../03_audit/08_concept_audit_guide.md)
> **主要来源**: [SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md](../../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RFCs](https://github.com/rust-lang/rfcs)
---

> **Bloom 层级**: 评价

## 一、核心命题

> **审计报告 [SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md](../../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md) 指出项目存在"两头强、中间弱、底层散"的结构性失衡。
> 本索引追踪 Phase A（通用 PL 基座）、Phase B（C/C++ 工程层对比）、Phase C（表征空间坐标系）的补全状态，
> 列出已完成的文件、仍存在的已知问题，以及下一步建议。**

---

## 二、Phase A：通用 PL 基座

| 审计任务 | 优先级 | 状态 | 文件 |
|:---|:---:|:---:|:---|
| 变量模型 | P0 | ✅ 完成 | [Variable Model](../../01_foundation/03_values_and_references/20_variable_model.md) |
| 求值策略 | P0 | ✅ 完成 | [Evaluation Strategies](../../04_formal/03_operational_semantics/18_evaluation_strategies.md) |
| 副作用与纯度 | P0 | ✅ 完成 | [Effects and Purity](../../01_foundation/00_start/21_effects_and_purity.md) |
| 控制流深化 | P1 | ✅ 完成 | [Control Flow](../../01_foundation/04_control_flow/07_control_flow.md) |
| 数据抽象谱系 | P1 | ✅ 完成 | [Data Abstraction Spectrum](../../01_foundation/02_type_system/22_data_abstraction_spectrum.md) |
| 统一路线图 | — | ✅ 新增 | [PL Foundations Roadmap](../00_framework/pl_foundations_roadmap.md) |

---

## 三、Phase B：C/C++ 工程层对比

| 审计任务 | 优先级 | 状态 | 文件 |
|:---|:---:|:---:|:---|
| ABI 与对象模型 | P0 | ✅ 完成 | [C++ ABI Object Model](../../05_comparative/01_systems_languages/18_cpp_abi_object_model.md) |
| Move 语义系统对比 | P0 | ✅ 完成 | [Rust vs C++ §7.3](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) |
| 异常安全深度 | P0 | ✅ 完成 | [Exception Safety](../../02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md) |
| SFINAE / 模板元编程 | P1 | ✅ 完成 | [Traits §5.8](../../02_intermediate/00_traits/01_traits.md) |
| 构造/初始化/运算符/RTTI/友元 | P1 | ✅ 完成 | [Surface Features](../../05_comparative/00_paradigms/16_cpp_rust_surface_features.md) + 专门文件 |
| 预处理器 vs 宏 | P2 | ✅ 完成 | [Preprocessor vs Macros](../../02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md) |
| 统一路线图 | — | ✅ 新增 | [C/C++ Engineering Roadmap](../00_framework/cpp_rust_engineering_roadmap.md) |

### Phase B 专门文件清单

- [RTTI 与动态类型识别](../../02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md) — C++ `typeid`/`dynamic_cast` vs Rust `Any`/`TypeId`
- [C 预处理器 vs Rust 宏](../../02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md) — 文本替换 vs 语法树卫生性
- [异常安全](../../02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md) — strong/basic/no-throw vs `Result`/`panic`
- [构造与初始化](../../02_intermediate/00_traits/28_construction_and_initialization.md) — 构造函数 vs 结构体字面量
- [友元 vs 模块可见性](../../02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md) — `friend` vs `pub(crate)`/`pub(super)`

---

## 四、Phase C：表征空间坐标系

| 审计任务 | 优先级 | 状态 | 文件 |
|:---|:---:|:---:|:---|
| 模式组合代数 | P0 | ✅ 完成 | [Pattern Composition Algebra](../../06_ecosystem/03_design_patterns/73_pattern_composition_algebra.md) |
| 算法-模式语义桥 | P0 | ✅ 完成 | [Algorithm-Pattern Semantic Bridge](../00_framework/semantic_bridge_algorithms_patterns.md) |
| 统一模式索引 | P1 | ✅ 新增 | [Pattern Semantic Space Index](../00_framework/pattern_semantic_space_index.md) |
| 并发/分布式模式谱系 | P2 | ✅ 已存在 | [Parallel Distributed Pattern Spectrum](../../03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md) |
| 模板去同质化 | P1 | ⚠️ 未启动 | 需后续为 23 个形式化模式文件设计差异化结构 |

---

## 五、新增文件总清单

| 文件 | 层级 | 作用 |
|:---|:---|:---|
| [Pattern Semantic Space Index](../00_framework/pattern_semantic_space_index.md) | 00_meta | 模式语义空间坐标系导航 |
| [C/C++ Engineering Roadmap](../00_framework/cpp_rust_engineering_roadmap.md) | 00_meta | C++ 迁移者主题簇地图 |
| [PL Foundations Roadmap](../00_framework/pl_foundations_roadmap.md) | 00_meta | 通用 PL 基座导航 |
| [Foundations Gap Closure Index](foundations_gap_closure_index.md) | 00_meta | 本文件：补全状态追踪 |
| [RTTI and Dynamic Typing](../../02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md) | 02_intermediate | C++ RTTI vs Rust `Any` |
| [Preprocessor vs Macros](../../02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md) | 02_intermediate | C 预处理器 vs Rust 宏 |
| [Exception Safety](../../02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md) | 02_intermediate | 异常安全深度对比 |
| [Construction and Initialization](../../02_intermediate/00_traits/28_construction_and_initialization.md) | 02_intermediate | 构造与初始化对比 |
| [Friend vs Module Privacy](../../02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md) | 02_intermediate | 友元 vs 模块可见性 |
| [C++ Rust Surface Features](../../05_comparative/00_paradigms/16_cpp_rust_surface_features.md) | 05_comparative | 构造/运算符/RTTI/友元综合速查 |

---

## 六、已知遗留问题

### 6.1 SUMMARY.md 占位符 ✅ 已解决

`concept/SUMMARY.md` 中的 22 个 `LINK_PLACEHOLDER` 条目已替换为 `00_meta/placeholders/placeholder-N.md`。

- **解决方案**: 创建了 22 个占位符文件，保留导航结构，同时使 `mdbook build` 成功通过。
- **状态**: 占位符文件保留待创建主题的标题和说明，未来可逐步替换为真实内容。

### 6.2 内容文件中的 LINK_PLACEHOLDER

除 `SUMMARY.md` 外，`concept/` 其他 Markdown 文件中仍有约 688 个 `LINK_PLACEHOLDER` 链接（分布在 212 个文件中）。这些链接指向尚未创建的 concept 文件或外部资源。

- **影响**: 不影响 `mdbook build`（mdbook 只检查 `SUMMARY.md` 中的文件路径），但会降低内容导航体验。
- **建议**: 作为长期工程债务，分批替换为真实文件路径或移除链接。

### 6.2 自动双语标注残留

经抽查，未发现明显的 i18n 脚本机械残留。正常的关键术语双语标注（如"所有权 (Ownership)"）符合 [Terminology Glossary](../01_terminology/terminology_glossary.md) 规范。

### 6.3 重复文件已清理

`concept/06_ecosystem/99_pattern_composition_algebra.md` 已删除，与 `35_pattern_composition_algebra.md` 合并。

---

## 七、下一步建议

1. **处理 SUMMARY.md 占位符**：决定是为每个 LINK_PLACEHOLDER 创建文件，还是重构为纯文本列表。
2. **模板去同质化**：为 23 个形式化模式文件设计差异化结构（L4 证明导向 / L6 工程导向 / L7 前沿导向）。
3. **反向链接增强**：在已有概念文件中添加指向新创建基座/对比文件的交叉引用。
4. **练习与测验**：为新创建的文件设计配套测验，纳入 `exercises/` 或 `concept/XX_quiz_*.md`。

---

## 八、L1 / L2 / L3 总结

| 层级 | 要点 |
|:---|:---|
| **L1** | Phase A/B/C 的 P0 和大部分 P1 任务已通过新建/现有文件补全。 |
| **L2** | 新增的路线图和索引文件建立了从通用 PL 到 C++ 对比再到模式语义空间的结构化导航。 |
| **L3** | 基础知识缺口已从"分散缺失"转变为"有文件覆盖、有索引导航、有状态追踪"的受控状态，但仍需解决 SUMMARY.md 占位符和模板去同质化等工程问题。 |

---

> **Checklist**: 已建立 Phase A/B/C 补全状态追踪 / 列出新增文件 / 记录已知遗留问题 / 提出下一步建议。
