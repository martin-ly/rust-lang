# 概念一致性审计报告 (Concept Consistency Report)

> 生成时间: 2026-05-13T07:47:26.865681
> 扫描文件数: 37
> 提取概念定义数: 249
> 跨文件引用数: 87

## 目录

- [概念一致性审计报告 (Concept Consistency Report)](#概念一致性审计报告-concept-consistency-report)
  - [目录](#目录)
  - [一、执行摘要](#一执行摘要)
  - [二、Send / Sync 一致性检查](#二send--sync-一致性检查)
  - [三、所有权三规则一致性检查](#三所有权三规则一致性检查)
  - [四、生命周期省略规则一致性检查](#四生命周期省略规则一致性检查)
  - [五、unsafe 语义一致性检查](#五unsafe-语义一致性检查)
  - [六、跨文件段落引用有效性检查](#六跨文件段落引用有效性检查)
  - [七、附录：概念定义统计](#七附录概念定义统计)
    - [7.1 按概念分类统计](#71-按概念分类统计)
    - [7.2 按文件统计](#72-按文件统计)

---

## 一、执行摘要

| 检查项 | 状态 | 详情 |
|:---|:---|:---|
| Send / Sync 一致性 | ✅ 通过 | 检测到 3 项 |
| 所有权三规则一致性 | ✅ 通过 | 检测到 4 项 |
| 生命周期省略规则一致性 | ✅ 通过 | 检测到 0 项 |
| unsafe 语义一致性 | ✅ 通过 | 检测到 6 项 |
| 跨文件段落引用有效性 | ❌ 10 个无效引用 | 共 87 个引用 |
| **总计** | **10 错误 / 14 警告 / 0 提示** | — |

## 二、Send / Sync 一致性检查

| 严重程度 | 类型 | 文件 | 详情 |
|:---|:---|:---|:---|
| ⚠️ 警告 | Send 定义可能不完整 | concept\03_advanced\03_unsafe.md | 该文件中的 Send 定义未明确提及'跨线程转移/值move'核心语义 |
| ⚠️ 警告 | Send 定义可能不完整 | concept\05_comparative\01_rust_vs_cpp.md | 该文件中的 Send 定义未明确提及'跨线程转移/值move'核心语义 |
| ⚠️ 警告 | Send 定义可能不完整 | concept\02_intermediate\01_traits.md | 该文件中的 Send 定义未明确提及'跨线程转移/值move'核心语义 |

## 三、所有权三规则一致性检查

| 严重程度 | 类型 | 文件 | 详情 |
|:---|:---|:---|:---|
| ⚠️ 警告 | 所有权-唯一所有权 关键术语覆盖不足 | concept\03_advanced\01_concurrency.md | 期望包含术语: 唯一, 一个所有者, 单一, 资源唯一性，实际匹配 1/4 个 |
| ⚠️ 警告 | 所有权-唯一所有权 关键术语覆盖不足 | concept\05_comparative\01_rust_vs_cpp.md | 期望包含术语: 唯一, 一个所有者, 单一, 资源唯一性，实际匹配 2/4 个 |
| ⚠️ 警告 | 所有权-Move语义 关键术语覆盖不足 | concept\03_advanced\01_concurrency.md | 期望包含术语: move, 转移, 赋值, 传参, uninitialized，实际匹配 2/5 个 |
| ⚠️ 警告 | 所有权-Move语义 关键术语覆盖不足 | concept\04_formal\03_ownership_formal.md | 期望包含术语: move, 转移, 赋值, 传参, uninitialized，实际匹配 2/5 个 |

## 四、生命周期省略规则一致性检查

> ✅ 未检测到一致性问题。

## 五、unsafe 语义一致性检查

| 严重程度 | 类型 | 文件 | 详情 |
|:---|:---|:---|:---|
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\01_foundation\01_ownership.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\05_comparative\01_rust_vs_cpp.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\03_advanced\02_async.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\03_advanced\01_concurrency.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\02_intermediate\01_traits.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |
| ⚠️ 警告 | unsafe 语义表述不一致 | concept\01_foundation\02_borrowing.md | 该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'） |

## 六、跨文件段落引用有效性检查

> ❌ 发现 10 个无效段落引用：

| 来源文件 | 行号 | 目标文件 | 引用段落 | 原始文本 |
|:---|:---|:---|:---|:---|
| concept\00_meta\semantic_space.md | 728 | concept\04_formal\04_rustbelt.md | §7.3 | > **深入阅读**: Miri 的别名模型详见 [`03_unsafe.md`](../03_advanced/03_... |
| concept\00_meta\semantic_space.md | 899 | concept\02_intermediate\02_generics.md | §3 | > **深入阅读**: const generics 的能力边界详见 [`02_generics.md`](../02_... |
| concept\02_intermediate\02_generics.md | 66 | concept\04_formal\03_ownership_formal.md | §3 | > **形式化对应**: 生命周期参数在类型论中对应 **区域类型 (Region Types, Tofte & Tal... |
| concept\04_formal\02_type_theory.md | 502 | concept\02_intermediate\02_generics.md | §3 | > **深入阅读**: 生命周期约束求解详见 [`03_lifetimes.md`](../01_foundation/... |
| concept\05_comparative\safety_boundaries.md | 377 | concept\01_foundation\03_lifetimes.md | §7.5 | | 生命周期陷阱 | [`../01_foundation/03_lifetimes.md`](../01_founda... |
| concept\05_comparative\safety_boundaries.md | 378 | concept\01_foundation\04_type_system.md | §7.5 | | 类型系统绕过 | [`../01_foundation/04_type_system.md`](../01_foun... |
| concept\05_comparative\safety_boundaries.md | 379 | concept\02_intermediate\03_memory_management.md | §7.6 | | Rc/RefCell 循环 | [`../02_intermediate/03_memory_management.... |
| concept\05_comparative\safety_boundaries.md | 381 | concept\03_advanced\02_async.md | §7.6 | | Pin 不动性突破 | [`../03_advanced/02_async.md`](../03_advanced/... |
| concept\05_comparative\safety_boundaries.md | 382 | concept\03_advanced\03_unsafe.md | §7.6 | | unsafe 契约失效 | [`../03_advanced/03_unsafe.md`](../03_advanc... |
| concept\05_comparative\safety_boundaries.md | 383 | concept\04_formal\04_rustbelt.md | §5 | | RustBelt 证明边界 | [`../04_formal/04_rustbelt.md`](../04_form... |

**可用段落编号列表（目标文件前15个）：**

- `concept\04_formal\04_rustbelt.md`: 1.1, 1.2, 2.1, 2.2, 2.3, 3.1, 3.2, 3.3, 3.4, 3.5, 4.1, 4.2, 4.3, 6.1, 6.2 ...
- `concept\02_intermediate\02_generics.md`: 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 4.1, 4.2, 4.3, 4.4, 4.5, 5.1, 5.2, 5.3, 5.4 ...
- `concept\04_formal\03_ownership_formal.md`: 1.1, 1.2, 1.3, 1.4, 2.1, 2.2, 5.1, 5.2, 5.3, 6.4, 9.1, 9.2, 9.3, 9.4, 9.5 ...
- `concept\01_foundation\03_lifetimes.md`: 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 4.1, 4.2, 4.3, 4.4, 4.5, 4.6, 4.7, 4.8, 4.9 ...
- `concept\01_foundation\04_type_system.md`: 1.1, 1.2, 1.3, 2.1, 2.2, 4.1, 4.2, 4.3, 4.4, 4.5, 4.6, 4.7, 4.8, 4.9, 5.1 ...
- `concept\02_intermediate\03_memory_management.md`: 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 4.1, 4.2, 4.3, 4.4, 4.5, 5.1, 5.2, 5.3, 5.4 ...
- `concept\03_advanced\02_async.md`: 1.1, 1.2, 1.3, 2.1, 2.2, 2.3, 3.1, 3.2, 3.5, 5.1, 5.2, 6.1, 6.2, 6.3, 7.1 ...
- `concept\03_advanced\03_unsafe.md`: 1.1, 1.2, 1.3, 1.4, 2.1, 2.2, 2.3, 3.1, 3.2, 4.1, 5.5, 5.6, 6.1, 6.2, 6.3 ...

## 七、附录：概念定义统计

### 7.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| unsafe-UB | 55 | 15 |
| 所有权-Move语义 | 31 | 11 |
| Send+Sync | 29 | 13 |
| 所有权-作用域绑定 | 23 | 9 |
| unsafe-契约 | 22 | 9 |
| 所有权-唯一所有权 | 20 | 8 |
| unsafe-不变式 | 17 | 2 |
| Send | 10 | 3 |
| 生命周期-定义 | 10 | 6 |
| unsafe-语义 | 9 | 4 |
| 所有权-Copy例外 | 8 | 4 |
| Sync | 7 | 3 |
| 生命周期-Rule2 | 3 | 1 |
| 生命周期-Rule3 | 3 | 1 |
| 生命周期-Rule1 | 2 | 1 |

### 7.2 按文件统计

| 文件 | 概念定义数 | 跨文件引用数 | 章节数 |
|:---|:---|:---|:---|
| concept\00_meta\audit_checklist.md | 1 | 0 | 9 |
| concept\00_meta\concept_index.md | 6 | 0 | 8 |
| concept\00_meta\inter_layer_map.md | 11 | 0 | 13 |
| concept\00_meta\learning_guide.md | 7 | 0 | 13 |
| concept\00_meta\methodology.md | 0 | 0 | 20 |
| concept\00_meta\quick_reference.md | 5 | 1 | 0 |
| concept\00_meta\self_assessment.md | 9 | 1 | 0 |
| concept\00_meta\semantic_space.md | 12 | 19 | 30 |
| concept\00_meta\sources.md | 1 | 0 | 11 |
| concept\00_meta\todos.md | 0 | 0 | 3 |
| concept\01_foundation\01_ownership.md | 36 | 2 | 22 |
| concept\01_foundation\02_borrowing.md | 1 | 2 | 23 |
| concept\01_foundation\03_lifetimes.md | 12 | 2 | 38 |
| concept\01_foundation\04_type_system.md | 0 | 2 | 24 |
| concept\02_intermediate\01_traits.md | 4 | 1 | 24 |
| concept\02_intermediate\02_generics.md | 3 | 3 | 30 |
| concept\02_intermediate\03_memory_management.md | 14 | 1 | 24 |
| concept\02_intermediate\04_error_handling.md | 0 | 1 | 24 |
| concept\03_advanced\01_concurrency.md | 23 | 10 | 22 |
| concept\03_advanced\02_async.md | 1 | 3 | 24 |
| concept\03_advanced\03_unsafe.md | 55 | 2 | 24 |
| concept\03_advanced\04_macros.md | 0 | 1 | 24 |
| concept\04_formal\01_linear_logic.md | 10 | 2 | 12 |
| concept\04_formal\02_type_theory.md | 3 | 15 | 16 |
| concept\04_formal\03_ownership_formal.md | 3 | 5 | 21 |
| concept\04_formal\04_rustbelt.md | 4 | 4 | 18 |
| concept\05_comparative\01_rust_vs_cpp.md | 8 | 1 | 37 |
| concept\05_comparative\02_rust_vs_go.md | 2 | 0 | 25 |
| concept\05_comparative\03_paradigm_matrix.md | 0 | 0 | 13 |
| concept\05_comparative\safety_boundaries.md | 14 | 9 | 11 |
| concept\06_ecosystem\01_toolchain.md | 0 | 0 | 28 |
| concept\06_ecosystem\02_patterns.md | 3 | 0 | 15 |
| concept\06_ecosystem\03_core_crates.md | 1 | 0 | 21 |
| concept\06_ecosystem\04_application_domains.md | 0 | 0 | 22 |
| concept\07_future\01_ai_integration.md | 0 | 0 | 21 |
| concept\07_future\02_formal_methods.md | 0 | 0 | 35 |
| concept\07_future\03_evolution.md | 0 | 0 | 25 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
