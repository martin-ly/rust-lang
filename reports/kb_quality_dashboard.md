# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: The system cannot accept the date entered.
Enter the new date: (yy-mm-dd)
> 扫描文件数: 37

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 37 | 27 | ✅ |
| 总定理链 (⟹) | 301 | ≥400 | ⚠️ |
| 总反命题 | 92 | ≥40 | ✅ |
| 总 Mermaid 图 | 170 | ≥50 | ✅ |
| 编译验证代码块 | 245 | ≥150 | ✅ |
| 定理矩阵总行 | 3233 | — | — |
| 死链数量 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径覆盖率 |
|:---|:---|:---|:---|:---|
| L0 | 10 | 3.6 | 0.0 | 4/10 (40%) |
| L1 | 4 | 7.8 | 17.0 | 4/4 (100%) |
| L2 | 4 | 13.2 | 8.0 | 4/4 (100%) |
| L3 | 4 | 15.2 | 2.0 | 4/4 (100%) |
| L4 | 4 | 11.5 | 2.5 | 4/4 (100%) |
| L5 | 4 | 5.8 | 3.5 | 4/4 (100%) |
| L6 | 4 | 7.2 | 3.5 | 3/4 (75%) |
| L7 | 3 | 7.3 | 0.0 | 3/3 (100%) |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| concept\00_meta\concept_index.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| concept\00_meta\inter_layer_map.md | L0 | 过渡段落不足 (0 < 3) |
| concept\00_meta\learning_guide.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (2 < 3) |
| concept\00_meta\methodology.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\quick_reference.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\self_assessment.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\semantic_space.md | L0 | 过渡段落不足 (0 < 3) |
| concept\00_meta\sources.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\todos.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\03_advanced\01_concurrency.md | L3 | 过渡段落不足 (0 < 3) |
| concept\03_advanced\02_async.md | L3 | 过渡段落不足 (0 < 3) |
| concept\03_advanced\03_unsafe.md | L3 | 过渡段落不足 (0 < 3) |
| concept\04_formal\01_linear_logic.md | L4 | 过渡段落不足 (0 < 3) |
| concept\04_formal\02_type_theory.md | L4 | 过渡段落不足 (0 < 3) |
| concept\04_formal\03_ownership_formal.md | L4 | 过渡段落不足 (0 < 3); 缺失反命题 |
| concept\04_formal\04_rustbelt.md | L4 | 缺失反命题 |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 过渡段落不足 (0 < 3) |
| concept\05_comparative\02_rust_vs_go.md | L5 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| concept\05_comparative\safety_boundaries.md | L5 | 过渡段落不足 (0 < 3) |
| concept\06_ecosystem\03_core_crates.md | L6 | 过渡段落不足 (0 < 3) |
| concept\06_ecosystem\04_application_domains.md | L6 | 过渡段落不足 (0 < 3) |
| concept\07_future\01_ai_integration.md | L7 | 过渡段落不足 (0 < 3) |
| concept\07_future\02_formal_methods.md | L7 | 过渡段落不足 (0 < 3) |
| concept\07_future\03_evolution.md | L7 | 过渡段落不足 (0 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00_meta\audit_checklist.md | L0 | 180 | 0 | 0 | 0 | 0 | 0 | ✅ |
| concept\00_meta\concept_index.md | L0 | 403 | 1 | 2 | 0 | 0 | 0 | ❌ |
| concept\00_meta\inter_layer_map.md | L0 | 411 | 24 | 0 | 1 | 0 | 0 | ✅ |
| concept\00_meta\learning_guide.md | L0 | 287 | 2 | 0 | 0 | 1 | 0 | ❌ |
| concept\00_meta\methodology.md | L0 | 359 | 0 | 3 | 4 | 1 | 0 | ✅ |
| concept\00_meta\quick_reference.md | L0 | 535 | 0 | 0 | 0 | 25 | 0 | ❌ |
| concept\00_meta\self_assessment.md | L0 | 779 | 0 | 0 | 0 | 24 | 0 | ❌ |
| concept\00_meta\semantic_space.md | L0 | 1017 | 9 | 3 | 4 | 8 | 0 | ✅ |
| concept\00_meta\sources.md | L0 | 302 | 0 | 0 | 2 | 0 | 0 | ❌ |
| concept\00_meta\todos.md | L0 | 205 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\01_foundation\01_ownership.md | L1 | 700 | 5 | 6 | 7 | 10 | 16 | ✅ |
| concept\01_foundation\02_borrowing.md | L1 | 755 | 3 | 8 | 6 | 13 | 20 | ✅ |
| concept\01_foundation\03_lifetimes.md | L1 | 751 | 13 | 3 | 4 | 12 | 16 | ✅ |
| concept\01_foundation\04_type_system.md | L1 | 687 | 10 | 3 | 4 | 9 | 16 | ✅ |
| concept\02_intermediate\01_traits.md | L2 | 751 | 12 | 3 | 5 | 11 | 10 | ✅ |
| concept\02_intermediate\02_generics.md | L2 | 945 | 20 | 3 | 6 | 12 | 8 | ✅ |
| concept\02_intermediate\03_memory_management.md | L2 | 787 | 12 | 4 | 5 | 11 | 7 | ✅ |
| concept\02_intermediate\04_error_handling.md | L2 | 801 | 9 | 4 | 5 | 12 | 7 | ✅ |
| concept\03_advanced\01_concurrency.md | L3 | 1014 | 17 | 6 | 10 | 15 | 0 | ✅ |
| concept\03_advanced\02_async.md | L3 | 948 | 15 | 2 | 8 | 15 | 0 | ✅ |
| concept\03_advanced\03_unsafe.md | L3 | 947 | 13 | 3 | 9 | 10 | 0 | ✅ |
| concept\03_advanced\04_macros.md | L3 | 942 | 16 | 6 | 8 | 19 | 8 | ✅ |
| concept\04_formal\01_linear_logic.md | L4 | 483 | 15 | 3 | 4 | 4 | 0 | ✅ |
| concept\04_formal\02_type_theory.md | L4 | 542 | 18 | 3 | 4 | 2 | 0 | ✅ |
| concept\04_formal\03_ownership_formal.md | L4 | 573 | 10 | 0 | 4 | 0 | 0 | ✅ |
| concept\04_formal\04_rustbelt.md | L4 | 547 | 3 | 0 | 4 | 2 | 10 | ✅ |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 1852 | 9 | 5 | 13 | 2 | 0 | ✅ |
| concept\05_comparative\02_rust_vs_go.md | L5 | 430 | 1 | 4 | 4 | 2 | 0 | ✅ |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 501 | 6 | 4 | 7 | 0 | 14 | ✅ |
| concept\05_comparative\safety_boundaries.md | L5 | 405 | 7 | 0 | 5 | 0 | 0 | ✅ |
| concept\06_ecosystem\01_toolchain.md | L6 | 653 | 8 | 2 | 7 | 3 | 8 | ✅ |
| concept\06_ecosystem\02_patterns.md | L6 | 680 | 7 | 0 | 4 | 11 | 6 | ❌ |
| concept\06_ecosystem\03_core_crates.md | L6 | 619 | 7 | 3 | 5 | 2 | 0 | ✅ |
| concept\06_ecosystem\04_application_domains.md | L6 | 625 | 7 | 3 | 5 | 1 | 0 | ✅ |
| concept\07_future\01_ai_integration.md | L7 | 539 | 7 | 3 | 5 | 1 | 0 | ✅ |
| concept\07_future\02_formal_methods.md | L7 | 738 | 8 | 3 | 7 | 3 | 0 | ✅ |
| concept\07_future\03_evolution.md | L7 | 515 | 7 | 0 | 4 | 4 | 0 | ✅ |
