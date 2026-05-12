# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: The system cannot accept the date entered.
Enter the new date: (yy-mm-dd)
> 扫描文件数: 49

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 49 | 27 | ✅ |
| 总定理链 (⟹) | 275 | ≥400 | ⚠️ |
| 总反命题 | 108 | ≥40 | ✅ |
| 总 Mermaid 图 | 189 | ≥50 | ✅ |
| 编译验证代码块 | 195 | ≥150 | ✅ |
| 定理矩阵总行 | 4140 | — | — |
| 死链数量 | 4 | 0 | ❌ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径覆盖率 |
|:---|:---|:---|:---|:---|
| L0 | 8 | 4.2 | 0.0 | 2/8 (25%) |
| L1 | 6 | 3.8 | 5.7 | 0/6 (0%) |
| L2 | 6 | 6.8 | 0.0 | 0/6 (0%) |
| L3 | 5 | 11.6 | 0.0 | 2/5 (40%) |
| L4 | 5 | 10.0 | 1.0 | 1/5 (20%) |
| L5 | 5 | 3.6 | 1.4 | 0/5 (0%) |
| L6 | 5 | 5.8 | 1.4 | 0/5 (0%) |
| L7 | 4 | 5.5 | 0.0 | 0/4 (0%) |
| L? | 5 | 0.0 | 0.0 | 0/5 (0%) |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| concept\00.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\concept_index.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| concept\00_meta\inter_layer_map.md | L0 | 过渡段落不足 (0 < 3) |
| concept\00_meta\methodology.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\semantic_space.md | L0 | 过渡段落不足 (0 < 3) |
| concept\00_meta\sources.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\00_meta\todos.md | L0 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\01.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\01_foundation\01_ownership.md | L1 | 缺失认知路径 |
| concept\01_foundation\02_borrowing.md | L1 | 缺失认知路径 |
| concept\01_foundation\03_lifetimes.md | L1 | 缺失认知路径 |
| concept\01_foundation\04_type_system.md | L1 | 缺失认知路径 |
| concept\01_foundation\README.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\02.md | L2 | 缺失认知路径; 缺失反命题 |
| concept\02_intermediate\01_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\02_intermediate\02_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\02_intermediate\03_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\02_intermediate\04_error_handling.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\02_intermediate\README.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题; 定理链不足 (0 < 3) |
| concept\03_advanced\01_concurrency.md | L3 | 过渡段落不足 (0 < 3) |
| concept\03_advanced\02_async.md | L3 | 过渡段落不足 (0 < 3) |
| concept\03_advanced\03_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\03_advanced\04_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\03_advanced\README.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题; 定理链不足 (0 < 3) |
| concept\04_formal\01_linear_logic.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\04_formal\02_type_theory.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\04_formal\03_ownership_formal.md | L4 | 过渡段落不足 (0 < 3); 缺失反命题 |
| concept\04_formal\04_rustbelt.md | L4 | 缺失认知路径; 缺失反命题; 定理链不足 (2 < 3) |
| concept\04_formal\README.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\05_comparative\02_rust_vs_go.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 缺失认知路径; 定理链不足 (2 < 3) |
| concept\05_comparative\README.md | L5 | 缺失认知路径 |
| concept\05_comparative\safety_boundaries.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| concept\06_ecosystem\03_core_crates.md | L6 | 过渡段落不足 (0 < 3) |
| concept\06_ecosystem\04_application_domains.md | L6 | 过渡段落不足 (0 < 3) |
| concept\07_future\01_ai_integration.md | L7 | 过渡段落不足 (0 < 3) |
| concept\07_future\02_formal_methods.md | L7 | 过渡段落不足 (0 < 3) |
| concept\07_future\03_evolution.md | L7 | 过渡段落不足 (0 < 3) |
| concept\LSIP_Unified_Model_Panorama.md | L? | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\PLAN_Semantic_Space_Wave.md | L? | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\PostgreSQL_LSIP_Unified_Model.md | L? | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 死链检测

| 来源文件 | 引用路径 | 解析后的绝对路径 |
|:---|:---|:---|
| concept\00.md | PostgreSQL_18_Plus_Formal_Analysis.md | E:\_src\rust-lang\concept\PostgreSQL_18_Plus_Formal_Analysis.md |
| concept\00.md | sandbox:///mnt/agents/output/PostgreSQL_18_Cognitive_Map.md | E:\_src\rust-lang\concept\sandbox:\mnt\agents\output\PostgreSQL_18_Cognitive_Map.md |
| concept\00.md | sandbox:///mnt/agents/output/PostgreSQL_18_Data_Index_Analysis.md | E:\_src\rust-lang\concept\sandbox:\mnt\agents\output\PostgreSQL_18_Data_Index_Analysis.md |
| concept\07_future\01_ai_integration.md | ./02_intermediate/01_traits.md | E:\_src\rust-lang\concept\07_future\02_intermediate\01_traits.md |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00.md | L0 | 5657 | 0 | 6 | 1 | 0 | 0 | ❌ |
| concept\00_meta\audit_checklist.md | L0 | 180 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\00_meta\concept_index.md | L0 | 403 | 1 | 2 | 0 | 0 | 0 | ❌ |
| concept\00_meta\inter_layer_map.md | L0 | 411 | 24 | 0 | 1 | 0 | 0 | ❌ |
| concept\00_meta\methodology.md | L0 | 359 | 0 | 3 | 4 | 1 | 0 | ✅ |
| concept\00_meta\semantic_space.md | L0 | 1017 | 9 | 3 | 4 | 8 | 0 | ✅ |
| concept\00_meta\sources.md | L0 | 302 | 0 | 0 | 2 | 0 | 0 | ❌ |
| concept\00_meta\todos.md | L0 | 205 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\01.md | L1 | 1791 | 0 | 7 | 10 | 2 | 0 | ❌ |
| concept\01_foundation\01_ownership.md | L1 | 700 | 5 | 6 | 7 | 10 | 8 | ❌ |
| concept\01_foundation\02_borrowing.md | L1 | 755 | 3 | 8 | 6 | 13 | 10 | ❌ |
| concept\01_foundation\03_lifetimes.md | L1 | 633 | 8 | 3 | 4 | 10 | 8 | ❌ |
| concept\01_foundation\04_type_system.md | L1 | 687 | 7 | 3 | 4 | 9 | 8 | ❌ |
| concept\01_foundation\README.md | L1 | 173 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\02.md | L2 | 125 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\02_intermediate\01_traits.md | L2 | 751 | 10 | 3 | 5 | 11 | 0 | ❌ |
| concept\02_intermediate\02_generics.md | L2 | 945 | 15 | 3 | 6 | 12 | 0 | ❌ |
| concept\02_intermediate\03_memory_management.md | L2 | 787 | 9 | 4 | 5 | 11 | 0 | ❌ |
| concept\02_intermediate\04_error_handling.md | L2 | 801 | 7 | 4 | 5 | 12 | 0 | ❌ |
| concept\02_intermediate\README.md | L2 | 215 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\03_advanced\01_concurrency.md | L3 | 1014 | 14 | 6 | 10 | 15 | 0 | ✅ |
| concept\03_advanced\02_async.md | L3 | 948 | 15 | 2 | 8 | 15 | 0 | ✅ |
| concept\03_advanced\03_unsafe.md | L3 | 947 | 13 | 3 | 9 | 10 | 0 | ❌ |
| concept\03_advanced\04_macros.md | L3 | 942 | 16 | 6 | 8 | 19 | 0 | ❌ |
| concept\03_advanced\README.md | L3 | 219 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\04_formal\01_linear_logic.md | L4 | 483 | 15 | 3 | 4 | 4 | 0 | ❌ |
| concept\04_formal\02_type_theory.md | L4 | 542 | 18 | 3 | 4 | 2 | 0 | ❌ |
| concept\04_formal\03_ownership_formal.md | L4 | 484 | 10 | 0 | 4 | 0 | 0 | ✅ |
| concept\04_formal\04_rustbelt.md | L4 | 547 | 2 | 0 | 4 | 2 | 5 | ❌ |
| concept\04_formal\README.md | L4 | 199 | 5 | 0 | 1 | 0 | 0 | ❌ |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 1852 | 8 | 5 | 13 | 2 | 0 | ❌ |
| concept\05_comparative\02_rust_vs_go.md | L5 | 430 | 1 | 4 | 4 | 2 | 0 | ❌ |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 501 | 2 | 4 | 7 | 0 | 7 | ❌ |
| concept\05_comparative\README.md | L5 | 155 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\05_comparative\safety_boundaries.md | L5 | 405 | 7 | 0 | 5 | 0 | 0 | ❌ |
| concept\06_ecosystem\01_toolchain.md | L6 | 653 | 8 | 2 | 7 | 3 | 4 | ❌ |
| concept\06_ecosystem\02_patterns.md | L6 | 680 | 7 | 0 | 4 | 11 | 3 | ❌ |
| concept\06_ecosystem\03_core_crates.md | L6 | 619 | 7 | 3 | 5 | 2 | 0 | ❌ |
| concept\06_ecosystem\04_application_domains.md | L6 | 625 | 7 | 3 | 5 | 1 | 0 | ❌ |
| concept\06_ecosystem\README.md | L6 | 122 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\07_future\01_ai_integration.md | L7 | 539 | 7 | 3 | 5 | 1 | 0 | ❌ |
| concept\07_future\02_formal_methods.md | L7 | 738 | 8 | 3 | 7 | 3 | 0 | ❌ |
| concept\07_future\03_evolution.md | L7 | 515 | 7 | 0 | 4 | 4 | 0 | ❌ |
| concept\07_future\README.md | L7 | 143 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\LSIP_Unified_Model_Panorama.md | L? | 584 | 0 | 0 | 1 | 0 | 0 | ❌ |
| concept\PLAN.md | L? | 186 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\PLAN_Semantic_Space_Wave.md | L? | 250 | 0 | 0 | 0 | 0 | 0 | ❌ |
| concept\PostgreSQL_LSIP_Unified_Model.md | L? | 683 | 0 | 3 | 0 | 0 | 0 | ❌ |
| concept\README.md | L? | 129 | 0 | 0 | 0 | 0 | 0 | ❌ |
