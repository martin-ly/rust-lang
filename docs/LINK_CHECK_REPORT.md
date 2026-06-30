# 链接有效性检查报告

## 统计
| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 50081 |
| 有效链接 | 23749 |
| 损坏链接 | 16 |
| 外部链接 | 26315 |
| 仅锚点链接 | 15211 |

## 损坏链接清单（按问题类型分组）

### 文件不存在 (13个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\research_notes\10_rustc_dev_guide_alignment.md | software_design_theory/07_crate_architectures/ | `../software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md` | 文件不存在: docs\software_design_theory\07_crate_architectures\00_crate_architecture_master_index.md |
| docs\research_notes\10_rust_194_195_feature_matrix.md | toolchain | `../../06_toolchain/` | 文件不存在: 06_toolchain |
| docs\research_notes\software_design_theory\07_crate_architectures\22_redis_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |
| docs\research_notes\software_design_theory\07_crate_architectures\22_redis_architecture.md | 缓存与消息队列设计 | `../../../../concept/06_ecosystem/15_caching_messaging.md` | 文件不存在: concept\06_ecosystem\15_caching_messaging.md |
| docs\research_notes\software_design_theory\07_crate_architectures\23_mongodb_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |
| docs\research_notes\software_design_theory\07_crate_architectures\24_regex_architecture.md | 字符串处理设计模式 | `../../../../concept/03_advanced/15_string_processing.md` | 文件不存在: concept\03_advanced\15_string_processing.md |
| docs\research_notes\software_design_theory\07_crate_architectures\26_kafka_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |
| docs\research_notes\software_design_theory\07_crate_architectures\27_kube_rs_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |
| docs\research_notes\software_design_theory\07_crate_architectures\28_lapin_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |
| docs\research_notes\software_design_theory\07_crate_architectures\32_vector_architecture.md | AI 集成与嵌入模型 | `../../../../concept/06_ecosystem/40_ai_integration.md` | 文件不存在: concept\06_ecosystem\40_ai_integration.md |
| docs\research_notes\software_design_theory\07_crate_architectures\33_sentry_architecture.md | anyhow / thiserror 错误处理 | `../../../../concept/03_advanced/03_error_handling.md` | 文件不存在: concept\03_advanced\03_error_handling.md |
| docs\research_notes\software_design_theory\07_crate_architectures\34_metrics_architecture.md | Prometheus 生态 | `../../../../concept/06_ecosystem/35_observability.md` | 文件不存在: concept\06_ecosystem\35_observability.md |
| docs\research_notes\software_design_theory\07_crate_architectures\37_aws_sdk_architecture.md | 分布式模式 | `../../../../concept/03_advanced/19_distributed_patterns.md` | 文件不存在: concept\03_advanced\19_distributed_patterns.md |

### 锚点不存在 (3个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\06_toolchain\03_rustdoc_advanced.md | 8.1  属性 {#81-doc-属性} | `#81-doc-属性-81-doc-属性` | 同文件锚点不存在: #81-doc-属性-81-doc-属性 |
| docs\research_notes\formal_modules\20_linkage_and_symbols.md |  与  {#linkage-internal-与-static} | `#linkage--internal-与-static-linkage-internal-与-static` | 同文件锚点不存在: #linkage--internal-与-static-linkage-internal-与-static |
| docs\research_notes\formal_modules\60_module_counterexamples.md | 8.  符号冲突 {#8-no\_mangle-符号冲突} | `#8-no_mangle-符号冲突-8-no_mangle-符号冲突` | 同文件锚点不存在: #8-no_mangle-符号冲突-8-no_mangle-符号冲突 |

## 修复建议

### 1. 文件不存在问题
- 检查链接路径是否正确
- 确认目标文件是否已被移动或删除
- 更新链接指向正确的文件位置

### 2. 锚点不存在问题
- 检查锚点ID是否与目标文件中的标题匹配
- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点
- 示例：`## Hello World!` -> `#hello-world`

### 3. 同文件锚点问题
- 检查文档中是否存在对应的标题
- 可能是文档结构已更改但目录未更新

## 源文件问题统计

| 源文件 | 损坏链接数 |
|:---|:---:|
| docs\research_notes\software_design_theory\07_crate_architectures\22_redis_architecture.md | 2 |
| docs\06_toolchain\03_rustdoc_advanced.md | 1 |
| docs\research_notes\10_rustc_dev_guide_alignment.md | 1 |
| docs\research_notes\10_rust_194_195_feature_matrix.md | 1 |
| docs\research_notes\formal_modules\20_linkage_and_symbols.md | 1 |
| docs\research_notes\formal_modules\60_module_counterexamples.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\23_mongodb_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\24_regex_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\26_kafka_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\27_kube_rs_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\28_lapin_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\32_vector_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\33_sentry_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\34_metrics_architecture.md | 1 |
| docs\research_notes\software_design_theory\07_crate_architectures\37_aws_sdk_architecture.md | 1 |

**总计 15 个文件包含损坏链接**