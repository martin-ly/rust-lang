# KG relatedTo 压缩报告
**日期**: 2026-08-04

将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：

| 谓词 | 数量 |
|---|---:|
| hasPart | 4269 |
| partOf | 432 |
| refines | 552 |
| dependsOn | 1117 |
| entails | 477 |
| equivalentTo | 0 |
| appliesTo | 128 |
| unchanged | 850 |

- 修改总数: 6975
- 未变更（仍 relatedTo）: 850

规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。
