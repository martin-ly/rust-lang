# KG relatedTo 压缩报告
**日期**: 2026-08-04

将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：

| 谓词 | 数量 |
|---|---:|
| hasPart | 4249 |
| partOf | 430 |
| refines | 544 |
| dependsOn | 1114 |
| entails | 476 |
| equivalentTo | 0 |
| appliesTo | 128 |
| unchanged | 849 |

- 修改总数: 6941
- 未变更（仍 relatedTo）: 849

规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。
