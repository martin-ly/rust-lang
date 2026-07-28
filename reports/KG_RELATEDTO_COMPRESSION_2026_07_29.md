# KG relatedTo 压缩报告

**日期**: 2026-07-29

将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：

| 谓词 | 数量 |
|---|---:|
| hasPart | 3992 |
| partOf | 450 |
| refines | 484 |
| dependsOn | 949 |
| entails | 497 |
| equivalentTo | 0 |
| appliesTo | 127 |
| unchanged | 896 |

- 修改总数: 6499
- 未变更（仍 relatedTo）: 896

规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。
