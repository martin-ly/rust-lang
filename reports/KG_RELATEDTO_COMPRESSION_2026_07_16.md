# KG relatedTo 压缩报告

**日期**: 2026-07-16

将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：

| 谓词 | 数量 |
|---|---:|
| hasPart | 3696 |
| partOf | 430 |
| refines | 429 |
| dependsOn | 898 |
| entails | 470 |
| equivalentTo | 0 |
| appliesTo | 121 |
| unchanged | 794 |

- 修改总数: 6044
- 未变更（仍 relatedTo）: 794

规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。
