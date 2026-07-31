# KG relatedTo 压缩报告
**日期**: 2026-07-31

将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：

| 谓词 | 数量 |
|---|---:|
| hasPart | 4165 |
| partOf | 450 |
| refines | 572 |
| dependsOn | 1054 |
| entails | 505 |
| equivalentTo | 0 |
| appliesTo | 128 |
| unchanged | 989 |

- 修改总数: 6874
- 未变更（仍 relatedTo）: 989

规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。
