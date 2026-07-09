# 三轨内容相似度检测报告

- **扫描文件数**: 1019
- **相似度阈值**: 0.6
- **潜在重复对**: 2

| 相似度 | 文件1 | 文件2 | 标题1 | 标题2 |
|:---|:---|:---|:---|:---|
| 0.75 | `concept\07_future\00_version_tracking\rust_1_97_preview.md` | `docs\06_toolchain\06_21_rust_1_97_features.md` | Rust 1.97.0 稳定特性详解 | Rust 1.97.0 特性参考 |
| 0.75 | `concept\07_future\00_version_tracking\rust_1_97_stabilized.md` | `docs\06_toolchain\06_21_rust_1_97_features.md` | Rust 1.97.0 稳定特性 | Rust 1.97.0 特性参考 |

## 建议

1. 相似度 > 0.8 的文件对：优先人工复核，考虑合并或归档
2. 相似度 0.6-0.8 的文件对：检查是否存在内容交叉引用需求
3. concept/ 优先：知识应以 concept/ 为主轨，其他轨道迁移或引用
