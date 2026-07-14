> **权威来源**: 本文件为 `crates/c14_semantic_web/` 的 crate 入口页。
> 通用 Rust 概念解释统一维护在 `concept/` 中；详见 [../../concept/06_ecosystem/06_data_and_distributed/](../../concept/06_ecosystem/06_data_and_distributed/)。
>
> 根据 AGENTS.md §2 Canonical 规则，`crates/` 不重复通用 Rust 概念解释；
> 如需深入学习，请前往 `concept/` 权威页。
>
# C14 Semantic Web

> Crate: `c14_semantic_web`
> **版本**: 3.1.0
> **Rust 版本**: 1.97.0+
> **状态**: 🚧 持续建设中

Rust 知识体系知识图谱工具链：解析、验证、推理与查询。

---

## 🎯 快速开始

1. 查看 [`docs/00_MASTER_INDEX.md`](docs/00_meta/00_master_index.md) 了解本 crate 的完整文档结构。
2. 查看 [`docs/ONE_PAGE_SUMMARY.md`](docs/one_page_summary.md) 获取核心概念速览。
3. 运行示例：

   ```bash
   cargo run -p c14_semantic_web --example kg_validate
   cargo run -p c14_semantic_web --example kg_query
   ```

## 📚 文档结构

| 文件 | 说明 |
|---|---|
| [`docs/00_MASTER_INDEX.md`](docs/00_meta/00_master_index.md) | 主索引与导航 |
| [`docs/ONE_PAGE_SUMMARY.md`](docs/one_page_summary.md) | 单页核心总结 |
| [`docs/PENDING_ITEMS.md`](docs/pending_items.md) | 待补充项 |
| [`docs/MIND_MAP.md`](docs/mind_map.md) | 思维导图/知识地图 |

## 🧪 测试

```bash
cargo test -p c14_semantic_web
```

---

*本文件基于 `docs/README.md` 整理，版本号与 workspace 保持一致。*
