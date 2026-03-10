# 智能文档搜索工具

> **最后更新**: 2026-03-08

---

## 简介

本项目提供全文搜索功能，帮助快速定位文档内容。

## 使用方式

### 在线搜索

访问在线文档平台使用内置搜索功能：
https://<username>.github.io/rust-lang/

### 本地搜索

```bash
# 构建搜索索引
cd tools/doc_search
cargo run -- build-index

# 执行搜索
cargo run -- search "所有权"
```

## 功能特性

- 🔍 全文搜索所有 Markdown 文档
- 🎯 智能排序，优先显示相关结果
- 📱 支持中文和英文搜索
- ⚡ 快速响应，毫秒级查询

## 相关文档

- [项目 README](../../README.md)
- [mdBook 使用说明](../../book/README.md)
