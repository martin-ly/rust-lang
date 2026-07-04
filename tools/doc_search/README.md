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
- [mdBook 使用说明](../../README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
