# 实践项目 {#实践项目}

> **EN**: Practice Index
> **Summary**: 实践项目 Practice Index.
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **目标**: 通过实际项目学习Rust
> **项目数**: 15个（入门5个 + 进阶5个 + 专家5个）

---

## 📚 项目列表 {#项目列表}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 📋 综合项目指南 {#综合项目指南}

| 项目 | 描述 | 包含项目数 |
|------|------|-----------|
| [跨模块实战项目指南](03_cross_module_practical_projects_2025_10_25.md) | 10 个渐进式跨模块实战项目总览 | 10 |

### 🟢 入门级（5个） {#入门级5个}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 项目 | 描述 | 所需知识 | 预计时间 |
|------|------|---------|---------|
| [项目 01: 命令行工具](03_project_01_cli_tool.md) | Todo CLI工具 | c01-c03 | 2-3h |
| [项目 02: 文件处理器](03_project_02_file_processor.md) | 文件搜索/复制/统计 | c01-c03 | 2-3h |
| [项目 03: 表达式计算器](03_project_03_calculator.md) | 支持四则运算的计算器 | c01-c04 | 3-4h |
| [项目 04: 密码生成器](03_project_04_password_generator.md) | 随机密码生成 | c01-c03 | 1-2h |
| [项目 05: 文本统计工具](03_project_05_text_statistics.md) | 类似wc的统计工具 | c01-c03 | 2h |

### 🟡 进阶级（5个） {#进阶级5个}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 项目 | 描述 | 所需知识 | 预计时间 |
|------|------|---------|---------|
| [项目 06: 并发下载器](03_project_06_concurrent_downloader.md) | 多线程/异步下载 | c05-c06 | 4-6h |
| [项目 07: 聊天服务器](03_project_07_chat_server.md) | TCP聊天服务器 | c05-c06, c10 | 5-7h |
| [项目 08: 内存缓存](03_project_08_cache_system.md) | 线程安全缓存 | c05 | 4-5h |
| [项目 09: 日志分析器](03_project_09_log_parser.md) | 高性能日志处理 | c01-c06 | 4-5h |
| [项目 10: 数据处理管道](03_project_10_data_pipeline.md) | 类似Unix管道 | c04-c06 | 5-6h |

### 🔴 专家级（5个） {#专家级5个}

| 项目 | 描述 | 所需知识 | 预计时间 |
|------|------|---------|---------|
| [项目 11: Web服务器](03_project_11_web_server.md) | HTTP服务器 | c06, c10 | 8-10h |
| [项目 12: WASM应用](03_project_12_wasm_app.md) | 浏览器WASM应用 | c12 | 6-8h |
| [项目 13: 数据库引擎](03_project_13_database_engine.md) | 嵌入式数据库 | c01-c08 | 10-12h |
| [项目 14: 异步运行时](03_project_14_async_runtime.md) | 简化版async运行时 | c06 | 12-15h |
| [项目 15: 分布式KV](03_project_15_distributed_system.md) | 分布式键值存储 | c05-c10 | 15-20h |

---

## 🎯 学习路径建议 {#学习路径建议}

### 初学者路径 {#初学者路径}

```
项目 01 → 项目 02 → 项目 04 → 项目 05 → 项目 03
```

### 有经验开发者路径 {#有经验开发者路径}

```
项目 03 → 项目 06 → 项目 08 → 项目 07 → 项目 11
```

### 专家路径 {#专家路径}

```
项目 11 → 项目 13 → 项目 14 → 项目 15
```

---

## 📊 统计 {#统计}

- **入门级**: 5个项目，总计约 10-14小时
- **进阶级**: 5个项目，总计约 22-29小时
- **专家级**: 5个项目，总计约 51-65小时
- **总计**: 15个项目，约 83-108小时

---

## 📝 说明 {#说明}

- 每个项目包含完整的需求、学习要点和参考实现
- 参考实现位于 `examples/<project-name>/`
- 建议按难度逐步完成

[返回文档中心](../README.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
