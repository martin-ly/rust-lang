# Rust 知识库后续工作计划

## 当前状态速览

| 指标 | 数值 |
|------|------|
| 核心文档数 | 74 篇 |
| 核心总行数 | 34,493 行 |
| 核心总字符数 | 798,614 字符 |
| Rust 1.95 补完 | ✅ 完成（541 行 / 40+ 项变更） |
| cfg_select! 链接 | ✅ 已修复（#115585） |

---

## 待解决问题

### 1. INDEX.md 索引重复

**问题**: `Vec::push_mut` 和 `Layout::dangling_ptr` 在 1.95 特性索引中出现两次：

- 第一次指向专项文档（collections.md / unsafe_audit.md）
- 第二次指向 rust_1_95.md（汇总文档）

**修复方案**: 保留指向专项文档的条目，移除指向 rust_1_95.md 的重复条目，或在备注列注明"详见文档 / 汇总"。

### 2. rust_1_95.md 模块 6 完整性

**状态**: 已覆盖 JSON target specs、$crate::{self}、Eq::assert_receiver_is_total_eq、mut ref 模式
**待确认**: 是否还有其他官方兼容性注意未收录

---

## 三阶段后续计划

### Phase 1: 索引清理与质量审查（立即，~30 分钟）

| # | 任务 | 目标文件 |
|---|------|----------|
| 1.1 | 去重 1.95 特性索引表格（push_mut / Layout API） | INDEX.md |
| 1.2 | 检查 1.96 预览索引表格与 rust_1_96_preview.md 一致性 | INDEX.md |
| 1.3 | 运行断裂链接扫描脚本 | 全局 |
| 1.4 | 更新文档统计数字（如执行后有变化） | INDEX.md |

### Phase 2: Rust 1.96.0 发布文档转正（2026-05-28 前后，~2 小时）

| # | 任务 | 目标文件 |
|---|------|----------|
| 2.1 | 抓取 Rust 1.96.0 官方 Release Notes | - |
| 2.2 | 将 rust_1_96_preview.md 扩展为完整发布文档（500+ 行） | rust_1_96.md |
| 2.3 | 更新 INDEX.md：1.96 特性索引转正（🧪 Beta → ✅ Stable） | INDEX.md |
| 2.4 | 同步更新相关核心文档（如新增 API 需要） | 按需 |
| 2.5 | 新建 rust_1_97_preview.md（前沿特性追踪） | 新建 |

**1.96 当前已知特性预览**:

- `VecDeque::truncate_front`
- `int_format_into`
- `RefCell::try_map`
- `cargo script` / frontmatter
- RFC 3550 新 Range 类型

### Phase 3: 知识库质量审计（持续，~4 小时，可分次）

| # | 任务 | 说明 |
|---|------|------|
| 3.1 | 断裂链接全面修复 | 运行 apply_link_fixes.py 或手动扫描 |
| 3.2 | 文档模板一致性检查 | 检查所有文档是否遵循 10 模块强制模板 |
| 3.3 | 代码示例可编译性验证 | 抽样验证关键代码片段 |
| 3.4 | 层 README 导航完整性 | 检查 7 个层 README 是否覆盖所有子目录 |
| 3.5 | 1.97 Nightly 特性追踪 | 每 6 周更新一次前沿预览文档 |

---

## 建议执行顺序

**Option A — 保守推进（推荐）**
> 先做 Phase 1 索引清理，然后等待 1.96 发布执行 Phase 2，最后执行 Phase 3 质量审计。
> 优点：节奏清晰，避免重复劳动。

**Option B — 并行推进**
> Phase 1 与 Phase 3 部分任务并行执行，1.96 发布前完成质量审计。
> 优点：在 1.96 发布前把知识库底座打牢。

**Option C — 仅做 Phase 1**
> 仅修复 INDEX.md 重复条目和断裂链接，其余等 1.96 发布后再议。
> 优点：最小工作量，快速收尾。

---

## 相关概念

- [Hello, World](../00_start/hello_world.md)
- [安装 Rust](../00_start/installation.md)
---\n\n## 权威来源索引\n\n> **来源: [Rust Reference - Edition 2024](https://doc.rust-lang.org/reference/)**\n\n> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**\n\n> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**\n\n> **[来源: Rust Internals Forum]**\n
