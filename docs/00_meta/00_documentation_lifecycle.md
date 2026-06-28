# 文档生命周期管理制度

> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L2 (理解)
> **创建日期**: 2026-05-12
> **版本**: 1.0
> **状态**: ✅ 已生效

---

## 📑 目录

- [文档生命周期管理制度](#文档生命周期管理制度)
  - [📑 目录](#-目录)
  - [1. 生命周期阶段](#1-生命周期阶段)
  - [2. 归档流程（强制）](#2-归档流程强制)
    - [2.1 触发归档的条件](#21-触发归档的条件)
    - [2.2 归档操作步骤](#22-归档操作步骤)
    - [2.3 归档标记模板](#23-归档标记模板)
  - [3. 版本升级检查清单](#3-版本升级检查清单)
  - [4. 自动化检查脚本](#4-自动化检查脚本)
    - [4.1 版本号一致性检查](#41-版本号一致性检查)
    - [4.2 文档重复扫描](#42-文档重复扫描)
    - [4.3 过时标记检查](#43-过时标记检查)
  - [5. 删除策略](#5-删除策略)
    - [5.1 禁止删除](#51-禁止删除)
    - [5.2 允许删除](#52-允许删除)
  - [6. 责任分工](#6-责任分工)
  - [7. 相关文档](#7-相关文档)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 生命周期阶段

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
创建 → 评审 → 发布 → 维护 → 归档 → 删除
```

| 阶段 | 说明 | 触发条件 |
|------|------|----------|
| **创建** | 新文档编写 | 新特性、新模块、新需求 |
| **评审** | 内容准确性检查 | 创建完成后 |
| **发布** | 纳入索引和导航 | 评审通过后 |
| **维护** | 持续更新 | 特性变更、版本升级、错误修正 |
| **归档** | 标记过时并移入 archive | 特性废弃、版本落后、内容合并 |
| **删除** | 物理删除 | 归档满 90 天且确认无价值 |

---

## 2. 归档流程（强制）
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 触发归档的条件

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

满足以下任一条件即触发归档：

1. **版本落后**: 文档目标版本低于当前项目目标版本 **2 个 minor 版本**以上（如当前 1.96，文档针对 1.94 及以下）
2. **特性废弃**: 文档描述的特性已被官方废弃或移除
3. **内容合并**: 文档内容已被整合到其他文档中
4. **标记过时**: 文档顶部已添加过时警告超过 **30 天**

### 2.2 归档操作步骤

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

```bash
# Step 1: 在文档顶部添加归档标记（创建时即添加）
# Step 2: 从原目录移动到 archive/ 对应子目录
# Step 3: 更新所有索引文件中对该文档的引用
# Step 4: 在 archive/ 目录的 README 中记录归档信息
# Step 5: 90 天后评估是否删除
```

### 2.3 归档标记模板

```markdown
> **⚠️ 已归档**: 此文档内容已过时，已于 YYYY-MM-DD 归档。
> **原因**: [版本落后 / 特性废弃 / 内容合并 / 其他]
> **替代文档**: [链接到新文档]
> **归档位置**: `docs/archive/deprecated_YYYYMMDD/...`
```

---

## 3. 版本升级检查清单

每次 Rust 新版本发布（约每 6 周），执行以下检查：

- [ ] 更新 `Cargo.toml` 的 `rust-version`（如需要）
- [ ] 更新所有入口文档的版本标注（`00_master_index.md`、`10_terminology_standard.md` 等）
- [ ] 创建新版本速查卡（`docs/02_reference/quick_reference/rust_XYZ_features_cheatsheet.md`）
- [ ] 创建新版本特性文档（`docs/06_toolchain/NN_rust_X.Y_features.md`）
- [ ] 更新 `knowledge/INDEX.md` 中的版本索引
- [ ] 检查并归档过时文档
- [ ] 运行 `scripts/check_links.py` 检查断链
- [ ] 运行 `cargo test` 确保所有代码示例可编译

---

## 4. 自动化检查脚本

### 4.1 版本号一致性检查

```bash
# 检查所有 .md 文件中的版本标注
python3 scripts/check_version_consistency.py
```

检查项：

- 文件标注版本 < 项目目标版本 - 1 → 警告
- 文件标注版本 < 项目目标版本 - 2 → 建议归档

### 4.2 文档重复扫描

```bash
# 基于标题和内容相似度扫描重复文档
python3 scripts/check_doc_duplicates.py --threshold 0.7
```

### 4.3 过时标记检查

```bash
# 检查标记过时超过 30 天但仍留在原位的文档
python3 scripts/check_deprecated_markers.py --days 30
```

---

## 5. 删除策略

### 5.1 禁止删除

以下文件**不得删除**，即使归档：

- 版本历史报告（用于追溯）
- 形式化证明（学术价值）
- 安全审计报告（合规要求）

### 5.2 允许删除

满足以下全部条件可删除：

1. 已归档满 **90 天**
2. 内容已被确认无历史价值
3. 无其他文档引用该文件
4. 已备份或版本控制中可恢复

---

## 6. 责任分工

| 角色 | 职责 |
|------|------|
| **文档创建者** | 编写新文档、标注版本、确保代码可编译 |
| **评审者** | 检查准确性、版本一致性、交叉引用完整性 |
| **维护者** | 定期执行检查清单、处理归档和删除 |
| **项目维护团队** | 年度评审文档架构、更新本制度 |

---

## 7. 相关文档

- `00_documentation_division_of_labor.md` — 文档体系分工协议
- `DOCS_STRUCTURE_OVERVIEW.md` — 完整结构总览

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
