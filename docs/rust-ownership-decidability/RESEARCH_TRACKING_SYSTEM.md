# Rust 形式化验证研究追踪系统

> **版本**: 1.0.0
> **更新频率**: 季度审查 + 实时重要更新
> **覆盖范围**: 学术会议、工业动态、工具更新

---

## 目录

- [Rust 形式化验证研究追踪系统](#rust-形式化验证研究追踪系统)
  - [目录](#目录)
  - [1. 系统概述](#1-系统概述)
  - [2. 追踪来源](#2-追踪来源)
    - [2.1 顶级会议](#21-顶级会议)
    - [2.2 预印本与期刊](#22-预印本与期刊)
    - [2.3 官方渠道](#23-官方渠道)
    - [2.4 工业动态](#24-工业动态)
  - [3. 季度审查流程](#3-季度审查流程)
  - [4. 重要研究跟踪](#4-重要研究跟踪)
    - [4.1 当前活跃项目](#41-当前活跃项目)
    - [4.2 预期发布](#42-预期发布)
  - [5. 工具版本跟踪](#5-工具版本跟踪)
    - [版本监控矩阵](#版本监控矩阵)
    - [版本检查脚本](#版本检查脚本)
  - [6. 文档更新流程](#6-文档更新流程)
    - [发现新研究后的处理流程](#发现新研究后的处理流程)
    - [更新类型](#更新类型)
  - [7. 历史更新记录](#7-历史更新记录)
    - [2026-03-12 大规模更新](#2026-03-12-大规模更新)
    - [未来更新计划](#未来更新计划)
  - [附录：快速检查清单](#附录快速检查清单)
    - [每日检查](#每日检查)
    - [每周检查](#每周检查)
    - [每月检查](#每月检查)
    - [季度检查](#季度检查)

---

## 1. 系统概述

本系统用于持续追踪 Rust 形式化验证领域的最新研究进展，确保文档内容始终保持与权威资源对齐。

**追踪目标**:

- 顶级会议论文 (PLDI, POPL, ICFP, OOPSLA, CAV, SOSP)
- 重要期刊论文 (TOPLAS, JFP)
- 预印本 (arXiv)
- 官方项目动态 (Rust Project Goals, RFMIG)
- 工业工具更新 (Kani, Verus, Creusot 等)

---

## 2. 追踪来源

### 2.1 顶级会议

| 会议 | 时间 | 重点追踪内容 | 优先级 |
|------|------|-------------|--------|
| **POPL** | 1月 | 编程语言理论、类型系统 | 🔴 高 |
| **PLDI** | 6月 | 语言设计与实现 | 🔴 高 |
| **ICFP** | 8-9月 | 函数式编程 | 🔴 高 |
| **OOPSLA** | 10月 | 面向对象与系统 | 🟡 中 |
| **CAV** | 7月 | 计算机辅助验证 | 🟡 中 |
| **SOSP** | 10月 | 操作系统 | 🟡 中 |
| **ESOP** | 4月 | 编程语言理论 | 🟢 低 |
| **TACAS** | 4月 | 工具与算法 | 🟢 低 |

**追踪方法**:

1. 会议接受论文列表发布后立即检查
2. 关注标题含 "Rust"、"ownership"、"verification" 的论文
3. 追踪已知研究团队的论文

### 2.2 预印本与期刊

**arXiv 追踪**:

- 搜索关键词: `Rust verification`, `ownership types`, `borrow checker`
- 关注作者: Ralf Jung, Derek Dreyer, Niko Matsakis 等
- 频率: 每周自动扫描

**期刊**:

- TOPLAS (ACM Transactions on Programming Languages)
- JFP (Journal of Functional Programming)

### 2.3 官方渠道

**Rust Formal Methods Interest Group**:

- 网站: <https://rust-formal-methods.github.io/>
- 会议: 月度线上会议
- 追踪: 演讲主题和录像

**Rust Project Goals**:

- 标准库验证: <https://rust-lang.github.io/rust-project-goals/2024h2/std-verification.html>
- Polonius: <https://rust-lang.github.io/rust-project-goals/2024h2/Polonius.html>

**官方博客**:

- Inside Rust: <https://blog.rust-lang.org/inside-rust/>
- Ralf Jung's Blog: <https://www.ralfj.de/blog/>

### 2.4 工业动态

**GitHub 监控**:

| 项目 | 仓库 | 追踪内容 |
|------|------|----------|
| Kani | model-checking/kani | 发布、功能更新 |
| Verus | verus-lang/verus | 发布、案例研究 |
| Creusot | creusot-rs/creusot | 发布、标准库支持 |
| Aeneas | AeneasVerif/aeneas | 发布、Lean 集成 |
| Miri | rust-lang/miri | Tree Borrows 进展 |

---

## 3. 季度审查流程

```
季度审查时间表:

Q1 (1-3月) 审查:
├── POPL 论文检查
├── 新年工具版本更新
└── 年度计划审查

Q2 (4-6月) 审查:
├── PLDI 论文检查 ⭐
├── ESOP/TACAS 检查
└── 工业工具半年更新

Q3 (7-9月) 审查:
├── CAV 论文检查
├── ICFP 论文检查 ⭐
└── 夏季进展评估

Q4 (10-12月) 审查:
├── OOPSLA/SOSP 检查 ⭐
├── 年度总结
└── 下一年计划
```

**审查任务清单**:

- [ ] 检查所有目标会议的新论文
- [ ] 更新 `academic-papers.md`
- [ ] 检查工具新版本
- [ ] 更新工具兼容性矩阵
- [ ] 检查官方项目进展
- [ ] 更新路线图文档
- [ ] 验证所有链接有效性
- [ ] 更新完成报告

---

## 4. 重要研究跟踪

### 4.1 当前活跃项目

| 项目 | 机构 | 负责人 | 状态 | 预期完成 |
|------|------|--------|------|----------|
| **Polonius** | Rust Team | lqd, Amanda Stjerna | 开发中 | 2025 |
| **Tree Borrows** | MPI-SWS | Ralf Jung | 评估中 | 稳定版? |
| **标准库验证** | Rust Team | Celina G. Val | 进行中 | 持续 |
| **RefinedRust** | MPI-SWS | Lennard Gaher | 原型 | 工具化? |
| **Aeneas** | Inria | Andreas Lattuada | 活跃 | 持续 |
| **Verus** | CMU/VMware | Andrea Lattuada | 活跃 | 持续 |

### 4.2 预期发布

**2025 年预期**:

- Polonius 位置敏感分析
- Tree Borrows 可能成为 Miri 默认
- 更多 Rust 标准库验证结果
- RefinedRust 工具公开发布

**研究前沿**:

- 并发 Rust 验证
- 异步 Rust 形式化
- 自引用类型语言特性
- Rust 编译器正确性证明

---

## 5. 工具版本跟踪

### 版本监控矩阵

| 工具 | 最新版本 | 最后检查 | 文档版本 | 同步状态 |
|------|----------|----------|----------|----------|
| Kani | 0.x | 2026-03 | 0.x | ✅ 同步 |
| Verus | 0.x | 2026-03 | 0.x | ✅ 同步 |
| Creusot | 0.x | 2026-03 | 0.x | ⚠️ 需验证 |
| Prusti | 维护模式 | 2026-03 | 维护 | ✅ 同步 |
| Aeneas | 活跃 | 2026-03 | 近期 | ✅ 同步 |
| Miri |  nightly | 2026-03 | nightly | ✅ 同步 |

### 版本检查脚本

```bash
#!/bin/bash
# 工具版本检查脚本 (示例)

echo "=== Rust 验证工具版本检查 ==="

echo "Kani:"
cargo install kani-verifier --dry-run 2>&1 | grep -i version

echo ""
echo "Miri:"
rustup run nightly miri --version

echo ""
echo "Creusot:"
cargo install cargo-creusot --dry-run 2>&1 | grep -i version

echo ""
echo "检查完成，请对比文档中的版本信息"
```

---

## 6. 文档更新流程

### 发现新研究后的处理流程

```
发现新论文/工具更新
        ↓
评估重要性
        ↓
┌───────┴───────┐
高重要性      低重要性
        ↓           ↓
立即更新     记录待处理
        ↓           ↓
创建/更新     季度审查
文档         时处理
        ↓
交叉引用
检查
        ↓
更新
完成报告
        ↓
提交更新
```

### 更新类型

| 类型 | 处理方式 | 时间要求 |
|------|----------|----------|
| 顶级会议论文 | 立即创建新文档 | 1周内 |
| 重要工具发布 | 更新工具文档 | 2周内 |
| 官方项目里程碑 | 更新路线图 | 1个月内 |
| 一般论文 | 季度批量处理 | 季度 |
| 链接修复 | 随时处理 | 即时 |

---

## 7. 历史更新记录

### 2026-03-12 大规模更新

**触发原因**: 网络资源对齐

**更新内容**:

- ✅ 新增 RefinedRust 深度解析 (PLDI 2024)
- ✅ 新增 Gillian-Rust 介绍
- ✅ 新增 Rust 标准库验证计划
- ✅ 新增 Tree Borrows 更新 (PLDI 2025)
- ✅ 新增 Polonius 完整解析
- ✅ 新增工业验证案例
- ✅ 新增 RefinedRust vs RustBelt 对比
- ✅ 更新学术参考文献
- ✅ 更新工具对比矩阵

**覆盖会议**: PLDI 2025, PLDI 2024, ICFP 2024, SOSP 2024

**新增字数**: ~10 万字

---

### 未来更新计划

**2025 Q2 预期**:

- [ ] PLDI 2025 论文深度解析 (6月)
- [ ] 工具版本同步检查
- [ ] Polonius 进展更新

**2025 Q3 预期**:

- [ ] ICFP 2025 论文检查
- [ ] 标准库验证进展更新

**2025 Q4 预期**:

- [ ] OOPSLA/SOSP 2025 检查
- [ ] 年度总结报告

---

## 附录：快速检查清单

### 每日检查

- [ ] arXiv Rust 相关新论文

### 每周检查

- [ ] RFMIG 会议更新
- [ ] 主要工具 GitHub 动态

### 每月检查

- [ ] 官方博客更新
- [ ] 工具新版本发布

### 季度检查

- [ ] 完整会议论文列表
- [ ] 文档全面审查
- [ ] 链接有效性检查
- [ ] 完成报告更新

---

**系统维护**: Rust 所有权可判定性研究项目
**最后更新**: 2026-03-12
**状态**: 活跃
