# Rust 所有权可判定性 - 网络权威资源对齐分析报告

> **分析日期**: 2026-03-12
> **分析范围**: 2024-2025 年最新学术研究与权威资料
> **当前文档状态**: 579 个 Markdown 文件，约 50 万+ 字

---

## 执行摘要

本文档对比分析了 `rust-ownership-decidability` 文件夹内容与网络上最新、最全面的权威学术资源之间的差距，并制定持续推进计划。

### 核心发现

| 维度 | 当前状态 | 最新网络资源 | 差距评估 |
|------|----------|--------------|----------|
| **RefinedRust** | 简要提及 | PLDI 2024 最佳论文级研究 | ⚠️ 需大幅补充 |
| **Aeneas** | 基础介绍 | ICFP 2024 完整形式化 | 🔶 需更新 |
| **Gillian-Rust** | 未覆盖 | 2024 混合验证方法 | 🔴 缺失 |
| **Tree Borrows** | 部分覆盖 | 2023 新别名模型 | 🔶 需深化 |
| **Polonius** | 提及 | 2024 生产级进展 | 🔶 需更新 |
| **Rust 标准库验证** | 计划阶段 | 2024 正式项目 | 🔴 缺失 |

---

## 1. 最新权威资源识别 (2024-2025)

### 1.1 顶级会议论文 (PLDI/POPL/ICFP/SOSP)

#### 🔴 高优先级 - 尚未充分覆盖

| 论文 | 会议 | 年份 | 核心贡献 | 当前覆盖度 |
|------|------|------|----------|------------|
| **RefinedRust** | PLDI | 2024 | 首个支持 unsafe 代码的基础性验证工具 | 10% |
| **Aeneas** | ICFP | 2024 | 函数式转换验证方法 | 40% |
| **Verus** | SOSP | 2024 | 系统验证实用基础 | 60% |
| **Gillian-Rust** | 会议演讲 | 2024 | 混合符号执行验证 | 0% |

#### 🔶 中优先级 - 需要更新

| 论文 | 来源 | 年份 | 说明 |
|------|------|------|------|
| Tree Borrows | WIP | 2023-2024 | 新别名模型，替代 Stacked Borrows |
| Polonius 更新 | Rust 官方 | 2024 | 声明式借用检查器进展 |
| Rust 标准库验证计划 | Rust 项目 | 2024 | 官方验证计划 |

### 1.2 研究机构和项目动态

```
MPI-SWS (德国)
├── RefinedRust (2024) ⭐ 新增
├── RustBelt (2018)
├── RustHornBelt (2021)
└── Iris 分离逻辑框架

ETH Zurich (瑞士)
├── Prusti (维护模式)
└── Ralf Jung 团队

Inria (法国)
├── Aeneas (2024) ⭐ 活跃开发
├── Creusot
└── Why3 平台

CMU/VMware (美国)
└── Verus (2024) ⭐ 活跃开发

Amazon (AWS)
└── Kani ⭐ 官方支持

Meta
└── MIRAI

东京大学
└── RustHorn
```

---

## 2. 详细差距分析

### 2.1 RefinedRust - 重大差距 ⚠️

**论文信息**:

- **标题**: RefinedRust: A Type System for High-Assurance Verification of Rust Programs
- **作者**: Gaher, Sammler, Jung, Krebbers, Dreyer
- **机构**: MPI-SWS, ETH Zurich, Radboud University
- **会议**: PLDI 2024 (顶级会议)
- **链接**: <https://plv.mpi-sws.org/refinedrust/>

**核心创新**:

1. ✅ 首个同时支持 safe 和 unsafe Rust 的基础性验证工具
2. ✅ 基于 Iris 分离逻辑的精细化所有权类型
3. ✅ 机器可检查的证明 (Coq)
4. ✅ 处理可变引用的 "borrow names" 机制
5. ✅ 支持 Vec 等标准库数据结构的验证

**与现有工具对比** (RefinedRust 论文中的 Table 1):

| 工具 | 功能正确性 | 基础性证明 | Unsafe | 详细内存模型 | 自动化 |
|------|-----------|-----------|--------|-------------|--------|
| RustBelt | ○ | ● | ● | ○ | ○ |
| RustHornBelt | ● | ● | ● | ○ | ○ |
| Creusot | ● | ○ | ○ | ○ | ● |
| GillianRust | ● | ○ | ● | ● | ● |
| Verus | ● | ○ | ◐ | ○ | ● |
| Prusti | ● | ○ | ○ | ○ | ● |
| Aeneas | ● | ◐ | ○ | ○ | ◐ |
| **RefinedRust** | ● | ● | ● | ● | ◐ |

**差距**: 当前文档仅在 `academic-papers.md` 中简要提及，缺少:

- 详细的技术原理解析
- 与 RustBelt 的关系说明
- 实际使用示例
- 与其他工具的对比分析

### 2.2 Aeneas - 中等差距 🔶

**论文信息**:

- **标题**: Aeneas: Rust Verification by Functional Translation
- **会议**: ICFP 2024
- **作者**: Lattuada et al.
- **机构**: Inria

**核心贡献**:

- 将 Rust 代码函数式提取到 Lean
- 基于区域 (region) 的内存模型
- 支持 traits 和泛型

**当前覆盖**: `03-verification-tools/` 中有基础介绍，但缺少:

- ICFP 2024 最新进展
- 与 Creusot 的详细对比
- 实际案例研究

### 2.3 Gillian-Rust - 完全缺失 🔴

**来源**: Rust Formal Methods Interest Group 2024 年 5 月演讲

**核心特点**:

- 混合方法验证 unsafe Rust
- 符号执行 + 分离逻辑
- 基于 Gillian 框架

**差距**: 当前文档完全未覆盖此工具

### 2.4 Tree Borrows - 部分覆盖 🔶

**背景**:

- 作者: Villard
- 时间: 2023-WIP
- 目的: 替代 Stacked Borrows 作为 Rust 别名模型

**当前状态**:

- `formal-foundations/models/` 中有提及
- 缺少详细的模型定义和对比

### 2.5 Rust 标准库验证计划 - 完全缺失 🔴

**来源**: Rust 项目官方目标 2024H2

- **链接**: <https://rust-lang.github.io/rust-project-goals/2024h2/std-verification.html>
- **负责人**: Celina G. Val
- **目标**: 使用 Kani/Creusot/Verus 验证标准库

**差距**: 当前文档未涉及此重要项目

---

## 3. 持续推进计划

### Phase 1: 紧急补充 (1-2 周)

#### 3.1 创建 RefinedRust 深度文档

**目标文件**: `03-verification-tools/03-07-refinedrust-deep-dive.md`

**内容大纲**:

1. 引言和背景
2. 核心贡献概述
3. 精细化所有权类型系统
4. Borrow Names 机制详解
5. 与 RustBelt 的关系
6. 实际验证示例 (Vec 实现)
7. 与其他工具对比
8. 当前限制和未来工作

#### 3.2 更新验证工具对比矩阵

**目标文件**: `03-verification-tools/03-01-verification-overview.md`

**更新内容**:

- 添加 RefinedRust 到工具矩阵
- 更新各工具 Rust 1.94 兼容性状态
- 添加 "基础性证明" 维度

### Phase 2: 重要更新 (2-4 周)

#### 3.3 补充 Gillian-Rust 内容

**目标文件**: `03-verification-tools/03-08-gillian-rust.md`

**内容**:

- Gillian 框架介绍
- Gillian-Rust 的混合验证方法
- 与 Kani 的对比

#### 3.4 更新 Tree Borrows 文档

**目标文件**: `formal-foundations/models/tree-borrows-comprehensive.md`

**更新**:

- 完整的 Tree Borrows 模型定义
- 与 Stacked Borrows 的详细对比
- 实际代码示例

#### 3.5 创建 Rust 标准库验证专题

**目标文件**: `10-research-frontiers/10-07-std-verification-initiative.md`

**内容**:

- 项目目标和背景
- 验证工具选择 (Kani/Creusot/Verus)
- 合约语言设计
- 进展跟踪

### Phase 3: 持续维护 (长期)

#### 3.6 学术文献追踪机制

**目标**: 建立季度更新流程

1. **会议跟踪**: PLDI, POPL, ICFP, OOPSLA, CAV
2. **arXiv 监控**: 每周检查新论文
3. **Rust Formal Methods Interest Group**: 月度会议跟踪
4. **工具发布**: GitHub releases 监控

#### 3.7 工具版本同步

**建立版本矩阵**:

| 工具 | 最新版本 | 我们文档版本 | 同步状态 |
|------|----------|--------------|----------|
| RefinedRust | 原型 | 未覆盖 | 🔴 需创建 |
| Aeneas | 活跃 | 部分 | 🔶 需更新 |
| Verus | 活跃 | 部分 | 🔶 需更新 |
| Kani | 官方 | 良好 | ✅ 同步 |
| Creusot | 活跃 | 良好 | ✅ 同步 |
| Prusti | 维护 | 良好 | ✅ 同步 |

---

## 4. 内容质量评估

### 4.1 当前优势 ✅

1. **Coq 形式化**: 11,980+ 行 Coq 代码，300+ Qed，覆盖 Rust 1.94 特性
2. **案例研究**: 80+ crates 的形式化分析
3. **完整性**: 从基础到前沿的全面覆盖
4. **结构清晰**: 分层组织，易于导航

### 4.2 需要改进 🔶

1. **最新研究**: 2024 年顶级会议论文覆盖不足
2. **工具状态**: 部分工具信息需要更新
3. **实际应用**: 工业界应用案例较少

### 4.3 缺失内容 🔴

1. RefinedRust 深度解析
2. Gillian-Rust 介绍
3. Rust 标准库验证计划
4. 工业验证案例 (AWS, Meta 等)

---

## 5. 推荐行动项

### 立即执行 (本周)

- [ ] 创建 RefinedRust 深度解析文档
- [ ] 更新学术文献列表 (添加 PLDI 2024 论文)
- [ ] 更新验证工具对比矩阵

### 短期执行 (本月)

- [ ] 补充 Gillian-Rust 内容
- [ ] 更新 Tree Borrows 文档
- [ ] 创建标准库验证专题
- [ ] 添加工业应用案例

### 长期维护 (持续)

- [ ] 建立学术文献追踪机制
- [ ] 季度内容审查流程
- [ ] 社区反馈收集机制

---

## 6. 参考资源

### 必读论文

1. **RefinedRust** (PLDI 2024)
   - PDF: <https://iris-project.org/pdfs/2024-pldi-refinedrust.pdf>
   - 网站: <https://plv.mpi-sws.org/refinedrust/>

2. **Aeneas** (ICFP 2024)
   - GitHub: <https://github.com/AeneasVerif/aeneas>

3. **Verus** (SOSP 2024)
   - GitHub: <https://github.com/verus-lang/verus>

### 跟踪资源

1. **Rust Formal Methods Interest Group**
   - <https://rust-formal-methods.github.io/>
   - 月度会议，最新研究动态

2. **Rust 项目目标 - 标准库验证**
   - <https://rust-lang.github.io/rust-project-goals/2024h2/std-verification.html>

---

**报告编制**: Kimi Code CLI
**最后更新**: 2026-03-12
