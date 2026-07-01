# 权威来源自动补全计划 {#权威来源自动补全计划}

> **概念族**: 权威来源对齐 / 补全计划
> **内容分级**: [核心级]
> **层级**: L0-L7
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [权威来源自动补全计划 {#权威来源自动补全计划}](#权威来源自动补全计划-权威来源自动补全计划)
  - [目录 {#目录}](#目录-目录)
  - [一、背景与目标 {#一背景与目标}](#一背景与目标-一背景与目标)
  - [二、当前覆盖率状态 {#二当前覆盖率状态}](#二当前覆盖率状态-二当前覆盖率状态)
  - [三、P0/P1/P2 缺口最大的概念族 TOP 10 {#三p0p1p2-缺口最大的概念族-top-10}](#三p0p1p2-缺口最大的概念族-top-10-三p0p1p2-缺口最大的概念族-top-10)
  - [四、`suggest_authoritative_sources.py` 使用说明 {#四suggest\_authoritative\_sourcespy-使用说明}](#四suggest_authoritative_sourcespy-使用说明-四suggest_authoritative_sourcespy-使用说明)
    - [功能 {#功能}](#功能-功能)
    - [命令行用法 {#命令行用法}](#命令行用法-命令行用法)
    - [输出示例 {#输出示例}](#输出示例-输出示例)
  - [五、下一阶段补全优先级 {#五下一阶段补全优先级}](#五下一阶段补全优先级-五下一阶段补全优先级)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、背景与目标 {#一背景与目标}

本文档是 `docs/research_notes/` [权威来源对齐网络](10_authoritative_source_alignment_network.md)的持续改进计划。目标是通过自动化建议工具，系统性地发现并补齐研究笔记中 P0 官方、P1 学术、P2 社区三个层级的权威来源缺口，确保每个核心概念族都有可追溯、可验证的国际化权威来源支撑。

---

## 二、当前覆盖率状态 {#二当前覆盖率状态}

根据 `scripts/maintenance/authority_coverage_dashboard.py` 对 `docs/research_notes/` 全部 309 篇 Markdown 文件的扫描结果：

| 指标 | 计数 | 比例 |
|------|-----:|-----:|
| 含 P0 官方来源 | 308 | 99.7% |
| 含 P1 学术来源 | 233 | 75.4% |
| 含 P2 社区来源 | 250 | 80.9% |
| 同时含 P0+P1+P2 | 204 | 66.0% |
| 缺少权威来源标记 | 0 | - |

当前 **P0 官方来源覆盖率已接近 100%**，主要缺口集中在 **P1 学术/形式化来源** 与 **P2 社区/生态来源**。具体而言：

- **P0**：仅 1 个文件缺少官方来源，可快速补齐。
- **P1**：76 个概念族文件缺少学术/形式化来源，重点分布在 Crate 架构、形式化模块、边界系统、速查卡等概念族。
- **P2**：59 个概念族文件缺少社区/生态来源，重点分布在形式化模块、软件设计、学习资源等领域。

---

## 三、P0/P1/P2 缺口最大的概念族 TOP 10 {#三p0p1p2-缺口最大的概念族-top-10}

按 `P0×100 + P1×10 + P2` 综合缺口服分排序，当前最需要补全的 10 个概念族如下：

| 排名 | 概念族 | 文件总数 | P0 缺口 | P1 缺口 | P2 缺口 | 主要推荐来源 |
|-----:|--------|---------:|--------:|--------:|--------:|--------------|
| 1 | 软件设计 / Crate 架构 | 22 | 0 | 20 | 0 | Rust API Guidelines、Rust Design Patterns、RustBelt |
| 2 | 形式化模块 | 7 | 0 | 4 | 6 | RFC 2126、Rust Reference Modules、RustBelt |
| 3 | 软件设计 / 边界系统 | 4 | 0 | 3 | 2 | Rust Reference、RustBelt、Rust Design Patterns |
| 4 | 速查卡 | 4 | 0 | 2 | 1 | Rust Reference、RustBelt、Rust Design Patterns |
| 5 | 形式化方法 | 24 | 0 | 1 | 2 | Rust Reference、RustBelt、Rust Design Patterns |
| 6 | 运维 / 链接审计 | 1 | 0 | 1 | 1 | Rust Reference、RustBelt、Rust Design Patterns |
| 7 | 权威来源对齐 / 行号锚点 | 1 | 0 | 1 | 1 | Rust Reference、RustBelt、Rust Design Patterns |
| 8 | 形式化模块 / 反例边界 | 1 | 0 | 1 | 1 | RFC 2126、Rust Reference Modules、RustBelt |
| 9 | 形式化模块 / 代码实践 | 1 | 0 | 1 | 1 | RFC 2126、Rust Reference Modules、RustBelt |
| 10 | 形式化方法 / 宏系统 | 1 | 0 | 1 | 1 | Rust Reference、RustBelt、Rust Design Patterns |

> 注：以上数据由 `suggest_authoritative_sources.py` 扫描生成，随文档更新而变化。P0 缺口权重最高，但当前 P0 已基本补全，因此 TOP 10 主要由 P1 缺口驱动。

---

## 四、`suggest_authoritative_sources.py` 使用说明 {#四suggest_authoritative_sourcespy-使用说明}

新脚本 `scripts/maintenance/suggest_authoritative_sources.py` 用于自动生成权威来源补全建议。

### 功能 {#功能}

- 递归读取 `docs/research_notes/` 下所有 Markdown 文件。
- 按 `概念族` 元信息分组。
- 对每个文件检测已覆盖的 P0/P1/P2 层级，列出缺少的层级。
- 根据概念族关键词匹配推荐权威来源链接（如所有权/借用、类型系统、并发/异步、unsafe/FFI/内存、模块、设计模式、Crate 架构、数据库/云原生、CI/CD/供应链、性能/测试、学习/面试等）。
- 输出 Markdown 报告，包含每个概念族下缺少各层级的文件及推荐链接。
- 信息性工具，退出码始终为 0。

### 命令行用法 {#命令行用法}

```bash
# 直接打印报告到标准输出 {#直接打印报告到标准输出}
python scripts/maintenance/suggest_authoritative_sources.py

# 将报告写入指定 Markdown 文件 {#将报告写入指定-markdown-文件}
python scripts/maintenance/suggest_authoritative_sources.py --output=suggestions.md
```
### 输出示例 {#输出示例}

```markdown
### 形式化模块 {#形式化模块}

**检测关键词**：模块

**推荐权威来源**：
- **P0**：[RFC 2126](https://rust-lang.github.io/rfcs/2126-path-clarity.html)；[Rust Reference Modules](https://doc.rust-lang.org/reference/items/modules.html)
- **P1**：[RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)

**缺口文件数**：4 / 7

| 文件 | 缺少层级 | 建议补充来源 |
|------|----------|--------------|
| `docs/research_notes/formal_modules/10_module_system_specification.md` | P1 | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) |
```
---

## 五、下一阶段补全优先级 {#五下一阶段补全优先级}

基于当前覆盖率与缺口分布，下一阶段补全按以下优先级推进：

| 优先级 | 行动项 | 目标概念族 | 预计产出 |
|--------|--------|------------|----------|
| P0 | 补齐唯一缺少 P0 的文件 | 权威来源对齐 / 版本跟踪 | P0 覆盖率达到 100% |
| P1 | 为 Crate 架构族补充学术/形式化来源 | 软件设计 / Crate 架构 | 10+ 个文件新增 RustBelt / RustSEM / RFC 引用 |
| P1 | 补齐形式化模块的学术来源 | 形式化模块、形式化模块 / 反例边界、形式化模块 / 代码实践 | 引用 RFC 2126、Rust Reference Modules、RustBelt |
| P1 | 补齐边界系统与速查卡的学术来源 | 软件设计 / 边界系统、速查卡 | 引用 Rust Reference、RustBelt |
| P2 | 补齐形式化模块与软件设计的社区来源 | 形式化模块、软件设计 / 边界系统 | 引用 Rust Design Patterns、Rust API Guidelines |
| P2 | 补齐学习资源与链接审计的社区来源 | 学习资源、运维 / 链接审计 | 引用 Rustlings、Rust Design Patterns |
| P3 | 持续运行自动化脚本 | 全量 docs/research_notes | 每月生成一次补全建议报告 |

补全原则：

1. **P0 优先**：任何缺少 P0 官方来源的文件应优先补齐，确保概念定义有官方规范支撑。
2. **P1 次之**：形式化/学术来源为定理、证明、语义模型提供背书，特别针对所有权、借用、类型系统、模块等核心概念族。
3. **P2 再次**：社区/生态来源补充实战工具、crate、最佳实践，提升工程落地性。
4. **按需推荐**：使用 `suggest_authoritative_sources.py` 生成建议后，由维护者人工审核链接与内容相关性，避免机械堆砌 URL。

---

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [权威来源对齐缺口分析](10_authoritative_alignment_gap_analysis.md)
- [权威来源版本跟踪表](10_authoritative_source_version_tracking.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [研究笔记完整索引](INDEX.md)

## 社区权威参考 {#社区权威参考}

- [This Week in Rust](https://this-week-in-rust.org/)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust 中文社区](https://rustcc.cn/)
