# 语义全领域对齐与国际权威内容补全计划

**EN**: Semantic Alignment & International Authority Coverage Plan for the Rust Knowledge Base
**Summary**: A phased plan to audit all semantic domains in `concept/`, identify gaps against the latest international authoritative sources (Rust 1.97.1 / Edition 2024), and align/extend content while preserving canonical uniqueness and quality gates.

> **Rust 版本**: 1.97.1 (Edition 2024) — latest stable patch as of 2026-07-16 ([Rust vs Go](http://rustvsgo.com/tooling/), [releases.rs](https://releases.rs/docs/1.97.0/))
> **权威来源基线**: [The Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [The Rustonomicon](https://doc.rust-lang.org/nomicon/), [Rust By Example](https://doc.rust-lang.org/rust-by-example/), [The Embedded Rust Book](https://docs.rust-embedded.org/book/), [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

## 1. 当前状态

- PDF 编译任务已暂停（`book/rust-concept-knowledge-base.pdf` 未最终生成），等待语义对齐任务确认后再决定继续或拆分输出。
- `concept/` 目录已覆盖 L0–L7 多层架构，但在以下语义域存在明显缺口或与 1.97.1 不完全对齐：
  - `no_std` / 裸机 / 嵌入式系统语义
  - Rust 惯用法（Idioms）体系化梳理
  - 算法模式与数据结构在 Rust 中的语义表达
  - 设计模式与架构模式（企业架构、系统架构语义）
  - 形式语义工程（计算语义模型、并发/异步/分布式语义）

---

## 2. 语义领域清单与缺口（基于 `concept/` 目录）

| 层级 | 目录 | 已覆盖主题 | 主要缺口 / 对齐需求 |
|------|------|-----------|-------------------|
| L0–L1 | `00_meta/` | 元框架、术语、来源、审计、导航 | 术语表需对齐最新 RFC / Reference 定义；国际化来源索引需补全 1.97.1 特性 |
| L1 | `01_foundation/` | 所有权、类型系统、控制流、集合、字符串、模块、错误、宏、测试 | 部分页仍基于旧版本示例；需补全 `NonZero`/`bit_width` 等 1.97 API；惯用法小节不系统 |
| L2 | `02_intermediate/` | Trait、泛型、内存、类型转换、模块、宏、迭代器 | 缺少“惯用法”专门系列；GAT / TAIT 与最新 Reference 对齐 |
| L3 | `03_advanced/` | 并发、异步、unsafe、过程宏、FFI、内联汇编 | 异步取消安全、Send/Sync 边界、FFI+async 交叉域需补全 |
| L4 | `04_formal/` | 类型论、所有权逻辑、分离逻辑、操作语义、模型检测、rustc 内部 | 计算语义模型、并发模型、算法语义、系统/架构语义、语义工程需补充国际来源 |
| L5 | `05_comparative/` | 范式对比、系统语言、托管语言、领域对比 | 需加入 Rust 1.97 与 C/C++/Go/Swift 的新特性对比 |
| L6 | `06_ecosystem/` | 工具链、Cargo、core crates、设计模式、Web、系统/嵌入式、数据/分布式、安全、FVV、测试、性能、领域应用、企业架构 | **设计模式/架构模式/惯用法/算法模式缺口最大**；`no_std` 嵌入式深度不够；企业架构语义零散 |
| L7 | `07_future/` | 版本跟踪、Edition 路线图、预览特性、研究实验 | 1.97.1 补丁页与语义注入双向链接需补全 |

---

## 3. 权威来源清单（国际化 + 最新）

1. **语言规范**: [The Rust Reference](https://doc.rust-lang.org/reference/) — 语义对齐的首要权威。
2. **学习主线**: [The Rust Programming Language](https://doc.rust-lang.org/book/) — 概念解释与示例。
3. **Unsafe / 底层**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)。
4. **嵌入式 / no_std**: [The Embedded Rust Book](https://docs.rust-embedded.org/book/)，[no-std 章节](https://docs.rust-embedded.org/book/intro/no-std.html)，[awesome-embedded-rust](https://github.com/rust-embedded/awesome-embedded-rust)。
5. **设计模式与惯用法**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)，[Idioms 章节](https://rust-unofficial.github.io/patterns/idioms/)，[GitHub 仓库](https://github.com/rust-unofficial/patterns)。
6. **版本特性**: [Rust 1.97.0 release notes](https://releases.rs/docs/1.97.0/)，[Rust vs Go 1.97 解读](http://rustvsgo.com/tooling/)，[byteiota Rust 1.97 分析](https://byteiota.com/rust-1-97-v0-symbol-mangling-default-and-pin-fix/)。
7. **算法 / 系统语义**: 学术来源（PLDI、POPL、OOPSLA Rust 相关论文）、Rust Reference / rustc-dev-guide。

---

## 4. 对称差与缺口分析（待执行）

执行以下脚本得到量化基线：

```bash
# 1. 权威覆盖缺口（concept/ 内容页 vs 权威来源）
python scripts/check_concept_authority_coverage.py --strict --include-crates

# 2. 版本语义注入双向链接
python scripts/check_version_semantic_injection.py --strict

# 3. 交叉/边界语义域覆盖
python scripts/check_cross_domain_coverage.py --strict

# 4. 内容重叠与伪 stub
python scripts/detect_content_overlap_v2.py --budget 999999
python scripts/triage_overlap.py
python scripts/check_stub_purity.py --strict

# 5. 代码块编译实测
python scripts/check_concept_code_blocks.py --strict --sample 0 --with-deps

# 6. 命名与元数据
python scripts/check_naming_convention.py --strict
python scripts/check_metadata_consistency.py --strict
```

---

## 5. 分阶段执行计划

### Phase 0 — 基线审计（1 轮）

- [ ] 运行 §4 全部脚本，输出 `reports/SEMANTIC_ALIGNMENT_BASELINE_2026_08_02.md`。
- [ ] 按语义领域分类汇总缺口：P0（阻塞/概念错误）、P1（权威来源缺失）、P2（示例/反例缺失）。
- [ ] 建立 `concept/SEMANTIC_ALIGNMENT_TRACKING.md` 追踪表。

### Phase 1 — 缺失语义域补全（优先级最高）

- [ ] **no_std / 裸机 / 嵌入式**：在 `concept/03_advanced/` 或 `concept/06_ecosystem/05_systems_and_embedded/` 创建权威页，覆盖 `no_std`、自定义 allocator、bare-metal、中断/异常模型、rtic/embassy 对比。
- [ ] **Rust 惯用法（Idioms）**：在 `concept/06_ecosystem/03_design_patterns/` 新建 `NN_idioms/` 系列，对齐 [Rust Design Patterns Idioms](https://rust-unofficial.github.io/patterns/idioms/)。
- [ ] **算法与数据结构模式**：在 `concept/06_ecosystem/11_domain_applications/` 或新建 `concept/06_ecosystem/16_algorithms_patterns/` 覆盖迭代器算法、零拷贝结构、并发数据结构。
- [ ] **设计模式 / 架构模式**：整理 `06_ecosystem/03_design_patterns/` 现有内容，补充企业架构、微服务、事件驱动、插件架构等 Rust 实现。
- [ ] **形式语义工程**：扩展 `04_formal/13_semantic_engineering/` 与 `04_formal/11_computational_models/`，加入计算等价、形式语言、数学函数语义、并发/异步/分布式计算模型。

### Phase 2 — 现有权威页对齐 1.97.1

- [ ] 扫描所有 `concept/` 文件中的 `Rust 版本` 声明，统一为 `1.97.0+ (Edition 2024)`；涉及 1.97.1 补丁的单独标注。
- [ ] 更新 1.97 稳定特性页：`v0 symbol mangling` 默认、`build.warnings`、`resolver.lockfile-path`、整数位操作 API、`pin!` soundness fix 等。
- [ ] 为每个新增/更新页添加 **EN** 标题、**Summary**、Bloom 层级、权威来源声明。
- [ ] 补充 `mindmap` 与反例节，满足 `check_mindmap_coverage.py`。

### Phase 3 — 交叉域与链接修复

- [ ] 补全 async+unsafe、FFI+async、Send/Sync boundaries、Pin+lifetimes 等交叉域权威页或链接。
- [ ] 修复 `mdbook-pandoc` 警告中的相对链接错误（`../crates/`、`../exercises/` 等）。
- [ ] 确保新增内容通过 `detect_content_overlap_v2.py` 和 `check_canonical_uniqueness.py`。

### Phase 4 — 验证与质量门

- [ ] 运行 23 项阻断质量门（用户已同意不做阻断门/钩子会阻碍推进，但仍作为验证手段）。
- [ ] 输出 `reports/SEMANTIC_ALIGNMENT_VERIFICATION_2026_08_02.md`。

### Phase 5 — 持续同步机制

- [ ] 每 Rust 新版本发布时，按 AGENTS.md §7 Patch Release 响应流程更新。
- [ ] 每月运行 `check_version_semantic_injection.py`、`check_cross_domain_coverage.py`、`check_stub_purity.py`。

---

## 6. 任务清单（可并行）

| # | 任务 | 目标文件/目录 | 负责人 | 阻塞门 |
|---|------|--------------|--------|--------|
| 1 | 运行基线审计脚本集 | `reports/SEMANTIC_ALIGNMENT_BASELINE_*.md` | AI | 无 |
| 2 | 创建 no_std / 裸机权威页 | `concept/03_advanced/05_no_std_bare_metal.md` 等 | AI | canonical、命名 |
| 3 | 创建 Rust 惯用法系列 | `concept/06_ecosystem/03_design_patterns/NN_idioms_*.md` | AI | overlap、stub |
| 4 | 创建算法模式页 | `concept/06_ecosystem/16_algorithms_patterns/` | AI | canonical、命名 |
| 5 | 扩展设计模式/架构模式 | `concept/06_ecosystem/03_design_patterns/`、`06_ecosystem/14_enterprise_architecture/` | AI | overlap、stub |
| 6 | 扩展形式语义工程 | `concept/04_formal/13_semantic_engineering/`、`04_formal/11_computational_models/` | AI | canonical、命名 |
| 7 | 对齐 Rust 1.97.1 特性 | `concept/07_future/00_version_tracking/` 及相关页 | AI | version injection |
| 8 | 修复相对链接与 mdbook-pandoc 警告 | 全 `concept/` | AI | kb_auditor |
| 9 | 代码块编译实测修复 | 涉及新增/修改页 | AI | code blocks gate |
| 10 | 质量门验证报告 | `reports/SEMANTIC_ALIGNMENT_VERIFICATION_*.md` | AI | 全部 23 门 |

---

## 7. 决策点（待您确认）

1. **是否继续 PDF 编译**？PDF 当前停留在 chunk1 渲染（已暂停）。建议：待语义对齐完成后再生成最终 PDF，避免重复编译。
2. **Phase 1 优先级排序**：建议按 `no_std/嵌入式 > 惯用法 > 算法模式 > 设计/架构模式 > 形式语义工程` 推进，是否与您的预期一致？
3. **是否一次性补全全部缺失域，还是先聚焦 3–5 个核心域**？推荐先聚焦核心域，确认后再扩展。
4. **质量门执行深度**：建议保留脚本验证但不做为阻塞提交（与此前一致），是否同意？

---

## 8. 风险与约束

- **范围风险**：语义领域极广，一次性 100% 覆盖不现实；本计划按优先级分阶段交付。
- **Canonical 约束**：新增通用 Rust 概念必须进入 `concept/`，`knowledge/`/`docs/`/`content/` 只做 stub/摘要，避免重复。
- **质量门约束**：新增内容需通过 `detect_content_overlap_v2.py`、`check_canonical_uniqueness.py`、`check_metadata_consistency.py`。

---

*Plan drafted: 2026-08-02. Next step: await user confirmation on priorities and scope before execution.*
