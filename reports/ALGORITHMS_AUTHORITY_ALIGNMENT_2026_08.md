# WS-B 算法与数据结构语义对齐表

**EN**: WS-B Algorithms and Data Structures Authority Alignment Report
**Summary**: Semantic alignment between local Rust algorithm concept pages and international authoritative sources (CLRS, Sedgewick, Rust Algorithm Club, Codeforces/AtCoder), documenting gaps closed during P7.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **日期**: 2026-08-04
> **工作流**: WS-B algorithms
> **治理依据**: AGENTS.md §2 Canonical、§3 去重、§4 命名与元数据、§5 质量门

---

## 一、国际化权威来源清单

| 领域 | 权威来源 | 本地对应位置 |
|:---|:---|:---|
| 算法教材 | [CLRS — *Introduction to Algorithms*, 4th ed.](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) | `concept/06_ecosystem/16_algorithm_patterns/` |
| 实现导向算法 | [Sedgewick & Wayne — *Algorithms*, 4th ed.](https://algs4.cs.princeton.edu/home/) | 同上 |
| Rust 算法实现 | [Rust Algorithm Club](https://rust-algo.club/) | 同上 |
| 竞赛编程模板 | [Codeforces Rust Guide](https://codeforces.com/blog/entry/93231) · [AtCoder Rust Resources](https://github.com/rust-lang-ja/atcoder-rust-resources) | `18_competitive_programming_idioms.md` |
| 形式语义 | [Oxide](https://arxiv.org/abs/1903.00982) · [RustBelt](https://doi.org/10.1145/3158154) | `concept/04_formal/` |

---

## 二、语义对齐表

| 维度 | 本地状态（P7 前） | 权威来源状态 | 差异 / 缺口 | 修复动作 |
|:---|:---|:---|:---|:---|
| **算法语义分类学** | `00_algorithm_patterns_overview.md` 已有模式目录，但缺少按求解策略与执行模型的显式分类学 | CLRS / Kleinberg & Tardos 按分治、贪心、DP、回溯、随机化、流式等系统分类 | 缺「求解策略 × 执行模型」二维坐标系 | 在 `00_algorithm_patterns_overview.md` 新增「算法语义分类学」章节，含矩阵、选型坐标系与 Rust 类型映射 |
| **计算等价视角** | 本地页给出迭代/递归代码示例，但未形式化「观察等价」概念 | 形式语义文献（Oxide、RustBelt）使用 operational / contextual equivalence | 缺迭代 vs 递归、尾递归 vs 循环、ADT 多实现等价的语义分析 | 在 `00_algorithm_patterns_overview.md` 新增「计算等价视角」章节，含证明草图、资源约束等价、正向/反向推理 |
| **经典数据结构覆盖** | `02_ownership_aware_data_structures.md` 覆盖并查集、线段树、Fenwick；链表/栈/队列/堆/B-树/跳表/Trie 缺少集中权威页 | CLRS / Sedgewick / Rust Algorithm Club 均覆盖上述全部结构 | 缺线性表、堆、B-树、跳表、Trie 的所有权感知实现与 `no_std` 适配 | 新建 `08_data_structures_in_rust.md`，覆盖链表/栈/队列/堆/B-树/跳表/Trie，并对并查集/线段树/Fenwick 给出 canonical 链接而非复制正文 |
| **竞赛编程惯用法** | 本地无专门页 | Codeforces/AtCoder 社区积累快读、快写、宏模板、题型模式 | 缺快读快写、宏模板、输入解析、题型模式 | 新建 `18_competitive_programming_idioms.md`，含 `FastInput`、`BufWriter`、`read!`/`out!`/`rep!` 宏、图/网格解析、前缀和/双指针/二分/BFS/DP/位运算/线段树模式 |
| **`no_std` 数据结构** | 仅在嵌入式页零星提及 | Embedded Rust / `alloc` 生态要求 `no_std` 算法可用 | 缺 `no_std` 下 `Vec`/`Box`/`BinaryHeap` 的使用示例与限制说明 | 在 `08_data_structures_in_rust.md` 新增「`no_std` 适配」节，给出可编译的 `#![no_std]` 栈示例 |
| **代码块可编译性** | 新增前无此内容 | 权威来源示例多为伪代码或特定在线评测框架 | 新增 Rust 代码需通过本地编译验证 | 所有新增/修改 `rust` 块均经 `rustc --edition 2024` 验证；依赖上下文或外部输入的块标注 `ignore`，失败示例标注 `compile_fail` / `should_panic` |
| **文件编号唯一性** | P7 计划建议新建 `02_data_structures_in_rust.md`，但目录已存在 `02_ownership_aware_data_structures.md` | AGENTS.md §4.0 要求同目录禁同号 | 编号冲突 | 按 AGENTS.md 使用空闲号 `08` 与下一个连续号 `18`，并在本表记录偏差原因 |

---

## 三、新增 / 修改文件列表

| 路径 | 动作 | 说明 |
|:---|:---|:---|
| `concept/06_ecosystem/16_algorithm_patterns/00_algorithm_patterns_overview.md` | 增强 | 新增「算法语义分类学」与「计算等价视角」两节，更新思维导图与章节编号 |
| `concept/06_ecosystem/16_algorithm_patterns/08_data_structures_in_rust.md` | 新建 | Rust 经典数据结构语义分析与 `no_std` 适配；含链表/栈/队列/堆/B-树/跳表/并查集/线段树/树状数组/Trie |
| `concept/06_ecosystem/16_algorithm_patterns/18_competitive_programming_idioms.md` | 新建 | 快读快写、宏模板、输入解析、题型模式、反例、决策树 |
| `concept/06_ecosystem/11_domain_applications/09_data_structures_in_rust.md` | 改为重定向 stub | 因与新建 `08_data_structures_in_rust.md` 主题重复，按 AGENTS.md §2/§3 转为 canonical 重定向 stub |
| `concept/SUMMARY.md` | 更新 | 在 `16_algorithm_patterns` 下注册 `08` 与 `18` 两个新条目 |
| `reports/ALGORITHMS_AUTHORITY_ALIGNMENT_2026_08.md` | 新建 | 本对齐表 |

---

## 四、去重与 Canonical 声明

- 新增 `08_data_structures_in_rust.md` 在涉及并查集、线段树、树状数组时，**未复制** `02_ownership_aware_data_structures.md` 的完整正文，而是提供选型语义矩阵并链接到 canonical 页。
- 新建前运行 `python scripts/detect_content_overlap.py`，未发现与现有文件的主题级重复。
- `00_algorithm_patterns_overview.md` 新增的算法分类学与 `01_algorithmic_paradigms.md` 保持分工：前者提供高维选型坐标，后者提供范式级实现目录；两者通过链接互引，避免正文重复。
- `check_canonical_uniqueness.py --strict` 发现已存在的 `11_domain_applications/09_data_structures_in_rust.md` 与新建 `08_data_structures_in_rust.md` 主题重复（文件名词干相同）。按 AGENTS.md §2/§3，将前者改为重定向 stub，指向后者作为唯一权威页。

---

## 五、代码块验证摘要

| 文件 | 可编译 std 块数 | `ignore` / `nostd` 块数 | 失败标注块数 | 结果 |
|:---|:---:|:---:|:---:|:---|
| `08_data_structures_in_rust.md` | 11 | 3 (`ignore`) + 1 (`nostd`) | 2 `should_panic` + 1 `compile_fail` | ✅ 全部符合预期 |
| `18_competitive_programming_idioms.md` | 13 | 5 (`ignore`) | 1 `should_panic` + 1 `compile_fail` | ✅ 全部符合预期 |
| `00_algorithm_patterns_overview.md`（新增部分） | 3 | 0 | 0 | ✅ 全部通过 |

验证命令示例：

```bash
rustc --edition 2024 -o /tmp/out /tmp/snippet.rs
```

> 完整文件级验证可通过 `python scripts/check_concept_code_blocks.py --strict --sample 0` 执行；由于本报告仅覆盖 WS-B 新增内容，上述摘要来自对新增块的独立编译测试。

---

## 六、命名规范说明

P7 计划建议新建 `02_data_structures_in_rust.md`，但 `concept/06_ecosystem/16_algorithm_patterns/` 已存在 `02_ownership_aware_data_structures.md`。根据 AGENTS.md §4.0「同目录禁同号」，采用以下编号：

- `08_data_structures_in_rust.md`（使用目录中空闲的 `08` 号）
- `18_competitive_programming_idioms.md`（`17` 之后的下一个连续号）

`concept/SUMMARY.md` 已同步更新。

---

## 七、后续建议

1. **形式语义深化**：`00_algorithm_patterns_overview.md` 中的「计算等价」目前为半形式化草图；后续可由 WS-F 在 `concept/04_formal/08_algorithm_semantics/05_algorithm_equivalence.md` 中补全操作语义定义。
2. **KG 刷新**：新增页涉及「链表」「B-树」「跳表」「Trie」「快读」「宏模板」等新实体，建议在集成阶段运行 `scripts/generate_kg_v3.py` 与 `apply_kg_semantic_predicates.py`，确保 KG 规模与谓词精度达标。
3. **依赖块实测**：`18_competitive_programming_idioms.md` 中部分 `ignore` 块依赖 `FastInput` 定义；若后续转为 `check_concept_code_blocks.py` 的依赖块机制，可标注 `dep` 并配置 crate 上下文。

---

> **文档版本**: 1.0 ｜ **最后更新**: 2026-08-04 ｜ **状态**: ✅ WS-B 完成
