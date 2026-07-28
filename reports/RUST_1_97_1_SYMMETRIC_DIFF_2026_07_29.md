> **内容分级**: [综述级]

# Rust 1.97.1 语义覆盖对称差分析报告

**EN**: Rust 1.97.1 Semantic Coverage — Symmetric Difference Analysis
**Summary**: 将 Rust 1.97.1 官方发布说明与项目 `concept/07_future/00_version_tracking/rust_1_97_1.md` 的语义论证覆盖进行对称差比较，确认无缺口，并提出可持续维护建议。

> **生成**: 2026-07-29
> **分析范围**: Rust 1.97.1 stable（2026-07-16）
> **权威来源**: [Announcing Rust 1.97.1 — Rust Blog](https://blog.rust-lang.org/2026/07/16/Rust-1.97.1/) · [rust-lang/rust#159035](https://github.com/rust-lang/rust/issues/159035) · [rust-lang/rust#159106](https://github.com/rust-lang/rust/pull/159106)

---

## 1. 官方语义集合（A）

Rust 1.97.1 官方公告明确包含以下语义点：

| # | 官方语义点 | 性质 |
|---:|---|---|
| A1 | 这是一个 **patch release**，不引入新语言特性、标准库 API 或 Cargo 功能 | 范围语义 |
| A2 | 修复一个 **LLVM 优化导致的误编译** | 正确性语义 |
| A3 | 采取**双重修复**：backport LLVM 修复 + 禁用 Rust 1.97.0 提高触发概率的生成 IR 变更 | 修复策略语义 |
| A4 | 该误编译根因自 **Rust 1.87 起即存在** | 影响范围语义 |
| A5 | 触发与 **enum discriminant -1 表示** 相关，在 x86-64 release 构建下可表现为 segfault | 触发机制语义 |

官方集合 **A = {A1, A2, A3, A4, A5}**。

---

## 2. 项目覆盖集合（B）

`concept/07_future/00_version_tracking/rust_1_97_1.md` 当前覆盖：

| # | 覆盖点 | 对应章节 |
|---:|---|---|
| B1 | 明确 1.97.1 为 patch release、无新特性、建议升级 | §1、§3 |
| B2 | 详细解释 LLVM **load-select 合并优化** bug：poison condition → UB dereference | §2.1 |
| B3 | 说明双重修复策略：LLVM backport + 回退 1.97.0 IR 变更 | §2.4 |
| B4 | 指出问题自 Rust 1.87 起潜伏 | §2.1、§3.1 |
| B5 | 分析 enum discriminant -1 表示如何触发 segfault（无符号偏移 2³²-1） | §2.2 |
| B6 | 提供 **最小复现（MRE）** 与 `rustc +1.97.0 -O` / `rustc +1.97.1 -O` 对比 | §2.5 |
| B7 | 讨论 safe Rust 语义保证与编译器正确性的关系 | §2.3、§5.5 |
| B8 | 给出 CI 验证清单、`rust-version` 同步建议 | §4 |
| B9 | 链接 LLVM IR poison/UB 语义权威页 | §6 |
| B10 | 引用 P0/P1/P2 国际权威来源（Rust Blog、GitHub issue/PR、LWN、byteiota） | §7 |

项目集合 **B ⊇ A**，并且在 A 的基础上增加了语义深度（poison/UB、MRE、safe Rust 保证、验证清单、国际来源）。

---

## 3. 对称差 A △ B

### 3.1 A \ B（官方有、项目无）

**无。** 官方公告中的 5 个核心语义点均已在项目权威页中覆盖。

### 3.2 B \ A（项目有、官方无）

这些属于项目为“可学习、可验证、可审计”而补充的上下文，不构成缺口：

- LLVM IR 层面 poison/UB 的精确语义推导
- 最小复现代码与编译命令
- 对 safe Rust 语义保证的批判性反思
- 企业/生产环境 CI 验证清单
- 与国际形式化语义页（`08_llvm_ir_poison_ub.md`）的交叉引用

---

## 4. 机器复核证据

```bash
python scripts/check_version_semantic_injection.py --strict
```

输出（2026-07-29）：

- 版本范围：1.90 – 1.97（含补丁 1.97.1）
- 提取特性数：74
- 已映射：74 / 74 = **100%**
- 补丁页双向链接完整：`rust_1_97_1.md` ✅

```bash
python scripts/check_concept_authority_coverage.py --strict --include-crates
```

输出（2026-07-29）：

- `rust_1_97_1.md` 命中 P0 官方来源（Rust Blog、GitHub rust-lang、Rust Reference）
- concept/ 内容页 any 覆盖率 100%，核心 L1-L4 无 P0 缺口

---

## 5. 后续可持续维护计划

| 优先级 | 任务 | 触发条件 | 负责人 |
|---:|---|---|---|
| P1 | 当 Rust 发布 1.97.2/1.98.0 时，复用本报告模板进行对称差分析 | 新版本发布 | 维护者 |
| P2 | 若 LLVM 上游发布关于 #208611 的更详细事后分析，补充到 `rust_1_97_1.md` §2.1 与 `08_llvm_ir_poison_ub.md` | 新权威来源出现 | 维护者 |
| P3 | 将 MRE 纳入 `scripts/check_concept_code_blocks.py` 的 nightly/版本回归抽样 | 代码块脚本升级 | 维护者 |
| P4 | 在 `concept/07_future/00_version_tracking/01_rust_version_tracking.md` 中维护补丁发布时间线 | 每季度 | 维护者 |

---

## 6. 结论

- **对称差为空**：Rust 1.97.1 的官方语义点已 100% 被项目权威页覆盖。
- **项目覆盖超过官方**：增加了形式化语义推导、可复现验证、安全语义反思与国际权威来源。
- **无需新增文件或修复**；按上述 P1–P4 计划持续监控即可。

---

*由 Kimi Code CLI 根据 `scripts/check_version_semantic_injection.py` 与 `scripts/check_concept_authority_coverage.py` 的实跑结果生成。*
