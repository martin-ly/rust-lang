# Rust 分层概念知识体系 — 深度对齐审计与批判性评估报告

> **审计日期**: 2026-05-29
> **审计基准**: Rust 1.96.0 stable (2026-05-28) / Edition 2024 / nightly 1.98.0
> **对标资源**: GitHub rust-lang/rust #156512 (Official Release Notes), releases.rs, doc.rust-lang.org, Cargo 1.96 CHANGELOG, Rust Project Goals 2026
> **审计性质**: 基于网络权威资源的独立交叉验证，聚焦**事实准确性**与**教育有效性**

---

## 执行摘要

本项目（Rust 分层概念知识体系 v1.2）在技术工程化层面（CI、Miri、自动化脚本、Bloom 标注）已达极高水准，但在**Rust 版本特性事实准确性**上存在**系统性错误**。
经过与官方 Release Notes、releases.rs、GitHub rust-lang/rust 等权威来源的逐条交叉验证，发现：

1. **严重事实错误**：将 `assert_matches!` 错误标注为 "Rust 1.77 稳定"（实际为 **1.96**）
2. **系统性版本号错位**：将 **1.68.0**（2023-03）已稳定的 `From<bool> for f32/f64`、`VecDeque::new const` 错误包装为 "1.96 新特性"
3. **Preview 文档严重失真**：1.96 preview 文档中列出的 6 项"候选特性"（`truncate_front`、`int_format_into`、`RefCell::try_map`、`cargo script frontmatter`、`proc_macro_value`）**均未进入 1.96 stable**，但文档声称"所有上述特性在 1.96 已稳定，无需 nightly"
4. **代码与声明脱节**：MSRV 已声明 1.96，但 `assert_matches!` 示例仍被 `#[cfg(feature = "nightly")]` 锁定，注释称"暂用 assert!(matches!()) 等价替代"

这些问题表明，项目的"版本对齐"目前停留在**批量替换版本号字符串**的层面，而非**语义层面的准确性验证**。
对于声称"100% Bloom 覆盖、0 死链接、权威来源对齐"的知识库而言，版本事实错误是**信誉级风险**。

---

## 第一部分：权威来源对齐验证

### 1.1 Rust 1.96.0 官方实际发布内容

**来源**: [GitHub rust-lang/rust #156512](https://github.com/rust-lang/rust/issues/156512) | [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/) | [Cargo 1.96 CHANGELOG](https://doc.rust-lang.org/beta/cargo/CHANGELOG.html)

| 特性 / API | 官方稳定版本 | 项目标注版本 | 审计结论 |
|:---|:---|:---|:---:|
| `assert_matches!` / `debug_assert_matches!` | **1.96.0** (2026-05-28) | 1.77.0 (`concept/` 文件) / 1.96.0 (`crates/` 文件，但代码未启用) | 🔴 **严重错误** |
| `core::range::Range` + `RangeIter` | **1.96.0** | 1.95.0 (部分) / 1.96.0 (部分) | 🟡 部分正确 |
| `core::range::RangeFrom` + `RangeFromIter` | **1.96.0** | 1.96.0 (`rust_196_features.rs`) | ✅ 正确 |
| `core::range::RangeToInclusive` + `RangeToInclusiveIter` | **1.96.0** | 1.95.0 (`rust_195_features.rs`) | 🟡 归属错位 |
| `From<T>` for `AssertUnwindSafe<T>` | **1.96.0** | 未在核心文档中明确覆盖 | ⚠️ 缺失 |
| `From<T>` for `LazyCell<T, F>` / `LazyLock<T, F>` | **1.96.0** | 未覆盖 | ⚠️ 缺失 |
| NonZero 整数范围迭代 (`Step` trait) | **1.96.0** | 1.96.0 (`rust_196_features.rs`) | ✅ 正确 |
| `ManuallyDrop` 常量作为模式 | **1.96.0** | 未确认覆盖 | ⚠️ 待查 |
| `expr` metavariable to `cfg` | **1.96.0** | 未确认覆盖 | ⚠️ 待查 |
| Never 类型在 tuple 中强制转换 | **1.96.0** | nightly-only (`rust_196_features.rs`) | 🟡 标注错误 |
| `From<bool> for f32/f64` | **1.68.0** (2023-03) | 1.96.0 (多个 `crates/*/rust_196_features.rs`) | 🔴 **严重错误** |
| `VecDeque::new` const | **1.68.0** (2023-03) | 1.96.0 (`rust_196_features.rs`) | 🔴 **严重错误** |
| `VecDeque::truncate_front` | **未进入 1.96** | 1.96 (`05_rust_1_96_preview.md`) | 🔴 **严重错误** |
| `int_format_into` / `NumBuffer` | **未进入 1.96** | 1.96 (`05_rust_1_96_preview.md`) | 🔴 **严重错误** |
| `RefCell::try_map` / `RefMut::try_map` | **未进入 1.96** (nightly) | 1.96 (`05_rust_1_96_preview.md`) | 🔴 **严重错误** |
| `cargo script` frontmatter | **非 1.96 新特性** | 1.96 (`05_rust_1_96_preview.md`) | 🔴 **概念错误** |
| `proc_macro_value` | **未进入 1.96** | 1.96 (`05_rust_1_96_preview.md`) | 🔴 **严重错误** |

### 1.2 错误影响分析

#### 🔴 级别错误（严重）

**错误 A: `assert_matches!` 版本号根本性错误**

- **位置**: `concept/02_intermediate/05_assert_matches.md` 第 12、88、113、118、362、405、410、413、454 行
- **错误内容**: 文档明确声明 "Rust 1.77 稳定化 `assert_matches!`"，并在来源列表中引用 `[Rust 1.77 Release Notes](https://releases.rs/docs/1.77.0/)`
- **官方事实**: [releases.rs/1.77.0](https://releases.rs/docs/1.77.0/) 中**没有任何关于 `assert_matches!` 的内容**。1.77 的关键特性是 `pin!` 宏、`atomic_from_ptr`、`impl DerefMut for PathBuf` 等。`assert_matches!` 直到 **1.96.0 (2026-05-28)** 才稳定。
- **学习者影响**: 信任此文档的学习者在 Rust 1.77-1.95 环境中使用 `assert_matches!` 将遭遇编译失败，严重损害知识库的**可信度**。
- **根因推测**: 该文档可能混淆了 `matches!`（1.42 稳定）与 `assert_matches!`（1.96 稳定），或误信了非官方来源的传闻。

**错误 B: 将 1.68.0 旧特性包装为 1.96 新特性**

- **位置**:
  - `crates/c02_type_system/src/rust_196_features.rs` 第 22 行
  - `crates/c10_networks/src/rust_196_features.rs`
  - `crates/c12_wasm/src/rust_196_features.rs`
  - `crates/c13_embedded/src/rust_196_features.rs`
- **错误内容**: 均声称 "Rust 1.96.0 稳定了 `impl From<bool> for f32` 和 `impl From<bool> for f64`"
- **官方事实**: [releases.rs/1.68.0](https://releases.rs/docs/1.68.0/) 明确列出 `impl From<bool> for {f32,f64}` 为 1.68.0 的 Stabilized API。该特性已稳定 **超过 3 年**。
- **学习者影响**: 将 3 年前的旧特性当作"最新稳定功能"学习，误导学习者对 Rust 演进节奏的认知。

**错误 C: `VecDeque::new` const 版本号错误**

- **位置**: `crates/c02_type_system/src/rust_196_features.rs` 第 66 行
- **错误内容**: "Rust 1.96.0 使 `VecDeque::new` 可在 `const` 上下文中调用"
- **官方事实**: [releases.rs/1.68.0](https://releases.rs/docs/1.68.0/) 的 "const contexts" 部分明确列出 `VecDeque::new`。该特性同样已稳定 3 年。

**错误 D: 1.96 Preview 文档的虚假声明**

- **位置**: `knowledge/06_ecosystem/emerging/05_rust_1_96_preview.md` 和 `docs/06_toolchain/06_19_rust_1_96_features.md`
- **错误内容**:
  - 声称 `VecDeque::truncate_front`、`int_format_into`、`RefCell::try_map`、`proc_macro_value` 为 "1.96 已稳定"
  - 声称 "所有上述特性在 1.96 已稳定，无需 nightly 编译器和 feature gate"
  - 底部代码块仍列出 `#! [feature(int_format_into)]` 等 feature gate，**自相矛盾**
- **官方事实**: 上述 4 项特性**均未进入 1.96 stable**。`RefCell::try_map` 仍是 nightly-only（`feature(refcell_try_map)`）；`VecDeque::truncate_front` 尚未稳定；`int_format_into` 仍在开发中。
- **学习者影响**: 这是**最直接的误导**——学习者阅读后会在 stable 编译器上尝试 nightly 特性，导致编译失败并困惑。

#### 🟡 级别错误（中等）

**错误 E: `assert_matches!` 代码未启用稳定特性**

- **位置**: `crates/c02_type_system/src/rust_196_features.rs` 第 492-497 行
- **错误内容**: `#[cfg(feature = "nightly")]` 守卫 + 注释 "assert_matches! 在 Rust 1.96+ 稳定；当前环境暂用 assert!(matches!()) 等价替代"
- **问题**: 项目全局 MSRV 已设为 1.96.0，该特性已稳定，无需 nightly 条件编译。代码与项目配置**自相矛盾**。

**错误 F: Never 类型标注错误**

- **位置**: `crates/c02_type_system/src/rust_196_features.rs` 第 94-96 行
- **错误内容**: "完整的 `!` 类型支持仍需 nightly 编译器 (`#![feature(never_type)]`)。在 stable Rust 中，`!` 的部分行为已通过 edition 2024 的 fallback 改进可用"
- **官方事实**: Rust 1.96 的 Language 变更明确包含 "Always coerce never types in tuple expressions"。这是**stable 语言级变更**，不应仅标记为 nightly。

---

## 第二部分：深度批判性意见

### 意见一："版本对齐"已沦为"字符串替换游戏"

项目 CHANGELOG 记录："全局批量替换：2,200+ 文件 `1.95.0+` → `1.96.0+`"。但这只是**语法层面的替换**，而非**语义层面的验证**。

**证据链**:

1. 替换逻辑无法捕获 "1.77" 这类**历史遗留的错误版本号**（因为替换脚本只匹配 `1.95`）
2. `crates/*/rust_196_features.rs` 被创建时，直接复制了"猜测清单"（基于 Beta 阶段的不确定信息），未在 1.96 正式发布后与官方 Release Notes **逐条核对**
3. 1.96 Preview 文档基于 2026-05-19 的 Beta 状态编写，但在 2026-05-28 正式发布后**未更新**（文档底部仍标注"预计发布: 2026-05-28"、"版本状态: 🧪 Beta 8"）

**核心问题**: 项目缺乏 "**版本声明 → 官方来源 → 代码验证**" 的三段式验证流程。`rust_{ver}_features.rs` 模块的编写似乎依赖社区传闻而非一手官方来源。

### 意见二：2,300+ "权威来源标注"与实质内容脱节

项目拥有 ~2,300 个文件的"权威来源标注"，但标注的存在不等于内容的准确。

**证据**:

- `05_assert_matches.md` 的权威来源列表包含 `Rust 1.77 Release Notes`，但如果标注者真的查阅了该页面，就会发现其中**根本没有 `assert_matches!`**。
- 这揭示了一个系统性问题：**来源标注可能是事后批量添加的**，而非内容创作时的一手验证；脚本检查的是"标注是否存在"，而非"标注与内容是否一致"。

### 意见三：Preview 文档的"期货化"写作损害信誉

`05_rust_1_96_preview.md` 采用了一种**过度自信**的写作风格：将 Beta 阶段的猜测直接表述为"已稳定"。

| 本项目表述 | 官方现实 |
|:---|:---|
| "VecDeque::truncate_front — 状态: FCP 已完成，等待合并" | **未进入 1.96 stable** |
| "int_format_into — 状态: 稳定化 PR #152902 推进中，需 FCP" | **未进入 1.96 stable** |
| "cargo script / frontmatter — 已在 1.96 稳定" | **非 1.96 新特性**（frontmatter 方式仍在演进） |
| "所有上述特性在 1.96 已稳定，无需 nightly 编译器和 feature gate" | **虚假声明** |

Rust 的稳定性承诺是其核心品牌。错误地声称某特性已稳定，是对学习者的**不负责任**，也是对 Rust 社区价值观的**背离**。

### 意见四：自动化质量管控存在"验证盲区"

项目拥有 51 个脚本、16 个 CI、Miri、死链检查、Bloom 检查，但：

| 检查项 | 实际状态 | 盲区 |
|:---|:---|:---|
| 代码编译通过 | ✅ | 无法验证代码**标注的版本号**是否正确 |
| 死链接为 0 | ✅ | 无法验证链接指向的内容**是否支持文档主张** |
| Miri 内存安全 | ✅ | 无法验证教学内容的**版本事实** |
| Bloom 100% | ✅ | 无法验证认知层级是否匹配 |
| 定理链 259 条 | ✅ | 无法验证定理的前提（如版本号）是否成立 |

**核心问题**: 自动化基础设施验证的是**技术正确性**（能不能编译），而非**事实正确性**（是不是真的）。这是一个**元层面的质量缺口**。

---

## 第三部分：与国际最新权威内容的差距（补充确认）

（以下差距在 `.kimi/COMPREHENSIVE_EXTERNAL_AUDIT_2026_05_29.md` 中已有提及，本次审计通过独立验证确认其准确性。）

### 3.1 形式化验证工具生态（2025-2026 重大进展未覆盖）

| 工具/进展 | 状态 | 本项目覆盖 |
|:---|:---|:---:|
| **AutoVerus / VeruSAGE** (Microsoft, 2025) | LLM 自动证明合成框架，已开源 | ❌ 未覆盖 |
| **Kani 0.65+** (Amazon, 2026) | 量词、循环契约、Autoharness、`--prove-safety-only` | ⚠️ 可能未更新 |
| **ESBMC** (Rust Foundation, 2025) | 通过 Goto-Transcoder 加入标准库验证 CI | ❌ 未覆盖 |
| **Safety Tags (RFC #3842)** | 21个基础标签覆盖 96.1% std unsafe API | ⚠️ 可能未覆盖 |
| **Tree Borrows (PLDI 2025)** | 论文已发表，Miri 默认 | ⚠️ 部分覆盖 |

### 3.2 编译器基础设施新功能

| 功能 | 状态 | 本项目覆盖 |
|:---|:---|:---:|
| **并行前端 (Parallel Frontend)** | Nightly 可用，8核提速20-25%，向稳定化推进 | ❌ 未覆盖 |
| **Cranelift 后端** | Nightly 预览，debug构建代码生成快20% | ❌ 未覆盖 |
| **build-std (RFC #3873)** | 已合并，允许从源码重建标准库 | ❌ 未覆盖 |
| **MemorySanitizer / ThreadSanitizer** | 目标已合并，向稳定化推进 | ❌ 未覆盖 |

### 3.3 Async Rust 前沿进展

| 进展 | 状态 | 本项目覆盖 |
|:---|:---|:---:|
| **async fn in dyn Trait** | Nightly 实验性 (feature gate) | ⚠️ 可能未覆盖 |
| **async drop** | MCP #727 通过，底层组件实现中 | ⚠️ 可能浅层覆盖 |
| **Return Type Notation (RTN)** | 推进中，用于 `+ Send` 边界表达 | ❌ 未覆盖 |
| **Pin ergonomics / safe pin projection** | RFC 讨论中 | ❌ 未覆盖 |
| **异步生成器** | 远期目标，同步生成器语法为先决条件 | ❌ 未覆盖 |

---

## 第四部分：可持续改进计划

### 总体策略：从"大而全"转向"深而精"，从"指标驱动"转向"事实驱动"

当前项目的策略是**广度优先**——覆盖所有可能的话题，并追求可量化的指标（259 定理链、0 死链、100% Bloom）。建议转向**深度优先**——在核心话题上达到**事实零错误**，边缘话题通过链接到外部资源解决。

---

### Phase 1: 紧急事实修复（1 周，2026-05-29 ~ 2026-06-05）

**目标**: 消除所有已发现的版本事实错误，建立"官方 Release Notes → 代码 → 文档"的一致性。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 1.1 | **修正 assert_matches! 版本号** | 修改 `concept/02_intermediate/05_assert_matches.md`：所有 "1.77" 改为 "1.96"；修正来源链接（替换为 1.96 Release Notes）；修正底部"对应 Rust 版本"字段；修正 `asp_marking_guide.md` 中相关条目 | 文件中无 "1.77" 残留；版本声明与官方一致 | 2h |
| 1.2 | **启用 assert_matches! 稳定代码** | 移除 `crates/c02_type_system/src/rust_196_features.rs` 中 `assert_matches_demo` 的 `#[cfg(feature = "nightly")]` 守卫；将 `assert!(matches!(...))` 替换为真正的 `std::assert_matches!`；同步修改 `crates/c02/c03/c04/c05/c08` 等 crate 的 `error.rs` 中已使用 `use std::assert_matches` 的测试代码 | `cargo test` 通过；代码中无 `assert!(matches!(...))` 的冗余断言模式 | 4h |
| 1.3 | **修正 From<bool> 版本号** | 修改所有 `crates/*/src/rust_196_features.rs` 中 `From<bool> for f32/f64` 的标注：将 "1.96 stable" 改为 "1.68 stable"；将该示例从 `rust_196_features.rs` **移至通用类型转换文档**或新建 `rust_168_features.rs` 作为历史复习 | 全局 `grep -r "From<bool>.*1\.96"` 返回 0（archive/ 除外） | 2h |
| 1.4 | **修正 VecDeque::new const 版本号** | 同上，将 `VecDeque::new` const 标注从 "1.96" 改为 "1.68"；从 `rust_196_features.rs` 中移除或归档 | 全局 `grep -r "VecDeque::new.*1\.96"` 返回 0 | 1h |
| 1.5 | **重写 1.96 Preview 文档** | 重写 `knowledge/06_ecosystem/emerging/05_rust_1_96_preview.md` 和 `docs/06_toolchain/06_19_rust_1_96_features.md`：**删除**所有未进入 1.96 stable 的特性（truncate_front, int_format_into, try_map, proc_macro_value）；**补充**实际进入 1.96 但缺失的内容（`From<T>` for AssertUnwindSafe/LazyCell/LazyLock、`ManuallyDrop` 模式、`expr` to `cfg`、Never tuple coercion、兼容性注意） | 文档中每个 1.96 特性均可链接到官方 Release Notes 的对应条目；文档顶部状态改为 "✅ Stable Released 2026-05-28" | 6h |
| 1.6 | **新增 1.96 缺失代码示例** | 在 `crates/c02_type_system/src/rust_196_features.rs` 中新增：`From<T>` for LazyLock 示例（展示从值直接构造 LazyLock）、`ManuallyDrop` 常量模式示例（match 中使用 ManuallyDrop 常量）、`expr` metavariable to `cfg` 示例（macro_rules! 演示） | 每个新增示例可编译并通过测试 | 4h |
| 1.7 | **建立版本事实核查脚本** | 创建 `scripts/version_fact_check.py`：扫描所有 `rust_{ver}_features.rs` 和版本特性文档，要求每个 "X.Y stable" 声明必须伴随官方来源链接；对无来源的版本声明标记为警告；建立可扩展的"已知特性-版本"数据库 | 脚本运行并标记当前所有未附来源的版本声明；输出报告 | 4h |

**Phase 1 总工时**: ~23 小时

---

### Phase 2: 核心学习体验重构（6 周，2026-06-06 ~ 2026-07-17）

**目标**: 解决"认知悬崖"问题，建立清晰的学习路径，引入基础交互机制，**并将"版本事实准确性"作为新的质量维度**。

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 2.1 | **受众分层标签** | 为 concept/ 全部 273 个文件添加 `**目标受众**: [初学者|进阶|专家|研究者]` 元数据；在 mdBook 中通过 CSS 高亮显示 | 100% concept/ 文件带标签；mdBook 渲染后标签可见 | 8h |
| 2.2 | **"最小必要知识集"定义** | 输出 `LEARNING_MVP_PATH.md`：从 Hello World 到独立编写多线程 CLI 的最少概念集合，明确每步预计时间（总计 40h） | 5 名测试学习者能在 40-60h 内按路径完成 | 16h |
| 2.3 | **L4-L7 解耦导航** | 在 L3 末尾创建 `03_advanced/README.md` 作为"分岔口"，清晰标注："如果你要编写生产 Rust 代码，L4-L7 可选"；L4 入口添加前置要求检查清单 | L3→L4 的跳转速率和学习者流失率（通过反馈收集）显著降低 | 8h |
| 2.4 | **术语英中对照表** | 建立 `concept/00_meta/terminology_glossary.md`，覆盖 100 个高频术语，格式：`所有权 (Ownership) [L1] — 定义 — 官方来源链接` | 与 TRPL 官方术语一致率 100%（脚本对比） | 8h |
| 2.5 | **嵌入式测验试点** | 在 `01_ownership.md`、`02_borrowing.md`、`03_lifetimes.md` 中各引入 5-10 道测验题，使用 Markdown 折叠块 `<details>` 实现 | 每个核心文件 ≥5 道测验，覆盖常见 misconceptions | 12h |
| 2.6 | **概念-代码-练习闭环** | 为每个 L1-L2 文件底部添加 `## 实践` 章节：对应 crates/ 代码示例链接 + 对应 exercises/ 题目链接 | 每个 L1-L2 文件底部有闭环导航 | 8h |
| 2.7 | **通用 PL 基座补充** | 在 L1 新增 `01_foundation/00_pl_prerequisites.md`（或扩展现有文件）：求值策略、副作用模型、变量模型、结构化程序定理的 Rust 视角 | 文件存在，且被 L1 学习路径引用 | 16h |

**Phase 2 总工时**: ~76 小时

---

### Phase 3: 内容瘦身与价值审计（8 周，2026-07-18 ~ 2026-09-12）

**目标**: 削减低价值内容，降低维护负担，提升整体价值密度，**消除"指标虚荣陷阱"**。

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 3.1 | **docs/ A/B/C 分级** | 运行脚本：扫描 docs/ 1,324 文件，按以下标准自动标记：A（过去6个月有内部链接/有代码示例/有定理链）；B（有内容但需更新）；C（纯综述/无代码/12个月无更新/与其他文件重复度>70%） | 每文件有 A/B/C 标签；C 类文件移入 archive/ | 16h |
| 3.2 | **三轨重复合并** | 使用相似度检测（如 `difflib` 或 `git diff --stat`）识别 concept/、knowledge/、docs/ 之间的重复内容；对重复度>60%的文件，保留最完整版本，其他改为链接 | 重复文件数量减少 50% 以上 | 24h |
| 3.3 | **前沿领域审查** | 审查 L6-L7 中量子计算、航天、区块链等内容：每个应用场景文档必须包含 ≥1 个可编译的 Rust 代码示例，否则降级为"外部资源链接" | 每个 L6-L7 文件有 `has_runnable_example` 标签 | 16h |
| 3.4 | **历史版本精简** | 评估 crates/ archive/：从"每个版本保留"改为"每3个版本保留一个快照+最新版本"（即 1.86, 1.89, 1.92, 1.95, 1.96） | archive/ 总大小减少 40% 以上 | 8h |
| 3.5 | **定理链指标改革** | 修改 `scripts/kb_auditor.py`：允许文件头部声明 `# theorem_chain: N/A`，描述性/综述性文档可豁免；仪表盘改为"未声明且缺少定理链的文件" | 当前 3 个"风险文件"得到合理解释 | 4h |
| 3.6 | **形式化工具生态补全** | 在 L4 或 L7 新增/更新：AutoVerus/VeruSAGE 介绍、Kani 0.65 新特性、ESBMC 集成、Safety Tags RFC、TrustInSoft | 每个工具/进展有 1 个概念解释 + 1 个可运行代码示例（如 Kani harness） | 16h |

**Phase 3 总工时**: ~84 小时

---

### Phase 4: 国际化基础设施（12 周，2026-09-13 ~ 2026-12-05）

**目标**: 建立英文骨架，突破中文圈天花板，**使版本事实错误能被全球社区审阅**。

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 4.1 | **i18n 技术选型** | 评估 mdBook 多语言方案：`mdbook-i18n`（基于 gettext）vs `mdbook-fluent` vs 自建 PO 工作流；输出 ADR | `I18N_ARCHITECTURE_DECISION.md` 存在，含决策记录 | 8h |
| 4.2 | **核心概念英文骨架** | 为 concept/ 273 个文件创建 `concept/en/` 英文骨架：标题 + 3句话摘要 + 关键代码示例的英文注释 + 术语标准化 | 273 个英文骨架文件存在 | 40h |
| 4.3 | **术语一致性脚本** | 运行脚本对比项目英文术语与官方 Rust 文档（TRPL/Reference）术语的一致性，标记差异 | 差异率 <5% | 8h |
| 4.4 | **双语导航 UI** | 在 mdBook theme 中添加语言切换按钮；如果技术限制，至少在每页顶部添加"[English Skeleton]"链接 | 用户可在概念页顶部切换中英文 | 8h |
| 4.5 | **英文 CI 检查** | 建立 `.github/workflows/en-docs-check.yml`：typos 拼写检查、链接检查、代码块编译检查 | CI 通过且稳定运行 | 8h |
| 4.6 | **TRPL 3rd Ed 对照更新** | 逐章对照 TRPL 第3版（2025-10）与项目 L1-L3 内容，标注叙事差异、新增概念、删除内容 | 输出 `TRPL_3RD_ED_DIFF.md`，含逐章对比 | 24h |

**Phase 4 总工时**: ~96 小时

---

### Phase 5: 教育效果验证与社区建设（持续，2026-12 起）

**目标**: 从"输出内容"转向"验证效果"，**让学习者而非指标成为质量评判者**。

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 5.1 | **最小规模可用性测试** | 邀请 3 名零基础 + 2 名有经验学习者，进行 1 小时有声思维测试（Think-Aloud），记录他们在 L1 核心概念中的困惑点 | 输出 `USABILITY_TEST_REPORT_2026.md`，含 ≥10 个可操作的改进项 | 16h |
| 5.2 | **教师反馈收集** | 联系 2-3 位 Rust 培训讲师（线上即可），收集对项目作为教学辅助材料的反馈 | 输出 `INSTRUCTOR_FEEDBACK_REPORT.md` | 8h |
| 5.3 | **贡献者指南** | 建立 CONTRIBUTING.md：区分文档/代码/翻译/审计四类贡献；提供"Good First Issue"标签模板；**特别添加"版本事实核查"贡献指南** | 新贡献者 30 分钟内能找到首个任务 | 4h |
| 5.4 | **社区对接** | 联系 RustCC、Rust 语言中文社区，申请纳入推荐资源；同时尝试联系 Rust Foundation 教育工作组 | 获得至少一个社区的官方推荐 | 8h |
| 5.5 | **季度僵尸内容清理** | 每季度运行脚本：统计 90 天内无内部链接、无 Git 提交的文件，自动创建 Issue 标记为"待审查" | 每季度处理 ≥5 个僵尸文件 | 2h/季 |
| 5.6 | **学习者反馈机制** | 在 mdBook 每页底部添加"此页对你有帮助吗？⭐⭐⭐⭐⭐"（使用简单 Google Form 或自建） | 每月收集 ≥10 条评分反馈 | 4h |

**Phase 5 总工时**: ~42 小时（含每季度维护）

---

## 第五部分：关键决策点（需您确认）

以下决策将显著影响项目方向，请明确选择：

### 决策 1：是否立即启动 Phase 1 紧急事实修复？

> 当前项目中存在多项**版本事实错误**，可能导致学习者在使用 1.96 之前的 Rust 版本时编译失败，或误将 3 年前的旧特性当作新功能学习。

- **选项 A**: 立即执行 Phase 1（**推荐**）。优先修复 assert_matches! 版本号、From<bool> 错位、1.96 Preview 失真等问题。
- **选项 B**: 仅修复最严重的一项（assert_matches! 1.77 → 1.96），其余推迟到下一版本周期。
- **选项 C**: 暂不修复，等待社区反馈或下一个版本周期统一处理。

**审计建议**: 选 **A**。版本事实错误是**信誉级风险**。对于声称"0 死链接、100% 权威来源对齐"的知识库，版本号错误是最容易被学习者发现且最难以辩解的问题。每多存在一天，被学习者发现的概率就增加一分。

### 决策 2：如何处理 `rust_{ver}_features.rs` 系列模块？

> 当前 crates/ 中每个 crate 都有 `rust_195_features.rs`、`rust_196_features.rs` 等文件，但部分文件包含**虚假或错位**的版本特性，且存在"为填充文件而硬凑特性"的风险。

- **选项 A**: 全面审计并修正所有 `rust_{ver}_features.rs`，建立"每个特性必须链接到官方 Release Notes"的强制规范。
- **选项 B**: **删除** `rust_{ver}_features.rs` 系列模块，将版本特性分散到对应的概念文档和常规代码示例中，避免"为版本而版本"的形式主义（**推荐**）。
- **选项 C**: 保留当前结构，但仅维护最新两个版本的文件，旧版本文件移入 archive/。

**审计建议**: 选 **B**。版本演进应该是**有机的**（在概念文档中自然提及"此特性在 1.96 稳定"），而非**模块化的**（为每个版本硬凑一个独立文件）。模块化组织是导致"From<bool> 被包装成 1.96 特性"这类错误的温床。

### 决策 3：核心产品定位

> 项目应聚焦的**单一核心产品**是什么？

- **选项 A**: 中文世界最深入的"所有权-借用-生命周期"学习路径（放弃广度，在核心概念上超越 TRPL）
- **选项 B**: 中文 Rust 开发者的全栈参考手册（保持当前 L0-L6 覆盖，但删减 L7 和 docs/ 深度研究）
- **选项 C**: 形式化 Rust 研究资料库（将 L4 作为核心差异化竞争力，弱化初学者内容）
- **选项 D**: 维持现状（继续 L0-L7 全覆盖，接受维护负担）

**审计建议**: 选 **A**。理由：

1. 所有权是 Rust 最独特、最难、最核心的概念；
2. 中文世界尚无在此维度上超越 TRPL 的资源；
3. 聚焦后才能投入资源做教育效果验证和交互式体验；
4. 只有聚焦，才能避免"1,773 文件、46 万行"带来的维护灾难。

### 决策 4：形式化内容定位

> L4 形式化层（线性逻辑、范畴论、分离逻辑）如何处理？

- **选项 A**: 真正形式化（提供 Verus/Kani 可验证的代码，引用最新学术论文 DOI，邀请 PL 研究者审阅）
- **选项 B**: 形式化直觉（保留符号和推理，但明确标注"此为教学类比，非严格证明"）
- **选项 C**: 降级为高级参考（删除线性逻辑/范畴论等纯数学内容，保留 RustBelt/Tree Borrows/Safety Tags/Kani 等**工程形式化**）

**审计建议**: 选 **C**。理由：

1. 项目无 PL 形式化领域专家背书；
2. 真正形式化需要机器验证（Verus/Kani/Coq），Markdown 中的符号是"伪形式化"，可能误导学习者；
3. Tree Borrows、Safety Tags、Kani 等**工程形式化**才是 Rust 开发者真正需要的。

### 决策 5：国际化投入优先级

> 在资源有限的情况下，国际化的第一步是什么？

- **选项 A**: 核心概念全英文化（273 个 concept/ 文件完整翻译，投入巨大）
- **选项 B**: 英文骨架 + 术语标准化（仅标题/摘要/代码注释英文化，投入中等）
- **选项 C**: 术语英中对照表 + 关键代码英文注释（最小投入，先建立基础）
- **选项 D**: 暂不国际化（先解决教育有效性问题，再考虑语言扩展）

**审计建议**: 选 **B**。理由：

1. 英文骨架足以被全球搜索引擎索引，突破"不可发现"问题；
2. 代码示例的英文注释是最大痛点（crates.io、RFC、GitHub Issue 全英文）；
3. 完整翻译需要专业译者，当前资源不足；
4. 英文版本能使全球 Rust 社区参与审阅，**间接帮助发现版本事实错误**。

---

## 附录：新增权威来源清单

| 来源 | URL | 本项目应重点对标维度 |
|:---|:---|:---|
| Rust 1.96.0 Official Release Notes | <https://github.com/rust-lang/rust/issues/156512> | 版本事实核查一手来源 |
| releases.rs 1.96.0 | <https://releases.rs/docs/1.96.0/> | 版本历史查询 |
| Cargo 1.96 CHANGELOG | <https://doc.rust-lang.org/beta/cargo/CHANGELOG.html> | 工具链变更 |
| Rust 1.68.0 Release Notes | <https://releases.rs/docs/1.68.0/> | From<bool> / VecDeque::new const 实际稳定版本 |
| AutoVerus / VeruSAGE | <https://github.com/microsoft/verus-proof-synthesis> | 形式化验证 + AI 辅助 |
| Kani 0.65+ | <https://model-checking.github.io/kani/> | 标准库验证、循环契约、Autoharness |
| Safety Tags RFC #3842 | <https://github.com/rust-lang/rfcs/pull/3842> | Unsafe API 安全契约标准化 |
| ESBMC for Rust | <https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/> | 形式化验证工具生态 |
| Rust Project Goals 2026 | <https://rust-lang.github.io/rust-project-goals/2026/> | 前沿特性跟踪 |
| Async Rust Project Goals | <https://rust-lang.github.io/rust-project-goals/2025h1/async.html> | async fn in dyn Trait、async drop、RTN |
| Tree Borrows Paper | <https://doi.org/10.1145/3735592> | Miri 别名模型 |
| Rustlings v6 | <https://github.com/rust-lang/rustlings> | 练习体系对标 |
| 100 Exercises | <https://rust-exercises.com/> | 项目制学习 |
| Google Comprehensive Rust | <https://google.github.io/comprehensive-rust/> | 多语言、工业案例、3天结构 |
| Brown University Book | <https://rust-book.cs.brown.edu/> | 交互式测验、Aquascope |

---

> **审计结论**: 本项目在技术严谨性和内容广度上已达到**中文 Rust 生态的顶尖水平**，但在**版本事实准确性**这一基础维度上出现了**系统性失误**。这并非能力问题，而是**流程问题**——"批量替换版本号"的自动化流程无法替代"逐条核对官方 Release Notes"的人工验证。建议立即执行 Phase 1 紧急修复（消除版本事实错误），将"官方来源核对"固化为内容生产的强制流程，然后以 Phase 2 核心学习体验重构为战略重心，从"输出内容"转向"验证学习效果"。
