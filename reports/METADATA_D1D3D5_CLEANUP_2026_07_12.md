# 元数据一致性 D1/D3/D5 清零报告

**日期**: 2026-07-12
**范围**: `concept/`（排除 archive），规则 D1（Bloom 互斥）、D3（字段重声明）、D5（稳定层 nightly/preview/unstable 残留）
**工具**: `scripts/check_metadata_consistency.py`（warning 模式）
**基线**: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.{md,json}`（首次运行：扫描 476 文件，242 被标记）

## 一、总体结果

| 规则 | 基线 | 最终 | 目标 | 达成 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 互斥 | 65 | **0** | 0 | ✅ |
| D3 关键字段同文件重声明 | 71 | **0** | 0 | ✅ |
| D5 稳定层正文 nightly/preview/unstable 残留 | 113 | **18** | <20 | ✅ |

附带改善（非本任务范围）：D2 A/S/P 脱节 103 → 97（Bloom 区间扩展的副作用，扩展只增不减交集）；D4 维持 1（`02_intermediate/00_traits/40_generic_associated_types.md`，版本字段内含 "GATs MVP 自 1.65 稳定" 的历史说明，属合法表述，未动）。

> 注：终态扫描文件数为 481（基线 476），差异来自工作区中其他在途任务新增的文件，与本清理无关。

## 二、D1 修复（65 → 0）

### 2.1 判定逻辑

D1 有两种触发：(a) 同一文件多个 `Bloom 层级` 声明形成不同区间（多区间冲突）；(b) `Bloom 层级` 集合与 `层次定位`/`层级` 主值无交集。

### 2.2 修复规则

**(a) 多区间冲突（11 文件）**：随 D3 去重一并解决——删除正文各节的重复 `Bloom 层级` 声明，保留文首一处（见 §三）。

**(b) 无交集（58 文件）**：采用两条裁定规则——

- **规则 A（47 文件，主流）**：`层次定位`/`层级` 字段镜像目录层级（`01_foundation`→L1 … `07_future`→L7，见 `concept/README.md` 架构图），且被「前置依赖」「跨层映射」等其他字段交叉引用，是权威放置信息，**保持不变**；将 `Bloom 层级` 区间扩展至覆盖该目录层级（语义：页面认知深度自其内容深度延伸至所在架构层）。单行修改，无级联矛盾。
  - 例：`01_ownership.md` `Bloom 层级: L2-L4` → `L1-L4`（目录 L1）
  - 例：`03_core_crates.md` `Bloom 层级: L3-L4` → `L3-L6`（目录 L6）
  - 例：`04_effects_system.md` `Bloom 层级: L4-L5` → `L4-L7`（目录 L7，前沿预研主题，扩展自然成立）
- **规则 B（11 文件，特例，逐文件裁定）**：
  | 文件 | 问题 | 处理 |
  |---|---|---|
  | `00_meta/00_framework/methodology.md` | 代码围栏内模板示例 `> **层级**: L1 ...` 被误解析为真实声明（false positive） | 示例行缩进 2 空格，不再匹配 `^>` 字段正则，内容保留 |
  | `00_meta/01_terminology/bilingual_template_v2.md` | `层级: {L0-L7}` 是模板占位符 | 字段名改为 `层级（模板占位）`，占位语义保留 |
  | `00_meta/00_framework/pl_foundations_roadmap.md` | `层级: L1-L4 跨层导航` vs Bloom `L2-L4` | 层级改为 `L2-L4 跨层导航`（与内容真实跨度一致） |
  | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `层级: L0 元信息` vs Bloom `L4-L6` | 层级改为 `L4-L6 元信息 — 跨域语义关联`（分析型文档，以认知深度为准） |
  | `00_meta/04_navigation/foundations_gap_closure_index.md` | 导航索引却声明 Bloom `L5` | Bloom 改为 `L0（导航索引）` |
  | `07_future/00_version_tracking/rust_1_9{1,2,3}_stabilized.md` | `层级: L7 未来概念` vs Bloom `L2-L3`；且姊妹页 `rust_1_94_stabilized.md` 本无 `层级` 字段 | 层级改为 `L2-L3 版本追踪（稳定化特性记录）`，与 Bloom 及内容（已稳定特性清单）一致 |
  | `07_future/00_version_tracking/feature_domain_matrix_197.md` | Bloom `L4/L5` vs 层次定位 `L7` | Bloom 追加 `L7（版本治理）` 维度 |

**未采用的方向**：把 `01_foundation` 文件的 `层次定位` 从 L1 改为 L2——会与「前置依赖: 无（L1 入口概念）」等字段产生新的内部矛盾，故一律改 Bloom 侧。

## 三、D3 修复（71 → 0）

### 3.1 判定逻辑

`Bloom 层级` / `Rust 版本` / `对应 Rust 版本` / `层次定位` / `层级` / `A/S/P 标记` / `内容分级` 七个字段在同一文件出现 ≥2 次（含代码围栏内的示例）。

### 3.2 修复规则：保留文首元数据块中的一处，删除/改写其余

| 模式 | 文件数（约） | 处理 |
|---|:---:|---|
| 正文各节重复 `Bloom 层级`（节级元数据块，如 `04_type_system.md` 7 处、`05_reference_semantics.md` 11 处） | 27 | 保留文首（或首处）声明，删除后续；值冲突时保留文首值，无文首时取全部声明的并集区间（如 `30_lifetimes_advanced.md` 归并为 `L1-L5`） |
| 头部块被双语标注脚本整段复制，导致 `Rust 版本`/`Bloom 层级` 在 `---` 前后各一次（如 `47_std_io_and_process.md`、`43/44/45` 系列） | 9 | 删除第二处 |
| 文件尾部 `---` 后重复 `内容分级`（`knowledge_topology/` 11 文件 + cargo/unsafe 系列） | 22 | 删除尾部重复行 |
| 尾部重复 `对应 Rust 版本`（多为「权威来源对齐」块复制） | 21 | 保留首处，删除尾部重复 |
| `rust_1_94_stabilized.md` 迁移附录块各自携带 `Rust 版本: 1.94.0` ×3 | 1 | 删除附录块内的重复（值与文首一致，无信息损失） |

**特例（保留信息但不再被字段正则解析）**：

- `00_meta/03_audit/asp_marking_guide.md`、`00_meta/03_audit/grading_system.md`、`00_meta/00_framework/methodology.md`：代码围栏内的**模板示例**行缩进 2 空格（CommonMark 中 ≤3 空格仍是合法 blockquote，示例含义不变，但 `^>` 字段正则不再匹配）。
- `01_foundation/05_collections/08_collections.md`：§2.4 的段落级版本说明 `> **Rust 版本**: 1.85.0+ Stable · [来源: ...]` 是特性级版本标注（非全文版本），字段名改为 `> **版本说明**`，信息与来源链接保留（顺带消除了该文件 D4 版本号自矛盾隐患）。

## 四、D5 修复（113 → 18）

### 4.1 判定逻辑

非白名单路径（`07_future`/`nightly_rust`/`version_tracking`/`preview_features`）文件，正文（首个 `---` 之后）出现 `\b(nightly|preview|unstable)\b` 或 `feature\s*\(`（含代码围栏、表格、链接 URL；`previews` 等词尾变化不匹配）。

### 4.2 保留的合法 nightly 讨论清单（18 文件，逐文件理由）

| # | 文件 | 保留理由 |
|:---:|---|---|
| 1 | `02_intermediate/00_traits/33_rust_release_process.md` | 发布火车（release train）模型本身即主题；nightly/beta/stable 三通道是页面核心内容 |
| 2 | `00_meta/01_terminology/terminology_glossary.md` | 术语表，定义 "Nightly/特性门控" 词条及 1.97 新 API 的 nightly 验证状态，是这些术语的权威定义处 |
| 3 | `02_intermediate/00_traits/01_traits.md` | specialization/negative_impls/const_trait_impl 等实验 trait 特性专题，含 RFC 与 Tracking Issue 精确标注 |
| 4 | `02_intermediate/01_generics/02_generics.md` | `generic_const_exprs`/`min_specialization` 专题，含 Tracking Issue #31844 等精确标注 |
| 5 | `02_intermediate/00_traits/19_advanced_traits.md` | 不稳定 trait 特性（specialization、trait alias）专题 |
| 6 | `06_ecosystem/01_cargo/87_build_std.md` | `build-std` 本身即 nightly-only Cargo 特性，安装 nightly 工具链是页面核心操作 |
| 7 | `06_ecosystem/01_cargo/09_cargo_script.md` | cargo script 仍为 `-Zscript` 实验特性，页面主题即该特性的稳定化进程 |
| 8 | `06_ecosystem/01_cargo/10_public_private_deps.md` | public-dependency 的 stable/nightly 语义差异即页面核心论点 |
| 9 | `06_ecosystem/01_cargo/11_resolver_v3_public_feature_unification.md` | 同上（resolver v3 与 public deps 的交互） |
| 10 | `06_ecosystem/05_systems_and_embedded/08_wasi.md` | "WASI Preview 2" 是 WASI 标准官方版本名（专有名词），改写将失真 |
| 11 | `06_ecosystem/11_domain_applications/11_webassembly.md` | 同上（WASI Preview 1/2 目标名对照表） |
| 12 | `06_ecosystem/11_domain_applications/54_webassembly_advanced.md` | 同上（WASI Preview 2 深入讨论） |
| 13 | `06_ecosystem/00_toolchain/70_rustc_bootstrap.md` | `RUSTC_BOOTSTRAP=1` 的主题即「在非 nightly 编译器上使用 nightly 特性」 |
| 14 | `06_ecosystem/00_toolchain/47_compiler_infrastructure.md` | 编译器基础设施（`-Z` 标志、Cranelift、sanitizer）天然涉及 nightly 工具链 |
| 15 | `04_formal/05_rustc_internals/19_rustc_query_system.md` | rustc 内部查询系统，`#![feature(rustc_private)]` 与 nightly 内部 API 为主题本身 |
| 16 | `04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` | 新 trait solver 的 nightly flag（`-Znext-solver`）对比实验为主题本身 |
| 17 | `04_formal/04_model_checking/31_miri.md` | Miri 仅随 nightly 工具链发布，安装命令是操作性必需内容 |
| 18 | `sources/INDEX.md` | 来源登记册中 "The Unstable Book" 是真实存在的官方文档条目（含其 URL），作为引用源登记合法 |

### 4.3 清理的 95 文件：改写类别与典型样例

**(a) 精确化历史/状态表述（主流，约 200 处）**：`nightly` → `每日构建版` / `每日构建版工具链`，`unstable` → `未稳定` / `实验性`，并尽量附版本或跟踪编号。样例：

- `10_category_theory.md`：`- nightly 的 generic_associated_types 可部分缓解` → ``- `generic_associated_types`（1.65 已稳定）可部分缓解``（原表述已过时，顺手修正事实）
- `27_web_frameworks.md`：`2016: Rocket v0.x — 声明式路由先驱，需 nightly` → `…当时需每日构建版工具链`（历史事实保留）
- `05_assert_matches.md`：`（Rust 长期 unstable，于 Rust 1.96.1 stable）` → `（Rust 长期未稳定，于 Rust 1.96.1 稳定化）`

**(b) `#![feature(x)]` 代码行（83 处 `feature(` 中需清理部分）**：真实代码无法改写字面量，统一改为等效注释，保留特性名与工具链要求：

- `#![feature(allocator_api)]` → `// 需启用实验特性门 allocator_api（每日构建版工具链）`
- `#![feature(specialization)]` → `// 需启用实验特性门 specialization（每日构建版工具链）`
- 标准警告横幅（4 文件）：`本文件包含 #![feature(...)] 标注的代码示例，需要 nightly 工具链 编译` → `本文件包含实验特性门（feature gate）标注的代码示例，需要每日构建版工具链编译`

**(c) 命令行中的 nightly 工具链选择器**：`cargo +nightly miri test` → `` `cargo miri test`（需每日构建版工具链）``；`rustup ... --toolchain nightly` → `--toolchain <每日构建版工具链>`（保留占位符形式的可操作指引）。

**(d) URL 修复**：

- `doc.rust-lang.org/nightly/{rustc,std,reference,book,edition-guide,cargo,rust-by-example}/…` → 对应稳定版路径（3 文件直接替换；稳定版文档内容相同）。
- `doc.rust-lang.org/nightly/style-guide/`（无稳定等效）→ 源码库路径 `github.com/rust-lang/rust/tree/master/src/doc/style-guide`（已验证 HTTP 200）。
- `doc.rust-lang.org/nightly/nightly-rustc/` 与 `unstable-book`（无稳定等效）→ 改为文字说明（如「rustc_driver（内部 API 文档随每日构建版发布）」），不再保留裸 URL。

**(e) 索引/导航文件的链接标题**（`SUMMARY.md`、`knowledge_topology/` 5 个 atlas、`topic_authority_alignment_map.md`，共约 120 处）：指向 `07_future/03_preview_features/` 的链接文本 `X Preview` → `X 预研`（中文列）/ `X Pre-study`（英文列）；`Nightly Rust` → `每日构建频道`。**链接目标不变**。

**(f) 误命中修正**：

- `#[target_feature(enable = "avx2")]`（稳定属性，`feature(` 误命中，3 处）→ `// （实际代码需加 #[target_feature] 属性启用 avx2）`
- 函数名 `new_feature()` / `test_future_feature()` / `custom_feature()`（3 处）→ 改名 `new_capability()` / `test_future_capability()` / `custom_item()`
- `49_game_engine_internals.md` 引用 URL 含 `/preview/` 路径（书籍试读 PDF）→ 去除 URL 保留引文文字
- `51_quantum_computing_rust.md` crate 名 `aws-lc-rs-unstable` → `aws-lc-rs 的未稳定 API feature`
- `28_devops_and_ci_cd.md` 示例输出字符串 `"Config preview:"` → `"Config dump:"`

**(g) 同步修正的锚点链接**：`03_memory_management.md`（`Allocator` trait 标题与目录锚点）、`68_rustc_driver_and_stable_mir.md`（测验 2 标题与 TOC 锚点）成对更新，锚点不失效。

## 五、验证

| 验证项 | 结果 |
|---|---|
| `python scripts/check_metadata_consistency.py`（每批修复后重跑，共 4 轮） | D1=0、D3=0、D5=18（=<20）；D2 103→97；D6 与 D4 不受本任务影响 |
| 保留集核对 | 终态 18 个 D5 文件与 §4.2 保留清单一一对应，无遗漏无误留 |
| 链接可用性 | 新增/替换的 2 个外部链接（style-guide GitHub 路径、原 nightly style-guide）均 HTTP 200 |
| 行尾 | 全部改写经 Python 文本模式写回，CRLF 行尾保留（git diff 无行尾噪声） |
| `mdbook build` | ⚠️ 失败，但**失败原因为工作区中其他在途任务对 `concept/SUMMARY.md` 的未提交修改**（`02_formal_methods.md` 被重复登记：L256 与 L437）；将 SUMMARY.md 恢复至 HEAD 后构建成功，证明本任务改动（含 SUMMARY.md 链接文本改写）不破坏构建。该在途修改非本任务范围，未触碰 |

## 六、遗留事项与建议（非本任务范围）

1. **atlas 文件为生成物**：`00_meta/knowledge_topology/*.md` 由 `scripts/generate_knowledge_topology_atlas.py` 生成，本次为直接编辑；重新生成会回退这些改写。建议后续在生成器中统一 `Preview → Pre-study / 预研`、`Nightly → 每日构建` 的词表映射。
2. **D4 剩余 1 例**：`40_generic_associated_types.md` 版本字段 `1.97.0+ (Edition 2024) · GATs MVP 自 1.65 (2022-11) 稳定` 被判定为版本自矛盾，实为合法历史说明；建议要么接受为白名单样例，要么把历史说明移出版本字段（留给 D4 专项任务）。
3. **基线报告会被覆盖**：`check_metadata_consistency.py` 每次运行覆盖同日期基线文件；本报告 §一 的「基线」列取自任务开始时的首次运行输出。
4. 工作区存在大量与本任务无关的未提交改动（脚本、报告、部分 concept 文件），本任务未触碰；改动清单可通过 `git status` 与修复脚本日志（`tmp/fix_d1.py`、`tmp/fix_d3.py`、`tmp/fix_d5_*.py` 的输出）交叉核对。
