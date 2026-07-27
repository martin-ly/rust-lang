# 语义分析论证对称差梳理与后续完善计划

**EN**: Semantic Symmetric-Difference Audit and Remediation Plan
**Summary**: 以 Rust 1.97.1 为基准，对本项目 `concept/` 权威页与国际化权威来源（Rust Reference / Nomicon / TRPL 3rd Ed / Async Book / rustc-dev-guide / UCG）进行主题与内容对称差分析，输出可执行修复计划。

> **Rust 版本**: 1.97.1 (Edition 2024)
> **生成时间**: 2026-07-28
> **检查基线**: version_semantic_injection=74/74, cross_domain_coverage=16/16, authority_freshness=1.97.1 synced, semantic_health=99.7 OK
> **工具**: `scripts/check_version_semantic_injection.py`, `scripts/check_cross_domain_coverage.py`, `scripts/check_authority_freshness.py`, `scripts/semantic_health.py`, `scripts/concept_consistency_auditor.py`, 人工抽样 + 子代理对比
> **执行状态**:
>
> - 2026-07-28：完成 P0 任务 P0-1 至 P0-6（见 §5.2），验证通过。
> - 2026-07-28：完成 P1 任务 P1-1 至 P1-10（见 §5.2），验证通过。
> - 2026-07-28：完成 P2 任务 P2-1/2/3/6/9/10（见 §5.2），P2-8 进行中，P2-4/5/7 纳入下季度计划。
> - 2026-07-28：P2 批次完成后复跑阻断质量门：
>   - `cargo test --workspace --quiet` ✅
>   - `python scripts/kb_auditor.py --link-check` ✅（0 死链 / 0 跨层问题）
>   - `python scripts/concept_consistency_auditor.py --strict` ✅（0 错误 / 0 警告）
>   - `python scripts/semantic_health.py --strict` ✅（99.7 grade OK）
>   - `python scripts/check_concept_code_blocks.py --strict` ✅（candidate 300/300 pass，compile_fail 892/892 ok）
>   - `python scripts/detect_content_overlap_v2.py --budget 999999 | python scripts/triage_overlap.py` ✅（MERGE=0 / DOCS_INTERNAL=0）
>   - `python scripts/authority_semantic_diff.py --strict` ✅（P0=0 / P1=0）
> - 当前 P2 完成度 60%（6/10 项完成），剩余 P2-4/5/7/8 持续推进。

---

## 一、"对称差"定义与本项目口径

将「本项目语义论证集合」与「国际化权威语义标准集合」之间的对称差拆为三类：

| 类型 | 含义 | 典型例子 |
|:---|:---|:---|
| **A. 项目有、权威无** | 项目独创的深度延伸、学习路径、对比框架、生态深潜 | L0 元认知框架、跨语言对比矩阵、版本跟踪矩阵 |
| **B. 权威有、项目无/浅** | 官方文档有系统论述，但 `concept/` 未覆盖或仅覆盖皮毛 | lifetime elision 的 trait object/`'_` 规则、UB 清单 `isize::MAX` 边界、Pin structural pinning |
| **C. 双方都有但不一致** | 同一概念在双方解释中存在版本偏差、术语冲突、事实错误 | `unsafe extern` 2021 支持性、`let chains` 稳定版本、extern 块内 `type` 合法性 |

> 注意：自动化质量门已通过（外部缺口清单 10/10 已补充），但对称差中的 B/C 类大量属于**细节精度与语义深度**，无法被标题级对齐脚本捕获，需人工/子代理抽样对比。

---

## 二、当前基线状态（已验证）

### 2.1 自动化检查器结果

| 检查项 | 结果 | 说明 |
|:---|:---|:---|
| `check_version_semantic_injection.py --strict` | ✅ 74/74 | Rust 1.90–1.97 稳定特性双向链接覆盖 100% |
| `check_cross_domain_coverage.py --strict` | ✅ 16/16 | 关键交叉/边界语义域均有 `concept/` 非 stub 权威页 |
| `check_authority_freshness.py` | ✅ 1.97.1 synced | 上游 stable=1.97.1，距 1.98.0 稳定日 23 天 |
| `semantic_health.py --strict` | ✅ 99.7 grade OK | 元数据/拓扑/去重/KG 全绿 |
| `concept_consistency_auditor.py --strict` | ✅ 0 错误/0 警告 | 537 文件、4737 定义、302 跨文件引用全部有效 |
| `check_concept_authority_coverage.py --strict --include-crates` | ✅ any=100% none=0 | concept 与 crates docs 权威来源覆盖达标 |
| `check_stub_purity.py --strict` | ✅ 0 伪 stub | 非权威文件保持纯净 |
| `audit_content_completeness.py` | ✅ 0 处真实 body TODO | P0-6 已复核：一为图例符号误报，一为行截断显示误报 |

### 2.2 外部权威主题索引状态

- `concept/00_meta/02_sources/06_external_authority_topic_index.md` §十一「未覆盖缺口清单」10 项全部标记为「已补充」。
- 索引正文 ⚠️ 状态（2026-07-28 更新）：
  1. TRPL Final Project: Web Server — ✅ 已覆盖：`concept/03_advanced/06_low_level_patterns/04_network_programming.md` 与 `concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md` 覆盖 TRPL Ch21 核心概念（TCP 监听、线程池、优雅关闭）；逐步代码对照属示例级，由 TRPL 保留。
  2. Edition Guide Rust 2024 Standard library — 🔄 P2-8 进行中：待补 prelude 变更、`IntoIterator for Box<[T]>`、新增 unsafe fn 等细节。
  3. rustc-dev-guide MIR optimizations — 🔄 P2-7 进行中：待深化 StorageLive/Dead、drop elaboration、dataflow、常见 MIR passes。
  4. rustc-dev-guide next-gen solver — 🔄 P2-7 进行中：待深化 Chalk / next-gen solver / trait solver 与 lifetime selection 分离。

---

## 三、主题对称差

### 3.1 A 类：项目有、权威来源未直接强调（357 项）

来源：`concept/00_meta/02_sources/04_topic_authority_alignment_map.md` §4。

抽样 37 份非 meta 文件后分类：

| 子类 | 占比 | 说明 | 处理建议 |
|:---|---:|:---|:---|
| A1 合理项目创新 | 75.7% | 跨语言对比、学习路径、生态深潜、形式化桥梁 | 保留，需在页首明确标注 project-specific 深度 |
| A2 潜在过度扩展 | 5.4% | 通用 CS 理论（如图灵机、主定理）占据 L4；L6 数据结构与 L1 重复 | 标记为项目专属索引或改为 stub |
| A3 对齐工具漏匹配 | 18.9% | 实为标准 Rust 特性但 `topic_authority_aligner.py` 未命中 | 补充 authority mapping，移出「独有」列表 |

**A3 典型漏匹配主题（需补映射）**：

- `let chains` → RFC 2497 / Reference If expressions
- `never type` → RFC 1216 / Reference Never type
- `const generics` → RFC 2000 / Reference Generic parameters
- `Cow<T>` → std::borrow::Cow / TRPL Smart Pointers
- `sanitizers` → rustc-dev-guide / Unstable Book
- `unsafe reference` → Reference — Unsafety

### 3.2 B 类：权威有、项目无/浅（抽样发现 30+ 项）

按主题域汇总：

#### 3.2.1 所有权 / 借用 / 生命周期

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| Lifetime elision：trait object default lifetime bounds、`const`/`static` 隐式 `'static`、function pointer/closure trait elision、`'_` placeholder | Reference — Lifetime Elision | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` §2.3 | P1 |
| Variance 表格缺 `dyn Trait<T> + 'a`、`PhantomData<T>`、`[T]`/`[T; n]`、`fn() -> T` 等行 | Reference — Subtyping and Variance | `04_formal/00_type_theory/02_subtype_variance.md` §1.3 | P1 |
| 每个使用点独立计算 variance 的规则（Reference 混合 variance struct 示例） | Reference — Subtyping and Variance | `02_subtype_variance.md` | P2 |
| Reference Pointer Types 的 bit validity / transmute 规则 | Reference — Pointer Types | `02_borrowing.md` | P2 |
| TRPL Ch4.1 堆/栈动机图示 | TRPL Ch4.1 | `01_ownership.md` | P2 |

#### 3.2.2 Unsafe / 内存模型 / UB

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| UB 清单：pointer span / `isize::MAX` 边界 | Reference — BCU | `04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | P1 |
| Misaligned place 投影细节、`*` 投影计数、`repr(packed)` 约束 | Reference — BCU | `06_behavior_considered_undefined.md` §3 | P1 |
| 引用/`Box` 的 liveness duration bounds 枚举 | Reference — BCU | `06_behavior_considered_undefined.md` | P1 |
| 读取未初始化内存的 union/padding 例外 | Reference — BCU | `06_behavior_considered_undefined.md` | P2 |
| `MaybeUninit` 切片 API、`with_exposed_provenance`、1.96 valid-for-read/write 重构 | Release Notes / std docs | `03_advanced/02_unsafe/06_memory_model.md` | P2 |

#### 3.2.3 Async / Pin

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| `.await` desugaring 缺 `IntoFuture::into_future` 与临时 `Pin::new_unchecked` | Reference — Await expressions | `03_advanced/01_async/01_async.md` §3.1b | P0 |
| `async fn` 参数捕获与 drop 顺序边界 | Reference — Async functions | `01_async.md` §3.1 | P1 |
| `async unsafe fn` 语义：future 可安全 await，仅调用需 unsafe | Reference — Functions | `01_async.md` | P1 |
| Pin structural pinning、`Pin::set`、赋值、`ManuallyDrop` 反模式 | std::pin docs | `03_advanced/01_async/08_pin_unpin.md` §4.2/5 | P1 |

#### 3.2.4 FFI / extern

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| extern 块内只允许函数与静态变量；`type` 别名/extern types 为不稳定特性 | Reference — External Blocks | `03_advanced/04_ffi/01_rust_ffi.md` §2.1/2.2 | P0 |
| bare `extern { }` 无 ABI 字符串正在被淘汰 | Reference — External Blocks | `01_rust_ffi.md` 多处示例 | P1 |
| `unsafe extern` 在 2021 Edition 自 1.82 起即可使用（可选） | Edition Guide / Reference | `05_unsafe_extern_blocks.md` §2.3 | P0 |

#### 3.2.5 类型系统 / 编译器内部

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| 递归类型必须包含 nominal type、递归字段须为指针类型 | Reference — Types | `01_foundation/02_type_system/01_type_system.md` | P1 |
| `str` 作为 built-in primitive type 的分类 | Reference — Types | `01_type_system.md` | P2 |
| HM / Principal type 定理表述过强 | Reference / rustc-dev-guide | `01_type_system.md` §6.3 | P1 |
| Trait solver：selection 不考虑 lifetime、type-check/codegen 分两次 selection | rustc-dev-guide | `04_formal/05_rustc_internals/03_trait_solver_in_rustc.md` | P2 |
| MIR：`StorageLive`/`StorageDead`、promoted constants、ValTrees、debug scopes | rustc-dev-guide | `04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md` | P2 |
| Monomorphization collection vs instantiation 时间区分 | rustc-dev-guide | `02_mir_codegen_llvm_primer.md` | P2 |

#### 3.2.6 版本跟踪 / Edition

| 缺口 | 权威来源 | 项目位置 | 优先级 |
|:---|:---|:---|:---:|
| `let chains` 稳定版本应为 1.88.0 / Edition 2024 | Release Notes 1.88.0 / Reference | `01_foundation/04_control_flow/03_let_chains.md` | P0 |
| `if-let guards` 稳定版本应为 1.95.0 | Release Notes 1.95.0 | `03_let_chains.md` | P0 |
| TRPL Ch21 Web Server 项目逐步对照 | TRPL Ch21 | `02_intermediate/00_traits/04_advanced_traits.md` / network programming pages | P2 |
| Edition 2024 std lib 细节（prelude、`IntoIterator for Box<[T]>`、新增 unsafe fn） | Edition Guide | `07_future/01_edition_roadmap/02_edition_guide.md` | P2 |

### 3.3 C 类：双方都有但语义不一致（已确认 10+ 项）

| 文件 | 不一致点 | 权威依据 | 优先级 |
|:---|:---|:---|:---:|
| `05_unsafe_extern_blocks.md` §2.3 | 称 `unsafe extern` 在 2021 Edition 不支持 | Edition Guide: 1.82 起所有 edition 可选 | P0 |
| `03_let_chains.md` §9 | `let chains` 1.64+ / `if-let guards` 1.83+ | 实际 1.88.0 / 1.95.0 | P0 |
| `01_rust_ffi.md` §2.1/2.2 | extern 块内写 `type FILE;` / `type Callback = ...` | Reference: 仅允许 fn/static；extern types 不稳定 | P0 |
| `01_async.md` §2.3 | Tokio 运行时重复两行 | 内部不一致 | P2 |
| `01_unsafe.md` §Step 5 | Miri 可部分检测数据竞争；后表又标 ❌ | Miri 单线程无法检测数据竞争 | P1 |
| `01_unsafe.md` §2.2 | 将栈溢出/除以零列为 UB 子类 | Reference BCU 未枚举；整数除零 panic | P1 |
| `03_lifetimes.md` §4.5 | 使用 `'static ⊑ 'a` 并称 `'static` 为「最大元」 | Reference 用 outlives；方向相反 | P2 |
| `04_lifetimes_advanced.md` §九/§十八 | 引用「TRPL — Advanced Lifetimes」链接指向基础章节或 404 | TRPL 3rd Ed 无独立 Advanced Lifetimes 章节 | P2 |
| `06_memory_model.md` §四 | Reference — MaybeUninit 链接指向 introduction 不存在的锚点 | 应改为 std 文档链接 | P2 |
| 多处 | Reference / Nomicon 链接指向首页而非具体章节 | 引用精度不足 | P2 |

---

## 四、项目内部 L1-L4 语义论证对称差

### 4.1 跨层术语与定理编号不一致

| 概念 | L1/L2 术语 | L4 术语 | 建议 |
|:---|:---|:---|:---|
| 所有权状态 | `Own(T) / Moved / Borrow(&T) / Borrow(&mut T) / Dropped` | `Own(p) / Shr(p) / Mut(p) / Dealloc(p)` | 在 L1/L4 增加显式状态映射表 |
| 定理编号 | `T-001 / T-002 / ...` | `L1 / L2 / T1 / C1 / C2` | 建立跨层 theorem registry 或 cross-layer theorem map |

### 4.2 层边界模糊 / 内容重复

| 主题 | 现状 | 建议 |
|:---|:---|:---|
| NLL / Polonius | L1、L3、L4 均完整讲解 | 权威页集中在 L4；L1/L3 改为摘要 + 链接 |
| Pin / Stacked Borrows / Tree Borrows | L4 所有权页大量侵入 L3 领域 | 迁移到 L3 或 L4 独立子页，L4 聚焦权限/分离逻辑 |
| Async L4 映射 | L3 async 元数据指向 L4 所有权形式化页 | 创建/指定专门 async 操作语义页，修正元数据链接 |

### 4.3 L4 形式化论断缺少下层代码实例

| 论断 | 所在页 | 缺失实例 | 建议 |
|:---|:---|:---|:---|
| 借用检查 P-完全性 | `04_borrow_checking_decidability.md` | 从 L1 引用不能比数据活得久 → 区域约束图 | 增加渐进实例 |
| 别名模型 TSO/Release-Acquire | `02_ownership_formal.md` | L1 `&mut/&T`、L2 `Arc<Mutex>` 示例 | 补充代码 ↔ 形式化映射 |
| Pin LTL 公理 | `02_ownership_formal.md` | L1 ownership / L2 `Box::pin` 渐进示例 | 建立 L1→L2→L3 示例链 |
| 运行时假设（`longjmp` 等） | `06_behavior_considered_undefined.md` | L3 Unsafe 未提供对应示例 | 在 L3 FFI 补充示例或双向链接 |

### 4.4 UB 术语在 L3 与 L4 之间不统一

- L3 使用「越界访问/无效枚举值/ABI 不匹配」等工程分类。
- L4 使用「越界 place projection / 产生无效值 / 错误调用约定或错误展开」等形式化分类。
- **建议**：建立 L3↔L4 UB 分类对照表，L4 每条 UB 项链接到 L3 对应反例。

---

## 五、后续可持续推进计划

### 5.1 治理机制（长期）

| 机制 | 频率 | 动作 | 负责人/工具 |
|:---|:---|:---|:---|
| 权威来源语义抽样审计 | 每 Rust 补丁版本发布 + 每季度 | 抽样 5–8 个核心 concept/ 页与 Reference/Nomicon 对比 | 维护者 + `scripts/authority_semantic_diff.py`（建议新增） |
| 跨层一致性审计 | 每季度 | 检查 L1/L3/L4 同主题术语、定理编号、示例映射 | `scripts/concept_consistency_auditor.py` 扩展跨层模式 |
| 对齐脚本字典更新 | 每半年 | 把 Brown Book、std docs、rustc-dev-guide、Unstable Book 纳入 `topic_authority_aligner.py` | 维护者 |
| 引用精确化巡逻 | 每月 | 扫描 `concept/` 中指向 Reference/Nomicon 首页的链接，改为具体锚点 | `scripts/kb_auditor.py` 扩展规则 |

### 5.2 任务清单（按优先级）

#### P0 — 立即修复（事实性错误，1–2 周内）

| # | 任务 | 目标文件 | 验收标准 |
|---:|---|---|---|
| P0-1 | ✅ **已完成**（2026-07-28）修正 `unsafe extern` 2021-vs-2024 对比表 | `concept/03_advanced/04_ffi/05_unsafe_extern_blocks.md` §2.3 | 表内 2021 列明确 `unsafe extern` 自 1.82 可选；`safe fn` 在 `unsafe extern` 块内可用 |
| P0-2 | ✅ **已完成**（2026-07-28）修正 `let chains` 与 `if-let guards` 稳定版本 | `concept/01_foundation/04_control_flow/03_let_chains.md` §7、§9、权威参考 | `let chains` = 1.88.0 / Edition 2024；`if-let guards` = 1.95.0 |
| P0-3 | ✅ **已完成**（2026-07-28）移除/修正 extern 块内 `type` 示例 | `concept/03_advanced/04_ffi/01_rust_ffi.md` §2.1/2.2 | 仅保留 fn/static；`FILE` 用 `#[repr(C)] struct File { _private: [u8; 0] }`；Callback 类型移到块外 |
| P0-4 | ✅ **已完成**（2026-07-28）更新 `.await` desugaring 规则 | `concept/03_advanced/01_async/01_async.md` §3.1b | 包含 `IntoFuture::into_future` 与临时 `Pin::new_unchecked` |
| P0-5 | ✅ **已完成**（2026-07-28）修复运行时矩阵重复 Tokio 行 | `concept/03_advanced/01_async/01_async.md` §2.3 | 第二行改为 `async-std`（已弃用可注） |
| P0-6 | ✅ **已完成**（2026-07-28）定位 2 处 body TODO；均为误报，无需修改 | `tmp/completeness_symdiff.json` | 一为 `external_authority_topic_index.md` 图例符号 `- ❌ — 真正缺口，待补充`；一为 `api_naming_conventions.md` 整行被截断显示，实际内容完整 |

#### P1 — 短期补齐（语义深度缺口，2–4 周内）

| # | 任务 | 目标文件 | 验收标准 |
|---:|---|---|---|
| P1-1 | ✅ **已完成**（2026-07-28）补齐 lifetime elision 全场景 | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | 覆盖 trait object default bounds、`const`/`static` `'static`、fn ptr/closure elision、`'_` |
| P1-2 | ✅ **已完成**（2026-07-28）扩展 variance 表格至 Reference 完整版 | `concept/04_formal/00_type_theory/02_subtype_variance.md` | 含 `dyn Trait<T> + 'a`、`PhantomData<T>`、`[T]`/`[T;n]`、`fn() -> T` |
| P1-3 | ✅ **已完成**（2026-07-28）扩展 UB 清单边界细节 | `concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | 含 pointer span/`isize::MAX`、misaligned place、liveness bounds、union/padding 例外 |
| P1-4 | ✅ **已完成**（2026-07-28）修正 Miri 数据竞争描述 | `concept/03_advanced/02_unsafe/01_unsafe.md` | 统一为「Miri 无法检测数据竞争」并交叉引用 Loom/TSan |
| P1-5 | ✅ **已完成**（2026-07-28）修正 UB 分类中栈溢出/除以零的表述 | `concept/03_advanced/02_unsafe/01_unsafe.md` | 区分为 runtime faults / aborts，引用 Reference overflow-checks caveat |
| P1-6 | ✅ **已完成**（2026-07-28）增加 `async fn` 参数捕获与 drop 顺序边界 | `concept/03_advanced/01_async/01_async.md` §3.1 | 含代码示例与 lifetime 错误解释 |
| P1-7 | ✅ **已完成**（2026-07-28）增加 `async unsafe fn` 边界示例 | `concept/03_advanced/01_async/01_async.md` | 展示 `.await` 无需 unsafe |
| P1-8 | ✅ **已完成**（2026-07-28）扩展 Pin structural pinning / `Pin::set` / ManuallyDrop 反模式 | `concept/03_advanced/01_async/08_pin_unpin.md` | 与 std::pin 文档对齐 |
| P1-9 | ✅ **已完成**（2026-07-28）弱化 HM / Principal type 定理表述 | `concept/01_foundation/02_type_system/01_type_system.md` | 改为条件/限定性 claim |
| P1-10 | ✅ **已完成**（2026-07-28）修正 `'static ⊑ 'a` 方向说明 | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | 明确 `⊑` = outlives，与 subtype 方向相反 |

#### P2 — 中期完善（结构优化与持续对齐，1–3 个月）

| # | 任务 | 目标文件 | 验收标准 |
|---:|---|---|---|
| P2-1 | ✅ **已完成**（2026-07-28）引用精确化：新增 `scripts/authority_link_precision.py`/`fix_authority_link_precision.py`，批量修复 112 处 S1 链接，剩余 31 处多为复合/元数据链接，需人工复核 | 全 `concept/` | S1 164 → 31；核心概念页首页链接基本清除 |
| P2-2 | ✅ **已完成**（2026-07-28）修正 TRPL Advanced Lifetimes 误导链接 | `concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` | 全部改为「TRPL — Lifetimes」指向 ch10-03-lifetime-syntax.html |
| P2-3 | ✅ **已完成**（2026-07-28）建立跨层 theorem registry / inter_layer_map 条目 | `concept/00_meta/04_navigation/04_inter_layer_map.md` §5.3、`theorem_registry.md` §8 | 所有权状态 Own/Shr/Mut/Dealloc、定理编号 T-xxx↔L4 本地记号、async 语义、UB L3↔L4 四组映射 |
| P2-4 | ⏳ 待后续季度处理：NLL/Polonius/Pin/Tree Borrows 跨层重复清理 | 多个文件 | 每主题单一权威页，其余 stub + 链接（涉及 L1/L3/L4 多处迁移，需单独专项） |
| P2-5 | ⏳ 待后续季度处理：创建/指定专门 async 操作语义 L4 页 | `concept/04_formal/03_operational_semantics/03_operational_semantics.md` 或新页 | 含 Future/poll/await 小步规则（需新增独立 L4 页） |
| P2-6 | ✅ **已完成**（2026-07-28）扩展 recursive type / `str` primitive / user-defined type limitations | `concept/01_foundation/02_type_system/01_type_system.md` | 类型分类矩阵新增 `str` 为 built-in primitive type；§5.4 递归类型限制已含名义类型锚点、递归字段须为指针 |
| P2-7 | ⏳ 待后续季度处理：扩展 trait solver 与 MIR 编译器内部细节 | `concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md`, `02_mir_codegen_llvm_primer.md` | 覆盖 lifetime-in-selection、type-check/codegen split、StorageLive/Dead、ValTrees |
| P2-8 | 🔄 **进行中**（2026-07-28）补齐 Edition 2024 std lib / rustfmt / TRPL Ch21 细节 | `concept/07_future/01_edition_roadmap/02_edition_guide.md`, `04_advanced_traits.md` | 解决外部索引中 4 处 ⚠️ |
| P2-9 | ✅ **已完成**（2026-07-28）扩展 `topic_authority_aligner.py` 字典 | `scripts/topic_authority_aligner.py` | 新增 `MANUAL_AUTHORITY_COVERAGE`，将 let chains / never type / const generics / Cow / sanitizers / unsafe reference 6 项移出「项目独有」 |
| P2-10 | ✅ **已完成**（2026-07-28）新增 `authority_semantic_diff.py` 检查器 | `scripts/authority_semantic_diff.py` | 核心页权威语义关键词扫描；当前 P0=0 / P1=0 |

---

## 六、建议新增的检查器/脚本

为将本轮对称差审计常态化，建议新增或扩展以下工具：

1. **`scripts/authority_link_precision.py`**
   - 扫描 `concept/` 中指向 `doc.rust-lang.org/reference/introduction.html` 或 `nomicon/` 根目录的链接。
   - 输出需要精确化的链接列表。

2. **`scripts/authority_semantic_diff.py`（原型）**
   - 对核心概念页（ownership/lifetimes/unsafe/async/types）做关键词覆盖扫描。
   - 检查是否包含 `IntoFuture`, `Pin::new_unchecked`, `isize::MAX`, `PhantomData`, `dyn Trait` 等权威关键词。
   - 作为观察门，不阻断 CI。

3. **`scripts/cross_layer_consistency.py` 扩展**
   - 在现有 `concept_consistency_auditor.py` 基础上增加跨层定理编号/术语一致性检查。

---

## 七、验收标准

- P0 任务全部完成并通过以下检查：
  - `cargo test --workspace --quiet`
  - `python scripts/kb_auditor.py`
  - `python scripts/check_concept_code_blocks.py --strict`
  - 重新运行 `check_version_semantic_injection.py` / `check_cross_domain_coverage.py` / `semantic_health.py` 仍通过
- P1 任务完成 ≥80%。
- P2 任务完成 ≥50% 或纳入下季度计划。
- 新增/修改的 concept 页均符合 AGENTS.md §4.2 元数据模板（EN/Summary/Rust 版本/Bloom 层级/权威来源）。

---

## 八、附录：抽样审计文件清单

| 审计组 | 文件 | 审计方式 |
|:---|:---|:---|
| 所有权/借用/生命周期 | `01_ownership.md`, `02_borrowing.md`, `03_lifetimes.md`, `04_lifetimes_advanced.md`, `06_memory_model.md` | 子代理 vs Reference/Nomicon |
| Async/Unsafe/FFI | `01_async.md`, `08_pin_unpin.md`, `01_unsafe.md`, `01_rust_ffi.md`, `05_unsafe_extern_blocks.md`, `03_let_chains.md` | 子代理 vs Reference/Edition Guide/Async Book |
| 类型系统/形式化 | `01_type_system.md`, `02_subtype_variance.md`, `03_trait_solver_in_rustc.md`, `02_mir_codegen_llvm_primer.md`, `06_behavior_considered_undefined.md` | 子代理 vs Reference/rustc-dev-guide |
| 内部一致性 | ownership/lifetimes/async/unsafe 四组 L1-L4 页 | 子代理跨层对比 |
| 项目独有主题 | `04_topic_authority_alignment_map.md` §4 抽样 37 份 | 子代理分类 |

---

> **维护说明**: 本计划应与 `concept/00_meta/02_sources/06_external_authority_topic_index.md` §十一「未覆盖缺口清单」联动更新。每完成一项 P0/P1/P2 任务，应在本计划对应条目后追加 `✅ 完成日期 + commit/PR 引用`。
