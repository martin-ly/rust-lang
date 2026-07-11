# 概念一致性审计器复活与遗留双权威页处置报告

> **日期**: 2026-07-12
> **范围**: `scripts/concept_consistency_auditor.py` 复活并接入质量门；首批矛盾处置；3 组遗留双权威页治理
> **状态**: ✅ 完成（未执行 git commit）

---

## 一、审计器复活（任务 1）

### 1.1 修复的问题

| 问题 | 处置 |
|---|---|
| 硬编码权威页路径全部失效（如 `concept/01_foundation/03_lifetimes.md`、`concept/03_advanced/03_unsafe.md`，文件已迁入子目录），导致 4 个假 ERROR | 新增 `CANONICAL_PAGES` 基线表 + `resolve_canonical()` 动态解析（基线不存在时按文件名回退查找） |
| 报告路径为固定的 `reports/concept_consistency_report.md` | 改为 `reports/CONCEPT_CONSISTENCY_AUDIT_<YYYY_MM_DD>.md`（与 reports/ 日期风格一致），删除旧报告文件 |
| 无 CLI，错误即 exit 1，无法作为观察门 | 新增 `--strict`（有 ERROR 级发现时 exit 1）/ `--json`；默认观察模式 exit 0 |
| 提取器为 4 套重复的手写函数 | 统一为规则表 `_EXTRACT_RULES`（标签/行模式/排除模式）+ 单一 `extract_concept_defs()` |

### 1.2 定义抽取覆盖（8 个概念族，1623 条定义 / 468 文件）

Send/Sync（基线 `concept/03_advanced/00_concurrency/17_send_sync_auto_traits.md`）、所有权、**借用（新）**、生命周期、**内部可变性（新）**、**Pin/Unpin（新）**、**协变逆变（新，基线 `04_formal/00_type_theory/06_subtype_variance.md`）**、unsafe。

### 1.3 矛盾检测能力

- 权威页存在性与核心定义覆盖校验（8 个概念族）
- 具体类型 Send/Sync 属性跨文件矛盾（`Rc !Send+!Sync` 型）
- 类型构造器变型矛盾（严格断言形式 + 假设语境过滤，见 §三）
- 通用极性冲突（可变引用独占 / RefCell 运行时检查 / Unpin 为 auto trait）
- 跨文件 § 段落引用有效性（新增链接文本内 § 归属、中文数字章节 §二 支持、误关联抑制）

---

## 二、质量门接入（任务 2）

> **注意**: AGENTS.md §5.1 已被前序会话（`reports/CANONICAL_UNIQUENESS_FIX_2026_07_12.md`）部分更新为「17 项」，将门 17 登记为 `check_canonical_uniqueness.py`，但该门未接入 `run_quality_gates.sh` / CI。为保持一致，本次将概念一致性审计器定为**门 18**，并补全门 17 的接线。

| 位置 | 变更 |
|---|---|
| `scripts/run_quality_gates.sh` | 新增 2 个观察门：`Canonical Uniqueness (observe)`（门 17）、`Concept Consistency Audit (observe)`（门 18）；汇总语更新为「18 gates (10 blocking + 8 semantic observe)」 |
| `.github/workflows/quality_gates.yml` | 仿照现有观察 job 新增 `canonical-uniqueness` 与 `concept-consistency-audit` 两个 job（均 `continue-on-error: true`），并加入 summary 的 `needs` 与评论模板 |
| `AGENTS.md` §5.1 | 更新为「18 项：10 阻断 + 8 语义观察」；门 17 补充进阶豁免说明与 ERROR 0 基线；新增门 18 条目（基线：错误 0 / 警告 0） |
| `scripts/README.md` | `concept_consistency_auditor.py` 登记更新为质量门 18 完整描述（`check_canonical_uniqueness.py` 前序已登记） |

两门均为 observe 模式：默认 exit 0，`--strict` 可转阻断。

---

## 三、首批矛盾处置（任务 3）

扩展后审计器首批输出 15 个 ERROR，逐条判定如下——**全部为假阳性或提取器缺陷**，规则修正后 0 错误：

### 3.1 概念矛盾类（3 项，均假阳性 → 调整规则）

| 发现 | 真因 | 规则修正 |
|---|---|---|
| `&T` 变型矛盾（ownership/borrowing 称 invariant vs 基线 covariant） | 匹配到 Iris「托管状态 (invariant)」、「位置不变性」等非变型语境的英文 invariant | 变型断言仅接受显式形式（「对 T 协变/逆变/不变」「→ 协变」「是/为/:/： + 关键词」、表格 `| T | 不变 |`），丢弃裸英文关键词 |
| `&mut T` 变型矛盾（基线页"假设…协变"、ownership_formal "逆方向"） | 反证法假设行、设问/反例行被当作事实断言 | 新增 `HYPOTHESIS_MARKERS` 行级过滤（假设/如果/为什么/误用/反例/不是…）；构造器与断言限定 40 字符内最近归属 |
| `RefCell` 运行时检查极性矛盾（24 文件） | 反向模式命中「而非编译期」「替代编译期检查」「等价于编译期借用检查」等一致性表述 | 反向模式收紧为显式断言（「借用检查…发生/进行/完成于编译期」），并加排除模式（而非/推迟/替代/移/等价/绕过/不同） |

**真矛盾：0 项**。知识库在 Send/Sync、所有权、借用、生命周期、内部可变性、Pin/Unpin、变型、unsafe 八个概念族上无跨文件定义矛盾。

### 3.2 跨文件 § 引用类（12 项：4 假阳性 + 1 中文数字支持 + 7 真陈旧引用）

| 引用 | 判定 | 处置 |
|---|---|---|
| `40_generic_associated_types.md:512` ×2、`37_async_cancellation_safety.md:404` | 假阳性：§ 在**链接文本内**（`[主题 §1.2](file.md)`），被错误关联到下一链接 | 新增模式 0：链接文本内 § 归属本链接（验证后 §1.2/§5.6/§9.5/§8.7/§2.2/§10.2 全部有效） |
| `migration_197_decision_tree.md:705`（迁移树 §7） | 假阳性：「迁移树 §7」指向本文自身，非链接目标 | 模式 3 增加间隔约束：`](link)` 与 § 之间只允许标点/空白，含中文或 `[` 即不关联 |
| `11_atomics...md:1412`（29_memory_model §2）、`comprehensive_rust_mapping.md:137`（17_cross_compilation §3） | 目标用中文数字章节（`## 二、`），验证器不支持 | `extract_sections` 新增中文数字标题映射（一..九十九）；`§二/§3` 验证通过 |
| `comprehensive_rust_mapping.md:104/109/118`（§1.1/§3/§3.2 均不存在） | **真陈旧引用** | 修正为 §2.6（rustup 工具链管理）/ §4.1（ADT 枚举+结构体）/ §1.2（match 模式匹配） |
| `learning_mvp_path_en.md:165/173/187`（quiz §1–2、§3–4 不存在） | **真陈旧引用** | 修正为 §一（并发基础 Q1–Q3）/ §2.1（通道模式，producer-consumer）/ §二（异步编程） |
| `11_atomics...md:1412` 句尾多余「§2」 | **真冗余引用**（「§Rust 1.97.0 交叉语义」已完整指节） | 删除句尾「 §2」 |

---

## 四、遗留双权威页处置（任务 4）

### 4.1 formal_methods（L4 ↔ L7）

通读两文后判定：**L7 页为唯一权威页**，L4 页改重定向 stub。

| 文件 | 体量 | 决策 | 理由 |
|---|---|---|---|
| `07_future/04_research_and_experimental/02_formal_methods.md` | 76KB | ✅ 权威页 | 内容最全新（changelog v1.3, 2026-05-22）：五层验证模型、类型系统→定理证明光谱、CI/CD 集成、工业案例、TLA+/P/PObserve 规约示例；35 处入链（导航/atlas/各层概念页均以其为 hub）；`concept_index.md` 已将其登记为 Formal Methods 入口 |
| `04_formal/04_model_checking/13_formal_methods.md` | 28KB → 1.4KB | 🔄 重定向 stub | 其核心内容（验证层次、Kani/Creusot/Miri 介绍、unsafe 边界验证模式、Prusti/Viper）已被 L7 页 §一/§五/§十一 覆盖并超越；13 处入链经 stub 重定向保持有效 |

配套变更：L7 页 EN Summary 由模板套话（"Core Rust concept covering practical examples."）重写为真实摘要，权威声明注明合并关系；`concept/SUMMARY.md`、`concept/04_formal/README.md`、`topic_authority_alignment_map.md` 中指向 L4 页的条目更新为权威页/注明重定向。

### 4.2 game_development（同目录 21 ↔ 26）

判定：**21 为唯一权威页**，26 改重定向 stub。

| 文件 | 决策 | 理由 |
|---|---|---|
| `21_game_development.md`（Rust 游戏开发生态） | ✅ 权威页 | 外部引用 hub：`49_game_engine_internals.md` 与 docs/ 下 bevy/wgpu/gui 三份架构研究笔记均链接 21；两文相似度仅 0.298 但主题完全重叠（ECS/wgpu/音频/反命题/边界测试/测验） |
| `26_game_development.md`（Rust 游戏开发） | 🔄 重定向 stub | 入链仅 SUMMARY/README/atlas；独有内容（winit、gltf、hecs、热重载折衷、archetype/序列化边界场景）已以「补充生态工具」一节迁入 21 的「六、来源与延伸阅读」，进阶场景指向 `07_game_ecs.md` 与 `49_game_engine_internals.md` |

`concept/SUMMARY.md`、`concept/06_ecosystem/README.md` 的 26 条目已注明重定向。

### 4.3 error_handling 三连（L1 basics ↔ L2 主页 ↔ L2 deep dive）

通读判定：**合法进阶关系，非重复权威页**。三者体量与定位清晰分层：L1 基础（35KB，Result/Option/? 入门）→ L2 主页（135KB，传播模式/自定义错误/工程实践总览）→ L2 深入（34KB，组合子代数/From 转换/错误链/thiserror-anyhow-eyre 框架生态）。处置：

1. 三页各新增「层级定位」声明，明确 basics → 主页 → deep dive 的进阶关系；
2. 互链补全：32 ↔ 04 已有双向链接，本次新增 04 → 16、16 → 32/04 的链接；
3. `check_canonical_uniqueness.py` 新增**进阶关系豁免**（`PROGRESSION_SUFFIXES = basics/basic/advanced/deep_dive`）：两词干去掉进阶后缀后基础词干相同即视为合法分层，不报双权威页（同时豁免 W3/W4/W8 及 lifetimes/lifetimes_advanced 等既有噪音 WARN）。

---

## 五、验证结果（任务 5）

| 验证项 | 命令 | 结果 |
|---|---|---|
| 权威页唯一性（阻断模式） | `python scripts/check_canonical_uniqueness.py --strict` | ✅ exit=0（ERROR 0；WARN 212 为既有跨层同主题观察项，不阻断） |
| 概念一致性审计（观察模式） | `python scripts/concept_consistency_auditor.py` | ✅ exit=0（468 文件 / 1623 定义 / 220 引用 / 0 错误 0 警告 0 提示） |
| 概念一致性审计（阻断模式） | `python scripts/concept_consistency_auditor.py --strict` | ✅ exit=0 |
| 新门接线运行 | 按 `run_quality_gates.sh` 的 `run_gate` 方式单独运行门 17/18 | ✅ 两门均 passed；`bash -n` 语法通过 |
| CI 配置 | `yaml.safe_load(quality_gates.yml)` | ✅ 解析通过 |
| 死链（定向） | 对全部新增/修改链接做路径解析检查 | ✅ 0 死链 |
| kb_auditor 全量死链 | 未运行（耗时；已以上述定向检查替代，全量留给 CI 门 7） | ⏭️ 跳过 |

## 六、遗留事项

1. `concept/00_meta/knowledge_topology/*_atlas.md`（自动生成文件）仍保留 13_formal_methods / 26_game_development 作为概念定义行，需下次 atlas 再生成时刷新；链接目标经 stub 仍有效。
2. `check_canonical_uniqueness.py` 的 212 条 WARN 多为合法的跨层同主题（如 rust_vs_cpp vs rust_vs_go、version_tracking 系列），属观察噪音；后续可考虑按目录白名单进一步降噪。
3. 审计器变型检测目前只追踪对类型参数 `T` 的变型；生命周期参数变型（`&'a T` 对 `'a` 协变）未建模，如需可后续扩展。
