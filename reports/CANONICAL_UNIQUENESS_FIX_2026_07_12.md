# Canonical 权威页唯一性修复报告

> **日期**: 2026-07-12
> **依据**: AGENTS.md §2 Canonical 规则（同一概念只能有一个权威页，其余改为重定向 stub）
> **范围**: 生命周期高级主题双权威页合并、Safety Tags 三份重复合并、新增权威页唯一性检查脚本
> **状态**: ✅ 完成（未执行 git commit）

---

## 一、合并决策与理由

### 1.1 生命周期高级主题（任务 1）

| 文件 | 体量 | 决策 |
|---|---|---|
| `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` | 73KB → 82KB | ✅ **保留为权威页** |
| `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` | 34KB → 0.8KB | 🔄 **改为重定向 stub** |

**理由**：

1. A 位于 `01_foundation/01_ownership_borrow_lifetime/`（所有权/借用/生命周期主目录），是生命周期主题的自然归属；
2. A 体量更全：独有 Polonius 专章、Elision 完整形式化、`impl Trait` 生命周期推断、Lending Iterator（GATs+HRTB）案例、union 安全边界、5 组边界测试；
3. B 的 HRTB/Elision/Pin 章节与 A 大面积重复，仅少量独有内容需迁移。

### 1.2 Safety Tags / RFC #3842（任务 2）

| 文件 | 体量 | 决策 |
|---|---|---|
| `concept/07_future/03_preview_features/08_safety_tags_preview.md` | 31KB → 32KB | ✅ **保留为 preview 权威页** |
| `concept/07_future/03_preview_features/31_safety_tags_preview.md` | 7KB → 0.7KB | 🔄 **改为重定向 stub（指向 08）** |
| `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` | 6.6KB → 1.2KB | 🔄 **改为重定向 stub（指向 08）** |

**理由**：

1. 08 最全面：含形式化语义（契约的谓词逻辑表示）、工具集成（Miri/Kani/Prusti）、演进路线、附录标准 Tag 库设想、5 组边界测试；
2. 31 与 08 同目录同主题（RFC #3842），内容完全被 08 覆盖；
3. 33 虽在 `04_formal/02_separation_logic/`，但经通读确认**不含独立的形式化（分离逻辑）推导**——其「形式化」内容仅为 3 条工具映射 bullet，与 31 的 v2 相似度达 0.855，且 08 的「二、形式化语义」一节已覆盖并超越。故按任务约定的"否则改 stub"分支处理，stub 中保留指向 AutoVerus/Miri/BorrowSanitizer 深度页的形式化延伸阅读链接。

---

## 二、内容迁移清单

### 2.1 迁入 `30_lifetimes_advanced.md`（新增「十八、变型、闭包生命周期与常见陷阱」）

| 来源（B 章节） | 迁移内容 | 去向 |
|---|---|---|
| B §1.3 变型 | 三种变型定义、类型构造器变型表（`&T`/`&mut T`/`Box`/`Cell`/`fn` 等）、生命周期变型规则 | A §18.1 |
| B §2.3 生命周期与闭包 | 引用/move 捕获、`'static` 闭包、借用闭包、Fn/FnMut/FnOnce 选择 | A §18.2 |
| B §三 模式矩阵 | 场景→方案→代码模式矩阵（6 种场景） | A §18.3 |
| B §五 常见陷阱 | 5 个陷阱（返回局部引用、标注不足、结构体存引用、HRTB 误用、忘记 move） | A §18.4 |
| B §10.3 边界测试 | `dyn Processor<'static>` trait object 生命周期固化编译错误 | A §18.5 |
| B 测验 4 | `T: Trait + 'static` 生命周期 bound 语义测验 | A 测验 6 |

**未迁移（A 已有等价或更全内容）**：B 的 HRTB 基础（A §10.1/§15 更全）、Elision 三条规则（A §13 形式化更全）、自引用与 Pin（A §10.2 更全）、B 测验 1/2/3/5（与 A 测验 1/2/3/4 重复）。A 的目录（📑 目录）已同步加入新章节与测验 6 条目。

### 2.2 迁入 `08_safety_tags_preview.md`

| 来源 | 迁移内容 | 去向 |
|---|---|---|
| 31/33 独有事实 | 「研究原型已梳理 21 个基础标签，覆盖 std 约 96% 公开 unsafe API」+ RFC #3842 `requires`/`checked` 机制摘要 | 08 §1.3 新增 blockquote |
| 31/33 独有来源 | RFC #3842 PR、safety-tool slides、safer-rust/safety-tags 研究仓库 | 08 §六 来源表 |

---

## 三、链接更新计数

### 3.1 指向 B（18_lifetimes_advanced.md）的链接 → 改指 A

| 文件 | 更新数 |
|---|---|
| `concept/SUMMARY.md`（并删除重复条目） | 1 链接 + 1 条目移除 |
| `concept/02_intermediate/README.md` | 1（加注合并说明） |
| `concept/03_advanced/README.md` | 1（L2→L1 表述修正） |
| `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md` | 1（标注已合并） |
| `concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md` | 1 |
| `concept/00_meta/02_sources/topic_authority_alignment_map.md` | 1（路径标注） |
| `concept/00_meta/03_audit/asp_marking_guide.md` | 1（ID 更新） |
| `docs/trpl_3rd_ed_diff.md` | 2 |
| `crates/c01_ownership_borrow_scope/docs/tier_02_guides/03_lifetimes_practice.md` | 1 |
| `crates/c04_generic/docs/tier_04_advanced/02_generics_and_lifetimes.md` | 1 |
| `scripts/replace_placeholder_generic.py`（CONCEPT_MAP） | 1 |
| **小计** | **13** |

另修复 2 处指向 A 的**既有死链**（相对路径错误，非本次引入）：
`crates/c01_.../tier_03_references/03_lifetimes_reference.md`、`crates/c02_type_system/docs/tier_02_guides/05_lifetimes_guide.md`。

### 3.2 指向 31/33（safety tags）的链接 → 改指 08

共 **23 处链接**（由脚本按相对路径自动重写），涉及 16 个文件：

- `concept/SUMMARY.md`（2 链接 + 2 重复条目移除，mdbook 禁止重复文件条目）
- `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md`、`02_attribute_relationship_atlas.md`、`05_logical_reasoning_atlas.md`（各行标注已合并）
- `concept/04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md`、`02_separation_logic/34_borrow_sanitizer_in_formal.md`
- `concept/04_formal/04_model_checking/`：`13_formal_methods.md`、`22_modern_verification_tools.md`、`24_autoverus.md`、`31_miri.md`、`32_kani.md`
- `concept/07_future/00_version_tracking/rust_1_98_preview.md`、`02_stabilized_features/borrow_sanitizer.md`
- `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md`、`33_autoverus_preview.md`
- `concept/07_future/04_research_and_experimental/43_rust_for_linux.md`
- `concept/00_meta/02_sources/topic_authority_alignment_map.md`（路径标注）

### 3.3 合计

**38 处链接重写 + 3 处 SUMMARY 重复条目移除 + 2 处既有死链修复**。
验证：对 concept/knowledge/docs/content/crates/exercises 全量扫描，75 处相关链接（lifetimes_advanced/safety_tags）**0 死链**；三个 stub 文件均不再含「本文件为 concept/ 权威页」声明。

---

## 四、新增脚本 `scripts/check_canonical_uniqueness.py`

- **检测 (a)**：多个非 stub 文件声明「本文件为 concept/ 权威页」且文件名词干相同/标题高度相似 → 疑似双权威页；
- **检测 (b)**：同目录编号不同但主题词干相同的双文件；
- **分级**：ERROR（词干完全相同，`--strict` 时 exit 1）/ WARN（模糊相似，仅报告不阻断，避免跨层合法主题误报，如 `Ownership` vs `Ownership Formal`）；
- **排除**：`archive/`、`sources/`、placeholder、template/atlas/glossary 文件、README/SUMMARY/INDEX；
- **stub 识别**：含「本主题已合并至」「本文件保留为重定向」等标记的文件不参与判定；
- 已登记至 `scripts/README.md` 审计与检查表。

**当前基线**：扫描 430 页，ERROR 3 处 / WARN 241 处。本任务修复的两对（lifetimes_advanced、safety_tags）均已归零。

### ⚠️ 新发现的既有违规（超出本任务范围，建议后续治理）

1. `concept/04_formal/04_model_checking/13_formal_methods.md` ↔ `concept/07_future/04_research_and_experimental/02_formal_methods.md`（同词干 `formal_methods`，EN 标题相同）；
2. `concept/06_ecosystem/11_domain_applications/21_game_development.md` ↔ `26_game_development.md`（同目录同词干，EN 标题相同）。

---

## 五、验证结果

| 验证项 | 结果 |
|---|---|
| `python scripts/detect_content_overlap.py` | ✅ exit 0；剩余 1 对（migration_197 vs cheatsheet，0.60）为既有的跨轨速查重叠，与本任务无关 |
| `python scripts/detect_content_overlap_v2.py --budget 999999` | ✅ 原 0.855 的 `33_safety_tags_in_formal` ↔ `31_safety_tags_preview` 对、lifetimes 双页对均消失；剩余命中均为既有无关对（如 autoverus 0.871） |
| 死链检查（相关链接 75 处） | ✅ 0 死链 |
| `python scripts/check_canonical_uniqueness.py` | ✅ 目标两对已归零；`--strict` exit 1 仅因上述 2 对既有违规 |
| `mdbook build` | ✅ 通过（SUMMARY.md 重复条目已清除） |

---

## 六、过程风险记录

执行期间（约 03:54、04:01）检测到**外部进程两次还原/修改 concept/ 下文件**（`git status` 显示非本任务产生的大量 00_meta 修改与 `concept_index.json`、`kg_data_v2.json` 删除）。本任务的全部内容编辑已在第二次还原后重新应用并逐项复核（stub 体量、合并章节、链接目标、mdbook 构建均二次验证通过）。建议主代理注意工作区存在并发写入者。
