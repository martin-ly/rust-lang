# 判定表推广报告（Decision Table Rollout）

> **日期**: 2026-07-12
> **范围**: `concept/` L1–L3 旗舰概念页
> **目标**: 将「判定表/判定矩阵」形式从少数页面推广到 25 个核心概念页
> **执行方式**: 一次性脚本 `tmp/rollout_decision_tables.py`（锚点唯一性校验 + CRLF 保持），未做 git commit

---

## 一、覆盖前后对比

| 指标 | 推广前（HEAD） | 推广后 |
|:---|:---:|:---:|
| 含「判定表/判定矩阵」**标题节**的 concept/ 文件数 | 6 | **31** |
| 其中本次新增 | — | **25** |

推广前的 6 个基线文件：`01_traits.md`（§2.3 Orphan Rule 判定矩阵）、`01_concurrency.md`（§2.1 Send/Sync 判定矩阵）、`17_send_sync_auto_traits.md`、`32_const_generics.md`（§八）、`40_generic_associated_types.md`（§六）、`37_async_cancellation_safety.md`（§五）。

> 说明：任务书中提到的 26 个候选里，`01_traits`、`01_concurrency`、`17_send_sync_auto_traits`、`32_const_generics`、`40_generic_associated_types` 经 grep 确认已有判定表/判定矩阵，按规则排除。`02_generics.md` 与 `02_async.md` 的 grep 命中经人工核实仅为指向他页的权威来源链接**提及**（blockquote），并非实际表格，故纳入本次推广。缺口由同属 L1–L3 旗舰层的 5 个补充页补齐：`03_memory_management`、`11_atomics_and_memory_ordering`、`13_panic_and_abort`、`39_dispatch_mechanisms`、（`14_structs` 与 `15_enumerations` 按实际文件名各计一页）。

## 二、25 页清单与行数

统一表头：`| 场景/条件 | 判定结论 | 依据（定理/规则） | 反例或失效条件 |`。插入位置均为「相关概念」节之前或决策树附近（`### x.y` 子节者同步补了目录条目）。

| # | 文件（相对 `concept/`） | 判定表节 | 行数 | 插入位置 |
|:---:|:---|:---|:---:|:---|
| 1 | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 5.3 判定表：值语义场景的所有权处置 | 7 | §5 决策树节内（§5.2 之后） |
| 2 | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | 5.3 判定表：函数签名的借用形态判定 | 7 | §5 决策树节内（§5.2 之后） |
| 3 | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | 判定表：生命周期标注与失效场景判定 | 8 | 「相关概念」之前 |
| 4 | `01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md` | 判定表：Move / Copy / Clone 处置判定 | 6 | 「相关概念」之前 |
| 5 | `01_foundation/02_type_system/04_type_system.md` | 判定表：多态机制与类型层级判定 | 6 | 「十一、相关概念链接」之前 |
| 6 | `02_intermediate/01_generics/02_generics.md` | 判定表：泛型使用与边界判定 | 7 | 「十一、相关概念链接」之前 |
| 7 | `02_intermediate/03_error_handling/04_error_handling.md` | 判定表：错误处理策略判定 | 8 | 「十、相关概念链接」之前 |
| 8 | `03_advanced/01_async/02_async.md` | 判定表：异步选型与 await 边界判定 | 6 | 「相关概念链接」之前 |
| 9 | `03_advanced/02_unsafe/03_unsafe.md` | 判定表：unsafe 使用与 UB 边界判定 | 9 | 「相关概念链接」之前 |
| 10 | `02_intermediate/02_memory_management/12_smart_pointers.md` | 判定表：智能指针选型判定 | 8 | 「相关概念」之前 |
| 11 | `02_intermediate/02_memory_management/08_interior_mutability.md` | 判定表：内部可变性选型判定 | 7 | 「相关概念」之前 |
| 12 | `03_advanced/01_async/06_pin_unpin.md` | 判定表：Pin 使用判定 | 6 | 「相关概念」之前 |
| 13 | `01_foundation/07_modules_and_items/11_modules_and_paths.md` | 判定表：模块可见性与路径判定 | 7 | 「相关概念」之前 |
| 14 | `02_intermediate/05_modules_and_visibility/10_module_system.md` | 判定表：可见性与 crate 组织判定 | 5 | 「相关概念」之前 |
| 15 | `01_foundation/07_modules_and_items/14_structs.md` | 6.4 判定表：结构体形式与更新语法处置 | 6 | §六 反例节内（§6.3 之后） |
| 16 | `01_foundation/07_modules_and_items/15_enumerations.md` | 6.4 判定表：枚举建模与匹配处置 | 7 | §六 反例节内（§6.3 之后） |
| 17 | `02_intermediate/07_iterators_and_closures/15_iterator_patterns.md` | 判定表：迭代器适配器与消费者判定 | 9 | 「相关概念」之前 |
| 18 | `02_intermediate/04_types_and_conversions/07_closure_types.md` | 判定表：闭包 Trait 约束与捕获判定 | 7 | 「相关概念」之前 |
| 19 | `03_advanced/03_proc_macros/04_macros.md` | 判定表：宏 vs 函数/泛型/const fn 判定 | 7 | 「相关概念链接」之前 |
| 20 | `06_ecosystem/04_web_and_networking/27_web_frameworks.md` | 判定表：Web 框架选型判定 | 6 | 「相关概念」之前 |
| 21 | `06_ecosystem/03_design_patterns/02_patterns.md` | 判定表：设计模式迁移与选型判定 | 6 | 「十、相关概念链接 {L6}」之前 |
| 22 | `02_intermediate/02_memory_management/03_memory_management.md` | 判定表：内存管理策略判定 | 7 | 「十、相关概念链接」之前 |
| 23 | `03_advanced/00_concurrency/11_atomics_and_memory_ordering.md` | 判定表：内存序选择判定 | 6 | 「相关概念」之前 |
| 24 | `01_foundation/08_error_handling/13_panic_and_abort.md` | 判定表：Panic vs Result 处置判定 | 6 | 「相关概念」之前 |
| 25 | `02_intermediate/00_traits/39_dispatch_mechanisms.md` | 5.6 判定表：静态 vs 动态分发场景判定 | 5 | §5 决策树节内（§5.5 之后） |

行数合计 166，全部落在 5–10 行要求内。

## 三、抽查 3 页质量自评

### 3.1 `01_ownership.md`（L1 基础层）

- **主题相关性**：7 行全部从本页既有内容提炼——§2.1 核心规则矩阵（唯一所有者）、§5.1 Copy 决策树三条件、§5.2 违规边界（E0382/E0499/E0502）、§6.1 RAII 定理与「模循环引用」限定、§8.3 `mem::forget`/`ManuallyDrop` 例外。无编造判定。
- **技术准确性**：move/借用/Box/Rc/Copy/Drop 六类场景的判定结论与编译器行为一致；`Box` 行明确指向 `12_smart_pointers.md` 权威页而非展开复述，符合 canonical 规则。
- **风格一致性**：`### 5.3` 子节与 §5.1/§5.2 决策树同级，表格分隔行 `|:---|` 与本页既有表格一致，目录已同步。
- **自评**：✅ 通过。可改进点：「依据」列对 §6.1 的引用可精确到前提编号（已部分做到）。

### 3.2 `03_unsafe.md`（L3 高级层）

- **主题相关性**：9 行 = §6.1「我需要用 unsafe 吗？」决策树四条路径（FFI/性能/布局/不用）+ §6.2 UB 边界判定五条（null 解引用/transmute/unsafe impl Send/未初始化内存/创建未解引用），外加 Miri/Tree Borrows 验证行，全部有页内出处。
- **技术准确性**：「创建裸指针合法、解引用才 UB」（§6.2 W1）、「`unsafe impl Send for Rc<T>` 编译通过但 UB」等关键区分均正确保留；「Miri 未覆盖全部 UB 种类」的失效条件避免了过度承诺。
- **风格一致性**：`## 判定表` 置于「相关概念链接」之前，与 32_const_generics 的「§八 判定表」位置模式一致。
- **自评**：✅ 通过。9 行为 25 页中最多，但 unsafe 页 UB 场景本身密集，未超 10 行上限。

### 3.3 `27_web_frameworks.md`（L6 生态层）

- **主题相关性**：6 行严格对应 §6.1 选型决策树的四个问题维度（Tower 生态/声明式 API/社区成熟度/OpenAPI）与 §6.2 场景化推荐矩阵（Serverless），失效条件直接引用 §7.1「Axum 万能论」反命题的 F1/F3 与 §7.2 性能反例。
- **技术准确性**：Axum/Rocket/Actix-web/Poem 的场景归属与页内决策树、推荐矩阵完全一致，未引入页外框架或新结论。
- **风格一致性**：表头加粗风格在本页 §6.2 使用 `| **场景** |`，本表按任务统一表头使用普通文本，与本仓 32_const_generics 判定表风格一致；可接受。
- **自评**：✅ 通过。「瓶颈在数据库」一行把 §7.2 的元认知反例转化为判定行，是该页决策内容的有效压缩。

## 四、验证结果

| 验证项 | 结果 |
|:---|:---|
| `python scripts/check_template_cliches.py --strict` | ✅ exit 0（未发现模板套话） |
| `python scripts/check_metadata_consistency.py` | ✅ exit 0；再生成报告与 HEAD 版本逐字节一致 ⟹ **无新增标记** |
| grep 覆盖统计 | ✅ 6 → 31（净增 25，见 §一） |
| 新增内容死链 | ✅ 新增内部链接仅 7 处，目标文件逐一确认存在（`02_borrowing.md`、`03_lifetimes.md`、`12_smart_pointers.md`、`32_const_generics.md`、`40_generic_associated_types.md`、`06_pin_unpin.md`、`37_async_cancellation_safety.md`） |
| 行尾一致性 | ✅ 25 个文件抽查均为全量 CRLF（如 01_ownership 1920/1920 行 CRLF） |
| 改动最小化 | ✅ git numstat：每页 12–16 行新增，删除行仅为 diff 对齐产生的空行配对，无正文删除；元数据块未触碰 |
| 目录同步 | ✅ 涉及目录（TOC）列有「相关概念」或同级子节条目的 21 页均已补判定表条目；4 页（03_lifetimes、23_move_semantics、04_macros、02_patterns）TOC 本无对应条目，未新增 |

## 五、备注

1. **未做 git commit**（按任务要求）。
2. 工作区中另有 8 个 `concept/` 文件（`28_ownership_inventories_brown_book.md`、`30_lifetimes_advanced.md`、`05_reference_semantics.md`、`07_control_flow.md`、`40_patterns.md`、`41_statements_and_expressions.md`、`08_collections.md`、`32_unsafe_boundary_panorama.md`）及 `concept_kb.json`、`scripts/README.md` 等存在**本次任务之前**的未提交改动，与本报告无关，未触碰。
3. 一次性脚本留存于 `tmp/rollout_decision_tables.py`（`tmp/` 不入版本控制），可供后续批次复用模式。
