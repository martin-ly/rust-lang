# Rust Effect System（效应系统）全面对齐计划

> **计划编号**: E-2026-06
> **创建日期**: 2026-06-02
> **状态**: ✅ Phase E1-E3 已完成 · Phase E4-E5 已完成
> **负责人**: Kimi Code CLI
> **批准状态**: 已获用户批准（ExitPlanMode，自由执行模式）

---

## 一、计划背景

Yoshua Wuyts（Rust Effects Initiative 核心维护者）在 2025-2026 年发布了 5 篇关于 Rust Effect System 的权威文章，构成了 Rust 效果系统设计空间当前最完整的公开论述。本计划的目标是将这些权威输出全面整合到 `concept/07_future/04_effects_system.md`，并同步更新相关交叉引用文件。

### 权威来源清单

| 文章 | 日期 | 核心贡献 | 整合章节 |
|:---|:---|:---|:---|
| "Why Effects?" | 2026-05 | 效应 = 隐式参数 + 类型化协程 + 语言原语 三合一 | 〇之三 |
| "Open and Closed Effect Systems" | 2025-05 | Rust 选择封闭效应系统（closed effect system） | 一之二 |
| "Syntactic Musings on the Fallibility Effect" | 2025-12 | `throws`/`throw` 语法；abstract vs concrete fallibility | 一之三 |
| "An Effect Notation Based on With-Clauses and Blocks" | 2026-03 | `eff`/`with`/`.do` 统一语法框架 | 2.4 |
| "A Grand Vision for Rust" | 2026-03 | Effects × Substructural Types × Refinement Types 三元愿景 | 6.3 |
| "Why `PIN` Is a Part of Trait Signatures" | 2024-10 | async 效果与 Pin 的深层耦合 | 6.4 |

---

## 二、Phase E1 — Yoshua Wuyts 核心输出整合（高优先级）

### E1.1 "Why Effects?" 章节 ✅

**目标**: 在 `04_effects_system.md` 中添加「〇之三 Why Effects?」章节

**内容要点**:

- 效应 = 隐式参数 + 类型化协程 + 语言原语 三合一论证
- 表格化展示三种视角的映射关系
- Rust 特别需要统一效果系统的原因（函数着色问题）
- 效果系统的最小公倍数（消除 2^N 组合爆炸）

**验收标准**:

- [x] 三合一论证以可视化表格呈现
- [x] 未来效果枚举（no-panic, no-diverge, deterministic, no-io）
- [x] 来源标注完整（Yoshua Wuyts 2026-05）

### E1.2 "Open and Closed Effect Systems" 章节 ✅

**目标**: 在 `04_effects_system.md` 中添加「一之二 开放与封闭效应系统」章节

**内容要点**:

- 开放 vs 封闭效应系统的分类矩阵（6 个维度）
- Rust 选择封闭效应系统的工程哲学论证
- 为什么 Rust 不能是开放的（4 个约束对照表）
- 封闭 ≠ 固定不变（版本扩展机制）

**验收标准**:

- [x] 分类矩阵覆盖来源/集合/代表语言/复杂度/实现难度/表达能力/兼容性
- [x] 明确引用 Yoshua Wuyts 2025-05

### E1.3 "Fallibility Effect" 章节 ✅

**目标**: 在 `04_effects_system.md` 中添加「一之三 Fallibility Effect」章节

**内容要点**:

- 当前问题：`Result` 是类型不是效果
- `throws` 效果：从类型到效果的跃迁
- Abstract vs Concrete Fallibility 区分
- `.do` 通用效果传播设计

**验收标准**:

- [x] 语法变体对比表（4 种变体）
- [x] `yeet` → `throw` 转变说明
- [x] `.do` 设计哲学解释

### E1.4 `~const` 语法废弃标注 ✅

**目标**: 在 `04_effects_system.md` 中所有 `~const` 引用处添加废弃方向说明

**修改位置**:

- [x] `〇之二` 学术谱系映射表：`| **Polymorphic Effect Types** | ... | ~const Trait (unstable, **已废弃方向**)`
- [x] `二` 效果类别表：`| **常量** | ... | ~const Trait (unstable, **已废弃方向**)`
- [x] `2.1` const fn 是效果泛型雏形：添加 `⚠️ 语法演进声明` 段落

### E1.5 学术谱系时间线更新 ✅

**目标**: 将学术谱系时间线扩展至 2026-05

**新增节点**:

- [x] 2025-05: "Open and Closed Effect Systems"
- [x] 2025-12: "Syntactic Musings on the Fallibility Effect"
- [x] 2026-03: "An Effect Notation Based on With-Clauses and Blocks"
- [x] 2026-03: "A Grand Vision for Rust"
- [x] 2026-05: "Why Effects?"

---

## 三、Phase E2 — 深度扩展与语法提案（中优先级）

### E2.1 "With-Clauses and Blocks" 章节 ✅

**目标**: 在 `04_effects_system.md` 中添加「2.4 With-Clauses」章节

**内容要点**:

- 核心语法：`eff`/`with`/`.do` 三关键字
- `with`-clauses 统一语法（函数/闭包/块/trait impl）
- 效果泛型：`eff` 关键字在泛型位置的使用
- 效果代数：并集、排除、互斥
- 效果别名与 stdlib 分层（Pure/Core/Alloc/Std）
- 模块级/文件级效果声明

**验收标准**:

- [x] 代码示例覆盖所有语法位置
- [x] 效果代数表格完整
- [x] 明确声明为"设计提案，非官方决策"

### E2.2 "A Grand Vision for Rust" 映射 ✅

**目标**: 更新「6.3 Rust 效果系统的未来演进」

**内容要点**:

- Rust 2030+ 三元愿景：Effects + Substructural Types + Refinement Types
- Substructural Types 谱系：Affine → Linear (`!Forget`) → Ordered (`!Move`)
- Refinement Types：pattern types (`usize is 1..`) + view types
- 与 Ada/SPARK 级别形式化保证的对比路径

**验收标准**:

- [x] 演进路线时间线扩展至 2030+
- [x] 三元愿景表格
- [x] pattern types / view types 代码示例

### E2.3 Pre-pre RFC 社区讨论分析 ⏭️ 降级

**说明**: 社区讨论分析在 v1.3 中未作为独立章节添加，但核心洞察已融入各章节（如封闭系统的工程权衡、语法演进声明）。如需独立章节可在后续版本补充。

### E2.4 Effect Aliases 组合规则 ✅

**目标**: 在 `2.4 With-Clauses` 中覆盖效果别名

**验收标准**:

- [x] `eff Pure = panic + diverge;` 等别名示例
- [x] stdlib 分层映射（total → Pure → Core → Alloc → Std）
- [x] 模块级 `pub mod bar with Std {}` 语法

### E2.5 Rust Project Goals 2026 更新 ✅

**目标**: 更新 `04_effects_system.md` 中 Rust Project Goals 引用

**验收标准**:

- [x] 6.3 中保留 2025H1 const traits 目标
- [x] 新增 with-clauses 作为远期可能方向

---

## 四、Phase E3 — 整理与质量（低优先级 + 整理）

### E3.1 Future effects（no-divergence, no-panic 等）✅

**目标**: 在文档中系统枚举未来可能的效果

**验收标准**:

- [x] `〇之三` 中未来效果表格（4 种效果 + 应用场景）
- [x] `6.3` 演进路线中标注中期目标（2029-2030）

### E3.2 Effect × Pin 交叉分析 ✅

**目标**: 添加 Effect System 与 Pin 的交叉分析

**文件**:

- [x] `04_effects_system.md` 新增「6.4 Effect × Pin」
- [x] `03_advanced/06_pin_unpin.md` 添加反向交叉引用

**内容要点**:

- Pin 是 async 效果的"附属类型系统"
- `Future::poll(self: Pin<&mut Self>)` 的 effect 语义
- gen/yield 效果同样面临 Pin 问题
- 统一效果系统中 Pin 的角色演变（隐藏 vs 显式）

### E3.3 根目录文件归档 ✅

**目标**: 将 `concept/` 根目录的 effect system 相关文件归档

**归档文件**:

- [x] `rust_effect_system_encyclopedia.md` (1848 行)
- [x] `rust_effect_system_comprehensive_analysis.md` (416 行)
- [x] `rust_effect_system_deepened_broadened_analysis.md` (596 行)
- [x] `rust_effect_system_boundary_analysis.md` (282 行)
- [x] `01.md` (2136 行)
- [x] `Rust vs C++：形式系统模型 vs 机制工程模型 —— 核心论点索引.md` (145926 行)

**归档位置**: `concept/archive/`
**归档说明**: `concept/archive/ARCHIVE_RUST_EFFECT_SYSTEM_ROOT_FILES.md`

### E3.4 `concept_index.md` 更新 ✅

**目标**: 在全局概念索引中添加 Effect System 条目

**验收标准**:

- [x] E 部分新增 "Effect System (效果系统)" 条目
- [x] 包含层级定位、交叉引用、Bloom 层级、语义链接

---

## 五、Phase E4 — 质量验证（每次修改后执行）

### E4.1 kb_auditor.py ✅

**执行命令**: `python scripts/kb_auditor.py`

**关键指标**:

- [x] 死链: 0
- [x] 跨层问题: 0
- [x] 模板化 ⟹: 0
- [x] 定理链: 1232（维持）

### E4.2 cargo test --workspace ✅

**执行命令**: `cargo test --workspace`

**结果**: 全部通过

### E4.3 外部链接有效性检查 ✅

**检查范围**: `04_effects_system.md` 中所有外部 URL

**发现问题与修复**:

- [x] `blog.yoshuawuyts.com/why-pin-is-a-part-of-trait-signatures/` → 404 → 修正为 `https://blog.yoshuawuyts.com/why-pin/`
- [x] 其余 21 个 URL 全部 200 OK

---

## 六、Phase E5 — 交叉引用一致性（补全）

### E5.1 引用 `04_effects_system.md` 的文件检查 ✅

**检查结果**:

- [x] `01_foundation/21_effects_and_purity.md` — 已引用 ✅
- [x] `03_advanced/02_async.md` — 已引用 ✅
- [x] `03_advanced/06_pin_unpin.md` — 新增反向引用 ✅
- [x] `04_formal/21_type_semantics.md` — 新增后置引用 ✅
- [x] `04_formal/23_programming_language_foundations.md` — 已引用 ✅
- [x] `07_future/05_rust_version_tracking.md` — 已引用 ✅
- [x] `07_future/11_const_trait_impl_preview.md` — 已引用 ✅（同时更新 `~const` 标注）

### E5.2 Wikipedia 概念对齐更新 ✅

**新增词条**:

- [x] Substructural type system
- [x] Refinement type
- [x] Row polymorphism

---

## 七、变更统计

| 指标 | 修改前 | 修改后 | 变化 |
|:---|:---:|:---:|:---:|
| `04_effects_system.md` 行数 | 1073 | ~1534 | +461 |
| 新增章节数 | 0 | 6 | +6 |
| 更新章节数 | 0 | 3 | +3 |
| 根目录归档文件数 | 0 | 6 | +6 |
| 死链 | 0 | 0 | 0 ✅ |
| 跨层问题 | 0 | 0 | 0 ✅ |
| 模板化 ⟹ | 0 | 0 | 0 ✅ |

---

## 八、已知遗留与后续建议

| 遗留项 | 优先级 | 说明 |
|:---|:---:|:---|
| Pre-pre RFC 社区讨论独立章节 | 低 | 核心洞察已融入现有章节，如需独立章节可后续补充 |
| `07_future/11_const_trait_impl_preview.md` 深度重写 | 中 | `~const` 已标注废弃方向，但文件整体仍以 `~const` 为叙述主轴，待 const trait 新语法明确后可全面重写 |
| 效果系统独立书籍章节 | 低 | 当前内容适合作为 concept 文档，如需 mdbook 独立章节可提取 |

---

> **最后更新**: 2026-06-02
> **计划状态**: ✅ 全部完成
> **质量基线**: 0 死链 · 0 跨层问题 · 0 模板化 ⟹ · cargo test 通过
