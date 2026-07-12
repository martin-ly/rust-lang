# 测验：元层框架与知识体系架构（L0）

> **EN**: Meta Framework and Knowledge Architecture Quiz
> **Summary**: L0 standalone quiz on the knowledge-base architecture itself: the L0–L7 layered structure, Bloom taxonomy mapping, A/S/P cognitive marking, and the canonical single-source-of-truth rules.
> **受众**: [进阶]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L0 元层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [Bloom 分类法](../00_framework/bloom_taxonomy.md) · [A/S/P 标记规范](../03_audit/02_asp_marking_guide.md) · [方法论](../00_framework/methodology.md) · [Concept 元层](../README.md) · [概念审计指南](../03_audit/01_concept_audit_guide.md) · [mdBook 官方文档](https://rust-lang.github.io/mdBook/)（P0 官方：测验体系托管框架，curl 200 实测 2026-07-13）
>
> **前置概念**:
> [Concept 元层](../README.md) ·
> [Bloom 分类法](../00_framework/bloom_taxonomy.md) ·
> [A/S/P 标记规范](../03_audit/02_asp_marking_guide.md) ·
> [方法论：思维表征与知识结构规范](../00_framework/methodology.md)

---

> **Bloom 层级**: L2-L3
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对知识体系自身架构（L0 元层）的掌握：分层职责、Bloom 映射、A/S/P 标记与 canonical 单一权威来源规则。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、分层架构

本节考查 L0–L7 八层架构的目录职责与认知定位：Q1 检验分层名称与层数记忆，Q2 检验目录归属判断。

### Q1. 🟢【单选】本知识体系采用的认知分层架构是？

- A. L1–L5 五层难度分级
- B. L0–L7 八层认知架构
- C. 初级 / 中级 / 高级三级划分
- D. 按 crate 模块划分，无统一层级

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：本知识库采用 **L0–L7 八层认知架构**：L0 元信息（`00_meta/`）、L1 基础（`01_foundation/`）、L2 进阶（`02_intermediate/`）、L3 高级（`03_advanced/`）、L4 形式化（`04_formal/`）、L5 对比（`05_comparative/`）、L6 生态（`06_ecosystem/`）、L7 未来（`07_future/`）。

**常见误解（干扰项分析）**：

- A/C：过于粗糙，无法承载"元信息层"与"形式化层"等差异化职责。
- D：crate 只是代码示例载体，分层是认知架构而非代码结构。

</details>

---

### Q2. 🟢 以下关于目录职责的判断，哪一项输出为真？

```rust,ignore
// 伪代码：判断哪个目录可作为概念的"权威来源"
fn is_authoritative(dir: &str) -> bool {
    match dir {
        "concept" => true,      // 权威概念层 L0-L7
        "knowledge" => false,   // 仅摘要/速查/重定向
        "docs" => false,        // 指南与参考，概念须链接 concept
        "archive" => false,     // 只读历史归档
        _ => false,
    }
}
```

| 选项 | 判断 |
|:---|:---|
| A | `knowledge/` 可以承载某个 Rust 概念的唯一深度解释 |
| B | `concept/` 是权威概念层，每个概念的唯一深度解释所在 |
| C | `archive/` 中的文件只要内容完整就是权威来源 |
| D | 四个目录都可以同时维护同一概念的完整正文 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B 为真。

**解析**：按 canonical 规则，`concept/` 是**权威概念层（L0–L7）**，每个 Rust 概念的唯一深度解释只存在于 `concept/`；`knowledge/` 只保留摘要、速查与重定向 stub；`docs/` 保留操作指南但概念解释必须链接回 `concept/`；`archive/` 是只读历史归档，不是权威来源。

**知识点**：[Concept 元层](../README.md) 的「子目录职责」表给出了 `00_meta/` 内部各子目录的分工，同样的职责分离原则适用于整个仓库。

</details>

---

## 二、Bloom 分类法映射

本节聚焦概念页元数据中的 Bloom 层级标注：Q3 做正向层级映射，Q4 辨析 L7 创造层的常见误用。

### Q3. 🟡【单选】按本体系的 Bloom 层级映射表，"unsafe 安全性审查、架构选型"对应哪一层？

- A. L3 应用
- B. L4 分析
- C. L5 评价
- D. L7 创造

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

**解析**：[Bloom 分类法](../00_framework/bloom_taxonomy.md) 的 Rust 映射表：L1 记忆（语法、API）→ L2 理解（能向他人讲解）→ L3 应用（写正确代码）→ L4 分析（借用检查错误分析、性能剖析）→ **L5 评价（unsafe 安全性审查、架构选型，产出技术评审文档）** → L6 综合（并发架构、系统级设计）→ L7 创造（新工具/语言/形式化系统）。

**常见误解（干扰项分析）**：

- A：L3 应用是"写出正确代码"，不含评审判断。
- B：L4 分析对应"调试、分解、推断"，如错误诊断报告。
- D：L7 创造要求产出原创系统，如为嵌入式设计的 arena allocator + 所有权追踪。

</details>

---

### Q4. 🟡 以下代码意图在 Bloom L7（创造层）"基于所有权模型设计新机制"，为什么方向错误？

```rust,ignore
// 试图在稳定 Rust 中"扩展" borrow checker 的行为
struct CustomRef<'a, T> {
    data: &'a T,
    // ❌ 意图：自定义借用检查规则
}
```

| 选项 | 判断 |
|:---|:---|
| A | 代码有语法错误，应改用 `Box<T>` |
| B | borrow checker 是编译器内置核心，不可扩展；L7 的正确路径是 proc macro / lint / 外部工具 |
| C | 只需加上 `unsafe` 块即可生效 |
| D | 应改用 nightly 的 `#![feature(custom_borrowck)]` |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：Rust 的 borrow checker 是**编译器核心**，不可扩展（不同于 TypeScript 的自定义类型守卫）。Bloom L7 在 Rust 中的含义不是修改编译器，而是**基于** Rust 的模型设计新系统，其实现路径有三：① **proc macro**——在 AST 层面添加检查（如 `#[derive(Valid)]`）；② **lint**——Clippy custom lint 或 rustc 插件（unstable）；③ **外部工具**——Miri、Kani。

**常见误解**：A 把语义问题当成语法问题；C 的 `unsafe` 只能绕过检查而非定制规则；D 中不存在 `custom_borrowck` 这个 feature gate。

</details>

---

## 三、A/S/P 三维认知标记

本节围绕 Assertion/Structure/Process 三标记的适用边界：Q5 选出全部正确表述，Q6 辨析 S 标记的误标场景。

### Q5. 🟡【多选】关于 A/S/P 三维认知标记，下列说法正确的有？（选出所有正确项）

- A. A/S/P 分别表示 Application（应用）、Structure（结构）、Procedure（程序）
- B. A/S/P 标记是对 Bloom 层级标注的替代，二者只能选其一
- C. A/S/P 标记连接 Krathwohl 知识维度与 Bloom 认知过程维度
- D. 每个概念文件可在头部标注 A/S/P 字段，并进入 concept_index 的索引列

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C、D**

**解析**：按 [A/S/P 标记规范](../03_audit/02_asp_marking_guide.md)：A/S/P 是 **A(应用) / S(结构) / P(程序)** 三维认知标记（A 正确）；它作为 Bloom 层级标注的**补充维度**而非替代（B 错误）；它连接 Krathwohl 知识维度与 Bloom 认知过程维度，把双维矩阵压缩为可操作的标签系统（C 正确）；使用方式为在概念文件头部增加 A/S/P 字段，并在 `concept_index.md` 增加索引列（D 正确）。

</details>

---

### Q6. 🟡【判断】A/S/P 标记中的 S（Structure）适合标注"借用检查错误诊断"这类操作步骤型知识。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**："借用检查错误诊断"是按步骤执行的**程序性**知识，应标 **P（Procedure）**；S（Structure）标注结构性契约与规范（如 Send/Sync 契约、Edition 规范）；A（Application）标注应用场景知识。规范文档 §四给出的示例中，"借用检查错误诊断"正是 P 标记的典型用例。

</details>

---

## 四、Canonical 单一权威来源规则

本节检验 AGENTS.md §2 的 canonical 规则：Q7 判断重复内容的正确处置，Q8 给出违规 stub 的修正方案。

### Q7. 🔴【单选】某个 Rust 概念已在 `concept/` 有权威页，`docs/` 中一份指南也写了该概念的完整解释。按 canonical 规则应如何处理？

- A. 两处都保留，内容多无害
- B. 删除 `concept/` 权威页，以 `docs/` 版本为准
- C. 将概念解释迁移到 `concept/` 权威页，`docs/` 中替换为 canonical 链接（指南可保留操作步骤）
- D. 在 `archive/` 再存一份备份作为第三来源

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

**解析**：canonical 规则要求任何概念只有一个权威页；合并优先级为 `concept/` > `knowledge/` / `docs/` / `content/`。`docs/` 指南可以保留操作步骤、决策树与速查表，但通用概念解释必须迁移到 `concept/` 权威页并替换为链接。禁止在多个目录保留相同概念的完整正文。

**常见误解**：A 直接违反"禁止双权威"红线；B 颠倒优先级；D 中 `archive/` 是只读历史归档，不得创建活跃内容副本。

</details>

---

### Q8. 🔴 以下 `knowledge/` 文件内容违反了哪条规则？应如何修正？

```markdown
# 生命周期（Lifetimes）

生命周期是 Rust 借用检查的核心机制。每个引用都有一个生命周期，
它标注了引用有效的范围……（以下 300 行完整概念解释，与
concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md 正文重复）
```

| 选项 | 判断 |
|:---|:---|
| A | 无违规，`knowledge/` 允许任意深度内容 |
| B | 违反"重定向 stub 只允许一句话说明 + 权威来源链接"，应删去重复正文改为 stub |
| C | 只需在文末加一条链接即可保留正文 |
| D | 应把 `concept/` 的权威页删掉，以本文件为准 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：按 canonical 规则，非权威位置只允许三种形式之一：权威页、摘要/速查页、重定向 stub。`knowledge/` 不能作为权威来源，其 stub 模板只允许"一句话说明 + `> **权威来源**: [concept/xxx.md](.)` 链接"。重复权威页正文是明确禁止的；发现重复时应保留较新、较完整、元数据齐全的版本作为权威页，被合并文件保留路径、内容改为重定向 stub。

</details>

---

### Q9. 🔴【多选】下列哪些位置**不得**作为通用 Rust 概念的权威来源？（选出所有正确项）

- A. `crates/c01_ownership_borrow_scope/docs/` 中的概念解释页
- B. `concept/01_foundation/` 中的概念页
- C. `exercises/` 中的练习题答案
- D. `book/` 中的 mdbook 构建输出

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C、D**

**解析**：`crates/` 是可编译代码示例 workspace，`crates/*/docs/` 只保留与 crate 直接相关的独特内容，概念解释不能放在这里（A 不得）；`exercises/` 是练习题与答案，不能替代概念解释（C 不得）；`book/` 是 `mdbook build` 输出目录，属构建产物（D 不得）。只有 `concept/`（及 `concept/` 未覆盖时经链接的 `content/` 专题页）可作权威来源，B 是合法的权威位置。

</details>

---

### Q10. 🟡【判断】`00_meta/` 元层提供导航索引、元数据标准、质量治理与来源对齐，但它不替代任何 L1–L7 的具体概念文件。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：按 [Concept 元层](../README.md) 的定位说明，`concept/00_meta/` 是知识体系的**元信息层（L0）**，提供四类服务：导航索引（L1–L7 间跳转）、元数据标准（受众、Bloom 层级、A/S/P 标记、内容分级）、质量治理（审计指南、去同质化模板、缺口追踪）、来源对齐（权威来源映射、术语表、双语模板）——但它明确"不替代任何具体概念文件"。

</details>

## 五、知识体系导航与治理

本节覆盖导航文件、quiz 注册表与治理机制：Q11–Q13 分别考查注册表位置、stub 约束与元层目录职责划分。

### Q11. 🟢【单选】全库测验资产（独立 quiz、嵌入式测验、exercises）的机器可读注册表位于？

- A. `docs/02_learning/quizzes/README.md`
- B. `concept/00_meta/quiz_registry.yaml`（人类可读索引为 `concept/00_meta/04_navigation/15_quiz_registry.md`）
- C. `knowledge/INDEX.md`
- D. `reports/` 下的夜间质量报告

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：`concept/00_meta/quiz_registry.yaml` 是全库测验资产的机器可读注册表，字段含层级/主题/题型/难度/题数/双向链接状态，由 `scripts/check_quiz_system.py` 校验一致性；人类可读索引是 `04_navigation/15_quiz_registry.md`。A 是学习指南索引（非机器可读）；C 是 knowledge 速查入口；D 是质量报告归档。

</details>

---

### Q12. 🟡【判断】`knowledge/` 中的重定向 stub 允许保留与 `concept/` 权威页相同的完整正文，只要文末附上权威来源链接。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：按 canonical 规则与 `knowledge/` stub 模板，重定向 stub 只允许"一句话说明 + `> **权威来源**: [concept/xxx.md](.)` 链接"，**禁止保留重复正文**——仅在文末加链接不构成合规 stub。发现重复时应将正文迁移到 `concept/` 权威页，stub 保留路径仅作入口。

</details>

---

### Q13. 🟡【多选】关于 `concept/00_meta/` 元层子目录的职责划分，下列对应正确的有？（选出所有正确项）

- A. `00_framework/` — Bloom 分类法、方法论等框架性规范
- B. `01_terminology/` — 术语表（glossary 对齐检查的权威表）
- C. `03_audit/` — 审计指南、A/S/P 标记规范等质量治理
- D. `05_quizzes/` — L1–L7 全部独立 quiz 的统一存放处

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A/B/C 与 [Concept 元层](../README.md) 的子目录职责表一致：框架规范、术语权威表、质量治理分属三个目录。D 错：`05_quizzes/` 只存放 **L0 元层自身**的独立 quiz；L1–L7 的 quiz 分布在各层的 `NN_quizzes/` 子目录（如 `01_foundation/11_quizzes/`、`06_ecosystem/13_quizzes/`），统一视图由 quiz 注册表提供而非物理集中。

</details>

---

### Q14. 🔴 以下治理脚本调用序列，哪一条与 AGENTS.md §5 的质量门纪律一致？

```bash
# 候选序列：新增一篇概念页后的本地验证
seq_a="python scripts/detect_content_overlap.py && python scripts/kb_auditor.py"
seq_b="mdbook build && python scripts/check_canonical_uniqueness.py --strict"
seq_c="python scripts/check_glossary_alignment.py --strict"
```

| 选项 | 判断 |
|:---|:---|
| A | 只需 `mdbook build` 通过即可提交 |
| B | 先查重（detect_content_overlap）再建页，提交前跑死链与 canonical 唯一性检查 |
| C | 术语对齐检查只在发布时运行，日常修改无需关心 |
| D | 阻断门通过后即可宣称"质量门全部通过"，无需核对语义观察门 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：AGENTS.md §3.1 要求新增内容**先查重**；§5.1 的 15 个阻断门包含 `kb_auditor`（死链/跨层）与 `check_canonical_uniqueness --strict`（权威页唯一性），提交前应本地验证。A 漏掉查重与死链；C 错——术语表对齐是独立检查项（`check_glossary_alignment.py --strict`）；D 直接违反 §6 红线 6：任何"全部通过"类结论必须同时核对 15 阻断门与 5 语义观察门。

</details>

---

### Q15. 🔴【多选】按 AGENTS.md §5.2 的观察门转正机制，下列说法正确的有？（选出所有正确项）

- A. 语义观察门默认 exit 0（warning），不因单项退化阻断 PR
- B. 观察门连续 4 周（或连续 10 次 CI 运行）达标后可评估转为阻断门
- C. 转正前提是本地实跑 `--strict` 当前 exit=0
- D. 观察门指标显著恶化时可直接忽略，无需在 PR 中说明

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：转正机制要求：观察门默认非阻断（A）；连续 4 周或 10 次 CI 达标后评估转正（B）；转正前提为 `--strict` 实跑 exit 0（C），转正后退化则按阻断门流程处置、不自动降级。D 错：§5.1 明确要求观察门指标显著恶化时应在 PR 描述中说明原因与后续治理计划，且 §6 红线 6 要求报告与观察门状态矛盾时以观察门最新报告为准并勘误。

</details>

---

> **变更记录**: 2026-07-12 新建（W3-b：L0 独立 quiz 补缺，10 题：单选 4 / 代码阅读 3 / 多选 2 / 判断 2；难度 🟢2 / 🟡5 / 🔴3）；2026-07-13 扩展至 15 题（+5 题「知识体系导航与治理」：单选/判断/多选/代码阅读混合；难度 🟢3 / 🟡7 / 🔴5）。
