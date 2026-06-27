# 概念一致性（Coherence）检查清单
>
> **EN**: Concept Consistency Audit Checklist
> **Summary**: A lightweight checklist to verify that a concept file is internally consistent, correctly cross-referenced, and aligned with the project's pedagogical style.
>
> **受众**: [贡献者]
> **层级**: L0 元信息
> **A/S/P 标记**: M — Meta
> **双维定位**: M×Aud — Audit / Quality Assurance
> **前置概念**: [Navigation Hub](./navigation.md) · [Terminology Glossary](./terminology_glossary.md)
> **后置概念**: [Foundations Gap Closure Index](./foundations_gap_closure_index.md)
---

## 一、结构一致性

- [ ] 文件顶部包含中英文标题、Summary、受众、层级、A/S/P 标记、双维定位、前置/后置概念。
- [ ] 核心命题在第一节明确给出，并用引用块（`>`）突出。
- [ ] 每个技术术语首次出现时提供英文对照。
- [ ] 文末包含 L1/L2/L3 总结或认知路径。

## 二、链接与引用

- [ ] 内部链接指向真实存在的 Markdown 文件（非 `placeholder-generic.md`）。
- [ ] 外部来源使用可点击的 HTTPS 链接，优先选择官方文档、学术论文、社区权威资源。
- [ ] 代码示例中的引用（如 RFC、论文）在文末延伸阅读列出。

## 三、代码示例

- [ ] Rust 示例标注 `edition2024` 或符合当前项目 `rust-version`。
- [ ] 故意失败的示例使用 `compile_fail` 或 `ignore` 并说明原因。
- [ ] C/C++ 示例与 Rust 示例形成明确对照。

## 四、教学风格

- [ ] Bloom 层级在元数据中标注，并在内容中体现（理解 → 应用 → 分析 → 评价）。
- [ ] 对比表使用统一的维度列，避免一边说“优势”一边说“缺点”。
- [ ] 避免空洞口号，每个主张附带代码、形式化定义或权威来源。

## 五、权威来源

- [ ] 至少引用一个官方文档（Rust Reference / TRPL / RFC）。
- [ ] 至少引用一个跨语言权威来源（cppreference、TAPL、PFPL 等）。
- [ ] 来源与论点一一对应，避免“来源堆积”。

## 六、常见反例

| 反模式 | 正确做法 |
|:---|:---|
| “Rust 没有运行时” | 说明 Rust 的零成本抽象与特定运行时（如 async executor）的区别 |
| “C++ 不安全” | 区分 C++ 的未定义行为类别与 Rust 的所有权检查 |
| 大量 `LINK_PLACEHOLDER` | 替换为真实链接或纯文本 |

---

> **Checklist**: 本清单用于审计单个 concept 文件的质量。项目级审计请参阅 [Quality Dashboard](./quality_dashboard_v2.md)。
