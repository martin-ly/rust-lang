# 模板去同质化指南
>
> **EN**: Template Deduplication Guide
> **Summary**: Guidelines for reducing boilerplate repetition across `concept/` files while preserving the bilingual header and core pedagogical structure.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [贡献者]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L0 元信息
> **A/S/P 标记**: M — Meta
> **双维定位**: M×Eva — Evaluation / Quality
> **前置概念**: [Bilingual Template](../01_terminology/bilingual_template.md) · [Concept Consistency Audit Checklist](concept_consistency_audit_checklist.md)
> **后置概念**: [Quality Dashboard](quality_dashboard_v2.md)
> **主要来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RFCs](https://github.com/rust-lang/rfcs)
---

## 一、目标

本项目早期通过脚本为大量 concept 文件注入了统一的尾部模板（认知路径、核心推理链、反命题与边界等）。
这些模板在快速构建知识体系时很有用，但也导致：

1. **信息密度下降**：相同模板段落反复出现，稀释了实质内容。
2. **维护成本上升**：修改一处通用表述需要改数百个文件。
3. **阅读体验受损**：读者每次翻到文件末尾都遇到高度重复的文本。

本指南定义如何保留必要结构、删除重复模板、将通用教学逻辑集中到元信息文件。

## 二、保留与删除清单

| 元素 | 处理方式 | 说明 |
|:---|:---|:---|
| 文件头元数据（EN/Summary/受众/层级/A/S/P/双维定位/前置后置概念/主要来源） | **保留** | 这是概念导航和国际化检索的基础 |
| 核心命题 | **保留** | 每个概念文件必须有的一句话定位 |
| L1 / L2 / L3 总结 | **选择性保留** | 如果文件本身已有清晰分层，保留；否则合并为一段 |
| 认知路径 + 核心推理链 + 反命题与边界 | **删除或迁移** | 集中迁移到 [Learning Guide](../04_navigation/learning_guide.md) 或本指南的附录 |
| 实践 / 延伸阅读 | **精简** | 只列出与本主题直接相关的 3-7 个来源/练习 |
| 文末 `> **Checklist**` | **删除** | 由 [Concept Consistency Audit Checklist](concept_consistency_audit_checklist.md) 统一承担 |

## 三、实施步骤

1. **抽样审计**：从每个层级（L1-L4）选 1-2 个文件作为示范。
2. **删除通用尾部**：移除“认知路径/核心推理链/反命题与边界”三段式模板。
3. **合并总结**：用 1-2 段话替代 L1/L2/L3 表格。
4. **精简延伸阅读**：保留权威来源，删除自我引用和重复链接。
5. **校验**：运行 `mdbook build` 和链接检查。

## 四、示范格式

去同质化后的文件末尾建议采用以下紧凑结构：

```markdown
## 总结

- **L1**：一句话核心结论。
- **L2**：与其他机制的关系或常见陷阱。
- **L3**：设计哲学与工程权衡。

## 延伸阅读

- [来源 A](.)
- [来源 B](.)
```

## 五、禁止事项

- 不要一次性批量删除所有文件的模板，应分层分批进行。
- 不要删除文件头元数据。
- 不要把“核心命题”简化为口号，必须包含可验证的具体论断。

## 六、批量去同质化检查清单

操作前请确认：

1. 已备份目标文件或处于版本控制下。
2. 已运行 `kb_auditor.py --link-check` 获取基线。
3. 已确定要移除的模板段落在目标文件中确实为复制内容。

## 七、进度追踪

- [x] L1 基础概念层示范文件（建议：变量模型、Move 语义）
- [x] L2 进阶概念层示范文件（建议：异常安全、RTTI）
- [x] L3 高级概念层示范文件（建议：Async 模式）
- [x] L4 形式化层示范文件（建议：求值策略）
- [ ] 批量去同质化脚本或清单

## 八、相关脚本

| 脚本 | 用途 |
|:---|:---|
| `scripts/kb_auditor.py` | 检查模板化 ⟹ 标记、元数据完整性 |
| `scripts/detect_content_overlap.py` | 发现跨文件重复正文 |
| `scripts/add_backward_reasoning.py` | 补充反向推理语句 |
| `scripts/add_backward_l2l3.py` | 补充 L2/L3 总结段落 |
