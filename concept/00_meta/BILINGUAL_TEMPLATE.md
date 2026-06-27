# Concept 文件双语模板（Bilingual Template）

> **EN**: Bilingual Concept Template
> **Summary**: Standardized bilingual header template for all `concept/` files to support internationalization.
>
> **适用范围**: `concept/` 目录下所有 L1-L7 概念文件
> **版本**: 1.0
> **状态**: 🔄 Q4 2026 国际化基础设施

---

## 一、文件头模板

每个 `concept/` 文件必须在正文前包含以下标准化头部：

```markdown
# {中文标题}
>
> **EN**: {English Title}
> **Summary**: {50-100 words English summary}
>
> **受众**: [初学者 | 进阶 | 研究者]
> **层级**: {L0-L7} {基础/进阶/高级/形式化/对比/生态/未来}概念
> **A/S/P 标记**: {A | S | P | A+S | S+P | ...}
> **双维定位**: {知识维度 × Bloom 层级}
> **前置概念**: [{Concept EN}](./{file}.md) · ...
> **后置概念**: [{Concept EN}](./{file}.md) · ...
> **主要来源**: [来源1] · [来源2] · ...
>
> **来源**: [TRPL — ...](...) · [Rust Reference — ...](...) · [RFC ...](...)
---
```

### 字段说明

| 字段 | 必填 | 长度/格式 | 说明 |
|:---|:---:|:---|:---|
| `EN` | ✅ | 1-5 个英文词 | 概念的官方英文名称，与术语表严格一致 |
| `Summary` | ✅ | 50-100 词 | 英文摘要，用于搜索引擎和国际社区发现 |
| `受众` | ✅ | 单选 | 初学者 / 进阶 / 研究者 |
| `层级` | ✅ | `L0`-`L7` | 认知层级 |
| `A/S/P 标记` | ✅ | 组合 | Application / Structure / Procedure |
| `双维定位` | ✅ | `C×Und` 等 | 知识维度 × Bloom 层级 |
| `前置概念` | ✅ | 链接列表 | 学习本概念前必须掌握的概念（英文名称） |
| `后置概念 | ✅ | 链接列表 | 学习本概念后可直接延伸的概念（英文名称） |
| `主要来源` | ✅ | 引用列表 | 学术/权威来源 |
| `来源` | ✅ | 链接列表 | TRPL / Reference / RFC 等官方链接 |

---

## 二、正文结构模板

每个概念文件正文应包含以下六要素：

```markdown
## 一、核心命题

> 用一句话概括本概念在 Rust 知识体系中的核心地位。

## 二、概念定义

### 2.1 形式化定义

> 精确、无歧义的定义。可包含数学符号或类型规则。

### 2.2 直觉解释

> 用类比或图示帮助初学者建立直觉。

## 三、属性关系

| 属性 | 说明 | Rust 表达 |
|:---|:---|:---|
| ... | ... | ... |

## 四、解释论证

> 为什么 Rust 这样设计？历史背景、权衡、与其他语言的差异。

## 五、示例代码

```rust
// 最小可运行示例
```

## 六、思维表征

### 6.1 思维导图

```mermaid
mindmap
  root((Concept))
    ...
```

### 6.2 决策树/矩阵（如适用）

## 七、反命题与边界

> 常见误解、反例、边界测试。

## 八、权威参考

- [TRPL — ...](...)
- [Rust Reference — ...](...)
- [RFC ...](...)
```

---

## 三、术语标注规范

正文中首次出现核心术语时，应使用双语标注：

```markdown
所有权（Ownership）是 Rust 的核心机制。
```

对于已收录在术语表中的术语，应优先使用术语表中的英文对照：

| 中文 | 英文 | 备注 |
|:---|:---|:---|
| 所有权 | Ownership | 不可翻译为 Property |
| 借用 | Borrowing | 区别于 Loan |
| 生命周期 | Lifetimes | 复数形式 |

---

## 四、国际化质量检查清单

在提交概念文件前，请确认：

- [ ] 文件头包含 `EN` 和 `Summary`
- [ ] `EN` 名称与 `concept/00_meta/terminology_glossary.md` 一致
- [ ] `Summary` 为 50-100 词英文
- [ ] 前置/后置概念使用英文名称
- [ ] 正文中核心术语首次出现时附带英文
- [ ] 代码示例可编译（如适用）
- [ ] 来源链接指向官方/TRPL/Reference/RFC

---

## 五、脚本集成

`scripts/add_bilingual_annotations.py` 将自动：

1. 扫描 `concept/` 中所有 Markdown 文件。
2. 检查文件头是否包含 `EN` 和 `Summary`。
3. 对未标注的核心术语添加英文注释。
4. 在"强制模式"下对缺失项报错。

运行方式：

```bash
python scripts/add_bilingual_annotations.py --mode enforce
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-06-27
**状态**: 🔄 模板冻结，待 Q4 批量应用
