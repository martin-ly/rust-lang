# Agent 协作指南：Rust 分层概念知识体系

> **作用域**：本文件适用于 `e:\_src\rust-lang` 及其所有子目录。当子目录存在更具体的 `AGENTS.md` 时，子目录规则优先。

---

## 1. 项目定位

这是一个**分层、可验证、可搜索**的 Rust 概念知识库，采用 **L0-L7 八层认知架构**。
核心目标不是“堆叠文档”，而是为每个 Rust 概念维护**单一、权威、可演进**的解释来源。

---

## 2. Canonical 规则：单一权威来源

任何 Rust 概念/主题必须只有一个**权威页（canonical page）**。其他位置只允许是以下三种形式之一：

| 形式 | 允许内容 | 禁止内容 |
|---|---|---|
| **权威页** | 完整概念解释、代码、反例、形式化、跨语言对比、工程实践 | 复制其他权威页内容 |
| **摘要/速查页** | 关键要点、链接到权威页、决策树、cheatsheet | 重复权威页的正文解释 |
| **重定向 stub** | 一句话说明 + `> **权威来源**: [concept/xxx.md](...)` 链接 | 保留重复正文 |

### 2.1 目录职责

| 目录 | 职责 | 是否可作为权威来源 |
|---|---|---|
| `concept/` | **权威概念层（L0-L7）**。每个 Rust 概念的唯一深度解释。 | ✅ 是 |
| `knowledge/` | 精简知识卡片、速查、学习入口。 | ❌ 否；只能摘要或重定向到 `concept/` |
| `docs/` | 指南、参考、实践项目、研究报告。 | ❌ 否；指南可保留操作步骤，概念解释必须链接到 `concept/` |
| `content/` | 专题深度内容（生态库、生产实践、学术研究）。 | ⚠️ 仅当 `concept/` 未覆盖时可作为该专题的权威页；否则必须链接 |
| `crates/` | 可编译代码示例与 workspace。`crates/*/docs/` 只保留与 crate 直接相关的独特内容。 | ❌ 概念解释不能放在这里 |
| `exercises/` | 练习题与答案。 | ❌ 不能替代概念解释 |
| `archive/` | 只读历史归档。内部文件不得与活跃目录重复。 | ❌ 不是权威来源 |
| `book/` | `mdbook build` 输出目录。除 `book/README.md` 外，不应提交到版本控制。 | ❌ 构建产物 |
| `tmp/` | 临时文件与缓存。不应提交到版本控制。 | ❌ 临时目录 |

### 2.2 如何判断权威页

1. 优先在 `concept/` 中按 L0-L7 层级查找对应主题。
2. 如果 `concept/` 已存在该主题，其他目录的重复文件必须改为重定向 stub 或摘要。
3. 如果 `concept/` 不存在但 `content/` 有专题深度文，可将 `content/` 文件作为该专题权威页，但需在 `concept/` 中创建链接或索引。
4. 禁止在多个目录中保留相同概念的完整正文。

---

## 3. 内容去重与合并政策

### 3.1 新增内容时

- **先查重**：运行 `python scripts/detect_content_overlap.py` 或手动搜索目标主题是否已存在。
- **不要复制**：如需在多个位置出现，创建重定向 stub，不要复制正文。
- **声明 canonical**：新增权威页应在文件顶部或元数据中注明其 canonical 地位。

### 3.2 修改内容时

- 如果修改的是非 `concept/` 文件，且该主题在 `concept/` 已有权威页，应：
  1. 将改动迁移到 `concept/` 的权威页；
  2. 将非权威文件改为摘要或重定向；
  3. 不要同时在两个位置维护相同内容。

### 3.3 发现重复时

按以下优先级合并：

1. `concept/` > `knowledge/` / `docs/` / `content/`
2. 较新、较完整、英文摘要/元数据齐全的版本优先
3. 保留有交叉引用、版本跟踪、Bloom 标签等元数据的版本
4. 被合并的文件保留路径，内容改为重定向 stub

---

## 4. 文件命名与格式

- Markdown/脚本/目录名使用 `snake_case` 或 `number_prefix_snake_case`。
- 禁止中文文件名、空格、混合大小写（过渡期例外：`archive/` 历史文件、`.kimi/` 日期风格文件、`reports/` 日期风格文件、`.github/ISSUE_TEMPLATE/`）。
- 每个 `concept/` 文件应包含 `**EN**` 英文标题和 `**Summary**` 英文摘要。

---

## 5. 常用命令

```bash
# 质量审计
python scripts/kb_auditor.py

# 内容重叠检测（关键！新增/修改前运行）
python scripts/detect_content_overlap.py

# 死链检查
python scripts/kb_auditor.py --link-check
# 或根据项目实际命令调整

# 构建验证
cargo build --workspace
cargo test --workspace

# mdbook 构建（输出到 book/，不应提交）
mdbook build
```

---

## 6. 修改时必须遵守的红线

1. **不要** 在 `book/` 中直接修改内容（除 `book/README.md`）。
2. **不要** 将 `tmp/` 中的临时文件提交到版本控制。
3. **不要** 在 `archive/` 中创建新的活跃内容副本。
4. **不要** 在 `crates/*/docs/` 中复制通用概念解释；应链接到 `concept/`。
5. **新增重复内容必须被 CI 或人工 review 拦截**。

---

## 7. 长期治理机制

| 机制 | 频率/触发条件 | 工具/负责人 |
|---|---|---|
| 内容重叠检测 | 每次 PR / 每周 | `scripts/detect_content_overlap.py` |
| 死链检查 | 每次大规模合并后 | `scripts/kb_auditor.py` |
| 归档审计 | 每季度 | 人工 + 脚本 |
| 版本页中心化管理 | Rust 新版本发布时 | `concept/07_future/rust_1_XX_*.md` |

---

**最后更新**：2026-07-01
