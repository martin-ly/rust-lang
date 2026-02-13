# AI 辅助 Rust 编程指南

> **最后更新**: 2026-02-13
> **目的**: 结合 AI 工具高效学习 Rust 与构建项目

---

## 1. AI 辅助学习路径

### 1.1 提示词模板 (Prompt Templates)

**概念解释**:

```text
请用简洁的中文解释 Rust 的 [概念名称]，并给出 1-2 个代码示例。
要求：示例能直接在 Rust Playground 运行。
```

**代码审查**:

```text
请审查以下 Rust 代码，指出潜在的所有权、生命周期或 idiomatic 问题，
并给出修改建议。代码：[粘贴代码]
```

**错误修复**:

```text
我遇到以下 Rust 编译错误，请解释原因并给出修复方案：
[粘贴错误信息]
```

### 1.2 与本项目结合

- **RAG 检索**: 将 `docs/02_reference/quick_reference/`、`crates/*/docs/` 纳入检索范围
- **Embedding 索引**: 建议将速查卡、00_MASTER_INDEX、决策树文档纳入向量索引，便于语义检索
- **上下文拼接**: 提问时附带相关速查卡或模块文档链接
- **示例驱动**: 引用本项目 `examples/` 中的示例让 AI 生成类似代码
- **错误码上下文**: 遇到编译错误时，附带 [ERROR_CODE_MAPPING](../docs/02_reference/ERROR_CODE_MAPPING.md) 中对应文档
- **练习巩固**: 结合 [RUSTLINGS_MAPPING](../exercises/RUSTLINGS_MAPPING.md) 让 AI 推荐对应习题

---

## 2. 常用 AI 工具

| 工具         | 适用场景           | 推荐用法                   |
| ------------ | ------------------ | -------------------------- |
| **Cursor**   | 代码补全、重构     | 在项目内直接编辑和运行     |
| **GitHub Copilot** | 行级补全    | 结合注释生成实现           |
| **Claude/GPT** | 概念解释、调试   | 粘贴错误信息 + 相关文档    |
| **rust-analyzer** | 静态分析   | 必须启用的 LSP，非 AI 但必备 |

---

## 3. 项目文档的 AI 友好性

本项目已具备：

- **结构化文档**: 各模块 00_MASTER_INDEX、速查卡
- **官方资源映射**: 便于 AI 引用权威来源
- **决策树与矩阵**: 适合作为技术选型上下文

**建议**: 使用 `tools/doc_search` 进行全文检索，将结果作为 AI 对话的上下文。

---

## 4. AI 辅助工作流（推荐）

| 阶段 | 工作流 | 工具 |
|------|--------|------|
| **学习概念** | 提示词「解释 [概念] + 示例」→ 附带速查卡链接 | Claude/GPT |
| **写代码** | 注释描述意图 → Copilot/Cursor 补全 → 验证 | Cursor/Copilot |
| **遇到错误** | 粘贴错误码 + [ERROR_CODE_MAPPING](../docs/02_reference/ERROR_CODE_MAPPING.md) 对应文档 | Claude/GPT |
| **巩固练习** | 学完模块 → 查 [RUSTLINGS_MAPPING](../exercises/RUSTLINGS_MAPPING.md) → 做对应习题 | Rustlings |
| **代码审查** | 粘贴代码 + 要求「按 Rust 惯用法审查」 | Claude/GPT |

---

## 5. 用 Rust 构建 AI 应用

Rust 在 AI/ML 领域有 Burn、Candle、llm 等生态，详见 [AI+Rust 生态指南](../docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md)。

---

## 6. 注意事项

1. **验证输出**: AI 生成的 Rust 代码务必 `cargo build` 和 `cargo test` 验证
2. **版本一致**: 明确指定 Rust 1.93.0+ 和 Edition 2024
3. **引用权威**: 对关键概念要求 AI 引用 The Rust Book 或 Reference

---

## 7. 相关文档

- [guides/README.md](./README.md) - 指南入口
- [AI+Rust 生态指南](../docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) - Burn/Candle/LLM、用 Rust 构建 AI
- [docs/02_reference/quick_reference/](../docs/02_reference/quick_reference/) - 速查卡
- [LEARNING_CHECKLIST.md](../LEARNING_CHECKLIST.md) - 学习清单与自测
- [ERROR_CODE_MAPPING.md](../docs/02_reference/ERROR_CODE_MAPPING.md) - 错误码→文档映射
- [RUSTLINGS_MAPPING.md](../exercises/RUSTLINGS_MAPPING.md) - 模块↔习题对应
