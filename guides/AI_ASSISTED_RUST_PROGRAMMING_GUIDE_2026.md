# AI 辅助 Rust 编程指南 2026 版

> **最后更新**: 2026-05-08
> **Rust 版本**: 1.96.0+ (MSRV) / Edition 2024
> **目的**: 结合 AI 工具高效学习 Rust 与构建项目
> **相比 2025 版更新**: 新增 1.95+ 特性提示词、Async Closures、Cargo Script、多维思维表征

---

## 1. AI 辅助学习路径（2026 版）

### 1.1 提示词模板 (Prompt Templates)

**概念解释（2026 版，含 1.95 特性）**:

```text
请用简洁的中文解释 Rust 的 [概念名称]，要求：
1. 结合 Rust 1.95.0 稳定版特性
2. 给出 1-2 个可直接在 Rust Playground 运行的示例
3. 说明该特性在 2024 Edition 下的行为差异（如有）
4. 指出常见误用和反例
```

**代码审查（2026 版，含 Safety Tags 意识）**:

```text
请审查以下 Rust 代码：
1. 检查所有权、生命周期、idiomatic 问题
2. 对于 unsafe 块，评估 SAFETY 注释是否充分
3. 检查是否使用了已弃用的模式（如 static mut）
4. 建议是否可以应用 Rust 1.95+ 新特性简化代码
5. 代码：[粘贴代码]
```

**错误修复（2026 版，含精确诊断）**:

```text
我遇到以下 Rust 编译错误（版本 1.95.0，Edition 2024）：
[粘贴错误信息]

请：
1. 解释根本原因（从 borrow checker / type system 角度）
2. 给出最小修复方案
3. 如果是常见错误，引用 rustc --explain 对应编号
4. 建议预防此类错误的惯用法
```

**特性迁移（新增：2024 Edition 迁移）**:

```text
请将以下 Rust 2021 Edition 代码迁移到 2024 Edition，
并应用 Rust 1.95+ 新特性优化：
[粘贴代码]

要求：
1. 使用 Edition 2024 的语法糖（如 if let guards, cfg_select!）
2. 移除已弃用的模式（如 static mut）
3. 应用新稳定 API（如 Atomic::update, push_mut）
4. 保持语义等价
```

**Async Closures 专项（新增）**:

```text
请帮我将以下旧式异步闭包迁移到 async closure (1.85.0+ 稳定)：
旧代码：|s: String| async move { process(s).await }

要求：
1. 使用 async |s: &str| { ... } 新语法
2. 使用 AsyncFn trait bound（如适用）
3. 解释旧范式与新范式的生命周期差异
4. 说明 Send bound 的处理策略
```

### 1.2 多维思维表征生成（新增）

```text
请为 Rust 的 [概念名称] 生成以下思维表征：
1. 概念演化推理树（从问题到解决方案到影响面）
2. 决策树（何时使用 vs 替代方案）
3. Wikipedia 概念对齐（定义、属性、示例、反例）
4. 与相关概念的关系图（Mermaid 格式）
```

---

## 2. 与本项目结合（2026 版更新）

### RAG 检索范围

将以下内容纳入 AI 检索上下文：

- **新报告**: `reports/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md`
- **新指南**:
  - `crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md`
  - `docs/06_toolchain/cargo_script_guide.md`
  - `docs/05_guides/SAFETY_TAGS_GUIDE.md`
  - `docs/06_toolchain/parallel_frontend.md`
  - `crates/c02_type_system/src/precise_capturing_guide.rs`
- **更新模块**: `crates/*/src/rust_195_features.rs`（1.95 特性全覆盖）
- **速查卡**: `docs/02_reference/quick_reference/`

### Embedding 索引建议

| 优先级 | 文档 | 理由 |
|--------|------|------|
| P0 | 对称差分析报告 v2.0 | 项目全局视图 |
| P0 | Async Closures 深度指南 | 重大范式变更 |
| P1 | 各 crate rust_195_features.rs | 最新 API 示例 |
| P1 | Safety Tags 指南 | 前沿趋势 |
| P2 | 决策树文档集 | 技术选型上下文 |

---

## 3. AI 辅助工作流（2026 版推荐）

| 阶段 | 工作流 | 工具 | 2026 新增 |
|------|--------|------|-----------|
| **学习概念** | 提示词「解释 [概念] + 示例」→ 附带速查卡链接 | Claude/GPT | 要求引用 1.95+ 特性 |
| **写代码** | 注释描述意图 → Copilot/Cursor 补全 → 验证 | Cursor/Copilot | 使用 AsyncFn / cfg_select! 等 |
| **遇到错误** | 粘贴错误码 + ERROR_CODE_MAPPING + 1.95 上下文 | Claude/GPT | 考虑 Edition 2024 影响 |
| **迁移升级** | 旧代码 → AI 迁移到 2024 Edition → 测试 | Claude/GPT | 自动化迁移提示词 |
| **代码审查** | 粘贴代码 + 要求「按 Rust 1.95 惯用法审查」 | Claude/GPT | Safety Tags / static mut 审计 |
| **技术选型** | 提供决策树上下文 → AI 分析优劣 | Claude/GPT | io_uring vs epoll, Embassy vs RTIC |

---

## 4. 2026 特性专项提示词

### 4.1 `if let` guards (1.95.0)

```text
请用 `if let` guards 简化以下嵌套 match 代码：
[粘贴代码]

要求：
1. 展示传统嵌套 vs if let guard 的对比
2. 说明 guard 中绑定的作用域限制
3. 说明与 let chains (1.88+) 的区别
```

### 4.2 `cfg_select!` (1.95.0)

```text
请将以下嵌套 cfg! 代码重构为 cfg_select!：
[粘贴代码]

要求：
1. 展示嵌套 cfg! vs cfg_select! 的对比
2. 说明适用场景（表达式级 vs 项级）
3. 给出跨平台库设计的最佳实践
```

### 4.3 `Atomic*::update` (1.95.0)

```text
请将以下 CAS 循环重构为 Atomic::update / try_update：
[粘贴代码]

要求：
1. 展示 fetch_update vs update 的语义差异
2. 说明 try_update 的适用场景（条件更新）
3. 警告：闭包必须是纯函数（无副作用）
```

### 4.4 `use<..>` precise capturing (2024 Edition)

```text
请为以下函数添加 use<..> 精确捕获，并解释原因：
[粘贴代码]

要求：
1. 说明 2021 Edition 的自动捕获行为
2. 说明 2024 Edition 的精确捕获优势
3. 给出 use<> / use<'a> / use<T> 的选择决策
```

---

## 5. 用 Rust 构建 AI 应用（2026 更新）

Rust 在 AI/ML 领域的生态持续演进：

| 框架 | 用途 | 2026 状态 |
|------|------|----------|
| **Candle** | 轻量 ML 推理 | 活跃，支持更多模型 |
| **Burn** | 深度学习框架 | 0.10+，训练能力增强 |
| **llm** | LLM 推理 | 被 Candle 生态整合 |
| **ort** | ONNX Runtime 绑定 | 生产级推理 |
| **Rust-BERT** | NLP 任务 | 基于 Candle 重构 |

详见 [AI+Rust 生态指南](../docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md)。

---

## 6. 注意事项（2026 版更新）

1. **验证输出**: AI 生成的 Rust 代码务必 `cargo build` 和 `cargo test` 验证
2. **版本一致**: 明确指定 **Rust 1.96.0+** 和 **Edition 2024**
3. **引用权威**: 对关键概念要求 AI 引用 The Rust Book、Reference、RFC
4. **安全性**: AI 生成的 unsafe 代码需人工复核 SAFETY 注释
5. **前沿特性**: 询问 nightly 特性时，要求 AI 标注 `#![feature(...)]` 和稳定性状态

---

## 7. 相关文档

- [guides/README.md](./README.md) - 指南入口
- [对称差分析报告 v2.0](../reports/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md) - 项目全局视图
- [Async Closures 深度指南](../crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md) - 异步闭包权威参考
- [Cargo Script 指南](../docs/06_toolchain/cargo_script_guide.md) - 脚本化 Rust
- [Safety Tags 预研](../docs/05_guides/SAFETY_TAGS_GUIDE.md) - unsafe API 标注
- [docs/02_reference/quick_reference/](../docs/02_reference/quick_reference/README.md) - 速查卡
- [LEARNING_CHECKLIST.md](../LEARNING_CHECKLIST.md) - 学习清单与自测
- [ERROR_CODE_MAPPING.md](../docs/02_reference/ERROR_CODE_MAPPING.md) - 错误码→文档映射
- [RUSTLINGS_MAPPING.md](../exercises/RUSTLINGS_MAPPING.md) - 模块↔习题对应

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
