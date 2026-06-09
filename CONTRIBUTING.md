# 贡献指南

> **目标**: 让每一位新贡献者在 **30 分钟内** 找到并提交首个任务。

---

## 贡献路径分类

本项目接受三类贡献，请选择最适合你的路径：

| 贡献类型 | 适合人群 | 典型任务 | 验收标准 |
|:---|:---|:---|:---|
| **📄 文档贡献** | 技术写作者、学习者、翻译者 | 概念文档勘误、术语更新、L6 生态层补充、多语言对照 | `kb_auditor.py` 0 问题 |
| **💻 代码贡献** | Rust 开发者、领域专家 | `crates/` 可编译示例、`exercises/` 练习题、嵌入式测验 | `cargo test --workspace` 通过 |
| **🔍 审计反馈** | QA 工程师、 meticulous 读者 | 死链报告、版本声明过期、逻辑矛盾、对称差检测 | 附具体文件路径和修复建议 |

---

## 快速开始（5 分钟）

### 1. 了解项目结构

```text
concept/    L0-L7 概念层（核心知识体系，258 文件）
docs/       参考文档、指南、研究报告
knowledge/  学习路径、练习、深度专题
crates/     可编译 Rust 代码示例（13 个 crate）
exercises/  练习题集合
examples/   跨模块综合示例
book/       mdBook 生成输出（无需手动编辑）
scripts/    维护脚本（kb_auditor.py、version_fact_check.py 等）
```

### 2. 找到你的第一个任务

| 如果你擅长... | 推荐任务 | 入口 | 难度 |
|:---|:---|:---|:---:|
| **写 Rust 代码** | `crates/` 中添加可编译示例 | `crates/c01_ownership_borrow_scope/src/` | ⭐ |
| **写文档** | 概念文件补充或勘误 | `concept/` 中任意 `.md` 文件 | ⭐ |
| **翻译/术语** | 术语英中对照表（100 术语，需与 TRPL 一致） | `concept/00_meta/terminology_glossary.md` | ⭐⭐ |
| **测试/QA** | 运行验证脚本并修复问题 | `scripts/kb_auditor.py` | ⭐⭐ |
| **教学** | 在练习题中添加 `// TODO:` 参考答案 | `exercises/src/` | ⭐⭐ |
| **领域专家** | L6 生态层代码示例（量子计算、嵌入式图形、工业案例等） | `concept/06_ecosystem/` 中标记 `[社区贡献欢迎]` 的文件 | ⭐⭐⭐ |
| **形式化验证** | Kani / Verus / Miri 可运行示例 | `crates/` 新增 `formal_verification_examples.rs` | ⭐⭐⭐⭐ |

**新手友好任务标签**（在文件中查找）：

- `TODO:` — 待补充的内容占位符
- `FIXME:` — 需要修正的错误
- `[待完善]` — 内容分级标签，表示需要扩展
- `[社区贡献欢迎]` — L6 生态文件缺少可编译 Rust 示例，欢迎提交 PR 补充
- `⚠️ **声明**: 本文件使用形式化符号...` — L4 文件已统一标注，如需更新形式化工具引用（Kani 0.65+ / AutoVerus 等）欢迎 PR

### 3. 环境准备

```bash
# Rust 工具链（MSRV 1.96.0）
rustup update stable

# 可选：安装验证工具
cargo install cargo-audit     # 依赖安全检查
cargo install mdbook          # 文档构建
cargo install mdbook-toc      # 目录生成（当前禁用，见 book.toml）

# 验证环境
cargo check --workspace       # 应全部通过
cargo test --workspace        # 应全部通过
```

---

## 贡献流程

### 小型修复（< 5 文件）

1. **Fork** 本仓库
2. 在对应文件中修改
3. 运行验证脚本：

   ```bash
   cargo check --workspace
   cargo test --workspace
   python scripts/kb_auditor.py        # 确保死链为 0
   python scripts/version_fact_check.py # 确保版本错误为 0
   ```

4. 提交 PR，描述修改内容和验证结果

### 大型变更（> 5 文件 或 新增章节）

1. 先在 **Issue** 中描述你的计划，避免与正在进行的工作冲突
2. 遵循 [执行计划](.kimi/EXECUTION_PLAN_CONFIRMED_2026_05_29.md) 的当前阶段方向
3. 修改后必须更新 `CHANGELOG.md`
4. 如涉及 Mermaid 图表，运行 `mdbook build` 验证

---

## 文档规范

### 概念文件头部模板（`concept/`）

```markdown
# 标题

> **受众**: [初学者] / [进阶] / [专家] / [研究者]
> **内容分级**: [综述级] / [实验级] / [专家级]
> **Bloom 层级**: 记忆 / 理解 / 应用 / 分析 / 评价 / 创造
> **前置概念**: [链接]
> **后置延伸**: [链接]

---
```

### L4 形式化文件特殊要求

必须包含声明：

```markdown
> ⚠️ **声明**: 本文件使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Verus](...)、[Kani](...)、[Coq](...)。
```

### 代码块规范

- Rust 代码块使用 `` ```rust `` 或 `` ```rust,ignore ``（如需要 nightly 特性）
- `compile_fail` 代码块必须**确实编译失败**
- 所有 crates/ 中的代码必须通过 `cargo check --workspace`

### 术语规范

- 首次出现英文术语时标注中文：`所有权 (Ownership)`
- 后续使用中文或英文均可，但同一文件内保持一致
- 参考 `concept/00_meta/terminology_glossary.md` 中的标准译法

---

## 验证清单（提交前必做）

```bash
# 1. 编译检查
cargo check --workspace

# 2. 测试检查
cargo test --workspace

# 3. 死链检查
python scripts/kb_auditor.py
# 期望输出: 死链: 0

# 4. 版本事实检查
python scripts/version_fact_check.py
# 期望输出: 发现问题: 0 处

# 5. 代码块编译检查（可选，耗时较长）
python scripts/code_block_compiler.py

# 6. 文档构建（如修改了 concept/ 中的 Mermaid 图表）
mdbook build
```

---

## 当前维护重点

根据 [执行计划](.kimi/EXECUTION_PLAN_CONFIRMED_2026_05_29.md)，**Phase 1-4 已完成**（2026-06-02）。当前进入**维护与持续跟踪期**：

### 常态化维护（每月/每季度）

1. **版本事实准确性**: Rust 1.96.0 特性覆盖完整，1.97 Preview 跟踪及时 → **每 6 周随版本发布更新**
2. **死链清零**: `kb_auditor.py` 死链保持 0 → **每月运行一次**
3. **编译通过**: `cargo check --workspace` 零错误 → **每次提交前必做**
4. **依赖安全**: `cargo audit` 0 高危 → **每季度运行一次**

### 优先缺口（欢迎贡献）

| 缺口 | 位置 | 难度 | 说明 |
|:---|:---|:---:|:---|
| L6 代码示例 | `concept/06_ecosystem/` 中 11 个 `[社区贡献欢迎]` 文件 | ⭐⭐⭐ | 量子计算、嵌入式图形、工业案例等领域需要可编译示例 |
| 形式化工具示例 | `crates/` 新增 / `concept/04_formal/` | ⭐⭐⭐⭐ | Kani 0.65+、AutoVerus、ESBMC 的可运行 Rust 示例 |
| TRPL 对照更新 | `docs/TRPL_3RD_ED_DIFF.md` | ⭐⭐ | 随 TRPL 在线版更新同步维护对照矩阵 |
| 新版本特性跟踪 | `crates/*/src/rust_197_features.rs` | ⭐⭐ | Rust 1.97/1.98 新特性示例和文档

---

## 联系方式

- **Issue 讨论**: 使用 GitHub Issues 提出改进建议
- **PR 提交**: 小型修复直接 PR，大型变更先开 Issue 讨论
- **质量仪表盘**: 查看 `reports/kb_quality_dashboard.md` 了解当前项目健康度

---

**返回项目主页**: [README.md](README.md)
