# 研究笔记最佳实践 {#研究笔记最佳实践}

> **EN**: Best Practices
> **Summary**: 研究笔记最佳实践 Best Practices. (stub/archive redirect)
>
> **概念族**: 综合研究
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2025-01-27
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 完成

---

## 📑 目录 {#目录}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [研究笔记最佳实践 {#研究笔记最佳实践}](#研究笔记最佳实践-研究笔记最佳实践)
  - [📑 目录 {#目录}](#-目录-目录)
  - [📋 概述 {#概述}](#-概述-概述)
    - [目标 {#目标}](#目标-目标)
  - [形式化论证最佳实践 {#形式化论证最佳实践}](#形式化论证最佳实践-形式化论证最佳实践)
  - [研究笔记与形式化体系衔接 {#研究笔记与形式化体系衔接}](#研究笔记与形式化体系衔接-研究笔记与形式化体系衔接)
  - [实质内容不足判断与修复 {#实质内容不足判断与修复}](#实质内容不足判断与修复-实质内容不足判断与修复)
  - [✍️ 编写最佳实践 {#编写最佳实践}](#️-编写最佳实践-编写最佳实践)
    - [1. 明确研究目标 {#1-明确研究目标}](#1-明确研究目标-1-明确研究目标)
    - [2. 提供理论基础 {#2-提供理论基础}](#2-提供理论基础-2-提供理论基础)
    - [3. 使用清晰的结构 {#3-使用清晰的结构}](#3-使用清晰的结构-3-使用清晰的结构)
  - [📚 内容组织最佳实践 {#内容组织最佳实践}](#-内容组织最佳实践-内容组织最佳实践)
    - [1. 模块化组织 {#1-模块化组织}](#1-模块化组织-1-模块化组织)
    - [2. 渐进式展开 {#2-渐进式展开}](#2-渐进式展开-2-渐进式展开)
    - [3. 交叉引用 {#3-交叉引用}](#3-交叉引用-3-交叉引用)
  - [🔗 链接管理最佳实践 {#链接管理最佳实践}](#-链接管理最佳实践-链接管理最佳实践)
    - [1. 使用相对路径 {#1-使用相对路径}](#1-使用相对路径-1-使用相对路径)
    - [2. 提供描述性链接文本 {#2-提供描述性链接文本}](#2-提供描述性链接文本-2-提供描述性链接文本)
    - [3. 维护链接完整性 {#3-维护链接完整性}](#3-维护链接完整性-3-维护链接完整性)
  - [💻 代码示例最佳实践 {#代码示例最佳实践}](#-代码示例最佳实践-代码示例最佳实践)
    - [1. 提供可运行的代码 {#1-提供可运行的代码}](#1-提供可运行的代码-1-提供可运行的代码)
    - [2. 添加注释和说明 {#2-添加注释和说明}](#2-添加注释和说明-2-添加注释和说明)
    - [3. 展示错误和解决方案 {#3-展示错误和解决方案}](#3-展示错误和解决方案-3-展示错误和解决方案)
  - [📖 文档格式最佳实践 {#文档格式最佳实践}](#-文档格式最佳实践-文档格式最佳实践)
    - [1. 使用一致的格式 {#1-使用一致的格式}](#1-使用一致的格式-1-使用一致的格式)
    - [2. 使用列表和表格 {#2-使用列表和表格}](#2-使用列表和表格-2-使用列表和表格)
    - [3. 使用代码块和引用 {#3-使用代码块和引用}](#3-使用代码块和引用-3-使用代码块和引用)
  - [🔍 可发现性最佳实践 {#可发现性最佳实践}](#-可发现性最佳实践-可发现性最佳实践)
    - [1. 使用关键词 {#1-使用关键词}](#1-使用关键词-1-使用关键词)
    - [2. 更新索引文件 {#2-更新索引文件}](#2-更新索引文件-2-更新索引文件)
    - [3. 提供多种查找方式 {#3-提供多种查找方式}](#3-提供多种查找方式-3-提供多种查找方式)
  - [🤝 协作最佳实践 {#协作最佳实践}](#-协作最佳实践-协作最佳实践)
    - [1. 遵循贡献指南 {#1-遵循贡献指南}](#1-遵循贡献指南-1-遵循贡献指南)
    - [2. 提供清晰的提交信息 {#2-提供清晰的提交信息}](#2-提供清晰的提交信息-2-提供清晰的提交信息)
    - [3. 响应反馈 {#3-响应反馈}](#3-响应反馈-3-响应反馈)
  - [✅ 质量保证最佳实践 {#质量保证最佳实践}](#-质量保证最佳实践-质量保证最佳实践)
    - [1. 使用质量检查清单 {#1-使用质量检查清单}](#1-使用质量检查清单-1-使用质量检查清单)
    - [2. 代码审查 {#2-代码审查}](#2-代码审查-2-代码审查)
    - [3. 持续改进 {#3-持续改进}](#3-持续改进-3-持续改进)
  - [🎯 与 Rust 官方规范的对齐 {#与-rust-官方规范的对齐}](#-与-rust-官方规范的对齐-与-rust-官方规范的对齐)
    - [Rust API Guidelines {#rust-api-guidelines}](#rust-api-guidelines-rust-api-guidelines)
    - [Clippy lint 文档 {#clippy-lint-文档}](#clippy-lint-文档-clippy-lint-文档)
    - [Nomicon 重点章节 {#nomicon-重点章节}](#nomicon-重点章节-nomicon-重点章节)
    - [Rust Book 重点章节 {#rust-book-重点章节}](#rust-book-重点章节-rust-book-重点章节)
  - [🔗 相关资源 {#相关资源}](#-相关资源-相关资源)
    - [核心文档 {#核心文档}](#核心文档-核心文档)
    - [工具和资源 {#工具和资源}](#工具和资源-工具和资源)
  - [🆕 权威国际化内容升级 (Rust 1.97.0+) {#权威国际化内容升级-rust-1960}](#-权威国际化内容升级-rust-1961-权威国际化内容升级-rust-1960)
    - [本次升级要点 {#本次升级要点}](#本次升级要点-本次升级要点)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 📋 概述 {#概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本文档提供研究笔记系统的最佳实践指南，帮助研究者和贡献者创建高质量的研究笔记。

### 目标 {#目标}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- 提供清晰的编写指南
- 确保内容质量和一致性（Coherence）
- 优化用户体验
- 促进协作和贡献

---

## 形式化论证最佳实践 {#形式化论证最佳实践}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def BP1（形式化完备性）**：研究笔记 $N$ 满足**形式化完备**，当且仅当 $N$ 对核心概念有 Def/Axiom、对主要结论有定理及证明或证明思路、对边界有反例。

**Axiom BP1**：形式化完备的研究笔记与 [PROOF_INDEX](10_proof_index.md) 的论证链一致；公理→引理→定理→推论可追溯。

**定理 BP-T1（完备性蕴涵可追溯）**：若 $N$ 满足 Def BP1，则 $N$ 的核心定理可追溯至 [FORMAL_PROOF_SYSTEM_GUIDE](10_formal_proof_system_guide.md) 的概念-公理-定理映射。

*证明*：由 Def BP1；形式化完备蕴含定理有证明或证明思路；证明引用公理/引理，故可追溯至映射表。∎

**最佳实践**：

- ✅ 核心概念：给出形式化定义（Def）或引用已有定义
- ✅ 主要结论：用定理（T）陈述，并给出证明或证明思路
- ✅ 边界条件：重要断言补充反例
- ✅ 交叉引用：与 [PROOF_INDEX](10_proof_index.md)、[FORMAL_PROOF_SYSTEM_GUIDE](10_formal_proof_system_guide.md) 衔接

**证明深度**：L1 证明思路 / L2 完整证明 / L3 机器可检查；见 [PROOF_INDEX](10_proof_index.md) § 证明深度层次、[CORE_THEOREMS_FULL_PROOFS](10_core_theorems_full_proofs.md) L2 示例、[coq_skeleton](../../archive/deprecated/coq_skeleton/README.md)（归档只读） L3 骨架。

**引用**：[FORMAL_PROOF_SYSTEM_GUIDE](10_formal_proof_system_guide.md) 论证要素规范、
[THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](10_theoretical_and_argumentation_system_architecture.md) 论证体系五层、
[FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](10_formal_proof_critical_analysis_and_plan_2026_02.md) 批判性分析。

---

## 研究笔记与形式化体系衔接 {#研究笔记与形式化体系衔接}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def BP2（实质内容完备）**：研究笔记 $N$ 满足**实质内容完备**，当且仅当 $N$ 含：
形式化（Def/定理）、可运行代码、典型场景、反例或边界、
与 [formal_methods](formal_methods/README.md)、
[type_theory](type_theory/README.md)、
[PROOF_INDEX](10_proof_index.md) 的交叉引用。

**实践对照表**：

| 检查项 | 示例 | 形式化链接 |
| :--- | :--- | :--- |
| **形式化** | Def OW1、定理 T2 | [ownership_model](formal_methods/10_ownership_model.md) |
| **代码** | `let s = String::from("x"); take_ownership(s);` | 对应 T2 移动语义 |
| **场景** | 所有权（Ownership）转移、借用（Borrowing）、生命周期（Lifetimes） | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) |
| **反例** | 双重可变借用（Mutable Borrow）、悬垂引用 | [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](10_safe_unsafe_comprehensive_analysis.md) |
| **衔接** | 定理引用 PROOF_INDEX | [PROOF_INDEX](10_proof_index.md) |

**Rust 实质示例与定理对应**：

```rust
// 对应 ownership_model 定理 T2：移动后原绑定失效
fn example_ownership() {
    let s = String::from("hi");
    let t = s;  // 移动
    // println!("{}", s);  // 错误：s 已失效
}

// 对应 borrow_checker_proof 定理 T1：不可变借用可共存
fn example_borrow() {
    let x = 5;
    let r1 = &x;
    let r2 = &x;
    assert_eq!(*r1, *r2);
}

// 反例：违反借用规则
fn example_anti_pattern() {
    let mut v = vec![1, 2, 3];
    let r = &v[0];      // 不可变借用
    v.push(4);          // 错误：可变借用与不可变借用冲突
}
```

**引理 BP-L1**：若研究笔记满足 Def BP2，则其满足 Def BP1；实质内容完备蕴含形式化完备。

*证明*：由 Def BP1、BP2；形式化 + 代码 + 场景 + 反例 + 衔接 ⇒ 形式化完备。∎

---

## 实质内容不足判断与修复 {#实质内容不足判断与修复}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def BP3（实质内容不足）**：研究笔记 $N$ 存在**实质内容不足**，当且仅当 $N$ 存在以下至少一项：无 Def/定理或仅占位、
无可运行代码或代码与论点无关、无典型场景或仅泛泛描述、无反例或边界说明、
无与 [formal_methods](formal_methods/README.md)/[type_theory](type_theory/README.md)/[PROOF_INDEX](10_proof_index.md) 的交叉引用。

**常见无实质内容表现**：

| 表现 | 反例（不足） | 正例（充足） |
| :--- | :--- | :--- |
| 形式化 | 仅「定义见 X」无具体 Def | Def OW1、定理 T2 及证明思路 |
| 代码 | 伪代码或不可运行片段 | `cargo run` 可执行、对应某定理 |
| 场景 | 「可用于多种场景」无具体例 | 「Web API 请求→Builder 模式→Axum」 |
| 反例 | 无 | 双重可变借用（Borrowing）、悬垂引用、unwrap 空值 |
| 衔接 | 无引用 | 链接至 ownership_model T2、PROOF_INDEX |

**四步修复法**：

1. **补形式化**：为核心概念添加 Def（含符号、前置条件、结论）；为结论添加定理及证明思路；引用 [PROOF_INDEX](10_proof_index.md) 中已有证明。
2. **补代码**：添加可运行 Rust 示例（`cargo build` 通过）；在注释中标明对应定理（如 `// 对应 ownership T2`）。
3. **补场景与反例**：添加 1–3 个典型使用场景；添加 1–2 个反例及规避策略。
4. **补衔接**：在相关段落增加 `文档名` 链接至 formal_methods、type_theory、practical_applications。

**逐文档自检**：按 [CONTENT_ENHANCEMENT](10_content_enhancement.md) 实质内容检查清单逐项核对；若任一项为空或仅占位，则需修复。
见 [FAQ Q2.5](10_faq.md#q25-如何判断研究笔记是否有实质内容) 快速判断指引。

---

## ✍️ 编写最佳实践 {#编写最佳实践}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. 明确研究目标 {#1-明确研究目标}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**最佳实践**:

- ✅ 在研究笔记开头明确说明研究目标
- ✅ 使用清晰的问题陈述
- ✅ 定义预期成果和成功标准

**示例**:

```markdown
## 研究目标 {#研究目标-1}
> **[Rust Official Docs](https://doc.rust-lang.org/)**

本研究旨在形式化 Rust 的所有权模型，包括：

- 所有权转移的语义定义
- 借用规则的逻辑表达
- 生命周期约束的形式化
```

### 2. 提供理论基础 {#2-提供理论基础}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**最佳实践**:

- ✅ 引用相关的理论基础
- ✅ 解释关键概念和术语
- ✅ 提供必要的背景知识

**示例**:

```markdown
## 理论基础 {#理论基础-1}
> **[Rust Official Docs](https://doc.rust-lang.org/)**

本研究基于以下理论：

- **线性类型系统**: 用于建模所有权转移
- **分离逻辑**: 用于表达借用规则
- **依赖类型**: 用于形式化生命周期
```

### 3. 使用清晰的结构 {#3-使用清晰的结构}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**最佳实践**:

- ✅ 遵循 [研究笔记模板](10_template.md)
- ✅ 使用清晰的标题层次
- ✅ 保持逻辑流程连贯

**示例**:

```markdown
## 研究目标 {#研究目标-1}
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

## 理论基础 {#理论基础-1}
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

## 形式化定义 {#形式化定义}
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

## 证明目标 {#证明目标}
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

## 代码示例 {#代码示例}
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

## 参考文献 {#参考文献}
> **[来源: [crates.io](https://crates.io/)]**
```

---

## 📚 内容组织最佳实践 {#内容组织最佳实践}
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 1. 模块化组织 {#1-模块化组织}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**

**最佳实践**:

- ✅ 将复杂内容分解为小模块
- ✅ 使用清晰的章节划分
- ✅ 保持每个章节的独立性

**示例**:

```markdown
## 所有权模型形式化 {#所有权模型形式化}
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 基本定义 {#基本定义}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

### 所有权转移 {#所有权转移}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

### 借用规则 {#借用规则}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

### 生命周期约束 {#生命周期约束}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
```

### 2. 渐进式展开 {#2-渐进式展开}

> **来源: [ACM](https://dl.acm.org/)**

**最佳实践**:

- ✅ 从简单到复杂逐步展开
- ✅ 先介绍概念，再深入细节
- ✅ 提供足够的上下文

**示例**:

```markdown
## 类型系统基础 {#类型系统基础}
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 基本类型 {#基本类型}

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

首先介绍基本类型...

### 复合类型 {#复合类型}

> **[POPL - Programming Languages Research](https://www.sigplan.org/Conferences/POPL/)**

然后介绍复合类型...

### 高级类型 {#高级类型}

> **[PLDI - Programming Language Design](https://www.sigplan.org/Conferences/PLDI/)**

最后介绍高级类型...
```

### 3. 交叉引用 {#3-交叉引用}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**最佳实践**:

- ✅ 在相关章节间建立链接
- ✅ 引用其他研究笔记
- ✅ 提供相关资源链接

**示例**:

```markdown
有关所有权模型的详细讨论，请参见 [所有权模型形式化](formal_methods/10_ownership_model.md)。

有关类型系统的更多信息，请参考 [类型系统基础](type_theory/10_type_system_foundations.md)。
```

---

## 🔗 链接管理最佳实践 {#链接管理最佳实践}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 1. 使用相对路径 {#1-使用相对路径}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**

**最佳实践**:

- ✅ 使用相对路径而非绝对路径
- ✅ 确保链接路径正确
- ✅ 定期检查链接有效性

**示例**:

```markdown
✅ 正确: [研究路线图](10_research_roadmap.md)
❌ 错误: 研究路线图
```

### 2. 提供描述性链接文本 {#2-提供描述性链接文本}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

**最佳实践**:

- ✅ 使用描述性的链接文本
- ✅ 避免使用"点击这里"等模糊文本
- ✅ 在链接中提供上下文

**示例**:

```markdown
✅ 正确: 查看 [研究路线图](10_research_roadmap.md) 了解研究计划
❌ 错误: 点击 [这里](10_research_roadmap.md)
```

### 3. 维护链接完整性 {#3-维护链接完整性}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

**最佳实践**:

- ✅ 定期检查链接有效性
- ✅ 更新过时的链接
- ✅ 修复断开的链接

**工具**:

<!-- markdown-link-check-disable -->
```bash
# 检查链接有效性 {#检查链接有效性}
find docs/research_notes -name "*.md" -exec grep -l "\[.*\](.*)" {} \;
# 注：上述命令中的 `[.*]` 是正则表达式语法，匹配方括号内的任意内容 {#注上述命令中的-是正则表达式语法匹配方括号内的任意内容}
```
<!-- markdown-link-check-enable -->

---

## 💻 代码示例最佳实践 {#代码示例最佳实践}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 1. 提供可运行的代码 {#1-提供可运行的代码}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

**最佳实践**:

- ✅ 确保代码可以编译和运行
- ✅ 提供完整的代码示例
- ✅ 测试所有代码示例

**示例**:

```rust
// ✅ 好的示例：完整且可运行
fn main() {
    let x = 5;
    let y = &x;
    println!("{}", y);
}
```

### 2. 添加注释和说明 {#2-添加注释和说明}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**最佳实践**:

- ✅ 为代码添加清晰的注释
- ✅ 解释关键概念和实现
- ✅ 提供使用说明

**示例**:

```rust
// 所有权转移示例
fn take_ownership(s: String) {
    // s 的所有权被转移到这个函数
    println!("{}", s);
    // s 在这里被释放
}

fn main() {
    let s = String::from("hello");
    take_ownership(s);
    // s 在这里不再可用
}
```

### 3. 展示错误和解决方案 {#3-展示错误和解决方案}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

**最佳实践**:

- ✅ 展示常见错误
- ✅ 解释错误原因
- ✅ 提供解决方案

**示例**:

```rust,ignore
// ❌ 错误示例
fn main() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    let r3 = &mut s; // 错误：不能同时存在可变和不可变借用
}

// ✅ 正确示例
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    // r1 和 r2 在这里离开作用域
    let r3 = &mut s; // 现在可以创建可变借用
}
```

---

## 📖 文档格式最佳实践 {#文档格式最佳实践}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 1. 使用一致的格式 {#1-使用一致的格式}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

**最佳实践**:

- ✅ 遵循 Markdown 规范
- ✅ 使用一致的标题层次
- ✅ 保持格式统一

**示例**:

```markdown
# 一级标题（文档标题） {#一级标题文档标题}

## 二级标题（主要章节） {#二级标题主要章节}
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 三级标题（子章节） {#三级标题子章节}

> **[ACM - Systems Programming Languages](https://dl.acm.org/)**

#### 四级标题（小节） {#四级标题小节}

> **[IEEE - Programming Language Standards](https://ieeexplore.ieee.org/) <!-- link: known-broken -->**
```

### 2. 使用列表和表格 {#2-使用列表和表格}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

**最佳实践**:

- ✅ 使用列表组织信息
- ✅ 使用表格展示数据
- ✅ 保持列表和表格格式一致

**示例**:

```markdown
## 研究工具 {#研究工具}
> **[来源: [crates.io](https://crates.io/)]**

### 形式化验证工具 {#形式化验证工具}

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- **Coq**: 交互式定理证明器
- **Lean**: 函数式编程语言和证明助手
- **Prusti**: Rust 的形式化验证工具

### 性能分析工具 {#性能分析工具}
> **[来源: [docs.rs](https://docs.rs/)]**

| 工具         | 用途     | 特点           |
| :--- | :--- | :--- |
| Criterion.rs | 基准测试 | 统计分析       |
| perf         | 性能分析 | Linux 系统工具 |
| flamegraph   | 火焰图   | 可视化性能     |
```

### 3. 使用代码块和引用 {#3-使用代码块和引用}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**最佳实践**:

- ✅ 使用代码块展示代码
- ✅ 使用引用块展示重要信息
- ✅ 指定代码语言

**示例**:

```text
\`\`\`rust
fn main() {
    println!("Hello, world!");
}
\`\`\`

> **注意**: 这是一个重要的概念，需要特别注意。
```

---

## 🔍 可发现性最佳实践 {#可发现性最佳实践}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 1. 使用关键词 {#1-使用关键词}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**最佳实践**:

- ✅ 在文档中使用相关关键词
- ✅ 在元信息中包含关键词
- ✅ 更新快速参考索引

**示例**:

```markdown
> **关键词**: 所有权、借用、生命周期、形式化验证
```

### 2. 更新索引文件 {#2-更新索引文件}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**最佳实践**:

- ✅ 在相应目录的 README 中添加链接
- ✅ 更新主索引文件
- ✅ 更新完整索引
- ✅ 更新快速参考

**示例**:

```markdown
## 形式化方法研究 {#形式化方法研究}
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [所有权模型形式化](formal_methods/10_ownership_model.md) - 所有权模型的形式化定义
- [借用检查器证明](formal_methods/10_borrow_checker_proof.md) - 借用检查器的正确性证明
```

### 3. 提供多种查找方式 {#3-提供多种查找方式}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

**最佳实践**:

- ✅ 按研究领域分类
- ✅ 按研究目标分类
- ✅ 按关键词分类
- ✅ 提供搜索功能

---

## 🤝 协作最佳实践 {#协作最佳实践}
>
> **[来源: [crates.io](https://crates.io/)]**

### 1. 遵循贡献指南 {#1-遵循贡献指南}
>
> **[来源: [docs.rs](https://docs.rs/)]**

**最佳实践**:

- ✅ 阅读 [贡献指南](10_contributing.md)
- ✅ 遵循贡献流程
- ✅ 使用质量检查清单

### 2. 提供清晰的提交信息 {#2-提供清晰的提交信息}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**最佳实践**:

- ✅ 使用描述性的提交信息
- ✅ 说明变更内容
- ✅ 引用相关问题

**示例**:

```bash
git commit -m "添加所有权模型形式化研究笔记

- 添加所有权转移的形式化定义
- 提供借用规则的逻辑表达
- 包含代码示例和证明思路
- 更新形式化方法索引

相关: #123"
```

### 3. 响应反馈 {#3-响应反馈}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**最佳实践**:

- ✅ 及时响应反馈
- ✅ 认真考虑建议
- ✅ 实施改进措施

---

## ✅ 质量保证最佳实践 {#质量保证最佳实践}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 1. 使用质量检查清单 {#1-使用质量检查清单}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**最佳实践**:

- ✅ 使用 [质量检查清单](10_quality_checklist.md)
- ✅ 逐项检查质量要求
- ✅ 确保所有要求满足

### 2. 代码审查 {#2-代码审查}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**最佳实践**:

- ✅ 请他人审查代码
- ✅ 检查代码正确性
- ✅ 验证代码可运行性

### 3. 持续改进 {#3-持续改进}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

**最佳实践**:

- ✅ 定期审查和更新内容
- ✅ 收集用户反馈
- ✅ 实施改进措施

---

## 🎯 与 Rust 官方规范的对齐 {#与-rust-官方规范的对齐}
>
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
>
> **来源**: [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html)
>
> **来源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)

研究笔记的代码示例、API 设计与安全讨论应与以下官方规范保持一致：

### Rust API Guidelines {#rust-api-guidelines}

- **C-CASE**: 命名符合 RFC 430（类型 CamelCase、函数 snake_case）。
- **C-CONV**: 转换方法使用 `as_`（免费/借用）、`to_`（昂贵）、`into_`（消耗）。
- **C-GETTER**: Getter 省略 `get_` 前缀，直接使用字段名。
- **C-COMMON-TRAITS**: 公共类型尽早实现 `Copy、Clone、Eq、PartialEq、Ord、PartialOrd、Hash、Debug、Display、Default`。
- **C-SEND-SYNC**: 类型应尽可能实现 `Send`/`Sync`（手动实现为 unsafe，需严格论证）。
- **C-GOOD-ERR**: 错误类型实现 `std::error::Error + Send + Sync`，并提供清晰 `Display`。
- 完整清单见 [Rust API Guidelines Checklist](https://rust-lang.github.io/api-guidelines/checklist.html)。

### Clippy lint 文档 {#clippy-lint-文档}

- **correctness**: 可能产生错误结果的代码（如 `absurd_extreme_comparisons`）。
- **suspicious**: 很可能是 bug 的代码（如 `double_must_use`）。
- **style**: 不符合 Rust 风格的写法（如 `needless_return`）。
- **complexity**: 过度复杂的写法（如 `too_many_arguments`）。
- **perf**: 性能反模式（如 `vec_init_then_push`）。
- 完整 lint 列表与示例见 [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html)。

### Nomicon 重点章节 {#nomicon-重点章节}

| 主题 | Nomicon 章节 | 说明 |
| :--- | :--- | :--- |
| Unsafe 能力边界 | [what-unsafe-does.html](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | `unsafe` 允许的五种额外操作 |
| 行为 considered UB | [what-unsafe-does.html#behavior-considered-undefined](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | 语言层面的未定义行为清单 |
| 生命周期省略（Lifetime Elision） | [lifetime-elision.html](https://doc.rust-lang.org/nomicon/lifetime-elision.html) | 函数签名中的生命周期推断 |
| 子类型与型变 | [subtyping-and-variance.html](https://doc.rust-lang.org/nomicon/subtyping.html) | 协变/逆变/不变与内存安全（Memory Safety） |
| 发送与同步 | [send-and-sync.html](https://doc.rust-lang.org/nomicon/send-and-sync.html) | `Send`/`Sync` 的语义与手动实现 |
| 未初始化内存 | [uninitialized.html](https://doc.rust-lang.org/nomicon/uninitialized.html) | `MaybeUninit` 与 unsafe 初始化 |

### Rust Book 重点章节 {#rust-book-重点章节}

| 主题 | Rust Book 章节 | 说明 |
| :--- | :--- | :--- |
| 所有权与借用 | [ch04-00-understanding-ownership.html](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | 所有权、借用、slice |
| 泛型与 trait | [ch10-00-generics.html](https://doc.rust-lang.org/book/ch10-00-generics.html) | 泛型、trait、生命周期 |
| 迭代器（Iterator）与闭包 | [ch13-00-functional-features.html](https://doc.rust-lang.org/book/ch13-00-functional-features.html) | 闭包（Closures）、迭代器 |
| 并发编程 | [ch16-00-concurrency.html](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | 线程、`Mutex`、`Arc`、Send/Sync |
| 高级 trait / unsafe | [ch19-00-advanced-features.html](https://doc.rust-lang.org/book/ch19-00-advanced-features.html) | 不安全 Rust、高级 trait、宏（Macro） |

> 实践建议：在编写研究笔记的代码示例时，先运行 `cargo clippy -- -W clippy::all`，并对 unsafe 段落给出对应 Nomicon 章节的引用。

---

## 🔗 相关资源 {#相关资源}
>
> **[来源: [crates.io](https://crates.io/)]**

### 核心文档 {#核心文档}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [研究笔记模板](10_template.md) - 研究笔记模板
- [贡献指南](10_contributing.md) - 贡献流程和规范
- [质量检查清单](10_quality_checklist.md) - 质量检查标准
- [维护指南](10_maintenance_guide.md) - 系统维护指南

### 工具和资源 {#工具和资源}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [工具使用指南](10_tools_guide.md) - 研究工具详细指南
- [快速参考](10_quick_reference.md) - 快速查找指南
- [常见问题解答](10_faq.md) - 常见问题解答

---

**维护团队**: Rust Research Community
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🆕 权威国际化内容升级 (Rust 1.97.0+) {#权威国际化内容升级-rust-1960}
>
> **来源**: [Rust Research Community]
> **适用版本**: Rust 1.97.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

- 新增「与 Rust 官方规范的对齐」章节，系统引用 Rust API Guidelines、Clippy lint 文档、Nomicon、Rust Book 具体章节。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Community
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/), [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html), [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 Rust API Guidelines、Clippy、Nomicon、Rust Book 章节对齐 [Authority Source Sprint Batch 9](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Best Practice](https://en.wikipedia.org/wiki/Best_Practice)**
> **来源: [Wikipedia - Code Review](https://en.wikipedia.org/wiki/Code_Review)**
> **来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)**
> **[ACM - Code Quality](https://dl.acm.org/)**
> **[IEEE - Software Engineering Standards](https://ieeexplore.ieee.org/) <!-- link: known-broken -->**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

---
