# Rust 所有权形式化文档 - 版本标注规范

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> 本文档定义了项目中所有 Rust 特性的版本标注标准，确保内容准确性和可维护性。

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权形式化文档 - 版本标注规范](.#rust-所有权形式化文档---版本标注规范)
  - [📑 目录](.#-目录)
  - [📋 版本标注分类](.#-版本标注分类)
    - [1. 已稳定特性 \[Stable X.XX\]](#1-已稳定特性-stable-xxx)
    - [2. 开发中特性 \[Unstable/Nightly\]](#2-开发中特性-unstablenightly)
    - [3. 理论模型 \[Theoretical\]](#3-理论模型-theoretical)
  - [🏷️ 文件头标注模板](.#文件头标注模板)
    - [模板 A: 真实特性](.#模板-a-真实特性)
    - [模板 B: 理论模型](.#模板-b-理论模型)
  - [📊 版本对照表](.#-版本对照表)
  - [✅ 审核检查清单](.#-审核检查清单)
    - [新建文档必须检查](.#新建文档必须检查)
    - [现有文档审核](.#现有文档审核)
  - [🔧 自动化检查](.#-自动化检查)
    - [检查脚本使用](.#检查脚本使用)
  - [📅 维护责任](.#-维护责任)
  - [📝 变更记录](.#-变更记录)
<a id="维护者-rust-ownership-decidability-team"></a>
  - [**维护者**: Rust-Ownership-Decidability Team](.#维护者-rust-ownership-decidability-team)
  - [相关概念](.#相关概念)
  - [权威来源索引](.#权威来源索引)
  - [权威来源索引](.#权威来源索引-1)

## 📋 版本标注分类
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1. 已稳定特性 [Stable X.XX]
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

**定义**: 已在 Rust 稳定版中发布的特性

**标注格式**:

```markdown
    ## 常量泛型 [Stable 1.51]

    > **稳定版本**: Rust 1.51 (2021年3月)
```

**使用场景**:

- 真实存在于 Rust 稳定版的特性
- 可以安全地在生产代码中使用
- 有明确的稳定版本号

---

### 2. 开发中特性 [Unstable/Nightly]
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

**定义**: 正在开发中，仅在 Nightly 版本可用或尚未稳定的特性

**标注格式**:

```markdown
    ## 精确捕获 (Precise Capturing) [Unstable]

    > **状态**: 开发中，跟踪 issue: #12345
    > **预计稳定版本**: 待定
```

**使用场景**:

- 有 RFC 但尚未实现完成
- 已实现但还在测试阶段
- 需要 `#![feature(...)]` 启用

---

### 3. 理论模型 [Theoretical]
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**定义**: 为教学或研究目的构建的理论构造，不是真实 Rust 特性

**标注格式**:

```markdown
    ## Reborrow Trait [Theoretical]

    > **⚠️ 免责声明**: 这是为教学目的构建的理论模型，不是真实 Rust 语言特性。
    > 用于说明借用检查器的内部工作原理。
```

**使用场景**:

- 简化复杂概念的教学模型
- 形式化验证的抽象构造
- 不对应真实 Rust 语法

---

## 🏷️ 文件头标注模板
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 模板 A: 真实特性
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```markdown
    # 特性名称

    **状态**: [Stable X.XX] / [Unstable] / [Deprecated]
    **最后更新**: YYYY-MM-DD
    **Rust 版本要求**: >= X.XX

    ## 概述
    ...
```

### 模板 B: 理论模型
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```markdown
    # 模型名称 [Theoretical]

    **⚠️ 免责声明**: 本文为教学/研究目的构建的理论模型，不是真实 Rust 特性。
    **最后更新**: YYYY-MM-DD
    **相关真实特性**: 列举相关的真实 Rust 特性

    ## 概述
    ...
```

---

## 📊 版本对照表
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 特性 | 文档原标注 | 正确标注 | 修正状态 |
|------|-----------|----------|----------|
| Const Generics | Rust 1.94 | [Stable 1.51] | 待修正 |
| Async/Await | Rust 1.94 | [Stable 1.39] | 待修正 |
| array_windows | - | [Stable 1.94] | 待添加 |
| LazyCell/LazyLock 新方法 | - | [Stable 1.94] | 待添加 |
| Reborrow Trait | Rust 1.94 | [Theoretical] | 待修正 |
| CoerceShared Trait | Rust 1.94 | [Theoretical] | 待修正 |
| Precise Capturing | Rust 1.94 | [Unstable] | 待修正 |

---

## ✅ 审核检查清单
>
> **[来源: [crates.io](https://crates.io/)]**

### 新建文档必须检查
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [ ] 特性是否真实存在于 Rust?
- [ ] 如果是真实特性，稳定版本号是多少?
- [ ] 如果是理论模型，是否添加免责声明?
- [ ] 文件头是否包含正确的版本标注?

### 现有文档审核

- [ ] 检查所有 "Rust 1.94" 标注
- [ ] 验证版本号的准确性
- [ ] 确认虚构特性有免责声明
- [ ] 更新最后更新时间

---

## 🔧 自动化检查

### 检查脚本使用

```bash
# 检查版本标注
python scripts/check_version_annotations.py

# 生成版本报告
python scripts/generate_version_report.py
```

---

## 📅 维护责任

| 任务 | 频率 | 负责人 |
|------|------|--------|
| 审核新文档的版本标注 | 每次提交 | 贡献者 |
| 检查 Rust Release Notes | 每6周 | 维护者 |
| 更新特性状态 | 每季度 | 维护者 |
| 全面审核所有标注 | 每半年 | 维护团队 |

---

## 📝 变更记录

| 日期 | 版本 | 变更内容 |
|------|------|----------|
| 2026-03-13 | v1.0 | 初始版本，建立标注规范 |

---

**规范版本**: v1.0
**最后更新**: 2026-03-13
**维护者**: Rust-Ownership-Decidability Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念

- [rust-ownership-decidability 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
