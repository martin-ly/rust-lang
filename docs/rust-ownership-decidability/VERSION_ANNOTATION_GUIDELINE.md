# Rust 所有权形式化文档 - 版本标注规范

> 本文档定义了项目中所有 Rust 特性的版本标注标准，确保内容准确性和可维护性。

---

## 📋 版本标注分类

### 1. 已稳定特性 [Stable X.XX]

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

### 模板 A: 真实特性

```markdown
    # 特性名称

    **状态**: [Stable X.XX] / [Unstable] / [Deprecated]
    **最后更新**: YYYY-MM-DD
    **Rust 版本要求**: >= X.XX

    ## 概述
    ...
```

### 模板 B: 理论模型

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

### 新建文档必须检查

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
