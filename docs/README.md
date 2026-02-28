# Rust 学习系统 - 文档中心

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 100% 完成（修订后验收标准）
> **项目主页**: [返回主 README](../README.md)
> **100% 推进**: [DOCS_100_PERCENT_PROGRESS](./DOCS_100_PERCENT_PROGRESS.md)
> **主索引**: [00_MASTER_INDEX.md](./00_MASTER_INDEX.md) - 按主题分类的完整文档导航
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW.md](./DOCS_STRUCTURE_OVERVIEW.md) - 按 00_COMPREHENSIVE_SUMMARY 格式 100% 覆盖 docs
> **概念说明**: 本文档中心是 Rust 形式化工程系统的知识库入口，按学习路径、速查参考、思维表征、专题指南、工具链和项目元文档六大主题组织。所有文档相互链接，形成完整的知识图谱。

---

## 🎯 快速示例

```rust
// Rust 1.93.1 Edition 2024 示例
fn main() {
    // 模式匹配
    let value = Some(42);
    if let Some(n) = value {
        println!("Value: {}", n);
    }

    // 迭代器
    let sum: i32 = (1..=10)
        .filter(|x| x % 2 == 0)
        .sum();
    println!("Sum of even numbers: {}", sum);

    // 异步（需要 tokio 运行时）
    // let result = async_function().await;
}

// 所有权示例
fn ownership_demo() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权转移
    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);     // 正确
}

// 泛型与 trait
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

---

## 🎯 按主题快速导航

| 主题 | 入口 | 说明 |
| :--- | :--- | :--- |
| **学习路径** | [00_MASTER_INDEX § 01_learning](./00_MASTER_INDEX.md#01-学习路径与导航) | 学习规划、官方资源映射 |
| **速查参考** | [02_reference](#-核心文档系统) | 20 个速查卡、边界特例 |
| **形式化理论** | [03_theory](#-核心文档系统) | 研究笔记、证明索引 |
| **思维表征** | [04_thinking](./00_MASTER_INDEX.md#04-思维表征) | 思维导图、决策树、矩阵 |
| **专题指南** | [05_guides](./00_MASTER_INDEX.md#05-专题指南) | 异步、线程、WASM、Unsafe 等 |
| **工具链** | [06_toolchain](#-核心文档系统) | 编译器、Cargo、版本演进 |
| **项目元文档** | [07_project](./00_MASTER_INDEX.md#07-项目元文档) | 知识结构、版本追踪 |

---

## 🎯 按角色导航

| 角色 | 推荐路径 | 核心文档 |
| :--- | :--- | :--- |
| **初学者** | 学习路径 → 速查卡 → C01 模块 | [01_learning/README.md](./01_learning/README.md) |
| **开发者** | 专题指南 → 速查卡 → 边界特例 | [05_guides/README.md](./05_guides/README.md) |
| **研究者** | 形式化理论 → 思维表征 → 证明索引 | [research_notes/README.md](./research_notes/README.md) |
| **维护者** | 项目元文档 → 版本追踪 | [07_project/](./07_project/README.md) |

---

## 🚀 核心文档系统 {#-核心文档系统}

### 1. 快速参考（quick_reference/）

**用途**: 快速查找 Rust 语法、模式、最佳实践

**入口**: [quick_reference/README.md](./02_reference/quick_reference/README.md)

**包含**: 20 个速查卡（含 AI/ML、类型、所有权、异步、泛型、错误处理、线程、宏、测试等）

**特色**: 所有 20 个速查卡已完成交叉引用、反例速查，版本 Rust 1.93.0+

```rust
// 速查表示例：所有权规则
let s = String::from("hello");  // s 进入作用域
let t = s;                       // s 的值移动到 t
// println!("{}", s);            // 错误！s 不再有效

// 借用规则
let u = &t;      // 不可变借用
let v = &t;      // 多个不可变借用 OK
// let w = &mut t;  // 错误！不能同时有可变和不可变借用
```

---

### 2. 研究笔记（research_notes/）

**用途**: 形式化方法、类型理论、软件设计理论

**入口**: [research_notes/README.md](./research_notes/README.md) | [形式化工程系统](./rust-formal-engineering-system/00_master_index.md)（索引层，映射到 research_notes）

**说明**: 形式化理论以 **research_notes** 为主内容，**rust-formal-engineering-system** 为索引映射层。

```rust
// 形式化验证示例（Kani）
#[kani::proof]
fn verify_overflow_safety() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a < 1000 && b < 1000);
    let result = a + b;
    assert!(result < 2000);  // Kani 验证此断言对所有输入成立
}
```

---

### 3. 工具链文档（06_toolchain/）

**用途**: 编译器、Cargo、rustdoc、Rust 1.89–1.93 版本演进

**入口**: [06_toolchain/README.md](./06_toolchain/README.md)

```toml
# Cargo.toml 示例
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"
rust-version = "1.93"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.35", features = ["full"] }

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

---

### 4. 完整文档索引

**所有根目录文档按主题分类** → [00_MASTER_INDEX.md](./00_MASTER_INDEX.md)

---

## 📊 文档统计

### 文档系统统计

| 类别 | 数量 | 状态 |
| :--- | :--- | :--- |
| 快速参考 | 20 个速查卡 | ⭐ (含 AI/ML、进程管理、网络编程、算法、设计模式、WASM) |
| 研究笔记 | 45+ 个研究文档 | 研究笔记系统100%完成 |
| 形式化系统 | 500+ 个理论文档 | 10个主要模块 |
| 工具链文档 | 5 个工具指南 | 包含 Rust 1.93 vs 1.92 对比 |
| 归档文件 | 100 个文件 | 已归档 |
| 文档完善度 | 100% | ✅（20/20 速查卡已完成） |
| 交叉引用 | 100% | ✅ (所有19个速查卡已完成) |

---

## 🛠️ 文档管理

### 📦 归档说明

与主题不相关的文件已归档，保持主目录简洁：

- [归档说明](./archive/README.md) - 归档文件分类说明
- [归档总结报告](./archive/root_completion_reports/ARCHIVE_SUMMARY.md) - 归档详情统计
- [归档完成报告](./archive/process_reports/2026_02/ARCHIVE_SUMMARY.md) - 归档工作总结

### 🧹 执行归档

如果需要整理文档结构：

```bash
# Linux/Mac
./scripts/archive_docs.sh

# Windows
scripts\archive_docs.bat
```

---

## 🔍 搜索文档

### 使用搜索工具

```bash
# 搜索关键词
cargo run -p rust-doc-search -- search "ownership"

# 正则表达式搜索
cargo run -p rust-doc-search -- search --regex "async.*await"

# 模糊搜索
cargo run -p rust-doc-search -- search --fuzzy "borrowing"
```

### 在线搜索

访问 mdBook 平台后，使用内置搜索功能（快捷键: `S`）

---

## 📞 获取帮助

### 问题和讨论

- 🐛 报告问题: [GitHub Issues](https://github.com/your-repo/rust-lang/issues)
- 💬 讨论交流: [GitHub Discussions](https://github.com/your-repo/rust-lang/discussions)

### 文档贡献

参见: [归档文件说明](./archive/README.md) - 查看归档的文件列表

---

## 📚 相关文档链接

### 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [./research_notes/formal_methods/README.md](./research_notes/formal_methods/README.md) |
| 证明索引 | 形式化证明集合 | [./research_notes/PROOF_INDEX.md](./research_notes/PROOF_INDEX.md) |
| 形式化工程系统 | 形式化系统索引 | [./rust-formal-engineering-system/00_master_index.md](./rust-formal-engineering-system/00_master_index.md) |

### 核心指南

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 测试覆盖指南 | 测试策略与覆盖率 | [./05_guides/TESTING_COVERAGE_GUIDE.md](./05_guides/TESTING_COVERAGE_GUIDE.md) |
| 最佳实践 | 工程最佳实践 | [./research_notes/BEST_PRACTICES.md](./research_notes/BEST_PRACTICES.md) |
| 工具指南 | 验证工具使用 | [./research_notes/TOOLS_GUIDE.md](./research_notes/TOOLS_GUIDE.md) |
| 质量检查清单 | 代码质量检查 | [./research_notes/QUALITY_CHECKLIST.md](./research_notes/QUALITY_CHECKLIST.md) |

---

## 📁 归档文件

过程性文档（完成报告、进度报告、审计报告、计划文档等）已归档至 [archive/process_reports/2026_02/](./archive/process_reports/2026_02/README.md) 以保持核心内容的清晰。

**归档文件包括**:

- 内容改进/深度强化完成报告
- 格式修复进度/完成报告
- 权威对齐审计/进度报告
- 项目评估/计划文档

**查看归档**:

- [归档摘要](./archive/process_reports/2026_02/ARCHIVE_SUMMARY.md) - 完整归档文件列表
- [archive/README.md](./archive/README.md) - 归档系统说明

---

## 🎉 最新更新

### 2026-02-20 🆕

- ✅ **文件归档**：34个过程性文档归档，核心内容更清晰
- ✅ **README 增强**：为所有索引层 README 添加代码示例和形式化链接

### 2026-02-13 🆕

- ✅ **主索引创建**：00_MASTER_INDEX.md 按主题分类导航
- ✅ **README 重构**：按主题分块展示，链至主索引
- ✅ **主题目录重组**：01_learning、02_reference、04_thinking、05_guides、06_toolchain、07_project
- ✅ **最佳实践合并**：BEST_PRACTICES_GUIDE + COMPREHENSIVE_BEST_PRACTICES → BEST_PRACTICES.md
- ✅ **版本文档归档**：RUST_192_* → archive/version_reports/；过程性文档 → archive/process_reports/
- ✅ **docs/docs 迁移**：14_workflow → 05_guides/workflow/
- ✅ **链接修复 100%**：MODULE_1.93、DOCUMENTATION_CROSS_REFERENCE_GUIDE、quick_reference、PROJECT_STRUCTURE、CONTRIBUTING、guides 等

### 2026-01-27 🆕

- ✅ **高级主题文档**：高级主题深度指南已创建（8个高级主题）
- ✅ **综合最佳实践**：综合最佳实践指南已创建（10个最佳实践主题）
- ✅ **性能测试报告**：性能测试报告已创建（46个基准测试文件汇总）
- ✅ **文档完善**：文档完善度达到 95%，整体项目完成度达到 90-95%

---

**维护团队**: Rust Learning Community
**最后更新**: 2026-02-20
**状态**: ✅ **Rust 1.93.0 更新完成**

---

🦀 **开始探索 Rust 学习之旅！** 🦀
