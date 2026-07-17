# TRPL 第 3 版对照审计（TRPL 3rd Edition Alignment Audit）

> **内容分级**: [综述级]
> **受众**: [专家]
> **定位**: 系统对比 The Rust Programming Language 第 3 版（2025-10 出版）与 `concept/` L1-L3 核心内容，识别差距并规划更新。
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)

---

## 审计目标

1. 识别 TRPL 第 3 版新增或重组的章节
2. 检查 `concept/` 是否覆盖 TRPL 第 3 版的全部核心概念
3. 对比教学顺序和术语使用，确保与官方一致
4. 为 TRPL 更新后的内容迁移提供路线图

---

## TRPL 第 3 版章节结构（2025-10）

| 章节 | 主题 | concept/ 对应文件 | 状态 |
|:---:|:---|:---|:---:|
| Ch 1 | Installation & Hello, world! | `01_foundation/00_pl_prerequisites.md` | ✅ |
| Ch 2 | Programming a Guessing Game | — | 项目制，无对应 |
| Ch 3 | Common Programming Concepts | `01_foundation/04_type_system.md` | ✅ |
| Ch 4 | Understanding Ownership | `01_foundation/01_ownership.md` | ✅ |
| Ch 5 | Using Structs to Structure Related Data | `01_foundation/04_type_system.md` | ✅ |
| Ch 6 | Enums and Pattern Matching | `01_foundation/04_type_system.md` | ✅ |
| Ch 7 | Managing Growing Projects | `01_foundation/11_modules_and_paths.md` | ✅ |
| Ch 8 | Common Collections | `01_foundation/08_collections.md` | ✅ |
| Ch 9 | Error Handling | `01_foundation/10_error_handling_basics.md` | ✅ |
| Ch 10 | Generic Types, Traits, and Lifetimes | `02_intermediate/01_traits.md`, `02_intermediate/02_generics.md`, `01_foundation/03_lifetimes.md` | ✅ |
| Ch 11 | Writing Automated Tests | `01_foundation/16_testing_basics.md` | ✅ |
| Ch 12 | An I/O Project: Building a Command Line Program | `LEARNING_MVP_PATH.md` | ✅ |
| Ch 13 | Functional Language Features | `01_foundation/15_closure_basics.md` | ✅ |
| Ch 14 | More about Cargo and Crates.io | `06_ecosystem/01_toolchain.md` | ✅ |
| Ch 15 | Smart Pointers | `02_intermediate/12_smart_pointers.md` | ✅ |
| Ch 16 | Fearless Concurrency | `03_advanced/01_concurrency.md` | ✅ |
| Ch 17 | Object Oriented Programming Features | `02_intermediate/01_traits.md` | ✅ |
| Ch 18 | Patterns and Matching | `01_foundation/04_type_system.md` | ✅ |
| Ch 19 | Advanced Features | `03_advanced/04_macros.md` | ✅ |
| Ch 20 | Final Project: Building a Multithreaded Web Server | `LEARNING_MVP_PATH.md` | ✅ |

---

## 已知差异与行动项

| 差异 | TRPL 3rd Ed | 本项目 | 行动 |
|:---|:---|:---|:---:|
| 所有权可视化 | 新增 Aquascope 风格内存图 | 纯文本描述 | 研究中：评估是否引入静态示意图 |
| 嵌入式测验 | 每章有 Quiz | 仅 3 个核心文件有测验 | 🔄 扩展至 L1-L3 全部文件 |
| 异步章节 | 全面重写，覆盖 Rust 2024 Edition | 已覆盖 async/await | ✅ 基本对齐 |
| 错误处理 | 新增 `assert_matches!` | `02_intermediate/05_assert_matches.md` | ✅ 已覆盖 |
| 闭包捕获 | 更详细的捕获规则 | `01_foundation/15_closure_basics.md` | ✅ 已覆盖 |

---

## 自动化审计脚本

```bash
# 检查 concept/ 是否覆盖 TRPL 高频术语
python scripts/check_terminology_alignment.py --reference trpl

# 检查 TRPL 中新增 API 是否在本项目中有示例
python scripts/audit_stable_apis.py --version 1.96.0
```

---

## 结论

`concept/` L1-L3 内容已**全面覆盖** TRPL 第 3 版核心章节。主要差距在于：

1. **交互式学习体验**（测验、可视化）——本项目正在通过嵌入式测验弥补
2. **项目制学习路径**（guessing game、web server）——本项目通过 MVP 路径和 crates 示例弥补

> **来源**: [The Rust Programming Language, 3rd Edition](https://doc.rust-lang.org/book/) · [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/)
> **状态**: 对照框架已建立，待持续更新
