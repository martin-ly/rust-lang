# 主题测验 {#主题测验}

> **EN**: Quizzes Index
> **Summary**: 主题测验 Quizzes Index — complete registry of the 21 standalone quiz files under `concept/`, grouped by L0–L7 layer.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-13
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

本目录收录 `concept/` 下全部 **21 个独立主题测验**的完整索引（共 **309 道主题题**；L1–L5 部分 quiz 另含 3 道元认知题），用于验证学习理解程度。题数按 `### Q…` / `### 问题…` 主题题统计。
机器可读注册表见 [`concept/00_meta/quiz_registry.yaml`](../../../concept/00_meta/quiz_registry.yaml)，人类可读索引（含题型/难度分布/回链状态）见 [测验体系注册表](../../../concept/00_meta/04_navigation/15_quiz_registry.md)。

## 测验索引 {#测验索引}

### L0 元层（00_meta）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 元层框架与知识体系架构 | [01_quiz_meta_framework.md](../../../concept/00_meta/05_quizzes/01_quiz_meta_framework.md) | 15 |

### L1 基础层（01_foundation）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 所有权、借用与生命周期 | [33_quiz_ownership_borrowing.md](../../../concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | 15 |
| 类型系统 | [24_quiz_type_system.md](../../../concept/01_foundation/11_quizzes/24_quiz_type_system.md) | 15 |
| 错误处理 | [25_quiz_error_handling.md](../../../concept/01_foundation/11_quizzes/25_quiz_error_handling.md) | 15 |
| 模块系统与测试 | [26_quiz_modules_testing.md](../../../concept/01_foundation/11_quizzes/26_quiz_modules_testing.md) | 15 |
| 闭包与迭代器 | [27_quiz_closures_iterators.md](../../../concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md) | 15 |
| 通用 PL 基座 | [29_quiz_pl_foundations.md](../../../concept/01_foundation/11_quizzes/29_quiz_pl_foundations.md) | 11 |

### L2 中级层（02_intermediate）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Trait 与泛型 | [04_quiz_traits_and_generics.md](../../../concept/02_intermediate/01_generics/04_quiz_traits_and_generics.md) | 15 |
| 内存管理 | [05_quiz_memory_management.md](../../../concept/02_intermediate/02_memory_management/05_quiz_memory_management.md) | 15 |
| C/C++ → Rust 基础对比 | [30_quiz_cpp_rust_foundations.md](../../../concept/02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md) | 13 |

### L3 高级层（03_advanced）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 并发与异步（Async） | [08_quiz_concurrency_async.md](../../../concept/03_advanced/00_concurrency/08_quiz_concurrency_async.md) | 15 |
| Unsafe Rust | [05_quiz_unsafe.md](../../../concept/03_advanced/02_unsafe/05_quiz_unsafe.md) | 15 |
| 宏（Macro）系统 | [10_quiz_macros.md](../../../concept/03_advanced/03_proc_macros/10_quiz_macros.md) | 15 |

### L4 形式化层（04_formal）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 形式化方法概念 | [06_quiz_formal_methods.md](../../../concept/04_formal/04_model_checking/06_quiz_formal_methods.md) | 15 |

### L5 对比层（05_comparative）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Rust vs 系统编程语言 | [02_quiz_rust_vs_systems.md](../../../concept/05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md) | 15 |

### L6 生态层（06_ecosystem）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Rust 工具链 | [06_quiz_toolchain.md](../../../concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md) | 15 |
| 网络与异步生态 | [01_quiz_networking_async_ecosystem.md](../../../concept/06_ecosystem/13_quizzes/01_quiz_networking_async_ecosystem.md) | 15 |
| 数据库与存储生态 | [02_quiz_database_storage.md](../../../concept/06_ecosystem/13_quizzes/02_quiz_database_storage.md) | 15 |
| 安全与测试生态 | [03_quiz_security_testing.md](../../../concept/06_ecosystem/13_quizzes/03_quiz_security_testing.md) | 15 |
| 领域应用生态 | [04_quiz_domain_applications.md](../../../concept/06_ecosystem/13_quizzes/04_quiz_domain_applications.md) | 15 |

### L7 前沿层（07_future）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 版本演进、Edition 机制与前沿特性 | [01_quiz_version_and_preview.md](../../../concept/07_future/05_quizzes/01_quiz_version_and_preview.md) | 15 |

> **覆盖状态（2026-07-13）**：L0–L7 各层均有独立 quiz；06 层按子领域 5 个（工具链/网络/数据库/安全测试/领域应用）。全部 quiz 按四级题型规范组织（代码阅读 + 单选/多选/判断），逐题难度标注（🟢/🟡/🔴），quiz↔concept 双向链接 21/21。规划见 `.kimi/RUST197_ALIGNMENT_AND_PEDAGOGY_PLAN_2026_07_12.md`（W3）。

## 使用方式 {#使用方式}

1. 先阅读对应的概念文件
2. 独立思考测验题目
3. 点击 `<details>` 展开核对答案与解析
4. 完成对应练习 crate 的编程挑战
