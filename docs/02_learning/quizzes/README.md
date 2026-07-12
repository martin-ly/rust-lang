# 主题测验 {#主题测验}

> **EN**: Quizzes Index
> **Summary**: 主题测验 Quizzes Index — complete registry of the 15 standalone quiz files under `concept/`, grouped by L1–L6 layer.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-12
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

本目录收录 `concept/` 下全部 **15 个独立主题测验**的完整索引（共 134 道主题题；每份另含 3 道元认知题），用于验证学习理解程度。题数按 `### Q…` / `### 问题…` 主题题统计。

## 测验索引 {#测验索引}

### L1 基础层（01_foundation）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 所有权、借用与生命周期 | [33_quiz_ownership_borrowing.md](../../../concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | 10 |
| 类型系统 | [24_quiz_type_system.md](../../../concept/01_foundation/11_quizzes/24_quiz_type_system.md) | 10 |
| 错误处理 | [25_quiz_error_handling.md](../../../concept/01_foundation/11_quizzes/25_quiz_error_handling.md) | 10 |
| 模块系统与测试 | [26_quiz_modules_testing.md](../../../concept/01_foundation/11_quizzes/26_quiz_modules_testing.md) | 10 |
| 闭包与迭代器 | [27_quiz_closures_iterators.md](../../../concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md) | 10 |
| 通用 PL 基座 | [29_quiz_pl_foundations.md](../../../concept/01_foundation/11_quizzes/29_quiz_pl_foundations.md) | 6 |

### L2 中级层（02_intermediate）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Trait 与泛型 | [04_quiz_traits_and_generics.md](../../../concept/02_intermediate/01_generics/04_quiz_traits_and_generics.md) | 10 |
| 内存管理 | [05_quiz_memory_management.md](../../../concept/02_intermediate/02_memory_management/05_quiz_memory_management.md) | 10 |
| C/C++ → Rust 基础对比 | [30_quiz_cpp_rust_foundations.md](../../../concept/02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md) | 8 |

### L3 高级层（03_advanced）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 并发与异步（Async） | [08_quiz_concurrency_async.md](../../../concept/03_advanced/00_concurrency/08_quiz_concurrency_async.md) | 10 |
| Unsafe Rust | [05_quiz_unsafe.md](../../../concept/03_advanced/02_unsafe/05_quiz_unsafe.md) | 10 |
| 宏（Macro）系统 | [10_quiz_macros.md](../../../concept/03_advanced/03_proc_macros/10_quiz_macros.md) | 10 |

### L4 形式化层（04_formal）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| 形式化方法概念 | [06_quiz_formal_methods.md](../../../concept/04_formal/04_model_checking/06_quiz_formal_methods.md) | 10 |

### L5 对比层（05_comparative）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Rust vs 系统编程语言 | [02_quiz_rust_vs_systems.md](../../../concept/05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md) | 10 |

### L6 生态层（06_ecosystem）

| 主题 | 测验文件 | 题数 |
| :--- | :--- | :---: |
| Rust 工具链 | [06_quiz_toolchain.md](../../../concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md) | 10 |

> **覆盖缺口（2026-07-12 盘点）**：L0/L7 层暂无独立 quiz；06 层仅工具链 1 个（网络/异步生态/数据库/安全/测试等子领域待补）。补齐计划见 `.kimi/RUST197_ALIGNMENT_AND_PEDAGOGY_PLAN_2026_07_12.md`（W3）。

## 使用方式 {#使用方式}

1. 先阅读对应的概念文件
2. 独立思考测验题目
3. 点击 `<details>` 展开核对答案与解析
4. 完成对应练习 crate 的编程挑战
