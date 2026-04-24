# Rust 编程练习体系

> **最后更新**: 2026-04-24
> **版本**: 阶段六 — 练习体系与权威认证对接
> **状态**: 30 道练习题已上线（目标 100+）

---

## 练习体系概览

本练习体系对接多个权威学习资源：

| 来源 | 内容 | 对接方式 |
| :--- | :--- | :--- |
| **Exercism** | 100+ 练习题 | 按主题分类映射，逐步扩展 |
| **Rustlings** | 交互式编译修复 | `rustlings_style/` 目录 |
| **LFRS 认证** | Linux Foundation 认证 | `docs/01_learning/LFRS_CERTIFICATION_MAPPING.md` |
| **Google Rust** | 4天综合课程 | `docs/01_learning/GOOGLE_RUST_MAPPING.md` |
| **Microsoft Guidelines** |  pragmatic 指南 | `docs/05_guides/PRAGMATIC_GUIDELINES_CHECKLIST.md` |

---

## 目录结构

```
exercises/
├── Cargo.toml                    # 练习库 crate 配置
├── src/
│   ├── lib.rs                    # 练习库入口
│   ├── ownership_borrowing/      # 所有权与借用（5/10 道）
│   ├── type_system/              # 类型系统（5/10 道）
│   ├── generics_traits/          # 泛型与特质（5/10 道）
│   ├── concurrency/              # 并发编程（5/10 道）
│   ├── async_programming/        # 异步编程（5/10 道）
│   ├── error_handling/           # 错误处理（3/5 道）
│   ├── macros/                   # 宏系统（2/5 道）
│   └── unsafe_rust/              # Unsafe Rust（0/5 道，预留）
├── docs/
│   └── <topic>/                  # 每道题的 README.md + hint.md
├── tests/                        # 集成测试（预留）
└── rustlings_style/              # 编译修复练习题（10 道）
```

---

## 快速开始

### 运行所有练习测试

```bash
cargo test -p exercises
```

### 按主题运行测试

```bash
# 所有权与借用
cargo test -p exercises ownership_borrowing::

# 异步编程
cargo test -p exercises async_programming::

# 错误处理
cargo test -p exercises error_handling::
```

### 运行单道练习的测试

```bash
cargo test -p exercises ownership_borrowing::ex01_borrow_checker_fix
```

### 自动化评测

使用提供的脚本生成完整报告：

```bash
# PowerShell (Windows)
.\scripts\exercise-check.ps1
.\scripts\exercise-check.ps1 -Topic concurrency

# Bash (Linux/macOS/Git Bash)
./scripts/exercise-check.sh
./scripts/exercise-check.sh --topic concurrency
```

---

## 练习题清单

### 所有权与借用 (5/10)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | borrow_checker_fix | Easy | ✅ |
| ex02 | string_slice | Easy | ✅ |
| ex03 | mutable_borrow | Easy | ✅ |
| ex04 | lifetime_basic | Medium | ✅ |
| ex05 | smart_pointer_rc | Medium | ✅ |

### 类型系统 (5/10)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | enum_pattern_match | Easy | ✅ |
| ex02 | struct_methods | Easy | ✅ |
| ex03 | type_conversion | Easy | ✅ |
| ex04 | generics_intro | Medium | ✅ |
| ex05 | trait_object | Medium | ✅ |

### 泛型与特质 (5/10)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | trait_bounds | Easy | ✅ |
| ex02 | associated_types | Medium | ✅ |
| ex03 | operator_overload | Medium | ✅ |
| ex04 | default_trait | Easy | ✅ |
| ex05 | trait_composition | Hard | ✅ |

### 并发编程 (5/10)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | thread_spawn | Easy | ✅ |
| ex02 | mutex_counter | Medium | ✅ |
| ex03 | channel_mpsc | Easy | ✅ |
| ex04 | rwlock_shared | Medium | ✅ |
| ex05 | arc_atomic | Medium | ✅ |

### 异步编程 (5/10)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | basic_async | Easy | ✅ |
| ex02 | future_combinator | Medium | ✅ |
| ex03 | tokio_task | Medium | ✅ |
| ex04 | async_channel | Medium | ✅ |
| ex05 | timeout_retry | Hard | ✅ |

### 错误处理 (3/5)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | result_option | Easy | ✅ |
| ex02 | custom_error | Medium | ✅ |
| ex03 | error_propagation | Medium | ✅ |

### 宏系统 (2/5)

| 编号 | 题目 | 难度 | 状态 |
| :--- | :--- | :--- | :--- |
| ex01 | declarative_macro | Medium | ✅ |
| ex02 | derive_macro_stub | Hard | ✅ |

---

## Rustlings 风格编译修复练习

位于 `exercises/rustlings_style/`，共 10 道。

使用方法：

```bash
cd exercises/rustlings_style/ex01_borrow_fix
cargo check    # 观察编译错误
# 修复 src/lib.rs
cargo test     # 验证修复
```

| 编号 | 题目 | 考点 | 难度 |
| :--- | :--- | :--- | :--- |
| ex01 | borrow_fix | 借用检查器基本规则 | Easy |
| ex02 | mutable_borrow | 可变引用排他性 | Easy |
| ex03 | lifetime_elision | 生命周期省略与显式标注 | Easy |
| ex04 | string_ownership | String 与 &str 所有权 | Medium |
| ex05 | struct_lifetime | 结构体中的生命周期 | Medium |
| ex06 | trait_bound_fix | 特质约束缺失 | Easy |
| ex07 | generic_type_fix | 泛型参数使用错误 | Easy |
| ex08 | closure_capture | 闭包捕获方式 | Medium |
| ex09 | iterator_consumer | 迭代器消费规则 | Medium |
| ex10 | match_exhaustive | match 穷尽性检查 | Easy |

---

## 学习路径建议

### 路径 A：零基础入门

1. 完成 `rustlings_style/ex01`–`ex03`（编译修复基础）
2. 完成 `ownership_borrowing/ex01`–`ex03`
3. 完成 `type_system/ex01`–`ex03`
4. 完成 `error_handling/ex01`
5. 对照 `docs/01_learning/LFRS_CERTIFICATION_MAPPING.md` 查漏补缺

### 路径 B：有经验者进阶

1. 直接运行 `cargo test -p exercises` 查看当前掌握度
2. 重点攻克标注为 Hard 的练习
3. 阅读 `docs/05_guides/PRAGMATIC_GUIDELINES_CHECKLIST.md`
4. 对照 `docs/01_learning/GOOGLE_RUST_MAPPING.md` 扩展知识面

### 路径 C：认证备考

1. 打开 `docs/01_learning/LFRS_CERTIFICATION_MAPPING.md`
2. 按 10 大考点顺序完成对应练习
3. 确保每个考点的测试全部通过
4. 使用 `scripts/exercise-check.ps1` 生成最终报告

---

## 贡献新练习

新增练习题请遵循以下规范：

1. 代码文件: `exercises/src/<topic>/exNN_name.rs`
2. 文档文件: `exercises/docs/<topic>/exNN_name.md`
3. 提示文件: `exercises/docs/<topic>/exNN_name_hint.md`
4. 在 `exercises/src/<topic>/mod.rs` 中注册模块
5. 难度分级: Easy / Medium / Hard
6. 所有文档和注释使用中文
7. 确保 `cargo check -p exercises` 通过

---

## 相关文档

- [LFRS_CERTIFICATION_MAPPING.md](../docs/01_learning/LFRS_CERTIFICATION_MAPPING.md)
- [GOOGLE_RUST_MAPPING.md](../docs/01_learning/GOOGLE_RUST_MAPPING.md)
- [PRAGMATIC_GUIDELINES_CHECKLIST.md](../docs/05_guides/PRAGMATIC_GUIDELINES_CHECKLIST.md)
- [RUSTLINGS_MAPPING.md](./RUSTLINGS_MAPPING.md)
