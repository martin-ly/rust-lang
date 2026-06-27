> **内容分级**:
>
> [综述级]
> **本节关键术语**: Compiletest · UI Test · Package Test · Tidy · Crater · rustc-perf · Miri · `distcheck` — [完整对照表](../00_meta/terminology_glossary.md)
>
# rustc 编译器测试体系

> **EN**: Testing the Rust Compiler
> **Summary**: Explains the multi-layer testing infrastructure for rustc, including compiletest, package tests, tidy, tool tests, Crater, and performance testing.
> **受众**: [专家 / 研究者]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Inf — 编译器基础设施
> **定位**: 把“rustc 如何保证每次修改不破坏生态”讲清楚，覆盖从单元测试到全生态系统回归的多层测试策略。
> **前置概念**: [Compiler Diagnostics and UI Tests](./69_compiler_diagnostics_and_ui_tests.md) · [Rustc Bootstrap](./70_rustc_bootstrap.md)
> **后置概念**: [Compiler Infrastructure](./47_compiler_infrastructure.md)

> **来源**: [Rustc Dev Guide — Testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html)

---

> **来源**: [Rustc Dev Guide — Testing the compiler](https://rustc-dev-guide.rust-lang.org/tests/intro.html) ·
> [Rustc Dev Guide — Running tests](https://rustc-dev-guide.rust-lang.org/tests/running.html) ·
> [Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html) ·
> [Rustc Dev Guide — Ecosystem testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html#ecosystem-testing)

## 📑 目录

- [rustc 编译器测试体系](#rustc-编译器测试体系)
  - [📑 目录](#-目录)
  - [一、测试金字塔](#一测试金字塔)
  - [二、Compiletest 与测试套件](#二compiletest-与测试套件)
  - [三、Package Tests](#三package-tests)
  - [四、Tidy 与 Formatting](#四tidy-与-formatting)
    - [Tidy](#tidy)
    - [rustfmt](#rustfmt)
  - [五、工具测试与 Book 文档测试](#五工具测试与-book-文档测试)
    - [工具测试](#工具测试)
    - [Book 文档测试](#book-文档测试)
    - [Linkchecker](#linkchecker)
    - [distcheck](#distcheck)
  - [六、生态系统测试：Crater](#六生态系统测试crater)
  - [七、性能测试：rustc-perf](#七性能测试rustc-perf)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：`compiletest` 主要用于测试什么？](#测验-1compiletest-主要用于测试什么)
    - [测验 2：UI 测试的独特价值是什么？](#测验-2ui-测试的独特价值是什么)
    - [测验 3：Crater 在 Rust 生态中扮演什么角色？](#测验-3crater-在-rust-生态中扮演什么角色)
    - [测验 4：`./x test tidy` 主要检查什么？](#测验-4x-test-tidy-主要检查什么)
  - [权威来源索引](#权威来源索引)

---

## 一、测试金字塔

```text
rustc 测试体系
├── 单元/包测试（library/compiler crates）
├── 编译器功能测试（compiletest / UI / mir-opt / codegen）
├── 工具测试（cargo/clippy/rustfmt/miri）
├── 文档测试（book doctests / linkchecker）
├── 生态系统测试（Crater）
└── 性能测试（rustc-perf）
```

> [来源: Rustc Dev Guide — Testing the compiler](https://rustc-dev-guide.rust-lang.org/tests/intro.html)

---

## 二、Compiletest 与测试套件

`compiletest` 是 rustc 的主测试框架，位于 `src/tools/compiletest`。它支持多种测试模式：

| 测试目录 | 用途 |
|:---|:---|
| `tests/ui/` | UI 测试：验证诊断输出 |
| `tests/compile-fail/` | 验证编译失败的代码 |
| `tests/run-pass/` | 验证能编译并运行的代码 |
| `tests/mir-opt/` | 验证 MIR 优化前后的变化 |
| `tests/codegen/` | 验证 LLVM IR / 汇编输出 |
| `tests/assembly/` | 验证汇编输出 |
| `tests/incremental/` | 验证增量编译行为 |

运行示例：

```bash
./x test tests/ui
./x test tests/mir-opt --bless
```

> **关键洞察**: UI 测试是 rustc 测试中最具特色的部分，它把“错误信息应该长什么样”也纳入了回归保护。
>
> [来源: Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html)

---

## 三、Package Tests

标准库和编译器内部 crate 使用普通 `#[test]` 单元/集成/文档测试：

```bash
./x test library/std
./x test library/core
./x test compiler/rustc_data_structures
```

- 标准库严重依赖文档测试；
- 编译器 crate 通常禁用文档测试；
- 测试文件单独放在 `tests/` 子模块，避免修改测试时重编译整个 crate。

---

## 四、Tidy 与 Formatting

### Tidy

Tidy 是 Rust 仓库的自定义检查工具，负责：

- 行长度限制；
- 许可证头检查；
- 文件命名规范；
- 禁止某些模式。

```bash
./x test tidy
./x test tidy --bless
```

### rustfmt

```bash
./x fmt
./x fmt --check
```

---

## 五、工具测试与 Book 文档测试

### 工具测试

`src/tools/` 下的工具（cargo、clippy、rustfmt、miri 等）都会运行各自的测试套件：

```bash
./x test src/tools/cargo
./x test src/tools/clippy
./x test src/tools/miri --test-args padding
```

### Book 文档测试

官方书籍（TRPL、Rustc Dev Guide 等）中的代码示例通过 `rustdoc --test` 验证：

```bash
./x test src/doc/book
```

### Linkchecker

检查所有文档链接是否有效：

```bash
./x test linkchecker
```

### distcheck

验证源码分发 tarball 能完整解压、构建并通过测试：

```bash
./x test distcheck
```

---

## 六、生态系统测试：Crater

Crater 是 Rust 项目的生态回归测试基础设施：

- 自动下载并构建 crates.io 上的大量 crate；
- 比较两个 rustc 版本之间的编译结果差异；
- 用于评估破坏性变更的影响范围。

```bash
# 典型使用方式（需要 Crater 服务权限）
crater run start=master end=pr-branch
```

> [来源: Rustc Dev Guide — Ecosystem testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html#ecosystem-testing)

---

## 七、性能测试：rustc-perf

`rustc-perf` 是跟踪编译器性能的专用基础设施：

- 定期在标准 benchmark suite 上测量编译时间；
- 检测回归并提供可视化对比；
- 是 Rust 编译器性能优化的重要依据。

> [来源: Rustc Dev Guide — Performance testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html#performance-testing)

---

## 嵌入式测验

### 测验 1：`compiletest` 主要用于测试什么？

<details>
<summary>✅ 答案与解析</summary>

主要用于测试 rustc 本身，包括 UI 测试、编译失败测试、MIR 优化、代码生成等多种测试模式。

</details>

---

### 测验 2：UI 测试的独特价值是什么？

<details>
<summary>✅ 答案与解析</summary>

UI 测试把编译器输出的错误信息、span、建议等也纳入回归测试，保证诊断质量不下降。

</details>

---

### 测验 3：Crater 在 Rust 生态中扮演什么角色？

<details>
<summary>✅ 答案与解析</summary>

Crater 通过批量构建 crates.io 上的 crate，检测 rustc 变更对整个生态系统的影响，评估破坏性变更。

</details>

---

### 测验 4：`./x test tidy` 主要检查什么？

<details>
<summary>✅ 答案与解析</summary>

Tidy 检查代码风格规范，如行长度、许可证头、命名约定、禁止模式等，是 Rust 仓库的质量门禁之一。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rustc Dev Guide — Testing the compiler](https://rustc-dev-guide.rust-lang.org/tests/intro.html) | ✅ 一级 | 编译器测试官方文档 |
| [Rustc Dev Guide — UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html) | ✅ 一级 | UI 测试官方文档 |
| [Rustc Dev Guide — Ecosystem testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html#ecosystem-testing) | ✅ 一级 | Crater 等生态测试 |
| [Rustc Dev Guide — Performance testing](https://rustc-dev-guide.rust-lang.org/tests/intro.html#performance-testing) | ✅ 一级 | rustc-perf 性能测试 |

---

> **权威来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.0 / rustc 测试体系

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Rustc Dev Guide compiler testing 文档
