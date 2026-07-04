# 常用开发工具（Useful Development Tools）

> **EN**: Useful Development Tools
> **Summary**: Rust 生态中常用的官方与社区开发工具：rustfmt、clippy、rustdoc、cargo、rust-analyzer，以及它们在开发流程中的定位。 Official and community development tools in the Rust ecosystem: rustfmt, clippy, rustdoc, cargo, and rust-analyzer.
>
> **受众**: [初学者]
> **内容分级**: [参考级]
> **Bloom 层级**: 记忆 → 理解
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **前置依赖**: [Toolchain](../../06_ecosystem/01_toolchain.md) · [Cargo Getting Started](../../06_ecosystem/80_cargo_getting_started.md)
> **后置概念**: [Testing Basics](16_testing_basics.md) · [Documentation](../../06_ecosystem/14_documentation.md) · [DevOps and CI/CD](../../06_ecosystem/28_devops_and_ci_cd.md)
> **定理链**: Source Code → Formatter → Linter → Tester → Documenter
>
> **来源**: [The Rust Programming Language — Appendix D: Useful Development Tools](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

---

## 认知路径

> **认知路径**: 本节从 "常用开发工具（Useful Development Tool" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 常用开发工具（Useful Development Tool 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 常用开发工具（Useful Development Tool 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与常用开发工具（Useful Development Tool的适用边界。
5. **迁移应用**: 将 常用开发工具（Useful Development Tool 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "常用开发工具（Useful Development Tool 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 常用开发工具（Useful Development Tool 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 常用开发工具（Useful Development Tool 规则被违反的直接信号。

> **反命题 3**: "其他语言对 常用开发工具（Useful Development Tool 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 常用开发工具（Useful Development Tool 具有语言特有的形态。

## 一、官方工具链

| 工具 | 作用 | 常用命令 |
|:---|:---|:---|
| `rustfmt` | 自动格式化代码 | `cargo fmt` |
| `clippy` | 静态分析与 lint | `cargo clippy` |
| `rustdoc` | 生成文档 | `cargo doc` |
| `cargo` | 构建、测试、依赖管理 | `cargo build`, `cargo test` |
| `rustc` | Rust 编译器 | `rustc main.rs` |

## 二、IDE 与编辑器支持

**rust-analyzer** 是官方推荐的 Rust 语言服务器，提供：

- 自动补全
- 跳转定义
- 类型提示
- 内联错误诊断
- 重构辅助

主流编辑器（VS Code、Vim/Neovim、Emacs、IntelliJ Rust）均支持 rust-analyzer。

## 三、开发工作流中的位置

```mermaid
graph LR
    A[编写代码] --> B[cargo fmt]
    B --> C[cargo clippy]
    C --> D[cargo check]
    D --> E[cargo test]
    E --> F[cargo doc]
```

## 四、与 CI 的集成

典型 CI 流水线会固定使用这些工具：

```bash
cargo fmt --check
cargo clippy -- -D warnings
cargo test
cargo doc --no-deps
```

---

> **权威来源**: [TRPL — Appendix D](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html) · [Rust Analyzer Manual](https://rust-analyzer.github.io/manual.html)
> **内容分级**: [参考级]
