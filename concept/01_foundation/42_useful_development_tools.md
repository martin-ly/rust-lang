# 常用开发工具（Useful Development Tools）

> **EN**: Useful Development Tools
> **Summary**: Rust 生态中常用的官方与社区开发工具：rustfmt、clippy、rustdoc、cargo、rust-analyzer，以及它们在开发流程中的定位。
>
> **受众**: [初学者]
> **内容分级**: [参考级]
> **Bloom 层级**: 记忆 → 理解
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md) · [Cargo Getting Started](../06_ecosystem/80_cargo_getting_started.md)
> **后置概念**: [Testing Basics](16_testing_basics.md) · [Documentation](../06_ecosystem/14_documentation.md) · [DevOps and CI/CD](../06_ecosystem/28_devops_and_ci_cd.md)
> **定理链**: Source Code → Formatter → Linter → Tester → Documenter
>
> **来源**: [The Rust Programming Language — Appendix D: Useful Development Tools](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

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
