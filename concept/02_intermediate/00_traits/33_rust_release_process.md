# Rust 发布流程（Rust Release Process）

> **EN**: Rust Release Process
> **Summary**: Rust 的版本发布模型：稳定版、Beta 版、Nightly 版的六周发布周期，以及 Rust 是如何构建和发布的。
>
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) · [Editions](32_editions.md)
> **后置概念**: [Nightly Rust](../../07_future/00_version_tracking/50_nightly_rust.md) · [Rust 1.96 Stabilized](../../07_future/00_version_tracking/rust_1_96_stabilized.md) · [Rust 1.97.0 Preview (Beta)](../../07_future/00_version_tracking/rust_1_97_preview.md)
> **定理链**: Nightly → Beta → Stable → Release Channel
>
> **来源**: [The Rust Programming Language — Appendix G: How Rust is Made and Nightly Rust](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) · [Rust Async Working Group — Async Foundations](https://rust-lang.github.io/async-fundamentals-initiative/) · [without.boats — Futures and Async](https://without.boats/blog/) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [MIT 6.824 — Distributed Systems](https://pdos.csail.mit.edu/6.824/) · [Rust Reference — Editions](https://doc.rust-lang.org/edition-guide/index.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)

---

---

## 认知路径

> **认知路径**: 本节从 "Rust 发布流程（Rust Release Process" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 发布流程（Rust Release Process 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Rust 发布流程（Rust Release Process 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Rust 发布流程（Rust Release Process的适用边界。
5. **迁移应用**: 将 Rust 发布流程（Rust Release Process 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust 发布流程（Rust Release Process 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Rust 发布流程（Rust Release Process 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Rust 发布流程（Rust Release Process 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Rust 发布流程（Rust Release Process 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Rust 发布流程（Rust Release Process 具有语言特有的形态。

## 一、发布频道

Rust 使用三个发布频道：

| 频道 | 更新频率 | 用途 |
|:---|:---|:---|
| Nightly | 每天 | 最新特性，可能不稳定 |
| Beta | 六周一次 | 下一稳定版的预览 |
| Stable | 六周一次 | 生产环境使用的稳定版本 |

## 二、六周发布周期

1. Nightly 持续集成新特性。
2. 每六周从 Nightly 分支出一个 Beta 版本。
3. Beta 期间只接受关键 bug 修复，不合并新特性。
4. 六周后 Beta 提升为 Stable。
5. 新的 Nightly 再开始下一个周期。

## 三、版本号规则

Rust 版本号遵循 SemVer：

```text
MAJOR.MINOR.PATCH
```

- `MAJOR` 目前始终为 1。
- `MINOR` 每六周递增。
- `PATCH` 用于稳定版紧急修复。

## 四、安装与切换频道

```bash
rustup toolchain install nightly
rustup default stable
rustup run nightly cargo build
```

## 五、特性门控与稳定化

不稳定特性需要：

```rust
#![feature(feature_name)]
```

特性需经过设计、实现、测试、FCP（Final Comment Period）后方可稳定化并进入 Stable。

---

> **权威来源**: [TRPL — Appendix G](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) · [Rust Forge — Release Process](https://forge.rust-lang.org/release/process.html)
> **内容分级**: [参考级]
