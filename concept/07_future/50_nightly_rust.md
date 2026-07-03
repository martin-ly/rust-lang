> **内容分级**: [研究级]
>
# Rust 的发布流程与 Nightly Rust

> **EN**: How Rust is Made and “Nightly Rust”
> **Summary**: Rust 的火车发布模型、Stability without Stagnation 原则、Nightly/Beta/Stable 三个发布通道、feature flags、rustup 通道切换以及 RFC 流程。
>
> **受众**: [初学者] / [中级]
> **Bloom 层级**: 理解
> **A/S/P 标记**: **P** — Process
> **双维定位**: P×Eco — 语言发布流程与生态演进
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md) · [Editions](44_edition_guide.md)
> **后置概念**: [Rust Version Tracking](05_rust_version_tracking.md) · [Rust 1.97 Preview (Beta)]((rust_1_97_preview.md)
> **定理链**: N/A — 流程/生态文档
> **主要来源**: [TRPL — Appendix G](https://doc.rust-lang.org/book/appendix-06-nightly-rust.html) · [Rust Forge — Release Process](https://forge.rust-lang.org/release/release-process.html) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [TRPL — Appendix G: How Rust is Made and “Nightly Rust”](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) · [Rust Release Channels](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html#choo-choo-release-channels-and-riding-the-trains)

---

## 一、Stability without Stagnation

Rust 的核心原则之一是 **“稳定而不停滞”**（Stability without Stagnation）：

- **稳定**：升级到新版本的 stable Rust 应该是无痛的，代码不会因为语言变化而意外损坏。
- **不停滞**：Rust 仍然可以持续实验和引入新特性，避免在稳定后才暴露重大设计缺陷。

实现这一平衡的关键是**发布通道**（release channels）和 **feature flags**。

---

## 二、发布通道：火车模型

Rust 采用 **火车模型**（train model）进行发布，共有三个通道：

| 通道 | 发布频率 | 用途 |
|:---|:---|:---|
| **Nightly** | 每晚 | 最新代码，包含实验性特性 |
| **Beta** | 每 6 周从 Nightly 分支 | 进入稳定前的测试期 |
| **Stable** | 每 6 周从 Beta 分支 | 正式发布，推荐生产使用 |

### 时间线示例

```text
Nightly: * - - * - - * - - * - - * - - * - * - *
                     |                         |
Beta:                * - - - - - - - - *       *
                                       |
Stable:                                *
```

- 每晚从 `main` 分支生成 Nightly。
- 每 6 周，当前 Nightly 被切出为 Beta。
- 再经过 6 周测试，Beta 成为 Stable。
- 每个 Stable 版本只被支持 6 周（即到下一个 Stable 发布时 EOL）。

> **好处**：如果某个特性错过当前发布窗口，只需等待 6 周即可进入下一个窗口，降低了赶工引入不成熟特性的压力。

---

## 三、不稳定特性与 Feature Flags

新特性在合并到 `main` 分支时，默认被 **feature flag** 保护：

```rust
#![feature(async_await)]
```

- 只有 **Nightly** 通道可以使用 `#![feature(...)]`。
- **Beta 和 Stable** 禁止使用 feature flag。
- 当特性经过充分测试并决定稳定化后，feature flag 被移除，特性随下一个 Stable 发布。

> 本书（TRPL）及本知识库主要覆盖 stable 特性；nightly-only 特性会单独标注。

---

## 四、使用 rustup 切换通道

```bash
# 安装 nightly 工具链
rustup toolchain install nightly

# 列出已安装工具链
rustup toolchain list

# 为当前项目设置 nightly
rustup override set nightly

# 恢复默认工具链
rustup override unset
```

> `rustup override` 只在当前目录生效，适合特定项目需要 nightly 的场景。

---

## 五、RFC 流程与团队

Rust 的重大变更通过 **RFC（Request for Comments）** 流程决策：

1. **提交 RFC**：社区任何人都可以撰写 RFC 提案。
2. **团队评审**：相关子团队（语言设计、编译器、文档、基础设施等）讨论并给出反馈。
3. **达成共识**：团队决定接受或拒绝 RFC。
4. **实现**：被接受的 RFC 会创建 tracking issue，由贡献者实现。
5. **进入 Nightly**：实现合入 `main`，默认由 feature flag 保护。
6. **稳定化决策**：经过 nightly 用户试用和团队评估后，决定是否移除 feature flag 并进入 stable。

---

## 六、实践建议

1. **生产环境使用 Stable**：获得最佳稳定性和长期支持预期。
2. **CI 中测试 Beta**：提前发现可能的回归问题。
3. **只在必要时使用 Nightly**：例如需要尝试前沿特性或为 Rust 贡献代码。
4. **关注 RFC 和 Release Notes**：了解即将到来的语言/工具链变化。

---

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Toolchain](../06_ecosystem/01_toolchain.md) | rustup 管理不同通道的工具链 |
| [Editions](44_edition_guide.md) | Edition 是 Rust 每 2-3 年发布的重大语法/库更新 |
| [Rust Version Tracking](05_rust_version_tracking.md) | 跟踪各版本稳定特性 |
| [Rust 1.97 Preview (Beta)]((rust_1_97_preview.md) | Stable 通道具体特性示例 |
