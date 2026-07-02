# Rust 发布流程（Rust Release Process）

> **EN**: Rust Release Process
> **Summary**: Rust 的版本发布模型：稳定版、Beta 版、Nightly 版的六周发布周期，以及 Rust 是如何构建和发布的。
>
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md) · [Editions](32_editions.md)
> **后置概念**: [Nightly Rust](../07_future/50_nightly_rust.md) · [Rust 1.96 Stabilized](../07_future/rust_1_96_stabilized.md) · [Rust 1.97 Preview](../07_future/rust_1_97_preview.md)
> **定理链**: Nightly → Beta → Stable → Release Channel
>
> **来源**: [The Rust Programming Language — Appendix G: How Rust is Made and Nightly Rust](https://doc.rust-lang.org/book/appendix-06-nightly-rust.html)

---

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

> **权威来源**: [TRPL — Appendix G](https://doc.rust-lang.org/book/appendix-06-nightly-rust.html) · [Rust Forge — Release Process](https://forge.rust-lang.org/release/release-process.html)
> **内容分级**: [参考级]
