# Rust 发布流程（Rust Release Process）

> **EN**: Rust Release Process
> **Summary**: The Rust release model: stable, beta, and nightly channels, the six-week release train, SemVer version numbering, feature gates and stabilization, plus how to use rustup to switch channels.
>
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **L1 基础入口**: [版本与工具链基础](../../01_foundation/00_start/37_operators_and_symbols.md)
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) · [Editions](32_editions.md)
> **后置概念**: [Nightly Rust](../../07_future/00_version_tracking/50_nightly_rust.md) · [Rust 1.96 Stabilized](../../07_future/00_version_tracking/rust_1_96_stabilized.md) · [Rust 1.97.0 Preview (Beta)](../../07_future/00_version_tracking/rust_1_97_preview.md)
> **定理链**: Nightly → Beta → Stable → Release Channel
>
> **来源**: [The Rust Programming Language — Appendix G: How Rust is Made and Nightly Rust](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) · [Rust Forge — Release Process](https://forge.rust-lang.org/release/process.html)

---

## 一、发布频道

Rust 使用三个发布频道，构成"发布火车"（release train）模型：(Source: [TRPL — Appendix G](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html))

| 频道 | 更新频率 | 用途 | 风险 |
|:---|:---|:---|:---|
| **Nightly** | 每天 | 最新特性、实验性 API | 可能不稳定，API 可能变更 |
| **Beta** | 六周一次 | 下一稳定版的预览 | 仅接受关键修复，较稳定 |
| **Stable** | 六周一次 | 生产环境使用 | 经充分测试，保证向后兼容 |

## 二、六周发布周期

```mermaid
flowchart LR
    N1[Nightly<br/>Day 0] --> N2[Nightly<br/>持续集成]
    N2 --> B[Beta 分支<br/>第 6 周]
    B --> S[Stable 发布<br/>第 12 周]
    S --> N3[下一周期 Nightly]
```

周期流程：

1. **Nightly 持续集成**：每天从 `master` 构建，包含最新合并的 PR。
2. **Beta 分支**：每六周从当前 Nightly 切出 `beta` 分支，生成下一个稳定版候选。
3. **Beta 冻结**：Beta 期间只接受关键 bug 修复、文档修正和安全补丁，不再合并新特性。
4. **Stable 提升**：六周后 Beta 提升为 Stable，并发布新版本。
5. **循环**：新的 Nightly 继续下一个六周周期。

## 三、版本号规则

Rust 版本号遵循 [Semantic Versioning](https://semver.org/)：(Source: [Rust Forge — Release Process](https://forge.rust-lang.org/release/process.html))

```text
MAJOR.MINOR.PATCH
```

- `MAJOR` 目前始终为 `1`，用于标识 Rust 1.x 时代。
- `MINOR` 每六周递增一次，带来新稳定特性。
- `PATCH` 用于稳定版紧急修复，如安全补丁或严重回归修复。

示例：

```text
1.96.0   # 常规六周稳定版
1.96.1   # 补丁修复
1.97.0   # 下一个稳定版
```

## 四、安装与切换频道

使用 `rustup` 管理工具链：

```bash
# 安装不同频道
rustup toolchain install stable
rustup toolchain install beta
rustup toolchain install nightly

# 设置默认频道
rustup default stable

# 临时使用某频道运行
rustup run nightly cargo build

# 使用 +channel 语法
cargo +nightly build
```

项目可通过 `rust-toolchain.toml` 固定频道：

```toml
[toolchain]
channel = "stable"
```

## 五、特性门控与稳定化

不稳定特性必须通过 nightly 编译器显式开启：

```rust
#![feature(feature_name)]
```

特性稳定化流程：

1. **RFC 设计**：复杂特性需先通过 RFC 流程获得社区共识。
2. **Nightly 实现**：在 nightly 中实现并收集实际使用反馈。
3. **稳定性测试**：通过 crater 运行、性能回归测试、文档补全。
4. **Final Comment Period (FCP)**：核心团队发起最终评议期。
5. **稳定化合并**：合并 `stabilization PR`，在下一 Beta/Stable 中可用。

## 六、Editions 与稳定版的关系

- **Edition**（如 2015/2018/2021/2024）是编译器可用的大型兼容性边界，不是单一版本。
- 每个稳定版都支持多个 Edition，使用 `--edition 2024` 即可启用新语法/行为。
- Edition 迁移通常通过 `cargo fix --edition` 自动完成。

## 七、实践建议

| 场景 | 推荐频道 |
|:---|:---|
| 生产环境 | `stable` |
| 验证下一版本兼容性 | `beta` |
| 尝试 nightly 新特性 | 独立分支/CI 中使用 `nightly` |
| 提交 bug 复现 | 优先使用最新 `stable` 或 `nightly` |

---

## 认知路径

1. **问题识别**：为什么 Rust 选择固定周期而非不定发布？—— 可预测性让生态和用户能提前规划迁移。
2. **概念建立**：理解 Nightly/Beta/Stable 三层模型及版本号规则。
3. **机制推理**：从 `master` 分支到 Beta 分支再到 Stable 发布，理解特性门控与稳定化门槛。
4. **边界辨析**：Editions 与版本号的区别；哪些特性需要 nightly、哪些已在 stable。
5. **迁移应用**：使用 rustup 在工作流中切换频道、固定项目工具链、验证 beta 兼容性。

### 定理链

- **T-RP-1 火车单调性**：每个稳定版只包含前六周 Beta 中已冻结的代码，不会引入 Beta 分支后的新特性。
- **T-RP-2 频道隔离性**：Nightly 与 Stable 使用不同的工具链目录，互不干扰。
- **T-RP-3 补丁保守性**：`PATCH` 版本仅修复严重问题，不改变公开 API 语义。

### 反命题

- ❌ "Stable 每周都有新特性" → Stable 严格六周一版，期间只有可能的 PATCH 修复。
- ❌ "Nightly 可以直接用于生产" → Nightly 可能包含回归和未稳定 API，仅适合实验和 CI 探测。
- ❌ " Edition 升级会强制破坏旧代码" → 同一编译器版本仍支持旧 Edition，迁移工具 `cargo fix` 可自动化。

---

> **权威来源**: [TRPL — Appendix G](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) · [Rust Forge — Release Process](https://forge.rust-lang.org/release/process.html)
> **内容分级**: [参考级]

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Hoare: Communicating Sequential Processes (CACM 1978)](https://dl.acm.org/doi/10.1145/359576.359585)
- **P2 生态/社区**: [docs.rs/sysinfo — 生态权威 API 文档](https://docs.rs/sysinfo) · [docs.rs/num_cpus — 生态权威 API 文档](https://docs.rs/num_cpus)
