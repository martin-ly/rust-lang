# 并行前端编译指南

> **层级**: L6 生态工具
> **前置概念**: [Cargo](../concept/06_ecosystem/01_toolchain.md) · [Build Systems](../concept/07_future/)
> **Bloom 层级**: 应用
> **[来源: Rust Compiler Team]** · **[来源: rustc_parallel_frontend 跟踪 Issue]** ✅

---

## 概述

Rust 编译器的**前端**（词法分析、语法分析、HIR 生成、类型检查）传统上是单线程的。对于大型 crate，前端可能占编译时间的 30–60%。

**并行前端**（Parallel Frontend）项目通过 `-Z threads=N` 将前端阶段并行化，显著缩短编译时间。

---

## 核心机制

```text
编译阶段时间分布（典型大型 crate）:
┌────────────────────────────────────────────────────────┐
│ 解析 (Parsing)          ████████░░░░░░░░░░░░  15%     │
│ 宏扩展 (Expansion)      ██████████░░░░░░░░░░  20%     │
│ HIR 生成               ████░░░░░░░░░░░░░░░░░   8%     │
│ 类型检查 (Type Check)   ████████████████░░░░  35%     │  ← 并行化重点
│ MIR 生成               ███░░░░░░░░░░░░░░░░░   5%     │
│ LLVM 后端              ████████████░░░░░░░░  25%     │  ← 已通过 codegen-units 并行
└────────────────────────────────────────────────────────┘

并行前端加速范围:
  · 类型检查中的独立函数可并行处理
  · 独立模块的 HIR 生成可并行
  · 宏扩展中的独立项可并行
```

---

## 使用方法

### 当前状态（nightly）

```bash
# 使用 nightly Rust + 并行前端
RUSTFLAGS="-Z threads=8" cargo +nightly build

# 或在 .cargo/config.toml 中配置
[build]
rustflags = ["-Z", "threads=8"]

# 推荐：根据 CPU 核心数动态设置
# macOS/Linux
export RUSTFLAGS="-Z threads=$(nproc)"
# Windows PowerShell
$env:RUSTFLAGS = "-Z threads=$env:NUMBER_OF_PROCESSORS"
```

### 性能预期

| 项目规模 | 单线程前端 | 8 线程前端 | 加速比 |
|:---|:---:|:---:|:---:|
| 小型 crate (<1K LOC) | 2s | 2s | 1.0x |
| 中型 crate (10K LOC) | 15s | 8s | 1.9x |
| 大型 crate (100K LOC) | 120s | 45s | 2.7x |
| 超大型 workspace | 600s | 200s | 3.0x |

> **[来源: Rust Compiler Team Benchmarks]** — 实际加速比取决于代码结构（并行化可分割度）

---

## 配置优化矩阵

| 场景 | 推荐配置 | 说明 |
|:---|:---|:---|
| CI/CD | `-Z threads=4` + `codegen-units=16` | 平衡速度和内存 |
| 本地开发 | `-Z threads=$(nproc)` | 最大速度 |
| 内存受限 | `-Z threads=2` | 减少并行内存峰值 |
| 确定性构建 | 不使用（或固定线程数） | 避免非确定性错误消息排序 |

---

## 与现有优化的协同

```toml
# Cargo.toml
[profile.dev]
codegen-units = 256          # 后端并行（已稳定）
incremental = true           # 增量编译（已稳定）

# 未来: 前端并行（ nightly ）
# RUSTFLAGS="-Z threads=8"

[profile.release]
codegen-units = 1            # 发布版减少 codegen-units 以优化
lto = "fat"                  # 链接时优化
```

---

## 限制与已知问题

| 问题 | 状态 | 缓解 |
|:---|:---:|:---|
| 错误消息顺序非确定 | 🟡 已知 | 使用 `--error-format=json` |
| 内存使用增加 | 🟡 预期 | 减少线程数 |
| 某些 crate 编译失败 | 🟡 修复中 | 回退单线程 |
| 仅 nightly | 🔴 待稳定 | 跟踪 rust#107374 |

---

## 跟踪状态

- **跟踪 Issue**: rust#107374 (Parallel Frontend)
- **Rust Project Goals 2026**: 计划 2026–2027 稳定化
- **当前阶段**: Nightly 可用，广泛测试阶段

---

> **权威来源**: [Rust Compiler Team](https://github.com/rust-lang/compiler-team), [rustc_parallel_frontend](https://github.com/rust-lang/rust/issues/107374)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.95.0+ Nightly
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
