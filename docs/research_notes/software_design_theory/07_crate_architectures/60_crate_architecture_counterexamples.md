> **Canonical 说明**: 本文件专注 **Crate 架构反例分析**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [设计模式](../../../../concept/06_ecosystem/03_design_patterns/02_patterns.md)
> - [架构模式](../../../../concept/06_ecosystem/03_design_patterns/35_architecture_patterns.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。

# Crate 架构反例边界 {#crate-架构反例边界}

> **EN**: Crate Architecture Counterexamples
> **Summary**: Crate 架构反例边界 Crate Architecture Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6
> **概念族**: Crate 架构 / 反例边界
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Crate 架构反例边界 {#crate-架构反例边界}](#crate-架构反例边界-crate-架构反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. 循环 crate 依赖 {#1-循环-crate-依赖}](#1-循环-crate-依赖-1-循环-crate-依赖)
    - [现象 {#现象-6}](#现象-现象-6)
    - [编译器错误 {#编译器错误-1}](#编译器错误-编译器错误-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. 一个 package 定义多个 lib {#2-一个-package-定义多个-lib}](#2-一个-package-定义多个-lib-2-一个-package-定义多个-lib)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [编译器错误 {#编译器错误-1}](#编译器错误-编译器错误-1-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. 公开 API 暴露内部依赖类型 {#3-公开-api-暴露内部依赖类型}](#3-公开-api-暴露内部依赖类型-3-公开-api-暴露内部依赖类型)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [问题 {#问题-3}](#问题-问题-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. 过度拆分 micro-crate {#4-过度拆分-micro-crate}](#4-过度拆分-micro-crate-4-过度拆分-micro-crate)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [问题 {#问题-3}](#问题-问题-3-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. Feature flag 组合爆炸 {#5-feature-flag-组合爆炸}](#5-feature-flag-组合爆炸-5-feature-flag-组合爆炸)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [问题 {#问题-3}](#问题-问题-3-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. Workspace 中重复依赖版本 {#6-workspace-中重复依赖版本}](#6-workspace-中重复依赖版本-6-workspace-中重复依赖版本)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [问题 {#问题-3}](#问题-问题-3-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. 忽略 SemVer 的公开 API 变更 {#7-忽略-semver-的公开-api-变更}](#7-忽略-semver-的公开-api-变更-7-忽略-semver-的公开-api-变更)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [后果 {#后果}](#后果-后果)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 1. 循环 crate 依赖 {#1-循环-crate-依赖}

### 现象 {#现象-6}

```text
crate-a/Cargo.toml -> crate-b
crate-b/Cargo.toml -> crate-c
crate-c/Cargo.toml -> crate-a
```

### 编译器错误 {#编译器错误-1}

```text
error: cyclic package dependency: package `a` depends on itself
```

### 修复方案 {#修复方案-6}

- 提取公共抽象到第四个 crate。
- 使用 trait 反转依赖方向：底层 crate 定义 trait，上层 crate 实现。

---

## 2. 一个 package 定义多个 lib {#2-一个-package-定义多个-lib}

### 现象 {#现象-6}

```toml
[lib]
name = "foo"

[[lib]]
name = "bar"
```

### 编译器错误 {#编译器错误-1}

```text
error: cannot have more than one lib target
```

### 修复方案 {#修复方案-6}

- 拆分为多个 package 或 workspace member。
- 或保留一个 lib，其余功能作为 bin / example / module。

---

## 3. 公开 API 暴露内部依赖类型 {#3-公开-api-暴露内部依赖类型}

### 现象 {#现象-6}

```rust
// crate-a/src/lib.rs
pub fn parse(input: &str) -> internal_crate::Token { ... }
```

### 问题 {#问题-3}

用户被迫依赖 `internal_crate`，升级 `internal_crate` 会破坏下游。

### 修复方案 {#修复方案-6}

- 使用 newtype 包装：`pub struct Token(internal_crate::Token)`。
- 或公开 trait 而不是具体类型。

---

## 4. 过度拆分 micro-crate {#4-过度拆分-micro-crate}

### 现象 {#现象-6}

一个 workspace 包含 50+ 个微型 crate，每个 crate 只有 1-2 个模块（Module）。

### 问题 {#问题-3}

- 构建依赖图复杂，编译缓存命中率下降。
- 版本发布和协调成本高。
- 逻辑边界不清晰。

### 修复方案 {#修复方案-6}

- 按业务领域或发布单元聚合 crate。
- 每个 crate 应有独立的发布价值和清晰的公开 API。

---

## 5. Feature flag 组合爆炸 {#5-feature-flag-组合爆炸}

### 现象 {#现象-6}

```toml
[features]
default = ["a", "b", "c"]
a = ["dep:a"]
b = ["dep:b"]
c = ["dep:c"]
d = ["a", "b", "c", "dep:d"]
```

### 问题 {#问题-3}

- feature 组合指数增长，测试覆盖困难。
- 启用/禁用 feature 可能导致 API 缺失或编译失败。

### 修复方案 {#修复方案-6}

- feature 尽量正交。
- 使用 `cargo-hack` 测试所有 feature 组合。
- 避免 feature 互相依赖形成复杂网络。

---

## 6. Workspace 中重复依赖版本 {#6-workspace-中重复依赖版本}

### 现象 {#现象-6}

```toml
# crate-a/Cargo.toml {#crate-acargotoml}
serde = "1.0.150"

# crate-b/Cargo.toml {#crate-bcargotoml}
serde = "1.0.200"
```

### 问题 {#问题-3}

- Cargo 可能同时引入两个不兼容版本，增加二进制体积。
- 类型不兼容（如 `serde::Serialize` 来自不同版本）。

### 修复方案 {#修复方案-6}

- 在 workspace root 统一 `[workspace.dependencies]`。
- 各 crate 使用 `serde = { workspace = true }`。

---

## 7. 忽略 SemVer 的公开 API 变更 {#7-忽略-semver-的公开-api-变更}

### 现象 {#现象-6}

在 patch 版本中重命名公开函数或删除公开 trait 方法。

### 后果 {#后果}

下游 crate 在 `cargo update` 后编译失败。

### 修复方案 {#修复方案-6}

- 使用 `cargo public-api` 检测 API 变化。
- 遵循 SemVer：破坏性变更升级主版本；新增功能升级次版本。
- 使用 deprecation cycle：先标记 `#[deprecated]`，下个大版本删除。

---

## 总结 {#总结}

| 反例 | 涉及概念 | 典型错误/后果 | 修复方向 |
|------|----------|---------------|----------|
| 循环 crate 依赖 | 依赖图 | 编译错误 | 提取公共 crate / trait 反转 |
| 多个 lib | package 结构 | 编译错误 | 拆分 package |
| 暴露内部类型 | API 稳定性 | SemVer 破坏 | newtype / trait |
| 过度拆分 | 架构粒度 | 构建复杂 | 按领域聚合 |
| Feature 组合爆炸 | Cargo features | 测试遗漏 | 正交 feature / cargo-hack |
| 重复依赖版本 | workspace | 体积/类型不兼容 | workspace.dependencies |
| 忽略 SemVer | 版本管理 | 下游编译失败 | cargo public-api / deprecation |

> **权威来源**: [Cargo Book – Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [Cargo Book – Features](https://doc.rust-lang.org/cargo/reference/features.html) | [Rust API Guidelines – Versioning](https://rust-lang.github.io/api-guidelines/naming.html) | [SemVer for Rust](https://doc.rust-lang.org/cargo/reference/semver.html)

## 相关概念 {#相关概念}

- [Crate 架构主索引](00_crate_architecture_master_index.md)
- [模块系统代码实践](../../formal_modules/70_module_patterns_and_refactoring.md)
- [模块系统反例](../../formal_modules/60_module_counterexamples.md)
- [知识图谱索引](../../10_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../../10_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneas-verification.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
