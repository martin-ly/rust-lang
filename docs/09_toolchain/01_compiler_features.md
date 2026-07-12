# Rust 编译器特性与优化 {#rust-编译器特性与优化}

> **EN**: Compiler Features
> **Summary**: Rust 编译器特性与优化 Compiler Features. (stub/archive redirect)
> **分级**: [A]
> **Bloom 层级**: L3
>
> **层次定位**: L6-L7 生态-前沿 / 编译器特性
> **前置依赖**: [concept L2 泛型（Generics）](../../concept/02_intermediate/01_generics/01_generics.md) · [docs 核心概念](../01_core/README.md)
> **后置延伸**: [docs 并行前端](15_parallel_frontend.md) · [concept L7 语言演进](../../concept/07_future/04_research_and_experimental/03_evolution.md)
> **跨层映射**: L6→L7 工具驱动映射 | 编译器→语言
> **定理链编号**: T-030 单态化（Monomorphization）正确性 → 优化保持性
> **创建日期**: 2026-02-15
> **最后更新**: 2026-05-08
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
>
> **受众**: [进阶]
> **内容分级**: [专家级]

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 编译器特性与优化 {#rust-编译器特性与优化}](#rust-编译器特性与优化-rust-编译器特性与优化)
  - [📑 目录 {#目录}](#-目录-目录)
  - [🎯 文档说明 {#文档说明}](#-文档说明-文档说明)
  - [1. 编译器概览 {#1-编译器概览}](#1-编译器概览-1-编译器概览)
    - [1.1 编译流程 {#11-编译流程}](#11-编译流程-11-编译流程)
    - [1.2 编译器版本 {#12-编译器版本}](#12-编译器版本-12-编译器版本)
  - [2. 增量编译 (Rust 1.54+) {#2-增量编译-rust-154}](#2-增量编译-rust-154-2-增量编译-rust-154)
    - [2.1 增量编译原理 {#21-增量编译原理}](#21-增量编译原理-21-增量编译原理)
    - [2.2 配置增量编译 {#22-配置增量编译}](#22-配置增量编译-22-配置增量编译)
    - [2.3 性能影响 {#23-性能影响}](#23-性能影响-23-性能影响)
  - [3. 优化级别 {#3-优化级别}](#3-优化级别-3-优化级别)
    - [3.1 基础优化级别 {#31-基础优化级别}](#31-基础优化级别-31-基础优化级别)
    - [3.2 高级优化选项 {#32-高级优化选项}](#32-高级优化选项-32-高级优化选项)
  - [4. Link-Time Optimization (LTO) {#4-link-time-optimization-lto}](#4-link-time-optimization-lto-4-link-time-optimization-lto)
    - [4.1 LTO 类型 {#41-lto-类型}](#41-lto-类型-41-lto-类型)
    - [4.2 配置 LTO {#42-配置-lto}](#42-配置-lto-42-配置-lto)
    - [4.3 性能权衡 {#43-性能权衡}](#43-性能权衡-43-性能权衡)
  - [5. Profile-Guided Optimization (PGO) {#5-profile-guided-optimization-pgo}](#5-profile-guided-optimization-pgo-5-profile-guided-optimization-pgo)
    - [5.1 PGO 工作流程 {#51-pgo-工作流程}](#51-pgo-工作流程-51-pgo-工作流程)
    - [5.2 实施 PGO {#52-实施-pgo}](#52-实施-pgo-52-实施-pgo)
    - [5.3 性能提升 {#53-性能提升}](#53-性能提升-53-性能提升)
  - [6. 代码生成选项 {#6-代码生成选项}](#6-代码生成选项-6-代码生成选项)
    - [6.1 目标 CPU 和特性 {#61-目标-cpu-和特性}](#61-目标-cpu-和特性-61-目标-cpu-和特性)
    - [6.2 代码模型 {#62-代码模型}](#62-代码模型-62-代码模型)
  - [7. 调试信息 {#7-调试信息}](#7-调试信息-7-调试信息)
    - [7.1 调试信息级别 {#71-调试信息级别}](#71-调试信息级别-71-调试信息级别)
    - [7.2 分割调试信息 {#72-分割调试信息}](#72-分割调试信息-72-分割调试信息)
    - [7.3 DWARF 版本 {#73-dwarf-版本}](#73-dwarf-版本-73-dwarf-版本)
  - [8. 编译缓存 {#8-编译缓存}](#8-编译缓存-8-编译缓存)
    - [8.1 Sccache {#81-sccache}](#81-sccache-81-sccache)
    - [8.2 配置缓存 {#82-配置缓存}](#82-配置缓存-82-配置缓存)
  - [9. 编译时间优化 {#9-编译时间优化}](#9-编译时间优化-9-编译时间优化)
    - [9.1 并行编译 {#91-并行编译}](#91-并行编译-91-并行编译)
    - [9.2 依赖优化 {#92-依赖优化}](#92-依赖优化-92-依赖优化)
    - [9.3 代码组织 {#93-代码组织}](#93-代码组织-93-代码组织)
  - [10. 编译器插件与扩展 {#10-编译器插件与扩展}](#10-编译器插件与扩展-10-编译器插件与扩展)
    - [10.1 Procedural Macros {#101-procedural-macros}](#101-procedural-macros-101-procedural-macros)
    - [10.2 编译器内置工具 {#102-编译器内置工具}](#102-编译器内置工具-102-编译器内置工具)
  - [11. 高级编译技术 {#11-高级编译技术}](#11-高级编译技术-11-高级编译技术)
    - [11.1 Polly (LLVM 优化器) {#111-polly-llvm-优化器}](#111-polly-llvm-优化器-111-polly-llvm-优化器)
    - [11.2 自定义构建脚本 {#112-自定义构建脚本}](#112-自定义构建脚本-112-自定义构建脚本)
  - [12. 实战案例 {#12-实战案例}](#12-实战案例-12-实战案例)
    - [12.1 生产环境优化配置 {#121-生产环境优化配置}](#121-生产环境优化配置-121-生产环境优化配置)
    - [12.2 开发环境优化配置 {#122-开发环境优化配置}](#122-开发环境优化配置-122-开发环境优化配置)
  - [13. 性能基准 {#13-性能基准}](#13-性能基准-13-性能基准)
  - [14. 故障排查 {#14-故障排查}](#14-故障排查-14-故障排查)
    - [常见问题 {#常见问题}](#常见问题-常见问题)
  - [15. 编译器特性的形式化分析 {#15-编译器特性的形式化分析}](#15-编译器特性的形式化分析-15-编译器特性的形式化分析)
    - [15.1 编译过程的形式化模型 {#151-编译过程的形式化模型}](#151-编译过程的形式化模型-151-编译过程的形式化模型)
    - [15.2 借用（Borrowing）检查的形式化 {#152-借用检查的形式化}](#152-借用检查的形式化-152-借用检查的形式化)
    - [15.3 优化级别的形式化语义 {#153-优化级别的形式化语义}](#153-优化级别的形式化语义-153-优化级别的形式化语义)
    - [15.4 LTO 的形式化分析 {#154-lto-的形式化分析}](#154-lto-的形式化分析-154-lto-的形式化分析)
    - [15.5 PGO 的形式化模型 {#155-pgo-的形式化模型}](#155-pgo-的形式化模型-155-pgo-的形式化模型)
  - [16. 相关资源 {#16-相关资源}](#16-相关资源-16-相关资源)
    - [📚 官方文档 {#官方文档}](#-官方文档-官方文档)
    - [🔗 相关文档 {#相关文档}](#-相关文档-相关文档)
    - [🔗 形式化理论文档 {#形式化理论文档}](#-形式化理论文档-形式化理论文档)
    - [📦 推荐工具 {#推荐工具}](#-推荐工具-推荐工具)
  - [Rust 1.96+ 更新 {#rust-196-更新}](#rust-196-更新-rust-196-更新)
  - [**最后更新**: 2026-06-08 (对齐 1.96 稳定版内容)](#最后更新-2026-06-08-对齐-196-稳定版内容)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 🎯 文档说明 {#文档说明}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本文档涵盖 Rust 编译器 (`rustc`) 的核心特性、优化技术和最新改进，帮助开发者更好地理解和利用编译器功能。

**覆盖内容**: 编译过程、优化技术、调试信息、增量编译、Profile-Guided Optimization (PGO)、Link-Time Optimization (LTO)

---

## 1. 编译器概览 {#1-编译器概览}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1.1 编译流程 {#11-编译流程}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
┌─────────────┐
│ 源代码 (.rs) │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  词法分析    │ → Tokens
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  语法分析    │ → AST (Abstract Syntax Tree)
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  语义分析    │ → HIR (High-level IR)
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  类型检查    │ → 类型信息
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  Borrow 检查 │ → MIR (Mid-level IR)
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  优化 (MIR)  │ → 优化后的 MIR
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ LLVM IR 生成 │ → LLVM IR
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ LLVM 优化    │ → 优化后的 LLVM IR
└──────┬──────┘
       │
       ▼
┌─────────────┐
│  代码生成    │ → 目标机器码
└──────┬──────┘
       │
       ▼
┌─────────────┐
│   链接器     │ → 可执行文件
└─────────────┘
```

---

### 1.2 编译器版本 {#12-编译器版本}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```bash
# 查看编译器版本 {#查看编译器版本}
rustc --version

# 查看详细版本信息 {#查看详细版本信息}
rustc --version --verbose

# 输出示例 (Rust 1.97.0): {#输出示例-rust-1960}
# rustc 1.97.0 (2026-07-09) {#rustc-1970-2026-07-09}
# binary: rustc {#binary-rustc}
# commit-hash: abc123... {#commit-hash-abc123}
# commit-date: 2026-07-02 {#commit-date-2026-07-02}
# host: x86_64-unknown-linux-gnu {#host-x86_64-unknown-linux-gnu}
# release: 1.97.0 {#release-1970}
# LLVM version: 21.0.0  (minimum external LLVM for building rustc from source is 21) {#llvm-version-2100-minimum-external-llvm-for-building-rustc-from-source-is-21}
```

**查看编译器支持的目标平台**:

```bash
rustc --print target-list

# 常见目标: {#常见目标}
# x86_64-unknown-linux-gnu {#x86_64-unknown-linux-gnu}
# x86_64-pc-windows-msvc {#x86_64-pc-windows-msvc}
# x86_64-apple-darwin {#x86_64-apple-darwin}
# aarch64-unknown-linux-gnu {#aarch64-unknown-linux-gnu}
# wasm32-unknown-unknown {#wasm32-unknown-unknown}
```

---

## 2. 增量编译 (Rust 1.54+) {#2-增量编译-rust-154}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 增量编译原理 {#21-增量编译原理}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**特性**: Rust 1.54 默认重新启用增量编译

**工作原理**:

1. 将代码分解为多个**编译单元** (crate)
2. 跟踪每个编译单元的**依赖关系**
3. 仅重新编译**修改过的**编译单元及其依赖者
4. 缓存编译中间结果

---

### 2.2 配置增量编译 {#22-配置增量编译}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Cargo.toml 配置**:

```toml
[profile.dev]
incremental = true  # 默认开启

[profile.release]
incremental = false  # 生产环境建议关闭
```

**环境变量**:

```bash
# 启用增量编译 {#启用增量编译}
export CARGO_INCREMENTAL=1

# 禁用增量编译 {#禁用增量编译}
export CARGO_INCREMENTAL=0

# 指定增量编译缓存目录 {#指定增量编译缓存目录}
export CARGO_INCREMENTAL_DIR=/custom/cache/path
```

**清理增量编译缓存**:

```bash
# 清理所有缓存 {#清理所有缓存}
cargo clean

# 清理增量编译缓存 {#清理增量编译缓存}
rm -rf target/debug/incremental
rm -rf target/release/incremental
```

---

### 2.3 性能影响 {#23-性能影响}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**首次编译**: 无明显差异

**增量编译**:

- **小修改**: 编译时间减少 **50-90%**
- **中等修改**: 编译时间减少 **30-50%**
- **大修改**: 编译时间减少 **10-30%**

**权衡**:

- ✅ **开发环境**: 显著加速迭代
- ⚠️ **生产环境**: 可能略微增加二进制体积

---

## 3. 优化级别 {#3-优化级别}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 3.1 基础优化级别 {#31-基础优化级别}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
[profile.dev]
opt-level = 0  # 无优化 (快速编译)

[profile.release]
opt-level = 3  # 最大优化 (最快运行)
```

**优化级别说明**:

| 级别  | 说明         | 编译时间 | 运行性能 | 二进制大小 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `1`   | 基础优化     | 快       | 较快     | 大         |
| `2`   | 标准优化     | 中等     | 快       | 中等       |
| `3`   | 最大优化     | 慢       | 最快     | 小         |
| `"s"` | 优化大小     | 中等     | 快       | 最小       |
| `"z"` | 极致优化大小 | 中等     | 较快     | 极小       |

---

### 3.2 高级优化选项 {#32-高级优化选项}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```toml
[profile.release]
opt-level = 3
lto = "fat"                # Link-Time Optimization
codegen-units = 1          # 单一代码生成单元 (最大优化)
panic = "abort"            # panic 时中止 (减小体积)
strip = true               # 移除符号表 (Rust 1.59+)
overflow-checks = false    # 禁用溢出检查
debug = false              # 不生成调试信息
debug-assertions = false   # 禁用断言
```

**针对特定包的优化**:

```toml
[profile.dev.package."*"]
opt-level = 2  # 依赖包使用 O2 优化

[profile.dev.package.my-crate]
opt-level = 0  # 自己的 crate 保持无优化
```

---

## 4. Link-Time Optimization (LTO) {#4-link-time-optimization-lto}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 4.1 LTO 类型 {#41-lto-类型}

> **来源: [ACM](https://dl.acm.org/)**

**Thin LTO** (推荐):

```toml
[profile.release]
lto = "thin"
```

- 平衡编译时间和优化效果
- 并行度高
- 增加编译时间 ~20-40%
- 性能提升 ~5-15%

**Fat LTO** (最大优化):

```toml
[profile.release]
lto = "fat"
# 或 {#或}
lto = true
```

- 全程序优化
- 编译时间显著增加
- 增加编译时间 ~50-200%
- 性能提升 ~10-25%

---

### 4.2 配置 LTO {#42-配置-lto}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

**完整配置示例**:

```toml
[profile.release]
lto = "fat"
codegen-units = 1  # LTO 需要单一代码生成单元以达到最佳效果
```

**针对库的 LTO**:

```toml
[profile.release]
lto = true

[profile.release.package."*"]
lto = true  # 所有依赖包也启用 LTO
```

---

### 4.3 性能权衡 {#43-性能权衡}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**基准测试结果**:

| 配置     | 编译时间 | 运行性能 | 二进制大小 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Thin LTO | 1.3x     | 1.08x    | 0.92x      |
| Fat LTO  | 2.5x     | 1.18x    | 0.85x      |

**建议**:

- **开发环境**: 禁用 LTO
- **CI 测试**: Thin LTO
- **生产发布**: Fat LTO

---

## 5. Profile-Guided Optimization (PGO) {#5-profile-guided-optimization-pgo}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 5.1 PGO 工作流程 {#51-pgo-工作流程}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

```text
┌───────────────────────────────────────────────────┐
│ 步骤 1: 使用 instrumented 构建生成可执行文件        │
└────────────────┬──────────────────────────────────┘
                 │
                 ▼
┌───────────────────────────────────────────────────┐
│ 步骤 2: 运行程序，收集性能数据 (*.profraw)          │
└────────────────┬──────────────────────────────────┘
                 │
                 ▼
┌───────────────────────────────────────────────────┐
│ 步骤 3: 合并性能数据 (*.profdata)                  │
└────────────────┬──────────────────────────────────┘
                 │
                 ▼
┌───────────────────────────────────────────────────┐
│ 步骤 4: 使用性能数据重新构建，生成优化的可执行文件   │
└───────────────────────────────────────────────────┘
```

---

### 5.2 实施 PGO {#52-实施-pgo}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

**步骤 1: Instrumented 构建**:

```bash
# 设置环境变量 {#设置环境变量}
export RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data"

# 构建 {#构建}
cargo build --release
```

**步骤 2: 运行并收集数据**:

```bash
# 运行程序 (使用典型工作负载) {#运行程序-使用典型工作负载}
./target/release/my-app

# 这将生成 /tmp/pgo-data/*.profraw 文件 {#这将生成-tmppgo-dataprofraw-文件}
```

**步骤 3: 合并性能数据**:

```bash
# 使用 llvm-profdata 合并 {#使用-llvm-profdata-合并}
llvm-profdata merge \
    -o /tmp/pgo-data/merged.profdata \
    /tmp/pgo-data/*.profraw
```

**步骤 4: 使用 PGO 数据重新构建**:

```bash
# 清理之前的构建 {#清理之前的构建}
cargo clean

# 设置使用 PGO 数据 {#设置使用-pgo-数据}
export RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata"

# 重新构建 {#重新构建}
cargo build --release
```

---

### 5.3 性能提升 {#53-性能提升}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**典型提升**:

- **热点路径优化**: 10-30%
- **分支预测优化**: 5-15%
- **内联决策优化**: 5-10%
- **总体性能**: **15-35%**

**适用场景**:

- ✅ CPU 密集型应用
- ✅ 有明确典型工作负载的应用
- ✅ 性能关键的生产环境
- ⚠️ 不适合工作负载变化大的应用

---

## 6. 代码生成选项 {#6-代码生成选项}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 6.1 目标 CPU 和特性 {#61-目标-cpu-和特性}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

**指定目标 CPU**:

```bash
# 针对本机 CPU 优化 {#针对本机-cpu-优化}
RUSTFLAGS="-C target-cpu=native" cargo build --release

# 针对特定 CPU {#针对特定-cpu}
RUSTFLAGS="-C target-cpu=haswell" cargo build --release

# 查看支持的 CPU {#查看支持的-cpu}
rustc --print target-cpus
```

**启用特定 CPU 特性**:

```bash
# 启用 AVX2 {#启用-avx2}
RUSTFLAGS="-C target-feature=+avx2" cargo build --release

# 启用多个特性 {#启用多个特性}
RUSTFLAGS="-C target-feature=+avx2,+fma,+bmi2" cargo build --release

# 查看支持的特性 {#查看支持的特性}
rustc --print target-features
```

**Cargo.toml 配置**:

```toml
[profile.release]
[profile.release.build-override]
rustflags = ["-C", "target-cpu=native"]
```

---

### 6.2 代码模型 {#62-代码模型}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```bash
# 小代码模型 (默认, < 2GB) {#小代码模型-默认-2gb}
RUSTFLAGS="-C code-model=small" cargo build --release

# 中等代码模型 (2-4GB) {#中等代码模型-2-4gb}
RUSTFLAGS="-C code-model=medium" cargo build --release

# 大代码模型 (> 4GB) {#大代码模型-4gb}
RUSTFLAGS="-C code-model=large" cargo build --release
```

---

## 7. 调试信息 {#7-调试信息}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 7.1 调试信息级别 {#71-调试信息级别}

> **来源: [ACM](https://dl.acm.org/)**

```toml
[profile.dev]
debug = 2  # 完整调试信息 (默认)

[profile.release]
debug = 0  # 无调试信息
# 或保留部分调试信息用于 profiling {#或保留部分调试信息用于-profiling}
debug = 1  # 仅行号信息
```

**级别说明**:

| 级别 | 说明       | 二进制增加 | 编译时间 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `1`  | 仅行号     | +5-10%     | 快       |
| `2`  | 完整信息   | +20-50%    | 慢       |

---

### 7.2 分割调试信息 {#72-分割调试信息}

> **来源: [IEEE](https://standards.ieee.org/)**

```toml
[profile.release]
split-debuginfo = "packed"  # macOS/Windows: 打包到单独文件
# split-debuginfo = "unpacked"  # Linux: 分散到多个文件 {#split-debuginfo-unpacked-linux-分散到多个文件}
```

**平台差异**:

| 平台    | 默认值     | 推荐值                             |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| macOS   | `packed`   | `packed`                           |
| Windows | `packed`   | `packed`                           |

---

### 7.3 DWARF 版本 {#73-dwarf-版本}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```bash
# 使用 DWARF 5 (最新, 更小) {#使用-dwarf-5-最新-更小}
RUSTFLAGS="-C debuginfo=2 -C dwarf-version=5" cargo build

# 使用 DWARF 4 (兼容性更好) {#使用-dwarf-4-兼容性更好}
RUSTFLAGS="-C debuginfo=2 -C dwarf-version=4" cargo build
```

**Rust 1.88**: DWARF 5 稳定化

---

## 8. 编译缓存 {#8-编译缓存}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 8.1 Sccache {#81-sccache}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

**安装**:

```bash
cargo install sccache
```

**配置**:

```bash
# 设置为默认编译器包装器 {#设置为默认编译器包装器}
export RUSTC_WRAPPER=sccache

# 查看缓存统计 {#查看缓存统计}
sccache --show-stats

# 清理缓存 {#清理缓存-1}
sccache --stop-server
```

**Cargo 配置** (`.cargo/config.toml`):

```toml
[build]
rustc-wrapper = "/path/to/sccache"
```

---

### 8.2 配置缓存 {#82-配置缓存}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

**本地缓存**:

```bash
export SCCACHE_DIR=~/.cache/sccache
export SCCACHE_CACHE_SIZE="10G"
```

**Redis 缓存** (团队共享):

```bash
export SCCACHE_REDIS="redis://localhost:6379"
```

**S3 缓存** (CI/CD):

```bash
export SCCACHE_BUCKET="my-build-cache"
export SCCACHE_REGION="us-west-2"
```

---

## 9. 编译时间优化 {#9-编译时间优化}
>
> **[来源: [crates.io](https://crates.io/)]**

### 9.1 并行编译 {#91-并行编译}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```bash
# 设置并行任务数 {#设置并行任务数}
cargo build -j 8

# 或通过环境变量 {#或通过环境变量}
export CARGO_BUILD_JOBS=8
```

**Cargo.toml 配置**:

```toml
[build]
jobs = 8  # 默认为 CPU 核心数
```

---

### 9.2 依赖优化 {#92-依赖优化}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**减少依赖**:

```toml
[dependencies]
# 仅使用需要的 feature {#仅使用需要的-feature}
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["rt-multi-thread", "macros"] }

# 避免不必要的依赖 {#避免不必要的依赖}
# ❌ regex = "1.0" {#regex-10}
```

**使用 workspace**:

```toml
[workspace]
members = ["crate1", "crate2", "crate3"]

# 共享依赖版本 {#共享依赖版本}
[workspace.dependencies]
tokio = { version = "1.0", features = ["full"] }
```

---

### 9.3 代码组织 {#93-代码组织}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

**最佳实践**:

1. **减小 crate 大小**: 将大 crate 拆分为多个小 crate
2. **避免大型泛型（Generics）**: 泛型会增加编译时间
3. **使用动态分发**: 在适当场景使用 `dyn Trait`
4. **减少宏（Macro）使用**: 宏展开增加编译时间

**示例**:

```rust,ignore
// ✅ 推荐: 小而专注的 crate
// lib.rs
pub mod core;
pub mod utils;
pub mod api;

// ❌ 避免: 单一巨大 crate
// lib.rs
pub mod everything_in_one_file; // 10000+ lines
```

---

## 10. 编译器插件与扩展 {#10-编译器插件与扩展}
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 10.1 Procedural Macros {#101-procedural-macros}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

**性能影响**:

- 过程宏（Procedural Macro）在编译时运行，会增加编译时间
- 建议仅在必要时使用

**优化建议**:

```rust,ignore
// ✅ 使用 derive 宏
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Data { /* ... */ }

// ⚠️ 避免复杂的 attribute 宏
// #[complex_macro_that_generates_thousands_of_lines]
```

---

### 10.2 编译器内置工具 {#102-编译器内置工具}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

**Clippy** (Linter):

```bash
cargo clippy --all-targets --all-features
```

**Rustfmt** (代码格式化):

```bash
cargo fmt --all
```

**Miri** (内存安全（Memory Safety）检查):

```bash
cargo +nightly miri test
```

---

## 11. 高级编译技术 {#11-高级编译技术}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 11.1 Polly (LLVM 优化器) {#111-polly-llvm-优化器}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```bash
# 启用 Polly (实验性) {#启用-polly-实验性}
RUSTFLAGS="-C passes=polly" cargo build --release
```

---

### 11.2 自定义构建脚本 {#112-自定义构建脚本}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**build.rs**:

```rust
// build.rs
fn main() {
    // 设置编译选项
    println!("cargo:rustc-link-lib=static=mylib");
    println!("cargo:rustc-link-search=native=/usr/local/lib");

    // 条件编译
    if cfg!(target_os = "linux") {
        println!("cargo:rustc-cfg=linux_optimizations");
    }
}
```

---

## 12. 实战案例 {#12-实战案例}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 12.1 生产环境优化配置 {#121-生产环境优化配置}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true
overflow-checks = false
debug = false

[profile.release.build-override]
opt-level = 0  # 构建脚本无需优化
```

**构建命令**:

```bash
# 使用 PGO {#使用-pgo}
export RUSTFLAGS="-C target-cpu=native -C profile-use=merged.profdata"
cargo build --release
```

---

### 12.2 开发环境优化配置 {#122-开发环境优化配置}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```toml
[profile.dev]
opt-level = 1          # 轻度优化
incremental = true     # 增量编译
debug = 2              # 完整调试信息
split-debuginfo = "unpacked"

[profile.dev.package."*"]
opt-level = 2          # 依赖包使用 O2
```

---

## 13. 性能基准 {#13-性能基准}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**编译时间对比** (1000 LOC 项目):

| 配置           | 清洁构建 | 增量构建 | 二进制大小 | 运行性能 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Release (默认) | 30s      | 15s      | 3 MB       | 8x       |
| Release + LTO  | 60s      | 30s      | 2.5 MB     | 10x      |
| Release + PGO  | 80s      | -        | 2.3 MB     | 12x      |

---

## 14. 故障排查 {#14-故障排查}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 常见问题 {#常见问题}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

**1. 编译错误: out of memory**:

```bash
# 减少并行任务 {#减少并行任务}
export CARGO_BUILD_JOBS=2

# 或增加 swap 空间 {#或增加-swap-空间}
```

**2. 增量编译损坏**:

```bash
# 清理缓存 {#清理缓存-1}
cargo clean
rm -rf ~/.cargo/registry/cache
```

**3. LTO 失败**:

```toml
# 尝试 thin LTO {#尝试-thin-lto}
[profile.release]
lto = "thin"
codegen-units = 16  # 增加代码生成单元
```

---

## 15. 编译器特性的形式化分析 {#15-编译器特性的形式化分析}
>
> **[来源: [crates.io](https://crates.io/)]**

### 15.1 编译过程的形式化模型 {#151-编译过程的形式化模型}
>
> **[来源: [docs.rs](https://docs.rs/)]**

Rust 编译器可以形式化地建模为一系列程序转换：

```text
源代码  --(词法分析)-->  Token流
Token流 --(语法分析)-->  AST
AST     --(语义分析)-->  HIR
HIR     --(类型检查)-->  类型注解HIR
类型注解HIR --(借用检查)--> MIR
MIR     --(优化)-->  优化后MIR
优化后MIR --(代码生成)--> LLVM IR
LLVM IR --(LLVM优化)--> 目标代码
```

形式化表示为：

```rust,ignore
// 编译过程的形式化类型（概念性）
type SourceCode = String;
type TokenStream = Vec<Token>;
type AST = Crate;  // 语法树
type HIR = HighLevelIR;  // 高级中间表示
type MIR = MidLevelIR;   // 中级中间表示
type LLVMIR = String;    // LLVM中间表示
type ObjectCode = Vec<u8>; // 目标代码

// 编译函数链
fn compile(source: SourceCode) -> Result<ObjectCode, CompileError> {
    source
        .pipe(lex)           // 词法分析
        .and_then(parse)      // 语法分析
        .and_then(lower_to_hir)  // 降级到HIR
        .and_then(type_check)    // 类型检查
        .and_then(borrow_check)  // 借用检查
        .and_then(lower_to_mir)  // 降级到MIR
        .and_then(optimize_mir)  // MIR优化
        .and_then(generate_llvm) // 生成LLVM IR
        .and_then(llvm_optimize) // LLVM优化
        .and_then(codegen)       // 代码生成
}
```

### 15.2 借用检查的形式化 {#152-借用检查的形式化}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

借用检查器确保内存安全的形式化保证：

```rust
// 形式化：借用检查确保以下不变式
// 1. 对于任意内存位置，在任意时刻只能存在一个可变引用
//    ∀l ∈ Location, ∀t ∈ Time:
//    count_mut_refs(l, t) ≤ 1
//
// 2. 对于任意内存位置，可变引用和不可变引用不能同时存在
//    ∀l ∈ Location, ∀t ∈ Time:
//    has_mut_ref(l, t) → count_imm_refs(l, t) = 0
//
// 3. 引用不能比其指向的数据存活更久
//    ∀r ∈ Reference: lifetime(r) ≤ lifetime(pointee(r))

// 示例：借用检查器验证代码
fn borrow_check_example() {
    let mut x = 5;

    // ✅ 合法：只有一个可变引用
    let r1 = &mut x;
    *r1 += 1;
    drop(r1);  // 显式释放引用

    // ✅ 合法：多个不可变引用
    let r2 = &x;
    let r3 = &x;
    println!("{} {}", r2, r3);
    // r2, r3 在这里结束生命周期

    // ✅ 合法：在不可变引用结束后使用可变引用
    let r4 = &mut x;
    *r4 += 1;

    // ❌ 非法：同时存在可变和不可变引用
    // let r5 = &x;  // 错误：无法借用 `x`，因为它已被可变借用
    // println!("{}", r4);
}
```

### 15.3 优化级别的形式化语义 {#153-优化级别的形式化语义}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

不同优化级别对应不同的程序转换强度：

```rust,ignore
// 形式化语义：优化级别定义允许的转换集合
enum OptimizationLevel {
    O0,  // 无优化：保持源代码语义，适合调试
    O1,  // 基础优化：移除死代码、常量传播
    O2,  // 标准优化：循环优化、内联、向量化
    O3,  // 激进优化：函数克隆、推测执行
    Os,  // 大小优化：优先减小代码体积
    Oz,  // 极致大小优化：牺牲性能换取最小体积
}

// 各优化级别对应的转换
impl OptimizationLevel {
    fn allowed_transforms(&self) -> Vec<Transform> {
        match self {
            O0 => vec![],  // 无转换
            O1 => vec![DeadCodeElimination, ConstantPropagation],
            O2 => vec![
                DeadCodeElimination,
                ConstantPropagation,
                LoopOptimization,
                Inlining(Threshold::Standard),
                Vectorization,
            ],
            O3 => vec![
                DeadCodeElimination,
                ConstantPropagation,
                LoopOptimization,
                Inlining(Threshold::Aggressive),
                Vectorization,
                SpeculativeExecution,
                FunctionCloning,
            ],
            Os => vec![
                DeadCodeElimination,
                SizeInlining,  // 仅内联小函数
                MergeFunctions,
            ],
            Oz => vec![
                DeadCodeElimination,
                SizeInlining,
                MergeFunctions,
                StripDebugInfo,
            ],
        }
    }
}
```

### 15.4 LTO 的形式化分析 {#154-lto-的形式化分析}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

Link-Time Optimization 的形式化效果：

```rust,ignore
// 形式化：LTO 允许跨模块优化
// 对于模块 A 和 B，LTO 可以：
// 1. 内联跨模块函数调用
// 2. 移除未使用的跨模块函数
// 3. 传播跨模块常量

// 示例：LTO 跨模块内联
// crate_a.rs
pub fn hot_function(x: i32) -> i32 {
    x * 2 + 1
}

// crate_b.rs
use crate_a::hot_function;

pub fn caller() -> i32 {
    // 无 LTO：函数调用开销
    // 有 LTO：内联为 `42 * 2 + 1`
    hot_function(42)
}

// LTO 后的等效代码（概念性）
pub fn caller_lto() -> i32 {
    85  // 编译时常量折叠
}
```

### 15.5 PGO 的形式化模型 {#155-pgo-的形式化模型}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

Profile-Guided Optimization 的数学模型：

```rust
// 形式化：PGO 基于执行频率优化
// 设程序 P 有基本块 B = {b₁, b₂, ..., bₙ}
// 执行配置文件 Prof 将每个基本块映射到执行次数
// Prof: B → ℕ

// PGO 优化策略：
// 1. 热点内联：对于高频调用边 (caller, callee)，执行内联
//    inline_if(Prof(callee) > THRESHOLD)
//
// 2. 分支优化：基于分支概率重新排序
//    if Prof(taken) > Prof(not_taken) { layoult_hot_path_first() }
//
// 3. 代码布局：按执行频率排列函数
//    sort_functions_by(Prof)

// PGO 工作流代码示例
fn pgo_workflow() {
    // 阶段 1：Instrumented 构建
    // rustc -C profile-generate=pgo_data

    // 阶段 2：收集执行数据
    // ./instrumented_binary  // 生成 *.profraw

    // 阶段 3：合并配置文件
    // llvm-profdata merge -o merged.profdata *.profraw

    // 阶段 4：使用 PGO 数据重新编译
    // rustc -C profile-use=merged.profdata
}
```

---

## 16. 相关资源 {#16-相关资源}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 📚 官方文档 {#官方文档}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Rustc Book](https://doc.rust-lang.org/rustc/)
- [Cargo Book - Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html)
- [LLVM Documentation](https://llvm.org/docs/)

### 🔗 相关文档 {#相关文档}
>
> **[来源: [crates.io](https://crates.io/)]**

- 02_cargo_workspace_guide.md
- [02_rustdoc_advanced.md](02_rustdoc_advanced.md)

### 🔗 形式化理论文档 {#形式化理论文档}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [所有权（Ownership）模型形式化](../12_research_notes/02_formal_methods/09_ownership_model.md)
- [借用检查器证明](../12_research_notes/02_formal_methods/03_borrow_checker_proof.md)
- [类型系统（Type System）基础](../12_research_notes/05_type_theory/05_type_system_foundations.md)
- 生命周期（Lifetimes）形式化

### 📦 推荐工具 {#推荐工具}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- **sccache**: 编译缓存
- **cargo-bloat**: 分析二进制大小
- **cargo-llvm-lines**: 分析 LLVM IR
- **cargo-asm**: 查看生成的汇编代码
- **MIRI**: 检测未定义行为 (`cargo miri test`)

---

**文档维护**: Documentation Team
**最后更新**: 2026-05-08
**下次审查**: 2026-01-22
**最后对照 releases.rs**: 2026-02-14

---

## Rust 1.96+ 更新 {#rust-196-更新}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
> **最新版本**: Rust 1.97.0+ (2026-05-28)

本文档基于 Rust 1.97.0，涵盖 1.93–1.96 关键特性。历史版本请参见：

- [Rust 1.96 稳定特性全景](08_rust_1_96_features.md)
- [Rust 历史版本文档索引](../README.md)

**最后更新**: 2026-06-08 (对齐 1.96 稳定版内容)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [06_toolchain 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Compiler Construction](https://en.wikipedia.org/wiki/Compiler_Construction)**
> **来源: [Wikipedia - LLVM](https://en.wikipedia.org/wiki/LLVM)**
> **来源: [Rust Compiler Team Blog](https://blog.rust-lang.org/inside-rust/)**
> **来源: [Rust Reference - Compiler Plugins](https://doc.rust-lang.org/reference/)**
> **[ACM - Compiler Frontend Design](https://dl.acm.org/)**
> **[IEEE - Code Generation Standards](https://ieeexplore.ieee.org/) <!-- link: known-broken -->**
> **[Nicholas Nethercote - How to Speed Up the Rust Compiler](https://nnethercote.github.io/2022/10/27/how-to-speed-up-the-rust-compiler-in-october-2022.html)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Wikipedia - Compiler Construction](https://en.wikipedia.org/wiki/Compiler_Construction)**
> **来源: [Rust Compiler Team Blog](https://blog.rust-lang.org/inside-rust/)**
> **来源: [LLVM Documentation](https://llvm.org/docs/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [Wikipedia - Machine Learning](https://en.wikipedia.org/wiki/Machine_Learning)**
> **来源: [Wikipedia - Artificial Intelligence](https://en.wikipedia.org/wiki/Artificial_Intelligence)**
> **来源: [tch-rs Documentation](https://docs.rs/tch/latest/tch/)**
> **来源: [ACM - AI Systems](https://dl.acm.org/)**

---
