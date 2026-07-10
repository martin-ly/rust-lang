# Rust 1.97.0 内容对称差分析报告

**日期**: 2026-07-11
**分析范围**: 项目 `concept/07_future/00_version_tracking/rust_1_97_stabilized.md`、`crates/*/src/rust_197_features.rs` 与权威来源对比
**权威来源**:

- [Rust 1.97.0 Release Blog](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/)
- [releases.rs 1.97.0](https://releases.rs/docs/1.97.0/)
- [Rust Standard Library Docs](https://doc.rust-lang.org/std/)
- [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)

---

## 1. 执行摘要

项目对 Rust 1.97.0 的覆盖度较高，`rust_1_97_stabilized.md` 已列出大部分稳定特性。但存在以下关键差距：

1. **Symbol mangling v0** 与 **Linker output no longer hidden** 两个博客重点章节在项目文件中仅作为兼容性表格条目一笔带过，缺少独立深度解释。
2. **Cargo `build.warnings`** 未覆盖环境变量 `CARGO_BUILD_WARNINGS` 与 `--keep-going` 组合。
3. **NonZero 位查询方法** 的返回类型说明错误：`bit_width()` 返回 `NonZero<u32>`，不是 `u32`。
4. 多个 `rust_197_features.rs` 模块仍使用 `#[cfg(nightly)]` 分支包装已经稳定的 1.97 API，与项目 MSRV 1.97.0 的基线冲突。
5. 项目缺少对 **"fallback `{float}` to `f32`"** 语言变化的说明。

---

## 2. 权威特性清单（来源：blog + releases.rs）

| # | 特性 | 分类 | 项目状态 |
|---|------|------|----------|
| 1 | Symbol mangling v0 enabled by default | Compiler | ⚠️ 仅在兼容性表格提及 |
| 2 | Cargo `build.warnings` config | Cargo | ✅ 已覆盖，但缺少环境变量 |
| 3 | Linker output no longer hidden (`linker_messages` lint) | Compiler | ⚠️ 仅在兼容性表格提及 |
| 4 | `Default for RepeatN` | Std API | ✅ 已覆盖 |
| 5 | `Copy for ffi::FromBytesUntilNulError` | Std API | ✅ 已覆盖 |
| 6 | `Send for std::fs::File` on UEFI | Std API | ✅ 已覆盖 |
| 7 | `<{integer}>::isolate_highest_one` / `isolate_lowest_one` / `highest_one` / `lowest_one` / `bit_width` | Std API | ✅ 已覆盖 |
| 8 | `NonZero<{integer}>::isolate_highest_one` / `isolate_lowest_one` / `highest_one` / `lowest_one` / `bit_width` | Std API | ✅ 已覆盖，但返回类型说明有误 |
| 9 | `char::is_control` const stable | Std API | ✅ 已覆盖 |
| 10 | `must_use` on `Result<T, !>` / `ControlFlow<!, T>` | Language | ✅ 已覆盖 |
| 11 | `dead_code_pub_in_binary` lint | Language | ✅ 已覆盖 |
| 12 | `div32`, `lam-bh`, `lamcas`, `ld-seq-sa`, `scq` target features | Language | ✅ 已覆盖 |
| 13 | `cfg(target_has_atomic_primitive_alignment)` | Language | ✅ 已覆盖 |
| 14 | Allow trailing `self` in imports | Language | ✅ 已覆盖（示例可再增强） |
| 15 | nvptx64-nvidia-cuda baseline update | Platform | ✅ 已覆盖 |
| 16 | Cargo `resolver.lockfile-path` | Cargo | ✅ 已覆盖 |
| 17 | `cargo clean --target-dir` validation | Cargo | ✅ 已覆盖 |
| 18 | `cargo -m` shorthand | Cargo | ✅ 已覆盖 |
| 19 | `crates-io` remove `curl` dependency | Cargo | ✅ 已覆盖 |
| 20 | Rustdoc `--emit` / `--remap-path-prefix` | Rustdoc | ✅ 已覆盖 |
| 21 | `pin!` blocks deref coercions | Compatibility | ✅ 已覆盖 |
| 22 | Empty `#[export_name]` rejected | Compatibility | ✅ 已覆盖 |
| 23 | `f32: From<{float}>` future compat warning | Compatibility | ✅ 已覆盖 |
| 24 | `WSAESHUTDOWN` → `BrokenPipe` on Windows | Compatibility | ✅ 已覆盖 |
| 25 | Fallback `{float}` to `f32` in some cases | Language | ❌ 未覆盖 |
| 26 | `std::char` constants/functions deprecated | Compatibility | ✅ 已覆盖 |
| 27 | `varargs_without_pattern` lint in deps | Compatibility | ✅ 已覆盖 |
| 28 | Reject generic args to module path segments | Compatibility | ✅ 已覆盖 |
| 29 | Invalid macho `link_section` error | Compatibility | ✅ 已覆盖 |
| 30 | Certain `enum` encodings changed | Compatibility | ✅ 已覆盖 |
| 31 | Validate `#[link_name]` / `#[link(name)]` | Compatibility | ✅ 已覆盖 |

---

## 3. 对称差分析

### 3.1 权威有 → 项目弱/无（A - B）

#### 3.1.1 Symbol mangling v0 enabled by default

**权威内容**:

- 自 1.59 起可通过 `-Csymbol-mangling-version=v0` 选择
- 自 2025-11 起 nightly 默认启用
- 1.97 stable 默认启用；legacy mangling 仅能在 nightly 启用，计划移除
- 优点：泛型参数实例保留值（非仅 hash）、消除 Itanium ABI 不一致
- 影响：旧调试器/分析器可能无法 demangle、backtrace 格式可能变化

**项目现状**:

- 仅在第 7 节兼容性表格中一行："默认使用 v0 symbol mangling"
- 无独立章节、无迁移建议、无对 debugger/profiler 影响的说明

**差距等级**: 🔴 高

#### 3.1.2 Linker output no longer hidden by default

**权威内容**:

- 历史上 rustc 在链接成功时隐藏 linker stderr
- 1.97 默认启用 `linker_messages` warning lint
- 该 lint **不受 `warnings` lint group 控制**（特殊 lint）
- 常见误报已被过滤
- 临时静默方法：`[lints.rust] linker_messages = "allow"`

**项目现状**:

- 兼容性表格中："链接器输出默认警告"
- 无独立章节、未说明 "不受 `warnings` group 控制" 的关键语义

**差距等级**: 🔴 高

#### 3.1.3 Cargo `build.warnings` 的完整语义

**权威内容**:

- 替代 `RUSTFLAGS=-Dwarnings`
- 仅作用于 local packages，不影响依赖
- 支持环境变量 `CARGO_BUILD_WARNINGS=allow|warn|deny`
- 可与 `--keep-going` 组合收集全部错误/警告
- 不使 build cache 失效

**项目现状**:

- 仅给出 `.cargo/config.toml` 示例
- 未说明环境变量、local-only 语义、`--keep-going` 组合

**差距等级**: 🟡 中

#### 3.1.4 Fallback `{float}` to `f32` in some cases

**权威内容**:

- 语言层面变化：在某些情况下 `{float}` 会回退到 `f32`
- 属于 1.97 Language 变更

**项目现状**:

- 完全未覆盖

**差距等级**: 🟡 中

### 3.2 项目有 → 权威弱/或表述需谨慎（B - A）

#### 3.2.1 `crates-io` 移除 `curl` 依赖

- 项目已覆盖，权威来源也有。属正确内容。

#### 3.2.2 多个 `rust_197_features.rs` 仍使用 `#[cfg(nightly)]`

- 这些模块设计时 1.97 尚未 stable，用 `#[cfg(nightly)]` 包裹候选 API。
- 现在 1.97 已 stable 且为项目 MSRV，继续使用 `#[cfg(nightly)]` 会造成语义矛盾：stable 工具链下展示的是 "等效实现" 而非真实 API。

**差距等级**: 🔴 高（结构性问题）

### 3.3 语义偏差

#### 3.3.1 NonZero `bit_width()` 返回类型

**权威语义**:

- `NonZero<{integer}>::bit_width()` 返回 `NonZero<u32>`
- 因为输入非零，结果至少为 1

**项目原表述**:

- "`bit_width` 返回 `u32`"

**项目原示例**:

- `assert_eq!(n.bit_width(), 7);`（类型不匹配，无法编译）

**修复状态**: ✅ 已在本次分析中修复为 `assert_eq!(n.bit_width().get(), 7)` 并更正返回类型说明。

#### 3.3.2 `build.warnings` 作用域

**权威语义**:

- 仅控制 **local packages** 的警告

**项目表述**:

- "可统一控制本地包的 lint 警告级别"
- 基本正确，但可更明确 "不影响依赖"

#### 3.3.3 `must_use` 扩展

**权威语义**:

- 将 `Result<T, Uninhabited>` 与 `ControlFlow<Uninhabited, T>` 视为等价于 `T`

**项目表述**:

- 使用 `std::convert::Infallible` 作为错误类型示例
- 基本正确，但 `Uninhabited` 是更一般的术语，`!` 类型也属于 uninhabited

---

## 4. 已修复的具体错误

| 文件 | 问题 | 修复 |
|------|------|------|
| `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` | NonZero `bit_width()` 返回类型错误 | 改为 `NonZero<u32>`，示例加 `.get()` |

---

## 5. 后续计划与任务

### P0（必须立即做）

1. **重构 `rust_197_features.rs` 模块**
   - 移除/重构 `#[cfg(nightly)]` 分支，因为 1.97 API 已在 stable 可用
   - 在 `cfg(not(nightly))` 中的 "等效实现" 改为直接调用 1.97 原生 API
   - 保留 nightly-only 预览内容到 `rust_198_features.rs`
   - 受影响 crate：c01-c15, common（约 15 个文件）

2. **为 `rust_1_97_stabilized.md` 新增独立章节**
   - 2.x "Symbol mangling v0 默认启用"
   - 2.x "链接器输出默认显示 (`linker_messages` lint)"
   - 说明这两个特性的影响、迁移建议、与 CI/调试工具的交互

3. **完善 Cargo `build.warnings` 说明**
   - 补充 `CARGO_BUILD_WARNINGS` 环境变量
   - 说明仅作用于 local packages
   - 给出 CI 模板：`CARGO_BUILD_WARNINGS=deny cargo check --keep-going`

### P1（建议做）

1. **补充 `{float}` fallback 语言变更**
   - 在 Language 章节增加 2.x 节
   - 给出代码示例与迁移建议

2. **增强 import `self` 示例**
   - 给出能体现 "更多情况" 的示例（如 `use std::io::{self as io_mod};` 等）

3. **校对 `rust_1_97_stabilized.md` 代码示例可编译性**
   - 将所有 `rust,ignore` 示例改为可编译的 `rust` 代码块（如适用）
   - 运行 `rustdoc --test` 或 `cargo test --doc` 验证

### P2（长期治理）

1. **建立版本特性追踪自动化检查**
   - 在 `scripts/rust_version_tracker.py` 中增加与 releases.rs 的 diff 功能
   - 每次 Rust 新版本发布时自动生成 "内容覆盖缺口报告"

2. **引入 TRPL / Reference / Brown Book 的国际化链接**
   - 为每个 1.97 特性补充多语言权威来源链接
   - 例如：
     - TRPL 相关章节
     - Rust Reference 相关章节
     - Brown University Interactive Rust Book 对应内容

---

## 6. 批判性意见与建议

### 6.1 结构性问题

**`rust_197_features.rs` 的 nightly 分支与 MSRV 冲突**

当前项目 MSRV 已提升到 1.97.0，但源码中大量 `rust_197_features.rs` 仍把 1.97 API 放在 `#[cfg(nightly)]` 分支，stable 下使用 "1.96.1 等效实现"。这导致：

- 教学内容与工具链事实不一致
- 学生阅读源码时看到的是旧实现而非新 API
- 无法在 stable 下直接验证 1.97 新 API

**建议**: 将 `rust_197_features.rs` 重构为 "1.97 stable 特性展示"，删除过时的 nightly 包装。nightly-only 的 1.98+ 内容迁移到 `rust_198_features.rs`。

### 6.2 内容深度问题

**博客重点 vs 项目覆盖不平衡**

Rust 官方博客把 **v0 symbol mangling** 和 **linker messages** 作为 1.97 的两大 headline 特性，但项目文件仅作为兼容性条目处理。这反映出项目对 "哪些特性值得独立成节" 的判断与官方/社区关注焦点存在偏差。

**建议**: 建立 "官方博客 headline 特性必须独立成节" 的规则，确保项目与国际权威内容的重点一致。

### 6.3 代码示例可验证性

部分示例标记为 `rust,ignore`，无法通过 doctest 验证。这增加了示例错误的概率（如此次发现的 NonZero `bit_width()` 错误）。

**建议**: 版本特性摘要页中的代码示例应尽量使用可编译的 `rust` 代码块；仅对确实无法稳定编译的内容使用 `rust,ignore`。

### 6.4 权威来源对齐

项目文件顶部已有 releases.rs、Reference、TRPL、Brown Book 链接，但正文各小节缺少到这些来源的细粒度链接。

**建议**: 为每个特性补充 "See also" 链接，指向：

- std API 文档（Stabilized APIs）
- Rust Reference 相关章节（Language/Compiler 变更）
- Cargo Book / Rustdoc Book 相关章节（Cargo/Rustdoc 变更）

### 6.5 版本过渡语义

项目中有历史版本文件（`rust_196_features.rs`、`rust_1_96_stabilized.md`）与当前版本文件并存，这是好事。但需要更明确地区分：

- "当前稳定基线"（1.97.0）
- "历史特性归档"（1.96.x 及更早）

**建议**: 在 `crates/version_index.md` 和 `concept/07_future/00_version_tracking/05_rust_version_tracking.md` 中明确标注 "current stable" 与 "historical"。

---

## 7. 结论

Rust 1.97.0 的内容对齐工作已完成约 **85%**。剩余关键缺口集中在：

1. **两个 headline 特性**（v0 mangling、linker messages）的深度解释
2. **`rust_197_features.rs` 模块的 nightly 分支重构**
3. **少量语义偏差**（已修复 NonZero `bit_width`）

建议按 P0 → P1 → P2 优先级执行后续任务，确保项目内容与国际权威来源完全一致。
