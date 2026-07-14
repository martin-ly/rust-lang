# Rust 1.97.0 稳定特性

> **EN**: Rust 1.97.0 Stabilized Features
> **Summary**: Rust 1.97.0 于 2026-07-09 进入 stable 通道。本文档按官方发布笔记汇总已稳定的语言、标准库、Cargo、Rustdoc 与目标平台变更。
>
> **受众**: [进阶] / [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [参考级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **Rust 版本**: **1.97.0 stable**（项目 `rust-toolchain.toml` 保持 `stable` 通道，由 rustup 自动解析为当前 latest stable 1.97.0）
> **最后更新**: 2026-07-10
> **状态**: ✅ 已对齐 Rust 1.97.0 stable
>
> **权威来源**: · [Rust 1.97.0 Release Notes](https://releases.rs/docs/1.97.0/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.96 稳定特性](rust_1_96_stabilized.md)
> **后置概念**: [Rust 1.97.0 前沿特性预览](rust_1_97_preview.md) · [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)

---

## 1. 已稳定特性概览

Rust 1.97.0 的变更集中在以下几类：

| 类别 | 代表变更 |
|:---|:---|
| **语言** | `must_use` 对 `Result<T, !>` / `ControlFlow<!, T>` 的处理；`dead_code_pub_in_binary` lint；`cfg(target_has_atomic_primitive_alignment)`；新 target feature；import 中 `self` 的放宽 |
| **标准库** | `RepeatN` 实现 `Default`；`FromBytesUntilNulError` 实现 `Copy`；整数与 `NonZero` 位查询方法；`char::is_control` 进入 const 上下文 |
| **平台** | `nvptx64-nvidia-cuda` 提升硬件基线 |
| **Cargo** | `build.warnings`、`resolver.lockfile-path`、`-m` 简写、`cargo-clean` 目标目录校验 |
| **Rustdoc** | `--emit`、`--remap-path-prefix` 稳定化 |
| **兼容性** | v0 mangling 默认、`pin!` 阻止 deref coercion、空 `export_name` 报错等 |

---

## 2. 语言与编译器

1.97 语言与编译器层的八个稳定化/变更项，按工程影响排序：

1. **`must_use` lint 扩展**：`Result<T, E>` 中 `E` 为不可居住类型（`!`）等场景的 `must_use` 判定修正，减少无意义警告；同时一批 std API 补 `#[must_use]`。
2. **`dead_code_pub_in_binary` lint**：二进制 crate 中 `pub` 项不再豁免 dead_code 检查——`pub` 不再是压警告的逃生舱，需真实删除或 `#[allow]`。
3. **新稳定 target features**：一批 x86_64 指令集特性转入 `#[target_feature]` 稳定使用。
4. **`cfg(target_has_atomic_primitive_*)`**：按原子宽度做条件编译，`no_std`/嵌入式可移植代码的利器。

其余各项（诊断改进、lint 调整）属增量打磨。

判定依据：升级 1.97 后 CI 新增警告多为 `dead_code_pub_in_binary`——批量处理脚本：先删明显死代码，剩余显式 `#[allow(dead_code)]` 并注释用途。

### 2.1 `must_use` lint 扩展至 `Result<T, Uninhabited>` 与 `ControlFlow<Uninhabited, T>`

当 `Result` 的错误类型或 `ControlFlow` 的断裂类型为不可构造类型（uninhabited）时，编译器将其等价于内部成功/继续类型 `T` 来触发 `must_use` 诊断。

```rust,ignore
#[must_use]
struct ImportantToken;

fn give_token() -> Result<ImportantToken, std::convert::Infallible> {
    Ok(ImportantToken)
}

fn main() {
    // ⚠️ Rust 1.97+ 会警告：Result<ImportantToken, _> 的 must_use 被忽略
    give_token();
}
```

### 2.2 `dead_code_pub_in_binary` lint

新增 allow-by-default lint，用于标记二进制 crate 中未被使用的 `pub` 条目。可在 CI 中显式启用：

```rust,ignore
#![warn(dead_code_pub_in_binary)]

pub fn unused_in_binary() {}

fn main() {}
```

### 2.3 新稳定 target features

以下 target feature 在 1.97.0 稳定（均为 **LoongArch** 目标特性，详见权威页 [`05_atomics_and_memory_ordering.md`](../../03_advanced/00_concurrency/05_atomics_and_memory_ordering.md) §5）：

- `div32`
- `lam-bh`
- `lamcas`
- `ld-seq-sa`
- `scq`

```rust,ignore
#[cfg(all(target_arch = "loongarch64", target_feature = "lamcas"))]
fn native_sub_word_cas() {
    // lamcas 可用：AtomicU8/AtomicU16 的 CAS 走单条原子指令
}
```

### 2.4 `cfg(target_has_atomic_primitive_alignment)`

新增条件编译标志，用于判断目标平台上原子类型的对齐是否等于其对应原始整数类型的对齐。

```rust,ignore
#[cfg(target_has_atomic_primitive_alignment = "64")]
fn assumes_atomic_align() {
    // 64 位原子类型与 u64 对齐相同的平台
}
```

### 2.5 import 中 `self` 的放宽

在更多情况下允许 import 列表中以 `self` 结尾，减少语法限制。

```rust,ignore
use std::io::{self};
use std::io::{self, Write};
```

### 2.6 `{float}` 在未约束时回退到 `f32`

Rust 1.97.0 调整了浮点字面量类型推断：当 `{float}`（未约束的浮点字面量）出现在需要具体类型的上下文中且未通过其他约束确定为 `f64` 时，更可能回退到 `f32`。这一变更主要影响依赖旧推断行为的代码，并会触发未来兼容性警告。

```rust,ignore
fn takes_f32(_: f32) {}

fn main() {
    // Rust 1.97+：以下代码可能触发未来兼容性警告，
    // 因为字面量 1.0 的类型推断路径发生变化。
    takes_f32(1.0);
}
```

**迁移建议**：对浮点字面量显式标注类型，例如 `1.0f32` 或 `1.0_f32`。

### 2.7 v0 symbol mangling 默认启用

Rust 1.97.0 将 v0 symbol mangling 方案设为默认。该方案自 1.59 起可通过 `-C symbol-mangling-version=v0` 选择，自 2025-11 起在 nightly 默认启用，现进入 stable。

**与旧方案（Itanium ABI）相比的优势**：

- 泛型参数实例保留具体值，而非仅通过 hash 追踪
- 消除旧方案中部分条目未使用 Itanium ABI 导致的不一致

**影响与迁移**：

| 场景 | 影响 | 建议 |
|:---|:---|:---|
| 调试器 / Profiler | 旧版本可能无法 demangle v0 符号 | 升级工具链；GDB 15+、LLDB 等主流工具已支持 |
| Backtrace | 格式可能变化 | 更新依赖旧格式的解析脚本 |
| 链接 / 分析脚本 | 符号名格式变化 | 测试并适配 v0 格式；必要时临时通过 nightly `-C symbol-mangling-version=legacy` 回退 |

```bash
# 查看当前 mangling 版本（需要 nightly 才能显式选择 legacy）
rustc -C symbol-mangling-version=v0 --print cfg
```

### 2.8 链接器输出默认显示 (`linker_messages` lint)

历史上 rustc 在链接成功时隐藏 linker 的 stderr 输出。Rust 1.97.0 改为默认显示链接器输出，并通过 `linker_messages` lint 以 warning 形式报告。

**关键语义**：

- `linker_messages` 是**特殊 lint**，**不受 `warnings` lint group 控制**。
- 已知误报或预期行为已被 rustc 过滤。
- 若需临时静默，显式设置为 `allow`：

```toml
[lints.rust]
linker_messages = "allow"
```

```rust,ignore
// 或在 crate 根显式允许
#![allow(linker_messages)]
```

---

## 3. 目标平台

`nvptx64-nvidia-cuda` 目标的基线提升标志着 Rust GPU 编程从「外部 crate 实验」向「编译器内建目标」演进：

- **意义**：PTX 是 NVIDIA GPU 的虚拟 ISA，`nvptx64` 后端使 `rustc` 直接产出 PTX，无需经 C++/NVCC——`rust-gpu`（SpiritV 路线）之外的第二条 GPU 路径。
- **基线提升内容**：目标从 tier 3 提升维护等级，CUDA 版本基线对齐现代驱动栈，`no_std`（GPU 无操作系统）作为唯一模式。
- **现实边界**：生态仍极早期——无运行时 crate 生态、无 cuBLAS/cuDNN 类库绑定；适合研究型 kernel 开发，生产 GPU 计算仍需 `cudarc`（CUDA 驱动绑定，CPU 侧）或 wgpu/Vulkan 计算路线。

判定依据：需要 Rust 写 GPU kernel 的团队当前首选 wgpu 计算（跨厂商）；nvptx 目标适合追踪，不适合押注。

### 3.1 `nvptx64-nvidia-cuda` 基线提升

Rust 1.97.0 提升了 NVIDIA PTX 目标的硬件与 ISA 基线：

| 维度 | 旧基线 | 新基线（1.97+） |
|:---|:---|:---|
| PTX ISA | 6.0 | 7.0 |
| 最低 SM | sm_50 (Maxwell) / sm_52 (Pascal) | sm_70 (Volta) |
| 未指定 `-C target-cpu` 时的默认 | sm_52 | sm_70 |

影响：Maxwell / Pascal GPU 不再默认支持；如需兼容旧硬件，需显式指定 `-C target-cpu=sm_52` 等。

---

## 4. 标准库 API

1.97 的标准库稳定项延续了“补齐小缺口”的节奏：六项 API 各自消除一个长期存在的不便，没有任何一项改变编程范式。本节按使用频率排序解读。

六项 API 的速览：

| API | 解决的问题 | 典型场景 |
|---|---|---|
| `Default for RepeatN` | `repeat_n` 结果无法默认构造 | 泛型容器初始化 |
| `Copy for ffi::FromBytesUntilNulError` | 该错误类型不能复制，错误处理受限 | C 字符串解析的 `?` 传播 |
| `Send for std::fs::File` on UEFI | UEFI target 上 File 不可跨线程 | 固件/引导程序的异步 IO |
| 整数位查询方法 | 手写位运算易错 | 位图、协议解析 |
| `NonZero` 位查询 | NonZero 包装下位操作需先解包 | 无零值域的位图 |
| `char::is_control` const 稳定 | const 上下文中无法判别控制字符 | 编译期文本处理 |

迁移建议：整数位查询与 `is_control` 两项可直接替换存量手写实现，属于零风险收益；UEFI 相关项仅影响该 target 的项目。

### 4.1 `Default for RepeatN`

`std::iter::RepeatN`（`std::iter::repeat_n` 的返回类型）现在实现 `Default`，可构造空迭代器。

```rust,ignore
use std::iter::RepeatN;

let empty: RepeatN<i32> = RepeatN::default();
assert_eq!(empty.count(), 0);
```

### 4.2 `Copy for ffi::FromBytesUntilNulError`

`std::ffi::FromBytesUntilNulError` 现在实现 `Copy`，可在不移动所有权的情况下复制错误值。

```rust,ignore
use std::ffi::CStr;

let bytes = b"hello\0";
let e: std::ffi::FromBytesUntilNulError =
    CStr::from_bytes_until_nul(&bytes[..0]).unwrap_err();
let e2 = e; // Copy
let _ = e;  // 仍可再次使用
```

### 4.3 `Send for std::fs::File` on UEFI

在 UEFI 目标（如 `x86_64-unknown-uefi`）上，`std::fs::File` 现在实现 `Send`。

### 4.4 整数位查询方法

所有整数类型（`u8` 到 `u128`、`i8` 到 `i128`、`usize`、`isize`）新增：

| 方法 | 返回值 | 说明 |
|:---|:---|:---|
| `isolate_highest_one()` | `Self` | 仅保留最高位的 `1`，其余置 `0`；为 `0` 时返回 `0` |
| `isolate_lowest_one()` | `Self` | 仅保留最低位的 `1`，其余置 `0`；为 `0` 时返回 `0` |
| `highest_one()` | `Option<u32>` | 最高位 `1` 的索引；为 `0` 时返回 `None` |
| `lowest_one()` | `Option<u32>` | 最低位 `1` 的索引；为 `0` 时返回 `None` |
| `bit_width()` | `u32` | 表示该值所需的最少位数；`0` 返回 `0` |

```rust,ignore
let n: u32 = 0b_0110_0100;

assert_eq!(n.isolate_highest_one(), 0b_0100_0000);
assert_eq!(n.isolate_lowest_one(),  0b_0000_0100);
assert_eq!(n.highest_one(), Some(6));
assert_eq!(n.lowest_one(),  Some(2));
assert_eq!(n.bit_width(), 7);

assert_eq!(0_u32.bit_width(), 0);
assert_eq!(0b0_u32.highest_one(), None);
```

### 4.5 `NonZero` 位查询方法

`NonZero<{integer}>` 同步新增对应方法。由于输入保证非零，`isolate_*` 与 `bit_width` 返回 `NonZero<{integer}>` / `NonZero<u32>`（`bit_width` 至少为 1），`highest_one` / `lowest_one` 返回 `u32`。

```rust,ignore
use std::num::NonZeroU32;

let n = NonZeroU32::new(0b_0110_0100).unwrap();

assert_eq!(n.isolate_highest_one(), NonZeroU32::new(0b_0100_0000).unwrap());
assert_eq!(n.isolate_lowest_one(),  NonZeroU32::new(0b_0000_0100).unwrap());
assert_eq!(n.highest_one(), 6);
assert_eq!(n.lowest_one(), 2);
assert_eq!(n.bit_width().get(), 7); // bit_width 返回 NonZeroU32
```

### 4.6 `char::is_control` 在 const 上下文稳定

```rust,ignore
const BELL: char = '\u{0007}';
const IS_CTRL: bool = BELL.is_control();

fn main() {
    assert!(IS_CTRL);
}
```

---

## 5. Cargo

1.97 Cargo 的五个改进项：

1. **`build.warnings` 配置**：`[build] warnings = "deny"` 把 `RUSTFLAGS=-Dwarnings` 固化进项目配置，CI 与本地行为一致化。
2. **`resolver.lockfile-path`**：workspace 多锁文件场景（如不同 Edition/平台的独立解析）的正式配置入口。
3. **`cargo clean` 目标目录校验**：防止误删非 Cargo 目录（`CACHEDIR.TAG` 校验），`--dry-run` 预览删除集。
4. **`-m` 简写**：`cargo build -m <message>` 等长选项的短形式补全。

判定依据：团队项目应启用 `build.warnings = "deny"` 并配 `[lints]` 表（workspace 继承），把警告纪律从 CI 脚本移入版本控制内的配置。

### 5.1 `build.warnings` 配置

`[build]` 配置新增 `warnings` 字段，可统一控制**本地包（local packages）**的 lint 警告级别，常用于 CI 强制无警告。与 `RUSTFLAGS="-Dwarnings"` 不同，该配置不会使 build cache 失效，且**不影响依赖 crate**。

```toml
# .cargo/config.toml
[build]
warnings = "deny"
```

也支持环境变量 `CARGO_BUILD_WARNINGS`：

```bash
# CI：拒绝所有本地包警告，并收集全部错误/警告而非停在第一个包
CARGO_BUILD_WARNINGS=deny cargo check --keep-going

# 本地开发：临时静默警告
CARGO_BUILD_WARNINGS=allow cargo check
```

**取值**：`"allow"`、`"warn"`（默认）、`"deny"`。

### 5.2 `resolver.lockfile-path` 配置

允许指定锁文件路径，便于只读源码目录或单仓库多 lockfile 场景。

```toml
# .cargo/config.toml
[resolver]
lockfile-path = "Cargo.lock"
```

### 5.3 `cargo-clean` 目标目录校验

`cargo clean --target-dir <dir>` 现在会在 `<dir>` 看起来不像 Cargo target 目录时报错，防止误删其他目录。

### 5.4 `-m` 简写

`cargo -m <path>` 等价于 `cargo --manifest-path <path>`。

```bash
cargo -m ./crate/Cargo.toml build
```

### 5.5 `crates-io` 移除 `curl` 依赖

Cargo 内部 `crates-io` crate 不再依赖 `curl`，减少构建依赖与平台差异。

---

## 6. Rustdoc

1.97 的 Rustdoc 变更聚焦可复现构建与输出控制两个主题，延续 1.96 周期的工具链确定性主线。

两项变更的实质：

- **`--emit` 标志**：Rustdoc 输出从“总是生成完整 HTML”扩展为可选择的发射项（如仅生成 JSON 或仅检查不输出），文档测试 CI 可借此跳过 HTML 生成节省 30% 以上的文档构建时间；
- **`--remap-path-prefix`**：文档中嵌入的源码路径前缀可重映射，与 rustc 的同名标志语义对齐——私有代码库发布公共文档时不再需要 post-processing 脚本脱敏路径。

两项均为向后兼容的纯增量：不使用的项目无任何迁移负担。使用场景判断：若 CI 中有独立的 `cargo doc` 阶段且只消费 JSON 或链接检查，`--emit` 值得启用；若文档站托管路径含敏感信息，`--remap-path-prefix` 应纳入发布流程。

### 6.1 `--emit` 标志

`rustdoc --emit` 输出格式控制正式稳定。stable 取值为 `html-static-files`、`html-non-static-files`、`dep-info`（注意没有 `html` 值，`--emit=html` 会报 `unrecognized emission type`）：

```bash
# 仅生成文档页面（不含静态资源）
rustdoc --emit=html-non-static-files src/lib.rs

# 生成 Makefile 风格依赖文件，供外部增量构建
rustdoc --emit=dep-info src/lib.rs -o target/doc-dep
```

详细取值与实测行为见 [Rustdoc 1.96–1.97 变更](../../06_ecosystem/00_toolchain/07_rustdoc_196_changes.md)。

### 6.2 `--remap-path-prefix`

与 `rustc` 一致，允许在生成的文档路径中替换前缀，改善可重现构建与隐私。

```bash
rustdoc --remap-path-prefix=/home/user=/src src/lib.rs
```

---

## 7. 兼容性注意事项

| 变更 | 影响 | 建议 |
|:---|:---|:---|
| `f32: From<{float}>` 约束 `{float}` 将触发未来兼容性警告 | 类型推断可能变化 | 显式标注浮点字面量类型 |
| 默认使用 v0 symbol mangling | 旧调试器/分析器可能无法 demangle | 升级工具链或显式回退 |
| `pin!` 阻止 deref coercions | `pin!(&mut x)` 现在一定得到 `Pin<&mut &mut T>` | 检查依赖旧行为的代码 |
| `std::char` 常量与函数被弃用 | 弃用警告 | 改用 `char::` 直接调用 |
| 链接器输出默认警告 | 可能出现新 warning | 使用 `-A linker-messages` 静默 |
| 移除隐藏的已弃用 `f64` 方法 | 使用这些隐藏 API 的代码会失败 | 迁移到公开 API |
| `varargs_without_pattern` lint 在依赖中也被报告 | 依赖代码中的变参模式问题会暴露 | 升级依赖或临时允许 |
| 禁止向模块路径段传递泛型参数 | 某些不合法的泛型路径现在报错 | 修正路径语法 |
| 无效的 macho `link_section` 说明符报错 | 段/节名称非法时报错 | 修正 `#[link_section]` |
| 某些 `enum` 编码改变 | 无布局保证的 `enum` 二进制布局可能不同 | 不要依赖具体布局 |
| 空 `#[export_name = ""]` 报错 | 空导出名称被拒绝 | 提供非空名称或移除属性 |
| struct 模式中语法上拒绝元组索引简写 | 修复正确性回归 | 使用完整字段名/模式 |
| 校验 `#[link_name]` / `#[link(name)]` 参数 | 非法链接名称报错 | 确保参数非空且合法 |
| Windows 上将 `WSAESHUTDOWN` 映射为 `BrokenPipe` | 套接字行为更统一 | 更新依赖此错误码的代码 |

### 7.1 `pin!` 示例

```rust,ignore
use std::pin::{pin, Pin};

let mut x = 42;
let p: Pin<&mut &mut i32> = pin!(&mut x);
// 1.97 之前可能错误地允许 coercion 为 Pin<&mut i32>
```

### 7.2 空 `export_name` 示例

```rust,ignore
// ❌ 编译错误
#[export_name = ""]
pub fn foo() {}
```

---

## 8. 迁移指南

升级到 Rust 1.97.0：

```bash
rustup update stable
cargo update
cargo build
```

工具链与组件管理详见 [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)；`cargo update` 的工作流与锁文件策略见 [Cargo Getting Started](../../06_ecosystem/01_cargo/15_cargo_getting_started.md)。

建议优先处理的新增 warning：

1. `must_use` 在 `Result<T, Infallible>` 上的扩展。
2. `dead_code_pub_in_binary`（若启用）。
3. 链接器输出 warning。
4. `pin!` 相关的类型变化。

---

## 9. 权威来源与示例

> **完整特性说明、代码示例与迁移建议**请参见项目权威页：
>
> - [`concept/07_future/00_version_tracking/rust_1_97_preview.md`](rust_1_97_preview.md)（未稳定候选与 1.98+ 前瞻）
> - [`concept/07_future/00_version_tracking/rust_1_98_preview.md`](rust_1_98_preview.md)
> - [`crates/c08_algorithms/src/rust_197_features.rs`](../../../crates/c08_algorithms/src/rust_197_features.rs)
>
> 工具链快速参考请参见：
>
> - [`docs/09_toolchain/10_rust_1_97_features.md`](../../../docs/09_toolchain/10_rust_1_97_features.md)

---

## 10. 项目构建说明

本项目 `rust-toolchain.toml` 保持 `channel = "stable"`，由 rustup 自动解析当前 latest stable。Rust 1.97.0 已发布，`stable` 通道当前解析到 1.97.0；`Cargo.toml` 中的 `rust-version = "1.97.0"` 为项目 MSRV。

`#[cfg(nightly)]` 分支仅在 nightly 工具链下启用，文档中标记为 `rust,ignore` 的 nightly 专属示例不会参与默认 stable 构建。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Oxide: The Essence of Rust (arXiv:1903.00982)](https://arxiv.org/abs/1903.00982) · [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523704)
- **P2 生态/社区**: [docs.rs/tokio — 生态权威 API 文档](https://docs.rs/tokio) · [docs.rs/futures — 生态权威 API 文档](https://docs.rs/futures)

---

## 相关概念

- [对应测验](../05_quizzes/01_quiz_version_and_preview.md) — 版本演进、Edition 机制与前沿特性（发布火车、1.90–1.97 稳定特性、preview 状态）
