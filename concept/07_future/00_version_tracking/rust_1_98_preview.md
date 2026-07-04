# Rust 1.98+ 前沿特性预览

> **代码状态**: [实现级 — 代码已补充]
>
> **EN**: Rust 1.98+ Preview
> **Summary**: Rust 1.98 and beyond: nightly language features, compiler infrastructure, and ecosystem trends tracked for future stabilization.
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **跟踪版本**: nightly 1.99.0 (2026-06-22)
> **预计稳定时间**: 2026-09-04 及以后（Rust 1.98.0 计划发布日期）
> **当前阶段**: 🧪 Nightly 实验性 / 设计或 MCP 阶段
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **状态**: 特性集高度不确定，稳定时间和具体内容以官方发布为准
>
> **权威来源**:
>
> · [Rust Reference](https://doc.rust-lang.org/reference/)
> · [TRPL](https://doc.rust-lang.org/book/title-page.html)
> · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)
> · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
> · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> - [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
> - [Project Goals — Beyond the `&`](https://rust-lang.github.io/rust-project-goals/2026/pin-ergonomics.html)
> - [Project Goals — BorrowSanitizer](https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html)
> - [Project Goals — Field Projections](https://rust-lang.github.io/rust-project-goals/2026/field-projections.html)
> - [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
> - [Rust Internals Forum](https://internals.rust-lang.org/)
> - [releases.rs — nightly 1.98.0](https://releases.rs/)
>
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
> **前置概念**: N/A
---

> **后置概念**:
>
> [Rust 1.97 前沿特性预览](rust_1_97_preview.md)
> · [Rust Specification](https://www.rust-lang.org/)
> · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
>
> **前置依赖**:
>
> [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> · [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

---

---

> **过渡**: 从 Rust 1.98+ 前沿特性预览 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Rust 1.98+ 前沿特性预览 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Rust 1.98+ 前沿特性预览 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Rust 1.98+ 前沿特性预览 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Rust 1.98+ 前沿特性预览 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Rust 1.98+ 前沿特性预览 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 一、语言特性预览

### 1.1 Pin Ergonomics（&pin mut / &pin const）

**状态**: 🧪 Lang experiment，Project Goals 2026 旗舰目标 "Beyond the &"

**跟踪 Issue**: [rust-lang/rust#130494](https://github.com/rust-lang/rust/issues/130494)

**核心问题**: `Pin<&mut T>` 的 API 出了名的不友好，手动 pin projection 容易出错，且难以教授。

**提案方向**:

- 引入 `&pin mut T` 和 `&pin const T` 原生借用（Borrowing）类型
- 自动 reborrow、autoref、pattern matching 支持
- 若 `T: Unpin`，`&pin mut T` 与 `&mut T` 可互相 coerce
- 对 `!Unpin` 类型，`Drop` 可能需要 `fn drop(&pin mut self)`

**代码示例** (nightly):

```rust,ignore
#![feature(pin_ergonomics)]

struct ListNode {
    value: i32,
    next: Option<std::pin::Pin<Box<ListNode>>>,
}

fn process(node: &pin mut ListNode) {
    // 自动 pin projection，无需 unsafe
    println!("{}", node.value);
}
```

**深度文档**: [15_pin_ergonomics_preview.md](../03_preview_features/15_pin_ergonomics_preview.md)

**教学提示**: 这是 async/self-referential 类型的基础；稳定后将大幅简化 futures 和 pin-project 类 crate 的教学。

---

### 1.2 Reborrow Traits

**状态**: 🧪 设计阶段，Project Goals 2026 旗舰目标 "Beyond the &"

**核心问题**: 当前 Rust 无法泛化地表达 "可以 reborrow" 的能力，导致 `&mut T`、`Pin<&mut T>`、`&Cell<T>` 等需要各自重复的 API。

**提案方向**:

- 引入类似 `Reborrow` / `ReborrowMut` 的 trait
- 统一 `&mut`、pinned mutable reference、interior-mutable references 的 reborrow 语义
- 可能与 Pin ergonomics 协同解决 auto-borrowing

**影响**: 一旦稳定，将深刻影响低层 API 设计（如 IO traits、buffer APIs、self-referential structs）。

```rust,ignore
// 假设性 Reborrow traits（最终 API 以 RFC 为准）
pub trait Reborrow {
    type Output;
    fn reborrow(&self) -> Self::Output;
}

pub trait ReborrowMut {
    type Output;
    fn reborrow_mut(&mut self) -> Self::Output;
}

// 未来可能统一 &mut T、Pin<&mut T>、&Cell<T> 的 reborrow API
fn process_buffer<B: ReborrowMut>(buf: &mut B)
where
    B::Output: AsRef<[u8]>,
{
    let tmp = buf.reborrow_mut();
    // 在 tmp 的生命周期内继续使用 buf，而不需要完全移动所有权
    let _ = tmp.as_ref();
}
```

---

### 1.3 Field Projections

**状态**: 🧪 设计阶段，Project Goals 2026 旗舰目标 "Beyond the &"

**跟踪**: [Project Goals — Field Projections](https://rust-lang.github.io/rust-project-goals/2026/field-projections.html)

**核心问题**: 当前无法安全地在 trait 中表达 "返回某字段的引用（Reference）/投影"，pin projection 尤其困难。

**提案方向**:

- 允许 trait 定义字段投影
- 编译器可验证投影的合法性
- 与 Pin ergonomics 配合，提供安全的 self-referential/pinned 字段访问

**影响**: 可能取代大量 `pin-project` / `pin-project-lite` 宏（Macro）的使用场景。

```rust,ignore
// 假设性字段投影 trait（最终 API 以 RFC 为准）
trait FieldProjection {
    type Field<T>;

    // 在 trait 中安全地返回某个字段的 pinned 投影
    fn project<T>(self: Pin<&mut Self>) -> Pin<&mut Self::Field<T>>;
}

struct Form {
    header: Header,
    body: Body,
}

impl FieldProjection for Form {
    type Field<header> = Header; // 示意，非真实语法
    // ...
}
```

---

### 1.4 Return Type Notation (RTN)

**状态**: 🧪 RFC 3654；Project Goals 2026 目标 "Prepare TAIT + RTN for stabilization"

**核心问题**: `impl Trait` 返回类型中无法命名关联类型，导致 `async fn` / `-> impl Iterator` 的返回类型难以在 trait bound 中表达。

**提案语法**:

```rust,ignore
trait Processor {
    fn process(&self) -> impl Future<Output = i32>;
}

fn spawn_processor<P>(p: P)
where
    P: Processor,
    P::process(): Send,  // RTN: 约束 process() 的返回类型为 Send
{
    tokio::spawn(async move { p.process().await });
}
```

**深度文档**: [12_return_type_notation_preview.md](../03_preview_features/12_return_type_notation_preview.md)

**1.98+ 展望**: RTN 可能在 1.98 或 1.99 进入 FCP，是 async-fn-in-traits 完全替代 `#[async_trait]` 的关键拼图。

---

### 1.5 Async Drop

**状态**: 🧪 MCP #727 已通过；实验性实现中

**核心问题**: 当前 `drop` 是同步的，无法 `await` 异步（Async）清理操作（如关闭连接、刷新缓冲区）。

**1.98+ 展望**:

- `AsyncDrop` trait 设计已确定
- `async fn drop(&mut self)` 语法支持
- 距离稳定尚有设计工作，预计 1.99+ 才能进入 FCP

```rust,ignore
#![feature(async_drop)]

struct AsyncFile {
    // 持有需要异步刷新的资源
}

impl AsyncDrop for AsyncFile {
    async fn drop(&mut self) {
        // 异步清理：刷新缓冲区、关闭连接等
        self.flush().await;
    }
}
```

**深度文档**: [18_async_drop_preview.md](../03_preview_features/18_async_drop_preview.md)

---

### 1.6 Async Iteration / Async Iterator

**状态**: 🧪 讨论阶段，无广泛共识

**核心问题**: `Stream` trait 在 `futures` crate 中，std 缺乏原生的 async iteration 抽象。

**1.98+ 展望**:

- 可能引入 `AsyncIterator` trait（`async fn next(&mut self) -> Option<Self::Item>`）
- `for await` 语法仍在讨论
- 预计不会在 1.98 稳定，但可能在 nightly 中有更多实验

---

## 二、标准库 API 预览

本小节跟踪已进入 Rust 1.98 稳定通道或极有可能进入 1.98 的标准库 API。等效实现与 nightly 测试位于 [`crates/c08_algorithms/src/rust_197_features.rs`](../../../crates/c08_algorithms/src/rust_197_features.rs)。

### 2.1 已确认进入 1.98 的 API

| API | PR | 说明 |
|:---|:---|:---|
| `f32::add_algebraic` / `f64::add_algebraic` 等 `float_algebraic` intrinsics | [#157029](https://github.com/rust-lang/rust/pull/157029) | 允许编译器在代数等价前提下重排浮点运算，提升向量化/优化空间 |
| `int_format_into` | [#152544](https://github.com/rust-lang/rust/pull/152544) | 整数直接格式化到现有缓冲区，避免 `write!` 的堆分配 |
| `core::range::{RangeFull, RangeTo}` / `legacy::*` | [#156629](https://github.com/rust-lang/rust/pull/156629) | 将 `std::ops::RangeFull`、`std::ops::RangeTo` 下沉到 `core::range`，服务 `no_std` |
| `NonZero<T>::from_str_radix` | [#157877](https://github.com/rust-lang/rust/pull/157877) | 按指定进制解析非零整数，结果为 0 时返回 `Err` |
| `Box::as_ptr` / `Box::as_mut_ptr` | #157876 | 不物化引用（Reference）的原始指针（Raw Pointer）访问，对 aliasing model 更友好 |
| `hex_literal_case` (rustfmt) | [rustfmt #6935](https://github.com/rust-lang/rustfmt/pull/6935) | 十六进制字面量大小写风格配置 |

```rust
// 1.98+ 使用示例（概念性，当前需 nightly 或等待稳定）
use std::num::NonZeroU32;

fn demo_198_apis() {
    // NonZero::from_str_radix
    let n = NonZeroU32::from_str_radix("1a", 16).unwrap();
    assert_eq!(n.get(), 26);

    // Box::as_mut_ptr
    let mut boxed = Box::new(42);
    let ptr: *mut i32 = boxed.as_mut_ptr();
    unsafe { *ptr = 100; }
    assert_eq!(*boxed, 100);
}
```

**代码实现**:

[`demo_float_algebraic()`](../../../crates/c08_algorithms/src/rust_197_features.rs) ·
[`demo_int_format_into()`](../../../crates/c08_algorithms/src/rust_197_features.rs) ·
[`demo_core_range_completion()`](../../../crates/c08_algorithms/src/rust_197_features.rs) ·
[`demo_nonzero_from_str_radix()`](../../../crates/c08_algorithms/src/rust_197_features.rs) ·
[`demo_box_as_ptr()`](../../../crates/c08_algorithms/src/rust_197_features.rs)

---

### 2.2 等待中 / 可能推迟至 1.98+ 的 API

| API | 状态 | 说明 |
|:---|:---|:---|
| `VecDeque::truncate_front` / `retain_back` | 🔄 FCP finished / waiting | PR [#151973](https://github.com/rust-lang/rust/pull/151973) FCP 已完成，当前等待 review / FCP completion；已确定错过 1.97 cutoff，进入 1.98 通道 |
| `RandomSource` / `DefaultRandomSource` | 🔄 等待 libs-api | PR [#157168](https://github.com/rust-lang/rust/pull/157168)，可插拔随机数源抽象 |
| `Box::into_non_null` / `Vec::into_non_null` (`box_vec_non_null`) | 🔄 PFCP | tracking issue [#130364](https://github.com/rust-lang/rust/issues/130364)，转换为 `NonNull<T>`；当前 nightly 方法尚未出现，名称待确认 |
| `#[optimize]` 属性 | 🔄 PFCP / Blocked | PR [#157273](https://github.com/rust-lang/rust/pull/157273)，函数级优化提示 |
| `size_of_val_raw` / `align_of_val_raw` / `Layout::for_value_raw` | 🔄 等待 review | PR [#157572](https://github.com/rust-lang/rust/pull/157572)，裸值尺寸/对齐计算 |
| C-variadic function definitions | 🔄 PFCP | PR [#155942](https://github.com/rust-lang/rust/pull/155942)，定义 C 风格可变参数函数 |
| `proc_macro_value` | 🔄 等待 review | PR [#152092](https://github.com/rust-lang/rust/pull/152092)，过程宏（Procedural Macro）在编译期产生值 |
| `local_key_cell_update` | 🔄 等待 libs-api | PR [#157734](https://github.com/rust-lang/rust/pull/157734)，`LocalKey::update` 相关 Cell 更新 API |
| `#[my_macro] mod foo;` (proc_macro_hygiene) | 🔄 PFCP | PR #157857，过程宏（Procedural Macro）卫生性的一部分 |

---

### 2.3 Nightly 探测结果（2026-06-28）

> 探测脚本: [`scripts/probe_rust_198_apis.rs`](../../../scripts/probe_rust_198_apis.rs)
> 完整报告: [`reports/RUST_198_NIGHTLY_PROBE_2026_06_28.md`](../../../reports/RUST_198_NIGHTLY_PROBE_2026_06_28.md)

使用 `rustc 1.98.0-nightly (2026-06-26)` 对 17 项候选 API 进行无 feature gate 编译探测：

| 状态 | 数量 | 代表 API |
|---|---|---|
| ✅ 已可用 | 11 | `i32::isqrt`、`u32::isqrt`、`ptr::with_exposed_provenance`、`ptr::without_provenance`、`ptr::dangling`、`Ipv6Addr::is_unique_local`、`CStr::from_bytes_until_nul`、`std::pin::pin!`、`From<bool> for f32/f64`、`Waker::noop` |
| ❌ 仍不可用 | 6 | `Pin::as_deref_mut`、`NonZeroI32::isqrt`、`Vec::into_non_null`、`Box::into_non_null`、`VecDeque::truncate_front`、`VecDeque::retain_back` |

**关键发现**:

- `i32::isqrt` 等整数平方根 API 已在 nightly 可用，预计进入 1.98.0 stable。
- Provenance 相关 API (`with_exposed_provenance`、`without_provenance`、`dangling`) 已在 nightly 可用，是 strict provenance 迁移的重要信号。
- `Pin::as_deref_mut` 在当前 nightly 仍不存在，说明 Pin ergonomics 仍在演进，教学中应保持保守。
- 从 1.97.0 推迟的 `Box::into_non_null`、`Vec::into_non_null`、`VecDeque::truncate_front`、`VecDeque::retain_back` 仍未稳定，代码中需继续保留等效实现。

---

## 三、编译器与工具链预览

### 3.1 Cranelift Backend（生产级）

**状态**: 🧪 Project Goals 2026 旗舰目标 "Flexible, fast(er) compilation"

**核心问题**: LLVM backend 编译慢，debug 构建尤其明显。

**提案方向**:

- 将 `cranelift` 作为可选 codegen backend
- 通过 `cargo build -Zcodegen-backend=cranelift` 使用
- 目标：debug 构建速度显著提升

**1.98+ 展望**:

- 继续完善稳定性和功能完整性
- 可能在 1.99 或 1.100 进入稳定预览

**教学提示**: 可在 `.cargo/config.toml` 中展示本地启用方式，但强调仍为 nightly。

```toml
# .cargo/config.toml
[unstable]
codegen-backend = true

[build]
rustflags = ["-Zcodegen-backend=cranelift"]
```

---

### 3.2 Parallel Frontend

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: rustc 前端（parse / expand / resolve / type-check）目前基本是单线程，无法充分利用多核。

**提案方向**:

- 在 crate 内部并行化前端阶段
- 通过 `-Zthreads=N` 实验

**1.98+ 展望**: 实验性支持持续完善，稳定化时间未定。

---

### 3.3 build-std

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: 交叉编译、`no_std`、自定义 target 时需要从源码构建标准库。

**提案方向**:

- 稳定化 `cargo build -Zbuild-std`
- 支持 MSan/TSan、自定义 allocator、profile-guided 标准库构建

**1.98+ 展望**: 是 MSan/TSan 稳定化的前置条件之一。

---

### 3.4 Next-Generation Trait Solver

**状态**: 🧪 已实现，默认在 nightly 中启用进行测试

**核心问题**: 旧 trait solver 在复杂泛型（Generics）、GATs、TAIT、RTN 等场景下存在限制和 bugs。

**1.98+ 展望**:

- 继续通过 crater 测试验证兼容性
- 预计 1.99+ 成为默认 solver
- 需要大量实际项目测试反馈

---

## 四、Cargo 与生态预览

### 4.1 Public/Private Dependencies（RFC #3516）

**状态**: 🔄 FCP 准备中；Project Goals 2026 目标

**核心问题**: crate 无法声明某个依赖是 "public"（其类型会出现在本 crate 的 public API 中），导致 semver 检查工具难以判断破坏性变更。

**提案语法**:

```toml
[dependencies]
serde = { version = "1.0", public = true }
```

**1.98+ 展望**: 可能在 1.98 或 1.99 稳定 MVP。

---

### 4.2 Cargo SBOM Precursor

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: 供应链安全需要机器可读的依赖清单（Software Bill of Materials）。

**提案方向**:

- 在 `Cargo.lock` 之外生成 SBOM 信息
- 可能与 `cargo metadata` 或新的 `cargo sbom` 子命令结合

**1.98+ 展望**: 2026 年重点推进，可能产生新的实验性子命令。

---

### 4.3 cargo-script 稳定化

**状态**: 🧪 已在 Rust 1.79 nightly；Project Goals 2026 目标 "Stabilize cargo-script"

**核心问题**: Rust 缺少类似 Python/Node 的轻量级脚本执行方式。

**提案方向**:

- 稳定化 `cargo +nightly -Zscript`
- 支持文件顶部的 TOML frontmatter

**1.98+ 展望**: 有望在 1.98 或 1.99 稳定。

---

### 4.4 Sized Hierarchy / const Sized / Scalable Vectors

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: `Sized` trait 层级过于粗糙，`extern types` 和 SVE (Scalable Vector Extension) 需要更精细的大小信息。

**提案方向**:

- 细化 `Sized` trait hierarchy
- 引入 `const Sized` 支持编译期未知但运行时（Runtime）确定的大小
- 为 AArch64 SVE / SME 提供标准库支持

**1.98+ 展望**: 基础 trait hierarchy 可能在 1.98 进入 FCP；SVE/SME 支持为 nightly 长期目标。

---

## 五、形式化与安全预览

### 5.1 Safety Tags（RFC #3842）

**状态**: 🧪 RFC 讨论中

**核心问题**: 当前 safety comments 是自由文本，难以工具化检查。

**提案方向**:

- `#[safety::requires(...)]` 标注 unsafe 函数的前提条件
- `#[safety::checked(...)]` 标注调用处已检查的条件
- Clippy / rust-analyzer 未来可提供 IDE 支持

**深度文档**: [33_safety_tags_in_formal.md](../../04_formal/02_separation_logic/33_safety_tags_in_formal.md)

---

### 5.2 BorrowSanitizer

**状态**: 🧪 Rust Project Goal 2026；LLVM RFC 已发布

**核心问题**: Miri 精确但极慢，且无法跨越 FFI 边界检测 Tree Borrows 违规。

**提案方向**:

- 基于 LLVM 的 sanitizer，在运行时（Runtime）检测 Tree Borrows 违规
- 支持 C/C++/Rust 混合代码

**深度文档**: [34_borrow_sanitizer_in_formal.md](../../04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md)

---

### 5.3 MemorySanitizer / ThreadSanitizer 稳定化

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: MSan/TSan 需要 `-Zbuild-std`，使用门槛高。

**1.98+ 展望**:

- 稳定化 MSan/TSan 支持
- 提供预编译的 instrumented 标准库

---

## 六、WebAssembly 与嵌入式预览

### 6.1 Wasm Components

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: Rust 需要更好地支持 WebAssembly Component Model 和 WASI Preview 2/3。

**1.98+ 展望**:

- 新增/稳定化三个 compiler target
- 实验性支持 Wasm-specific 语言特性
- WASI Preview 3（原生 async I/O）预计 2026 年发布

**关联**: `c12_wasm` 模块（Module）应跟踪 `wasm32-wasip1` / `wasm32-wasip2` target 和 `cargo-component`。

---

## 七、跟踪与更新机制

### 7.1 更新频率

- 每两周检查一次 [releases.rs](https://releases.rs/) 和 [Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) 更新
- 每次 Rust nightly 升级后，验证本文件中的 nightly 代码示例是否仍可编译

### 7.2 状态标记约定

| 标记 | 含义 |
|:---|:---|
| 🧪 | Nightly 实验性 |
| 🔄 | MCP / RFC / PFCP 阶段 |
| ✅ | 已稳定 |
| ❌ | 已取消或无限期推迟 |
| ⏳ | 等待上游决策 |

### 7.3 关联文档

- [Rust 1.97 前沿特性预览](rust_1_97_preview.md)
- [Pin Ergonomics 预览](../03_preview_features/15_pin_ergonomics_preview.md)
- [Return Type Notation 预览](../03_preview_features/12_return_type_notation_preview.md)
- [Async Drop 预览](../03_preview_features/18_async_drop_preview.md)
- [Safety Tags](../../04_formal/02_separation_logic/33_safety_tags_in_formal.md)
- [BorrowSanitizer](../../04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md)
- [AutoVerus / Verus](../../04_formal/04_model_checking/24_autoverus.md)
- [Tree Borrows 深度](../../04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md)
- [1.97/1.98 API 等效实现与测试](../../../crates/c08_algorithms/src/rust_197_features.rs)

---

## 八、待补充代码任务

- [x] 为本文件中的每个特性补充最小 nightly 示例（使用 `rust,ignore`，待 API 稳定后转为可编译示例）
- [x] 在 `crates/c08_algorithms/src/rust_197_features.rs` 中维护 1.97/1.98 API 的等效实现与单元测试
- [x] 补充 1.98 已确认标准库 API 预览（`float_algebraic`、`int_format_into`、`core::range`、`NonZero::from_str_radix`、`Box::as_ptr`、`hex_literal_case`）
- [ ] 将本文件关键术语同步到 `concept/00_meta/terminology_glossary.md`（待 1.98 特性稳定后执行）
