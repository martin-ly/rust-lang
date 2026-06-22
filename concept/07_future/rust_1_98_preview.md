# Rust 1.98+ 前沿特性预览

> **代码状态**: [综述级 — 待补充代码]
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
> - [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
> - [Project Goals — Beyond the `&`](https://rust-lang.github.io/rust-project-goals/2026/goals/beyond-the-and.html)
> - [Project Goals — BorrowSanitizer](https://rust-lang.github.io/rust-project-goals/2026/goals/borrowsanitizer.html)
> - [Project Goals — Field Projections](https://rust-lang.github.io/rust-project-goals/2026/goals/field-projections.html)
> - [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
> - [Rust Internals Forum](https://internals.rust-lang.org/)
> - [releases.rs — nightly 1.98.0](https://releases.rs/)
>
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链

---

> **后置概念**: [Rust 1.97 稳定特性](./rust_1_97_preview.md) · [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md) · [Toolchain](../06_ecosystem/01_toolchain.md)

---

## 一、语言特性预览

### 1.1 Pin Ergonomics（&pin mut / &pin const）

**状态**: 🧪 Lang experiment，Project Goals 2026 旗舰目标 "Beyond the &"

**跟踪 Issue**: [rust-lang/rust#130494](https://github.com/rust-lang/rust/issues/130494)

**核心问题**: `Pin<&mut T>` 的 API 出了名的不友好，手动 pin projection 容易出错，且难以教授。

**提案方向**:

- 引入 `&pin mut T` 和 `&pin const T` 原生借用类型
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

**深度文档**: [15_pin_ergonomics_preview.md](15_pin_ergonomics_preview.md)

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

**核心问题**: 当前无法安全地在 trait 中表达 "返回某字段的引用/投影"，pin projection 尤其困难。

**提案方向**:

- 允许 trait 定义字段投影
- 编译器可验证投影的合法性
- 与 Pin ergonomics 配合，提供安全的 self-referential/pinned 字段访问

**影响**: 可能取代大量 `pin-project` / `pin-project-lite` 宏的使用场景。

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

**深度文档**: [12_return_type_notation_preview.md](12_return_type_notation_preview.md)

**1.98+ 展望**: RTN 可能在 1.98 或 1.99 进入 FCP，是 async-fn-in-traits 完全替代 `#[async_trait]` 的关键拼图。

---

### 1.5 Async Drop

**状态**: 🧪 MCP #727 已通过；实验性实现中

**核心问题**: 当前 `drop` 是同步的，无法 `await` 异步清理操作（如关闭连接、刷新缓冲区）。

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

**深度文档**: [18_async_drop_preview.md](18_async_drop_preview.md)

---

### 1.6 Async Iteration / Async Iterator

**状态**: 🧪 讨论阶段，无广泛共识

**核心问题**: `Stream` trait 在 `futures` crate 中，std 缺乏原生的 async iteration 抽象。

**1.98+ 展望**:

- 可能引入 `AsyncIterator` trait（`async fn next(&mut self) -> Option<Self::Item>`）
- `for await` 语法仍在讨论
- 预计不会在 1.98 稳定，但可能在 nightly 中有更多实验

---

## 二、编译器与工具链预览

### 2.1 Cranelift Backend（生产级）

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

### 2.2 Parallel Frontend

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: rustc 前端（parse / expand / resolve / type-check）目前基本是单线程，无法充分利用多核。

**提案方向**:

- 在 crate 内部并行化前端阶段
- 通过 `-Zthreads=N` 实验

**1.98+ 展望**: 实验性支持持续完善，稳定化时间未定。

---

### 2.3 build-std

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: 交叉编译、`no_std`、自定义 target 时需要从源码构建标准库。

**提案方向**:

- 稳定化 `cargo build -Zbuild-std`
- 支持 MSan/TSan、自定义 allocator、profile-guided 标准库构建

**1.98+ 展望**: 是 MSan/TSan 稳定化的前置条件之一。

---

### 2.4 Next-Generation Trait Solver

**状态**: 🧪 已实现，默认在 nightly 中启用进行测试

**核心问题**: 旧 trait solver 在复杂泛型、GATs、TAIT、RTN 等场景下存在限制和 bugs。

**1.98+ 展望**:

- 继续通过 crater 测试验证兼容性
- 预计 1.99+ 成为默认 solver
- 需要大量实际项目测试反馈

---

## 三、Cargo 与生态预览

### 3.1 Public/Private Dependencies（RFC #3516）

**状态**: 🔄 FCP 准备中；Project Goals 2026 目标

**核心问题**: crate 无法声明某个依赖是 "public"（其类型会出现在本 crate 的 public API 中），导致 semver 检查工具难以判断破坏性变更。

**提案语法**:

```toml
[dependencies]
serde = { version = "1.0", public = true }
```

**1.98+ 展望**: 可能在 1.98 或 1.99 稳定 MVP。

---

### 3.2 Cargo SBOM Precursor

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: 供应链安全需要机器可读的依赖清单（Software Bill of Materials）。

**提案方向**:

- 在 `Cargo.lock` 之外生成 SBOM 信息
- 可能与 `cargo metadata` 或新的 `cargo sbom` 子命令结合

**1.98+ 展望**: 2026 年重点推进，可能产生新的实验性子命令。

---

### 3.3 cargo-script 稳定化

**状态**: 🧪 已在 Rust 1.79 nightly；Project Goals 2026 目标 "Stabilize cargo-script"

**核心问题**: Rust 缺少类似 Python/Node 的轻量级脚本执行方式。

**提案方向**:

- 稳定化 `cargo +nightly -Zscript`
- 支持文件顶部的 TOML frontmatter

**1.98+ 展望**: 有望在 1.98 或 1.99 稳定。

---

### 3.4 Sized Hierarchy / const Sized / Scalable Vectors

**状态**: 🧪 Project Goals 2026 旗舰目标

**核心问题**: `Sized` trait 层级过于粗糙，`extern types` 和 SVE (Scalable Vector Extension) 需要更精细的大小信息。

**提案方向**:

- 细化 `Sized` trait hierarchy
- 引入 `const Sized` 支持编译期未知但运行时确定的大小
- 为 AArch64 SVE / SME 提供标准库支持

**1.98+ 展望**: 基础 trait hierarchy 可能在 1.98 进入 FCP；SVE/SME 支持为 nightly 长期目标。

---

## 四、形式化与安全预览

### 4.1 Safety Tags（RFC #3842）

**状态**: 🧪 RFC 讨论中

**核心问题**: 当前 safety comments 是自由文本，难以工具化检查。

**提案方向**:

- `#[safety::requires(...)]` 标注 unsafe 函数的前提条件
- `#[safety::checked(...)]` 标注调用处已检查的条件
- Clippy / rust-analyzer 未来可提供 IDE 支持

**深度文档**: [22_safety_tags.md](../04_formal/22_safety_tags.md)

---

### 4.2 BorrowSanitizer

**状态**: 🧪 Rust Project Goal 2026；LLVM RFC 已发布

**核心问题**: Miri 精确但极慢，且无法跨越 FFI 边界检测 Tree Borrows 违规。

**提案方向**:

- 基于 LLVM 的 sanitizer，在运行时检测 Tree Borrows 违规
- 支持 C/C++/Rust 混合代码

**深度文档**: [23_borrow_sanitizer.md](../04_formal/23_borrow_sanitizer.md)

---

### 4.3 MemorySanitizer / ThreadSanitizer 稳定化

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: MSan/TSan 需要 `-Zbuild-std`，使用门槛高。

**1.98+ 展望**:

- 稳定化 MSan/TSan 支持
- 提供预编译的 instrumented 标准库

---

## 五、WebAssembly 与嵌入式预览

### 5.1 Wasm Components

**状态**: 🧪 Project Goals 2026 目标

**核心问题**: Rust 需要更好地支持 WebAssembly Component Model 和 WASI Preview 2/3。

**1.98+ 展望**:

- 新增/稳定化三个 compiler target
- 实验性支持 Wasm-specific 语言特性
- WASI Preview 3（原生 async I/O）预计 2026 年发布

**关联**: `c12_wasm` 模块应跟踪 `wasm32-wasip1` / `wasm32-wasip2` target 和 `cargo-component`。

---

## 六、跟踪与更新机制

### 6.1 更新频率

- 每两周检查一次 [releases.rs](https://releases.rs/) 和 [Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) 更新
- 每次 Rust nightly 升级后，验证本文件中的 nightly 代码示例是否仍可编译

### 6.2 状态标记约定

| 标记 | 含义 |
|:---|:---|
| 🧪 | Nightly 实验性 |
| 🔄 | MCP / RFC / PFCP 阶段 |
| ✅ | 已稳定 |
| ❌ | 已取消或无限期推迟 |
| ⏳ | 等待上游决策 |

### 6.3 关联文档

- [Rust 1.97 稳定特性](./rust_1_97_preview.md)
- [Pin Ergonomics 预览](15_pin_ergonomics_preview.md)
- [Return Type Notation 预览](12_return_type_notation_preview.md)
- [Async Drop 预览](18_async_drop_preview.md)
- [Safety Tags](../04_formal/22_safety_tags.md)
- [BorrowSanitizer](../04_formal/23_borrow_sanitizer.md)
- [AutoVerus / Verus](../04_formal/24_autoverus.md)
- [Tree Borrows 深度](../04_formal/25_tree_borrows_deep_dive.md)

---

## 七、待补充代码任务

- [x] 为本文件中的每个特性补充最小 nightly 示例（使用 `rust,ignore`，待 API 稳定后转为可编译示例）
- [x] 在 `crates/c02_type_system/src/rust_198_features.rs` 中创建 1.98+ 特性占位模块
- [ ] 将本文件关键术语同步到 `concept/00_meta/terminology_glossary.md`（待 1.98 特性稳定后执行）
