# Rust 1.97 前沿特性预览

> **内容重叠提示**: 本文与 [`docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md`](../../docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md) 内容高度重叠。`docs/` 版本提供快速参考；`concept/` 版本为项目权威主轨。
> **代码状态**: [实现级 — 代码已补充]
>
> **EN**: Rust 1.97.0 Preview
> **Summary**: Preview of Rust 1.97.0 stable features and ongoing ecosystem trends, aligned with official Rust Project Goals 2026.
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **跟踪版本**: beta 1.97.0（2026-05-22 从 master 分支，来源: [releases.rs](https://releases.rs/docs/1.97.0/)）
> **预计稳定时间**: 2026-07-09（Rust 1.97.0 计划发布日期，来源: [Rust Forge](https://forge.rust-lang.org/)）
> **当前阶段**: 🧪 Nightly 实验性 / 1.97 已进入 Beta 分支 / 距离发布日还有 11 天
> **发布日准备**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 已就绪；`CHANGELOG.md` 已预置 `[3.1.0]` 模板
>
> **2026-06-28 探测快讯**（详见 [`reports/RUST_197_API_PROBE_2026_06_28.md`](../../reports/RUST_197_API_PROBE_2026_06_28.md)）：
>
> - ✅ 当前 nightly（rustc 1.98.0，built 2026-06-26）已无需 feature gate 的 API：`NonZero` bit ops、`const char::is_control`、`NonZeroU32::midpoint/isqrt`、`ptr::fn_addr_eq`、`const size_of_val/align_of_val`、`BuildHasherDefault::new` const、`Box::as_ptr`、`int::format_into`。
> - ❌ 仍不可用或仍需 feature gate：`VecDeque::truncate_front`（仍不稳定）、`VecDeque::retain_back`（方法不存在）、`Vec::into_non_null`（方法不存在）。
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **状态**: 部分特性已 MCP 通过，实现中；稳定版发布前特性集可能调整
>
> **权威来源**:
>
> - [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
> - [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
> - [Rust Internals Forum](https://internals.rust-lang.org/)
> - [releases.rs — Rust 1.97.0 beta](https://releases.rs/docs/1.97.0/)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
> **前置概念**: N/A
---

> **后置概念**: [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md) · [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md)

## 一、语言特性预览

### 1.1 Async Drop (MCP #727 已通过，实现中)

**状态**: 🧪 Nightly 实验性，MCP 已通过。Project Goals 2026 中归属 "Control over Drop semantics" 路线图的子目标。

**核心问题**: 当前 Rust 中 `drop` 是同步的，无法 `await` 异步（Async）清理操作（如关闭网络连接、刷新文件缓冲区）。

**1.97 进展**:

- `AsyncDrop` trait 设计已确定
- `async fn drop(&mut self)` 语法支持
- 编译器已能生成异步（Async）析构状态机

**影响**: 解决异步资源释放的核心痛点，不再需要手动 `flush()`/`close()` 后丢弃。

**深度文档**: [18_async_drop_preview.md](18_async_drop_preview.md)

**代码示例** (nightly):

```rust,ignore
#![feature(async_drop)]

use std::async_drop::AsyncDrop;

struct AsyncFile {
    handle: tokio::fs::File,
}

impl AsyncDrop for AsyncFile {
    async fn drop(&mut self) {
        let _ = self.handle.flush().await;
        let _ = self.handle.shutdown().await;
    }
}
```
---

### 1.2 Return Type Notation (RTN)

**状态**: 🧪 RFC 3654 已发布；Project Goals 2026 目标 **[Prepare TAIT + RTN for stabilization](https://rust-lang.github.io/rust-project-goals/2026/rtn.html)**（#646）。完整稳定化受下一代 trait solver 工作阻塞，目标今年晚些时候；RTN 与 async closures 的新语法设计仍在寻求贡献者。

**核心问题**: `impl Trait` 返回类型中无法命名关联类型，导致 `async fn` / `-> impl Iterator` 的返回类型难以在 trait bound 中表达。

**提案语法**:

```rust,ignore
// 使用 RTN 在 trait bound 中引用返回类型
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

---

### 1.3 Pin Ergonomics / Safe Pin Projection

**状态**: 📋 RFC 讨论阶段，Project Goals 2026 明确目标

**跟踪 Issue**: [rust-lang/rust#125153](https://github.com/rust-lang/rust/issues/125153)
**Lang-team champion**: nrc
**Project Goals 2026**: #6.13 "Continue Experimentation with Pin Ergonomics" / #6.26 "Field Projections" / #6.48 "Reborrow traits"

**核心问题**: `Pin<&mut Self>` 的字段投影需要 `unsafe` 或 `pin-project` crate，学习曲线陡峭。自固定（self-referential）结构是异步运行时（Runtime）、无锁数据结构和内存映射 I/O 的核心抽象，但当前实现方式要求每个开发者理解 pinning contract。

**当前痛点** (需要 `unsafe` 或外部 crate):

```rust,ignore
// 当前：需要 pin-project crate 或手动 unsafe
use std::pin::Pin;

struct MyFuture {
    buf: Vec<u8>,
    ptr: *const u8, // 指向 buf 内部
}

impl MyFuture {
    // 手动 unsafe：开发者必须保证 ptr 始终指向 buf 内部
    unsafe fn get_ptr(self: Pin<&mut Self>) -> &mut *const u8 {
        let this = self.get_unchecked_mut();
        &mut this.ptr
    }
}
```
**可能方向**:

- **编译器派生**: `#[derive(PinProject)]` 进入标准库或 core，自动为 `!Unpin` 字段生成安全的投影
- **Safe API**: `Pin::map_unchecked` 的 safe 变体，编译器验证投影路径的结构性固定
- **Field projection 语法**: `pin.field` 直接获取 `Pin<&mut field>`，无需宏（Macro）介入

**Project Goals 2026 关联**: 被列为 "Better pin ergonomics" 子目标，属于异步 Rust 生态系统成熟度的关键路径。

**深度文档**: [18_field_projections_preview.md](18_field_projections_preview.md)（字段级安全投影）

---

### 1.4 Unnamed Enum Variants / Open Enums（RFC 3894）

**状态**: 🧪 Lang Experiment，2026-04-22 设计会议非正式批准

**跟踪 Issue**: [rust-lang/rust#156628](https://github.com/rust-lang/rust/issues/156628)
**Feature gate**: `#![feature(unnamed_enum_variants)]`
**Lang-team champion**: Josh Triplett
**Project Goals 2026**: 属于 2026 项目目标（Open Enums / FFI 互操作方向）

**核心问题**: C 的 `enum` 是"开放的"——允许将未命名整数值强制转换为 enum 类型；而 Rust 的 `enum` 是"封闭的"——所有有效值必须在定义中声明。这导致 `bindgen` 默认不生成 `repr(C) enum` 来互操作 C enum，而使用兼容性较差的替代方案。

**提案方向**: 引入匿名变体（unnamed variants），允许 enum 声明自身与未来可能分配的 discriminant 兼容：

```rust,ignore
#![feature(unnamed_enum_variants)]

#[repr(C)]
enum CCompatibleEnum {
    A = 1,
    B = 2,
    _  // 匿名变体：允许其他整数值
}
```
**意义**: 改善 Rust 与 C FFI 的 enum 互操作性，是 Rust for Linux 等项目的长期需求之一。

**深度文档**: [25_open_enums_preview.md](25_open_enums_preview.md)

> **来源**: [rust-lang/rust#156628](https://github.com/rust-lang/rust/issues/156628) · [RFC 3894](https://github.com/rust-lang/rust/issues/156628) · 可信度: ✅

---

### 1.5 Reborrow Traits (`DerefPin`, `AsPinRef`)

**状态**: 📋 早期设计讨论

**核心问题**: 当前 `Pin<&mut T>` 无法通过 trait 边界优雅地重新借用（Borrowing）为 `Pin<&mut U>`，导致泛型（Generics）代码中固定语义传递困难。

**场景示例**:

```rust,ignore
// 希望：通过 trait 约束实现 Pin 的隐式 reborrow
fn process<P>(pin: Pin<&mut P>)
where
    P: DerefPin<Target = Buffer>, // 假设的 trait
{
    // pin 自动 reborrow 为 Pin<&mut Buffer>
    pin.fill(0);
}
```
**关联**: Pin Ergonomics 的底层基础设施之一。若 Pin projection 进入标准库，reborrow trait 将提供泛型（Generics）层面的语义支撑。

**资源**: [rust-lang/rust#125153](https://github.com/rust-lang/rust/issues/125153) (Pin ergonomics umbrella issue)

---

## 二、编译器基础设施

### 2.1 并行前端 (Parallel Frontend)

**状态**: 🧪 Nightly，8核提速 20-25%

**进展**:

- `-Zthreads=8` 已可用
- 查询系统并行化基本完成
- 正在解决增量编译与并行前端的交互问题

**使用** (nightly):

```bash
RUSTFLAGS="-Zthreads=8" cargo build
```
**深度文档**: [09_parallel_frontend_preview.md](09_parallel_frontend_preview.md)

---

### 2.2 Cranelift 后端

**状态**: 🧪 Nightly 预览 | ⚠️ **官方因资金不足进展停滞 (2026-05)**

**进展**:

- `cg_clif` 已能通过大部分 rustc 测试
- 不支持 LTO（设计限制）
- **⚠️ Rust Project Goals 2026 已标记为 Not completed (lack of funding)**：Trifecta Tech Foundation 资金不足，生产就绪目标暂停
- 适合开发迭代，不适合 release；长期维护存疑

**使用** (nightly):

```bash
cargo +nightly build -Zcodegen-backend=cranelift
```
**深度文档**: [16_cranelift_backend_preview.md](16_cranelift_backend_preview.md)

---

### 2.3 build-std (RFC #3873/#3874)

**状态**: ✅ RFC #3873 已合并 | 🟢 RFC #3874 FCP 已通过（2026-04），等待合并

**核心能力**: 编译时重新构建标准库，允许：

- 自定义 panic handler（无需 `#![no_std]`）
- 补丁 std 中的 bug
- 嵌入式/OS 开发中裁剪 std

**使用** (nightly):

```bash
cargo +nightly build -Zbuild-std=core,alloc,std --target x86_64-unknown-linux-gnu
```
---

## 三、形式化验证生态

### 3.1 AutoVerus / VeruSAGE (Microsoft)

**状态**: ✅ 已开源

**核心能力**: LLM 自动证明合成，将自然语言规约转换为 Verus 可验证代码。

**资源**: [github.com/microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis)

**深度文档**: [02_formal_methods.md](02_formal_methods.md)

---

### 3.2 Kani 0.65+ (Amazon)

**状态**: ✅ 活跃开发

**1.97 新能力**:

- 量词支持 (`forall`, `exists`)
- 循环契约 (`#[kani::loop_invariant]`)
- Autoharness（自动生成 proof harness）

**资源**: [model-checking.github.io/kani](https://model-checking.github.io/kani/)

---

### 3.3 ESBMC for Rust

**状态**: ✅ Rust Foundation 资助项目

**核心能力**: 基于有界模型检查的 Rust 标准库验证，已加入标准库验证 CI。

**资源**: [rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc](https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc)

---

### 3.4 BorrowSanitizer (BSan)

**状态**: 🧪 Nightly 实验性

**跟踪 Issue**: [rust-lang/rust#126567](https://github.com/rust-lang/rust/issues/126567)
**Feature gate**: `-Zsanitizer=borrow`
**核心作者**: Gankra (Aria Beingessner)
**Project Goals 2026**: #6.7 "BorrowSanitizer"（由 2025H2 的 "Emit Retags in Codegen" 演进而来）

**核心能力**: 动态检测 stacked borrows / tree borrows 违规，是 Miri 的"生产环境"版本。与 Miri 相比：

| 维度 | Miri | BorrowSanitizer |
|:---|:---|:---|
| 运行方式 | 解释执行 | 编译期插桩，原生速度 |
| 性能开销 | 100-1000x | 2-5x |
| 适用场景 | 测试/CI | 生产环境压力测试 |
| 覆盖规则 | Tree Borrows (可配置) | Tree Borrows |
| 内存模型验证 | 完整 | 别名规则子集 |

**使用** (nightly):

```bash
RUSTFLAGS="-Zsanitizer=borrow" cargo +nightly test
```
**意义**: 使 Tree Borrows 规则从理论验证工具走向工程实践，可在大型代码库中检测 `unsafe` 代码的别名违规。与 Kani (静态) 形成互补：BSan 动态发现实际执行路径上的违规，Kani 穷举所有可能路径。

**深度文档**: [20_borrowsanitizer_preview.md](20_borrowsanitizer_preview.md) · [04_formal/22_modern_verification_tools.md](../04_formal/22_modern_verification_tools.md)

---

### 3.5 Safety Tags (RFC #3842)

**状态**: 📋 RFC 草案阶段

**核心能力**: 将 `# Safety` 注释提升为机器可读的安全契约，作为形式化验证工具与 Rust 编译器之间的桥梁。

**与 BSan/Kani 的关系**: Safety Tags 提供安全规约的标准化语法，BSan/Kani 可据此生成验证目标。三者共同构成 "注释 → 检查 → 证明" 的验证流水线。

**深度文档**: [04_formal/22_modern_verification_tools.md](../04_formal/22_modern_verification_tools.md)

---

## 四、异步 Rust 前沿

### 4.1 Async fn in dyn Trait

**状态**: 🧪 Nightly 实验性（截至 2026-06-26 仍未稳定，暂无稳定时间表）

**核心突破**: 若未来稳定，可消除 `#[async_trait]` 在 `dyn Trait` 场景中的需求。但目前仍处于早期实验阶段，需继续依赖 `async_trait`。

```rust,ignore
#![feature(async_fn_in_dyn_trait)]

trait Service {
    async fn handle(&self, req: Request) -> Response;
}

// 仅在 nightly 实验；生产环境 dyn Trait 仍需 async_trait
fn run_service(s: &dyn Service) {
    s.handle(req); // 编译器自动处理虚表调度
}
```
> **工程建议**：在 `dyn Trait` 需要异步方法的生产代码中，继续使用 `#[async_trait]`。AFIT（async fn in trait）已在 Rust 1.75+ stable，但仅适用于泛型/`impl Trait` 场景。

---

### 4.2 异步生成器 (Async Generators)

**状态**: 📋 远期目标

**愿景**: 替代手动 `Stream` 实现，提供类似 `yield` 的语法：

```rust,ignore
#![feature(async_generators)]

async gen fn counter_stream(max: usize) -> impl Stream<Item = usize> {
    for i in 0..max {
        yield i;
    }
}
```
---

## 五、标准库演进

### 5.1 新稳定 API 跟踪 (1.97 候选)

| API | 状态 | 说明 |
|:---|:---|:---|
| `VecDeque::truncate_front` | 🔄 FCP finished / waiting | 从头部截断双端队列（PR #151973 标签为 `finished-final-comment-period` / `disposition-merge` / `to-announce`，但截至 2026-06-26 仍列于 releases.rs Ongoing Stabilization PRs，**存在推迟至 1.98+ 风险**） |
| `int_format_into` | 🟢 1.98 已确认 | 整数格式化到现有缓冲区（PR #152544，已合并至 master；因晚于 1.97 cutoff，将进入 1.98） |
| `RefCell::try_map` | 🧪 Nightly | 尝试性 RefCell 映射 |
| `String::into_raw_parts` | 🧪 Nightly | 分解 String 为原始组件 |
| **`Box::as_ptr` / `Box::as_mut_ptr`** | 🟢 1.98 已确认 | `Box<T>` 返回不物化引用（Reference）的原始指针（PR #157876，已合并至 master；将进入 1.98）。此前为 nightly-only `box_as_ptr` |
| **`core::range::RangeFull` / `RangeTo` / `legacy::*`** | 🟢 1.98 已确认 | `core::range` 类型补全（PR #156629，已合并至 master），`RangeFull` 和 `RangeTo` 作为 `core::ops` 的 re-export，`legacy::*` 为旧类型提供新家；将进入 1.98 |
| **`float_algebraic`** | 🟢 1.98 已确认 | 浮点代数运算 intrinsics（`f32::add_algebraic` 等），允许编译器在代数等价前提下重组浮点运算（PR #157029，已合并至 master；将进入 1.98） |
| **`RandomSource` / `DefaultRandomSource`** | 🔄 等待 libs-api | 可插拔随机数源抽象（PR #157168，当前 `S-waiting-on-t-libs-api`） [来源: releases.rs 2026-06-23] |
| **`PathBuf::into_string`** | 🟢 1.98 已确认 | `PathBuf` 零成本转换为 `String`（PR #156840，已合并至 master；将进入 1.98） |
| **`Result::map_or_default` / `Option::map_or_default`** | 🟢 1.98 已确认 | 便捷映射并返回默认值（PR #156222，已合并至 master；将进入 1.98） |
| **`core::alloc::Alloc`** | 🔄 等待 review | `dyn` subset of `Allocator` 稳定化为 `core::alloc::Alloc` trait（PR #157286，4 days old） [来源: releases.rs 2026-06-06] |
| **`box_vec_non_null`** | 🔄 PFCP | `Box<T>` / `Vec<T>` → `NonNull<T>` 转换优化（PR #157226，`proposed-final-comment-period`，`disposition-merge`） [来源: releases.rs 2026-06-23] |
| **`new_range_remainder`** | 🧪 Nightly | 新 `core::range` 迭代器（Iterator）类型的 `remainder()` 方法（Tracking Issue #154458，2026-03-27），RFC 3550 的后续扩展 [来源: rust-lang/rust#154458] |
| **`VecDeque::retain_back`** | 🔄 FCP finished / waiting | `VecDeque` 反向保留元素（与 `truncate_front` 同在 PR #151973，FCP 已完成，当前等待 review / FCP completion；已确定错过 1.97 cutoff，推迟至 1.98+） [来源: releases.rs 2026-06-23] |
| **`supertrait_item_shadowing`** | 🔄 PFCP | 允许子 trait 覆盖父 trait 的关联项（PR #150055，proposed-final-comment-period） [来源: releases.rs 2026-06-19] |
| **`alignment_type` / `ptr_alignment_type`** | 🔄 PFCP | 类型级对齐抽象，部分稳定化为 `alignment_type`（PR #154065，proposed-final-comment-period） [来源: releases.rs 2026-06-19] |
| **`stack-protector`** | 🔄 PFCP / Blocked | 栈保护编译器选项（PR #148051，proposed-final-comment-period，同时 `S-blocked`） [来源: releases.rs 2026-06-19] |
| **`breakpoint` function** | 🔄 PFCP | 标准库断点函数（PR #142824，proposed-final-comment-period） [来源: releases.rs 2026-06-19] |
| **`proc_macro_value`** | 🔄 等待 review | 过程宏（Procedural Macro）值类型支持（PR #152092，`S-waiting-on-review`） [来源: releases.rs 2026-06-23] |
| **C-variadic function definitions** | 🔄 PFCP | C 可变参数函数定义稳定化（PR #155942，`proposed-final-comment-period`，`disposition-merge`） [来源: releases.rs 2026-06-23] |
| **`size_of_val_raw` / `align_of_val_raw` / `Layout::for_value_raw`** | 🔄 等待 review | 裸值尺寸/对齐计算（PR #157572，15 days old，`S-waiting-on-review`） [来源: releases.rs 2026-06-23] |
| **`#[optimize]` attribute** | 🔄 PFCP / Blocked | 函数级优化属性（PR #157273，proposed-final-comment-period，`S-blocked`，`needs-fcp`） [来源: releases.rs 2026-06-23] |
| **`never` type (`!`)** | 🔄 FCP finished / blocked | `!` 类型最终稳定化（PR #155697，finished-final-comment-period，`disposition-merge`，`S-blocked`）。Rust 2024 Edition 下已可用，此 PR 完成跨 edition 统一 [来源: releases.rs 2026-06-23] |
| **`NonZero<T>::highest_one()` / `lowest_one()`** | 🟢 1.97 已确认 | 非零整数最高/最低 set bit 索引（PR #155147，已合并至 1.97.0 milestone） |
| **`NonZero<T>::bit_width()`** | 🟢 1.97 已确认 | 非零整数表示所需的最少位数（PR #155131，已合并至 1.97.0 milestone） |
| **`NonZero<T>::from_str_radix()`** | 🟢 1.98 已确认 | 非零整数按指定进制解析（PR #157877，已合并至 master；将进入 1.98） |
| **`char::is_control()` const-stable** | 🟢 1.97 已确认 | `char::is_control()` 在 const 上下文可用（PR #155528，已合并至 1.97.0 milestone） |
| **`derive(CoercePointee)`** | 🔄 FCP 完成 / Blocked | 自动派生 `CoerceUnsized` 的 `CoercePointee`（PR #139673，finished-final-comment-period，`disposition-merge`，但 `S-blocked`） [来源: releases.rs 2026-06-19] |
| **Associated Type Position Impl Trait (ATPIT)** | 🔄 PFCP / Blocked | 关联类型位置 `impl Trait`（PR #133820，proposed-final-comment-period，`disposition-merge`，`S-blocked`） [来源: releases.rs 2026-06-19] |
| **`local_key_cell_update`** | 🔄 等待 libs-api | `LocalKey::update` 相关 Cell 更新 API（PR #157734，12 days old，`S-waiting-on-t-libs-api`） [来源: releases.rs 2026-06-23] |
| **`#[my_macro] mod foo;` (proc_macro_hygiene)** | 🔄 PFCP | 过程宏（Procedural Macro）卫生性的一部分（PR #157857，9 days old，`proposed-final-comment-period`，`disposition-merge`，`needs-reference-pr`） [来源: releases.rs 2026-06-23] |
| **`hex_literal_case` (rustfmt)** | 🟢 1.98 已确认 | 十六进制字面量大小写风格配置（rustfmt PR #6935，已合并；将进入 1.98） [来源: TWiR 656]

> **代码示例来源**: [`crates/c08_algorithms/src/rust_197_features.rs`](../../../crates/c08_algorithms/src/rust_197_features.rs) 包含以下 API 的等效实现和 nightly 测试。

---

### 5.2 VecDeque::truncate_front

**状态**: 🔄 FCP finished / waiting（与 `retain_back` 同在 PR #151973；已确定错过 1.97 cutoff，进入 1.98 稳定化通道）

**说明**: 从双端队列**前部**截断，保留后部 `n` 个元素。与 `truncate(n)`（保留前部 `n` 个）形成对称操作。

```rust,ignore
#![feature(vec_deque_truncate_front)]

use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);
deque.truncate_front(2);
assert_eq!(deque.make_contiguous(), &[4, 5]); // 保留后部 2 个
```
---

### 5.3 VecDeque::retain_back

**状态**: 🔄 FCP finished / waiting（与 `truncate_front` 同在 PR #151973；已确定错过 1.97 cutoff，进入 1.98 稳定化通道）

**说明**: 从双端队列**尾部**开始保留满足条件的元素，与 `retain`（从头部开始）互补。

```rust,ignore
#![feature(vec_deque_retain_back)] // feature gate 可能不存在，需跟踪 PR #151973

use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);
deque.retain_back(|x| x % 2 == 0);
assert_eq!(deque.make_contiguous(), &[2, 4]); // 保留偶数
```
---

### 5.4 NonZero 位操作 API 稳定化

**状态**: 🟢 Rust 1.97.0 稳定

**说明**: `NonZero<T>` 新增位相关查询方法，便于在无需额外 unwrap 的情况下处理非零整数的位模式。

```rust
use std::num::NonZeroU32;

let n = NonZeroU32::new(0b10100).unwrap();
assert_eq!(n.highest_one(), 4); // 最高 set bit 的索引
assert_eq!(n.lowest_one(), 2);  // 最低 set bit 的索引
// bit_width 返回同类型 NonZero，表示表示 self 所需的最少位数
assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap()); // 0b10100 需要 5 bits
```
**来源**: [PR #155147](https://github.com/rust-lang/rust/pull/155147) · [PR #155131](https://github.com/rust-lang/rust/pull/155131)

---

### 5.5 `char::is_control()` const 稳定化

**状态**: 🟢 Rust 1.97.0 稳定

**说明**: `char::is_control()` 现在可在 `const` 上下文中调用。

```rust
const SPACE_CTRL: bool = ' '.is_control(); // false
const NUL_CTRL: bool = '\0'.is_control();  // true
```
**来源**: [PR #155528](https://github.com/rust-lang/rust/pull/155528)

---

### 5.6 RefCell::try_map

**状态**: 🧪 Nightly

**说明**: 在 `RefCell` 借用（Borrowing）期间进行条件性映射，若闭包（Closures）返回 `None` 则保持原值不变。

```rust,ignore
#![feature(refcell_try_map)]

use std::cell::RefCell;

let cell = RefCell::new(Some(42));
let borrowed = cell.borrow();
let mapped = RefCell::try_map(borrowed, |opt| opt.as_ref()).ok();
// 若值为 None，try_map 返回 Err，原 borrow 保持不变
```
---

### 5.7 int_format_into

**状态**: 🟢 1.98 已确认

**说明**: 将整数直接格式化到预分配缓冲区，避免 `to_string()` 的堆分配。关键优化用于 `no_std` 和嵌入式场景。

```rust,ignore
#![feature(int_format_into)]

let mut buf = [0u8; 20];
let n = 12345i32;
let written = n.format_into(&mut buf);
assert_eq!(&buf[..written], b"12345");
```
---

### 5.8 float_algebraic

**状态**: 🟢 1.98 已确认

**说明**: 浮点代数运算 intrinsics（`f32::add_algebraic` / `sub_algebraic` / `mul_algebraic` / `div_algebraic` / `rem_algebraic` 等）允许编译器在代数等价前提下重组浮点运算（类似 `-ffast-math`），可能改变舍入行为。PR #157029 已合并至 master，将进入 1.98。

```rust,ignore
#![feature(float_algebraic)]

fn fast_sum(a: f64, b: f64, c: f64) -> f64 {
    // 使用实例方法而非属性
    a.add_algebraic(b).add_algebraic(c)  // 编译器可能重排为 a + (b + c)
}
```
> ⚠️ 这会打破 IEEE 754 严格语义，仅在可接受精度损失的场景使用。
>
> **来源**: [Tracking Issue #136468](https://github.com/rust-lang/rust/issues/136468) · [Impl PR #136457](https://github.com/rust-lang/rust/pull/136457)

---

### 5.7 RandomSource / DefaultRandomSource

**状态**: 🔄 等待 libs-api

**说明**: 可插拔随机数源抽象，允许 `rand::thread_rng()`、`getrandom`、`OsRng` 等通过统一 trait 接入标准库 API。

```rust,ignore
#![feature(random_source)]

use std::random::{RandomSource, DefaultRandomSource};

fn shuffle<T, R: RandomSource>(vec: &mut [T], rng: &mut R) { /* ... */ }

let mut rng = DefaultRandomSource::new();
shuffle(&mut data, &mut rng);
```
---

### 5.8 box_vec_non_null

**状态**: 🔄 PFCP

**说明**: 允许 `Box<T>` 和 `Vec<T>` 直接转换为 `NonNull<T>`，避免空指针检查开销。

```rust,ignore
#![feature(box_vec_non_null)]

use std::ptr::NonNull;

let boxed = Box::new(42);
let ptr: NonNull<i32> = Box::into_non_null(boxed);

let vec = vec![1, 2, 3];
let (ptr, len, cap): (NonNull<i32>, usize, usize) = Vec::into_non_null(vec);
```
> **状态更新 (2026-06-28)**: 当前 nightly 上 `Vec::into_non_null` 方法尚不存在；`Box::into_non_null` 亦未探测到。示例使用 tracking issue 中的预期名称，发布日需以实际 API 为准。

---

### 5.9 C-variadic function definitions

**状态**: 🔄 PFCP

**说明**: 在 Rust 中直接定义 C 风格可变参数函数，不再需要通过 `extern "C"` 声明 + 手写 C wrapper。

```rust,ignore
#![feature(c_variadic)]

use std::ffi::{c_char, c_int};

pub unsafe extern "C" fn my_printf(fmt: *const c_char, mut args: ...) -> c_int {
    // 可变参数处理...
    0
}
```
**典型场景**: 内核 printk、嵌入式日志、FFI 回调。

---

## 六、Cargo 与工具链

### 6.1 Cargo 新特性

| 特性 | 状态 | 说明 |
|:---|:---|:---|
| `target.'cfg(..)'.rustdocflags` | ✅ 1.96 已稳定 | 条件 rustdoc 标志 |
| `cargo lint` 子命令 | 📋 RFC 阶段 | 统一的 lint 管理接口 |
| 依赖图谱可视化 | 📋 设计阶段 | `cargo tree --graph` |
| **cargo-script 稳定化** | 🔄 FCP 已结束 | [RFC 3502](https://rust-lang.github.io/rfcs//3502-cargo-script.html)+3503 已批准；frontmatter（脚本顶部 `---` 元数据块）格式同步推进；**blocker 为 edition policy（lang/edition 方面）**；Project Goals 2026 Continued 来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) |
| **Cargo `-m` shorthand** | 🟢 1.97 已确认 | `cargo -m <path>` 作为 `--manifest-path` 的简写（Cargo #16858） 来源: [Cargo CHANGELOG 1.97](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md) |
| **Cargo improved `-p` errors** | 🟢 1.97 已确认 | 拼写错误的 `-p` 参数将提示相似的 workspace member 名称（Cargo #16844） 来源: [Cargo CHANGELOG 1.97](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md) |
| **Cargo `-Zscript` edition pinning** | 🧪 Nightly | 教育用户如何为脚本固定 edition（Cargo #16851） 来源: [Cargo CHANGELOG 1.97](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md) |
| **Cargo `-Zcargo-lints`** | 🧪 Nightly | 优先使用定义的 lint 级别而非默认值；`unused_dependencies` 忽略 rustc 的 `unused_crate_dependencies` 状态（Cargo #16879, #16877） 来源: [Cargo CHANGELOG 1.97](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md) |

### 6.2 rustfmt / clippy

- **clippy**: 新增 `manual_is_ascii_check` lint（1.97 nightly）
- **rustfmt**: `imports_granularity = "Module"` 稳定性改进

---

## 七、工业级采用里程碑

### 7.1 Rust for Linux

- Linux 6.12+ 已支持 Rust 内核模块（Module）
- Rust 1.96.0 `unused_features` lint 影响内核构建流程（已适配）
- 驱动开发框架 `pin-init` 成熟

### 7.2 Android Rust 化

- AOSP 中 Rust 代码占比持续增长
- Binder、Keystore、DNS 等核心组件已 Rust 化

### 7.3 Windows 驱动 Rust 支持

- Windows 11 24H2 引入 Rust 驱动开发工具链
- WDK (Windows Driver Kit) Rust 绑定预览

---

## 八、与本项目相关的追踪任务

| 特性 | 本项目影响 | 行动项 |
| :--- | :--- | :--- |
| Async Drop | c06_async 需要新增示例 | 跟踪 nightly 进展，稳定后补充 |
| RTN | c02_type_system trait 章节需更新 | 1.97 stable 后补充 |
| Pin Ergonomics | c06_async / c04_generic 需更新 | 跟踪 RFC 进展 |
| Reborrow Traits | c04_generic 需更新 | 与 Pin Ergonomics 同步 |
| 并行前端 | docs/ 编译器基础设施需覆盖 | Phase 4 执行 |
| Cranelift | docs/ 编译器基础设施需覆盖 | Phase 4 执行 |
| build-std | c13_embedded 需补充示例 | Phase 4 执行 |
| BorrowSanitizer | c07_process / 04_formal 需覆盖 | 跟踪 nightly 进展，与 Miri/Tree Borrows 文档对齐 |
| AutoVerus | L4/L7 形式化工具需覆盖 | Phase 3 执行 |
| ESBMC | L4/L7 形式化工具需覆盖 | Phase 3 执行 |

---

## 九、参考资源

| 资源 | URL |
| :--- | :--- |
| Rust Project Goals 2026 | [rust-lang.github.io/rust-project-goals/2026](https://rust-lang.github.io/rust-project-goals/2026/) |
| Async Rust Goals | [rust-lang.github.io/rust-project-goals/2025h1/async.html](https://rust-lang.github.io/rust-project-goals/2025h1/async.html) |
| Cranelift 后端目标 | [rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html](https://rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html) |
| 并行前端目标 | [rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html](https://rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html) |
| AutoVerus | [github.com/microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis) |
| Kani 文档 | [model-checking.github.io/kani](https://model-checking.github.io/kani/) |

---

> **最后更新**: 2026-06-19
> **下次复核**: 2026-07-03（1.97 Beta 分支稳定前）
> **维护者**: 本项目知识库团队
> **状态**: 🧪 活跃跟踪中，每 2 周更新一次
> **过渡**: Rust 1.97 前沿特性预览 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

## 嵌入式测验（Embedded Quiz）

### 测验 1：Rust 1.97 预计会包含哪些主要特性？（理解层）

**题目**: Rust 1.97 预计会包含哪些主要特性？

<details>
<summary>✅ 答案与解析</summary>

截至 2026-06-21，Rust 1.97.0 仍处于 Beta 阶段，最终稳定的特性集可能调整。
当前跟踪的前沿方向包括：async drop、Return Type Notation (RTN)、Pin ergonomics、BorrowSanitizer、`core::range` 类型补全、VecDeque 新 API 等。
`gen` 块、`const trait`、`effects system` 仍处于 nightly 实验或 RFC 阶段，**不应假设它们会在 1.97 稳定**；
`unsafe_op_in_unsafe_fn` 已在 Rust 2024 Edition（1.85.0）中默认 warn，不属于 1.97 新特性。
</details>

---

### 测验 2：`if let` 临时值生命周期延长解决了什么问题？（理解层）

**题目**: `if let` 临时值生命周期（Lifetimes）延长解决了什么问题？

<details>
<summary>✅ 答案与解析</summary>

允许 `if let Some(x) = get_lock().lock().as_ref()` 这样的代码编译通过，临时值的生命周期（Lifetimes）延长到 `if` 块结束。
</details>

---

### 测验 3：`unsafe_op_in_unsafe_fn` 默认启用有什么影响？（理解层）

**题目**: `unsafe_op_in_unsafe_fn` 默认启用有什么影响？

<details>
<summary>✅ 答案与解析</summary>

在 `unsafe fn` 中调用 `unsafe` 操作需要显式 `unsafe` 块。这提高了 unsafe 代码的可读性，明确区分函数声明和内部 unsafe 操作。
</details>

---

### 测验 4：Rust 的版本发布节奏是怎样的？（理解层）

**题目**: Rust 的版本发布节奏是怎样的？

<details>
<summary>✅ 答案与解析</summary>

每 6 周发布一个 stable 版本（如 1.95、1.96、1.97）。 nightly -> beta -> stable 的三轨道模型确保新特性经过充分测试。
</details>

---

### 测验 5：如何提前体验 Rust 1.97 的特性？（理解层）

**题目**: 如何提前体验 Rust 1.97 的特性？

<details>
<summary>✅ 答案与解析</summary>

安装 nightly 工具链：`rustup install nightly`。使用 `cargo +nightly build` 编译。关注 `#![feature(...)]` 的 stabilized 状态。
</details>

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Rust 1.97 前沿特性预览** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Rust 1.97 前沿特性预览 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Rust 1.97 前沿特性预览 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Rust 1.97 前沿特性预览 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Rust 1.97 前沿特性预览 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Rust 1.97 前沿特性预览 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Rust 1.97 前沿特性预览 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Rust 1.97 前沿特性预览 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
