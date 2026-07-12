# UnsafePinned 预研：可变引用别名语义的精确标注

> **代码状态**: ✅ 含 nightly 实测示例（`#![feature(unsafe_pinned)]`，rustc 1.99.0-nightly 2026-07-10 通过）
>
> **EN**: UnsafePinned Preview
> **Summary**: Preview of `core::pin::UnsafePinned` (RFC 3467) — the wrapper type that opts a field out of `&mut`-based aliasing guarantees, replacing the unsound `Unpin`-based noalias hack for self-referential generators and futures.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: 🧪 Nightly 实验性（library feature `unsafe_pinned`；tracking issue rust-lang/rust#125735）
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: stable 1.97.0 报 E0658；nightly 1.99.0 可用
> **预计稳定**: 待定（阻塞于 opsem 决议：issue #137750 — `UnsafePinned` 是否同时承担 `UnsafeCell` 式共享引用别名豁免）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析 UnsafePinned 别名语义
> **定位**: 跟踪 [RFC 3467](https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html) 引入的 `UnsafePinned<T>`，说明其与 `UnsafeCell`/`PhantomPinned`/`Unpin` 的语义分工，以及对自引用 Future 降级的安全性影响。
> **前置概念**: [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) · [Pin 与 Unpin](../../03_advanced/01_async/08_pin_unpin.md) · [Rust 内存模型](../../03_advanced/02_unsafe/06_memory_model.md) · [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md)
> **后置概念**: [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) · [Version Tracking](../00_version_tracking/01_rust_version_tracking.md) · [嵌入式系统生态](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md)
> **定理链**: N/A — 描述性/跟踪性文档，不涉及形式化定理链
---

> **来源**: [RFC 3467 — UnsafePinned](https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html) ·
> [std docs — `core::pin::UnsafePinned`](https://doc.rust-lang.org/std/pin/struct.UnsafePinned.html) ·
> [Tracking Issue #125735](https://github.com/rust-lang/rust/issues/125735) ·
> [Issue #137750 — UnsafePinned 与安全 Pin::deref 的交互决议](https://github.com/rust-lang/rust/issues/137750) ·
> [The Rustonomicon — Aliasing](https://doc.rust-lang.org/nomicon/aliasing.html)

## 📑 目录

- [UnsafePinned 预研：可变引用别名语义的精确标注](#unsafepinned-预研可变引用别名语义的精确标注)
  - [📑 目录](#-目录)
  - [一、动机：Unpin 不能承担别名豁免](#一动机unpin-不能承担别名豁免)
  - [二、三种"别名影响类型"的语义分工](#二三种别名影响类型的语义分工)
  - [三、编译器与 Miri 层面的影响](#三编译器与-miri-层面的影响)
  - [四、实测示例（nightly 1.99.0）](#四实测示例nightly-1990)
  - [五、稳定化阻塞项](#五稳定化阻塞项)
  - [六、反命题与边界分析](#六反命题与边界分析)
  - [⚠️ 反例与陷阱](#️-反例与陷阱)
  - [权威来源索引](#权威来源索引)

## 一、动机：Unpin 不能承担别名豁免

背景问题（RFC 3467 §Motivation）：Rust 的 `&mut T` 向 LLVM 发出 `noalias` 属性，承诺该引用独占所指向内存。但**自引用生成器/异步 Future** 内部持有指向自身字段的指针——字段被 `Pin<&mut Self>` 钉住后，内部指针与 `&mut` 共存，`noalias` 承诺即被违反。

历史上编译器用一个**未文档化的 hack**：对含 `impl !Unpin` 的类型不发射 `noalias`。这把"钉住语义"（`Unpin` 是移动语义标记）与"别名语义"（noalias 是内存模型属性）错误耦合，且对用户代码不可见、不可审计。

`UnsafePinned<T>` 的引入将两种语义**解耦**：

- `Unpin` / `PhantomPinned`：只表达**移动语义**（值能否安全地按位移动）；
- `UnsafePinned<T>`：表达**别名语义**（字段可能被外部指针别名，禁止编译器对经过它的 `&mut` 假设独占）。

## 二、三种"别名影响类型"的语义分工

RFC 3467 §Reference-level explanation 给出的对比矩阵（本页按 Rustonomicon 风格重述）：

| 类型 | 豁免对象 | 语义 |
|:---|:---|:---|
| `UnsafeCell<T>` | `&UnsafeCell<T>`（共享引用） | 禁用共享引用背后的不可变别名假设；安全包装（`RefCell`）可在 `&` 后暴露可变性（内部可变性，Interior Mutability） |
| `UnsafePinned<T>` | `&mut UnsafePinned<T>`（可变引用） | 禁用可变引用的独占别名假设；安全包装（`Pin<&mut MyFuture>`）可暴露"被钉住的可变引用" |
| `PhantomPinned` | 无（零大小标记） | 仅 `!Unpin` 标记；RFC 3467 计划将其定义为 `UnsafePinned<()>` |

关键不变量：`UnsafePinned<&mut T>`（按值完全拥有）**不特殊**，等价于 `&mut T`；`&UnsafePinned<T>` 也不特殊。特殊性只发生在 `&mut UnsafePinned<T>` 这一组合上。

## 三、编译器与 Miri 层面的影响

RFC 3467 列出的实现级变更：

1. **`UnsafeUnpin` 自动 trait**（内部实现细节，暂不暴露）：类似 `Freeze`，当类型不含按值 `UnsafePinned` 时自动实现。
2. **`noalias` 发射条件**：`&mut` 上的 `noalias` 仅对 `UnsafeUnpin` 类型发射（取代旧的 `Unpin` hack）。
3. **Niche 布局**：`UnsafePinned` 阻断 niche 优化（与 `UnsafeCell` 类似，参见 [Type Layout](../../04_formal/05_rustc_internals/08_type_layout.md)）。
4. **Miri 模型**：在 `UnsafePinned` 内部执行 `SharedReadWrite` 重标记（retag），取代旧的基于 `Unpin` 的 hack；这与 [Tree Borrows](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) 的别名树节点语义直接对应。
5. **生成器/异步降级**：跨 yield/await 点取地址的局部变量字段，降级后必须包裹 `UnsafePinned`。

## 四、实测示例（nightly 1.99.0）

以下示例在 `rustc 1.99.0-nightly (375b1431b 2026-07-10) --edition 2024` 实测编译通过：

```rust,ignore
// rust-toolchain: nightly；#![feature(unsafe_pinned)]
#![feature(unsafe_pinned)]
use std::pin::UnsafePinned;

// 模拟自引用 Future 的降级产物：state 可被安全移动，
// pinned_field 可能被内部自引用指针别名
struct Fut {
    state: u8,
    pinned_field: UnsafePinned<u8>,
}

fn main() {
    let f = Fut { state: 0, pinned_field: UnsafePinned::new(1) };
    assert_eq!(f.state, 0);
    // &mut f 不再对 pinned_field 部分承诺 noalias
}
```

在 stable 1.97.0 上同代码按预期报 `E0658: use of unstable library feature unsafe_pinned`（实测，tracking issue #125735）。

## 五、稳定化阻塞项

- **issue #137750（opsem 决议）**：由于 `Pin::deref` 是安全操作，任何时刻都可创建指向 Future 的共享引用；若 `UnsafePinned` 不同时具备 `UnsafeCell` 式共享引用别名豁免，Tree Borrows 下安全代码即可触发 UB。Ralf Jung 的结论倾向"必须同时具备"。该决议直接决定稳定化形态。
- **迁移路径**：`PhantomPinned = UnsafePinned<()>` 的等价定义、标准库中 `impl !Unpin` 用例的替换节奏。
- **`dereferenceable` 属性**：`Unpin` 目前也影响 `dereferenceable` 发射，`UnsafePinned` 是否继承该影响待 LLVM 侧语义明确。

## 六、反命题与边界分析

- **反命题 1：「UnsafePinned 是新的 UnsafeCell」**——不准确。它豁免的是 `&mut` 独占性而非 `&` 不可变性；是否兼具后者正是 issue #137750 的未决问题。
- **反命题 2：「安全代码需要关心 UnsafePinned」**——错误。它是不安全抽象作者的标注工具；安全代码经 `Pin<&mut T>` API 间接受益，无需直接命名该类型。
- **边界**：`UnsafePinned` 不改变 [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) 的内容，它改变的是**编译器被允许假设什么**——即把既有的未文档化行为转化为显式、可审计的语言机制。

## ⚠️ 反例与陷阱

**陷阱：对 `static mut` 取引用制造别名**。`UnsafePinned` 预研的出发点正是「别名影响类型」需要精确标注；2024 edition 已把 `static_mut_refs` 提升为 deny，最常见的别名来源之一在编译期即被拦截：

```rust,compile_fail
static mut COUNTER: u32 = 0;

fn bump() {
    let r: &mut u32 = unsafe { &mut COUNTER }; // 全局可变状态的引用别名
    *r += 1;
}
```

rustc 1.97.0（edition 2024）实测：`error: creating a mutable reference to mutable static`（`static_mut_refs` deny）。

**修正**：进程级可变状态用 `AtomicU32`（无别名问题）或 `SyncUnsafeCell`/`UnsafePinned`（nightly）显式标注内部可变性：

```rust
use std::sync::atomic::{AtomicU32, Ordering};
static COUNTER: AtomicU32 = AtomicU32::new(0);
fn bump() { COUNTER.fetch_add(1, Ordering::Relaxed); }
```

## 权威来源索引

> **权威来源**: [RFC 3467 — UnsafePinned](https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html) ·
> [std docs — `core::pin::UnsafePinned`](https://doc.rust-lang.org/std/pin/struct.UnsafePinned.html) ·
> [Tracking Issue #125735](https://github.com/rust-lang/rust/issues/125735) ·
> [Issue #137750](https://github.com/rust-lang/rust/issues/137750) ·
> [The Rustonomicon — Aliasing](https://doc.rust-lang.org/nomicon/aliasing.html) ·
> [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
>
> 以上链接于 2026-07-12 经 curl 实测全部返回 HTTP 200；代码示例经 `rustc 1.99.0-nightly --edition 2024` 实测编译通过（stable 1.97.0 按预期报 E0658）。
