> **内容分级**: [形式化]
>
> **本节关键术语**: 初始化不变式 (Initialization Invariant) · 部分初始化 (Partial Initialization) · PinInit / Init · 操作语义 (Operational Semantics) · 地址稳定性 (Location Stability) — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
# 原地初始化的操作语义
>
> **EN**: Operational Semantics of In-place Initialization
> **Summary**: Formal models for in-place initialization in Rust, covering the initialization invariant, partial initialization states, panic-safety obligations, and the `PinInit` / `Init` trait semantics used by the `pin-init` crate.
> **Rust 版本**: 1.97.0+ (Edition 2024)；`pin-init` / `pinned-init` 需 nightly
> **受众**: [形式化 / 专家]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L4 形式化语义
> **A/S/P 标记**: **S** — Structure
> **双维定位**: F×Eva — 评价初始化契约在形式模型中的充分性
> **前置概念**:
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) ·
> [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) ·
> [Pin Formal Semantics](12_pin_and_self_referential_semantics.md)
> **后置概念**:
> [In-place & Pinned Initialization Patterns](../../03_advanced/02_unsafe/11_in_place_pinned_initialization.md) ·
> [Field Projections](../../07_future/02_preview_features/23_field_projections_preview.md)
> **主要来源**:
> [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html) ·
> [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) ·
> [Rustonomicon — Working With Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninitialized.html) ·
> [Rustonomicon — Pinning](https://doc.rust-lang.org/nomicon/pin.html) ·
> [RFC 1892 — MaybeUninit](https://rust-lang.github.io/rfcs/1892-uninitialized-uninhabited.html) ·
> [Alice Ryhl — Init expressions](https://hackmd.io/@aliceryhl/BJutRcPblx) ·
> [pin-init crate docs](https://rust.docs.kernel.org/pin_init/)
>
> **内容去重提示**:
> 本文为 In-place Initialization 的 **形式化 companion**。
> 工程模式、代码示例与选型决策请见主权威页
> [`concept/03_advanced/02_unsafe/11_in_place_pinned_initialization.md`](../../03_advanced/02_unsafe/11_in_place_pinned_initialization.md)。

---

> **Bloom 层级**: L4
> **变更日志**:
> - v1.0 (2026-08-03): 初始形式化 companion，覆盖初始化不变式、部分初始化、panic safety、PinInit/Init 语义

---

## 一、初始化不变式（Initialization Invariant）

Rust 内存模型要求：任何被类型系统视为 `T` 的内存位置必须满足 `T` 的 **validity invariant**。对于未初始化内存，该不变式不成立，因此读取未初始化 `T` 是 UB。

`MaybeUninit<T>` 的类型态射可形式化为一个三态状态机：

```text
状态:
  Uninit  — 内存已分配，内容无意义
  Written — 已写入一个有效 T（但尚未被类型系统消费）
  Init    — 通过 assume_init 转为普通 T，受 validity invariant 约束

转移:
  uninit()        : () → Uninit
  write(v)        : Uninit → Written(v)
  assume_init()   : Written(v) → Init(v)   [unsafe：调用者保证当前为 Written]
  assume_init_ref : Written(v) → &T(v)     [unsafe]
  drop            : Init(v) / Written(v) → ()
```

> **[std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)** `MaybeUninit` does not drop its contents on drop unless it has been initialized; calling `assume_init` on uninitialized data is UB.

---

## 二、部分初始化与 Panic Safety

原地初始化往往以**部分初始化（partial initialization）**为中间状态：部分字段已写入，其余字段仍为 `Uninit`。若初始化函数 panic，必须 drop 已写入字段，否则资源泄漏。

### 2.1 形式化契约

对结构体 `S` 的字段集合 `F = {f₁, …, fₙ}`，定义初始化映射 `I: F → {Uninit, Written, Dropped}`。初始化过程是从全 `Uninit` 到全 `Written` 的转换。panic safety 要求：

```text
∀ f ∈ F. I(f) = Written ⟹ 在 panic 路径上调用 drop(I(f))
```

即：已初始化字段必须在 unwind 时被 drop，未初始化字段不得 drop。

### 2.2 `ManuallyDrop` 包装模式

标准工程实现用 `ManuallyDrop<MaybeUninit<T>>` 包装每个槽位，使得数组本身不会被自动 drop 未初始化的 `MaybeUninit`，同时在 panic guard 中手动清理已初始化元素。

```rust,ignore
use std::mem::{ManuallyDrop, MaybeUninit};

fn init_with_guard<F, T, const N: usize>(mut f: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    let mut slots: [ManuallyDrop<MaybeUninit<T>>; N] =
        [const { ManuallyDrop::new(MaybeUninit::uninit()) }; N];

    let mut i = 0;
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        while i < N {
            slots[i] = ManuallyDrop::new(MaybeUninit::new(f(i)));
            i += 1;
        }
    }));

    if result.is_err() {
        // Safety: slots[0..i] 已写入有效 T
        unsafe {
            for j in 0..i {
                ManuallyDrop::drop(&mut slots[j]);
            }
        }
        std::panic::resume_unwind(result.unwrap_err());
    }

    // Safety: 全部初始化完成
    let slots: [MaybeUninit<T>; N] = unsafe { std::mem::transmute_copy(&slots) };
    unsafe { std::mem::transmute_copy(&slots) }
}
```

> **注意**：真实 `Vec` / `HashMap` 的扩容路径使用更复杂的 drop guard，通常封装在 `RawVec` / `RawTable` 中。

---

## 三、`PinInit` / `Init`  Trait 语义

`pin-init` / `pinned-init` crate 用两个 trait 形式化初始化表达式：

| Trait | 目标类型 | 地址保证 | 失败处理 |
|:---|:---|:---|:---|
| `Init<T>` | 普通 `T` | 无 | `Error` |
| `PinInit<T>` | `T: !Unpin` | 初始化过程中地址不变 | `Error` |

### 3.1 操作语义

```text
Init<T>::init(self, slot: *mut T) -> Result<(), E>
  前置: slot 指向已分配、size_of::<T>() 字节、对齐的未初始化内存
  后置成功: *slot 已包含有效 T
  后置失败: 已初始化字段被 drop，*slot 回到未定义状态

PinInit<T>::init(self, slot: *mut T) -> Result<(), E>
  前置: slot 指向已分配且不会被移动的内存
  不变式: 初始化过程中 T 的地址不变
  后置成功: *slot 已包含有效 T，且 T 的地址对 safe 代码不可变
  后置失败: 同 Init
```

### 3.2 与普通 `new` 构造子的对比

```text
普通构造子:
  fn new(...) -> T   // 在栈或临时位置构造，之后 move

Init 表达式:
  fn init(...) -> impl Init<T>  // 描述如何在某块已分配内存上构造 T

PinInit 表达式:
  fn new(...) -> impl PinInit<T> // 描述如何在固定地址上构造 T: !Unpin
```

> **[Alice Ryhl — Init expressions](https://hackmd.io/@aliceryhl/BJutRcPblx)** Init expressions separate the *description* of initialization from the *location* where the value is constructed, enabling placement and pinned initialization without intermediate moves.

---

## 四、与内存模型的关系

### 4.1 Tree Borrows / Stacked Borrows

`MaybeUninit::as_mut_ptr()` 返回的裸指针在别名模型中不创建引用，因此不会引入 `&mut` 的 uniqueness 约束。只有调用 `assume_init_ref()` / `assume_init_mut()` 后，才生成具有 borrow stack / tag 的引用。

```text
MaybeUninit<T>              → 无引用，无 borrow tag
as_mut_ptr() → *mut T       → 裸指针，不受 borrow checker 追踪
write(v)    → &mut T        → 临时引用，写入后立即结束
assume_init_ref() → &T      → 创建共享引用，进入 borrow stack
assume_init_mut() → &mut T  → 创建唯一引用，进入 borrow stack
```

### 4.2 零尺寸类型（ZST）

对 ZST，`MaybeUninit<T>` 不分配内存，但语义状态机仍然成立：`Uninit` 与 `Written` 是编译期状态，不对应运行时字节。

---

## 五、边界与反例

### 反例 1：未初始化内存创建共享引用

```text
let x: MaybeUninit<i32> = MaybeUninit::uninit();
let _r: &i32 = unsafe { x.assume_init_ref() };
// UB：创建指向未初始化数据的 &T
```

### 反例 2：`PinInit` 失败后未回滚

```text
// 错误实现：fallible init 在失败时泄漏已初始化字段
impl PinInit<Self> for Device {
    fn init(self, slot: *mut Self) -> Result<(), Error> {
        // 初始化 field_a 成功
        // 初始化 field_b 失败 → field_a 未 drop，泄漏
    }
}
```

> **修正**：`pin-init` 的宏与 trait 实现自动生成 drop guard，保证失败路径回滚。

### 反例 3：将 `Init<T>` 用于 `!Unpin` 类型

```text
// 错误：对 !Unpin 类型使用 Init 而非 PinInit
fn build() -> impl Init<SelfReferential> { ... }
// 构造过程中 SelfReferential 可能被 move，导致自引用悬垂
```

---

## 六、形式化来源对齐

| 概念 | 来源 | 链接 |
|:---|:---|:---|
| Initialization invariant | Rust Reference / Rustonomicon | <https://doc.rust-lang.org/reference/memory-model.html> · <https://doc.rust-lang.org/nomicon/uninitialized.html> |
| MaybeUninit 形式化状态 | std docs | <https://doc.rust-lang.org/std/mem/union.MaybeUninit.html> |
| PinInit / Init | Alice Ryhl / pin-init | <https://hackmd.io/@aliceryhl/BJutRcPblx> · <https://rust.docs.kernel.org/pin_init/> |
| Pin 形式语义 | RFC 2349 / Rustonomicon | <https://rust-lang.github.io/rfcs/2349-pin.html> · <https://doc.rust-lang.org/nomicon/pin.html> |

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((In-place Initialization Semantics))
    Initialization Invariant
      Uninit
      Written
      Init
      Validity Invariant
    Partial Init
      Panic Safety
      Drop Guard
      ManuallyDrop
    PinInit Init
      Init<T>
      PinInit<T>
      Address Stability
      Failure Rollback
    Memory Model
      Tree Borrows
      Stacked Borrows
      ZST
    Boundaries
      UB on uninit reference
      UB on failed rollback
      UB on PinInit for Unpin misuse
```

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：`MaybeUninit<T>` 的三态是什么？（记忆层）

**题目**: 用状态机描述 `MaybeUninit<T>` 从创建到消费的过程。

<details>
<summary>✅ 答案与解析</summary>

三态：Uninit（未初始化）、Written（已写入有效 `T`）、Init（已通过 `assume_init` 转为普通 `T`）。转移由 `uninit()`、`write(v)`、`assume_init()` 触发，其中 `assume_init` 需要 unsafe 前提。
</details>

### 测验 2：panic safety 的形式化要求是什么？（分析层）

**题目**: 在部分初始化数组的 panic 路径上，哪些字段必须 drop，哪些不能 drop？

<details>
<summary>✅ 答案与解析</summary>

对已初始化的字段（`Written` 状态）必须调用 `drop`，否则资源泄漏；对未初始化字段（`Uninit`）不能调用 `drop`，因为 `drop` 会读取无效值导致 UB。
</details>
