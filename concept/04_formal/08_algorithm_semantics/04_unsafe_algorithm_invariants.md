> **内容分级**: [专家级]
>
# 不安全算法的语义不变量（Semantic Invariants of Unsafe Algorithms）

> **EN**: Semantic Invariants of Unsafe Algorithms
> **Summary**: Preconditions, postconditions, and aliasing invariants required to prove correctness of unsafe algorithms in Rust.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 系统讲解 Rust `unsafe` 算法的语义契约——从安全 API 与不安全实现之间的抽象屏障，到指针有效性、初始化、对齐、别名隔离等运行时不变量，以及循环不变量在维护 `Vec`、`MaybeUninit` 等数据结构正确性中的作用。
> **前置概念**: [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) · [Hoare Logic](../03_operational_semantics/02_hoare_logic.md)
> **后置概念**: [Separation Logic](../02_separation_logic/02_separation_logic.md) · [RustBelt](../02_separation_logic/01_rustbelt.md) · [Iterator Correctness](03_iterator_correctness.md)

---

> **来源**: [The Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html) ·
> [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [RustBelt](https://plv.mpi-sws.org/rustbelt/) ·
> [RustBelt (arXiv)](https://arxiv.org/abs/1705.05376) ·
> [Aeneas](https://aeneasverif.github.io/) ·
> [Creusot (GitHub)](https://github.com/creusot-rs/creusot) ·
> [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) ·
> [Miri](https://github.com/rust-lang/miri) ·
> [Kani](https://model-checking.github.io/kani/) ·
> [Astrauskas et al. 2019 — Prusti](https://doi.org/10.1145/3360573) ·
> [Denis 2021 — The Creusot Environment](https://hal-lara.archives-ouvertes.fr/hal-03526634/) ·
> [Müller et al. — Viper](https://doi.org/10.3233/978-1-61499-810-5-104)

---

## 📑 目录

- [不安全算法的语义不变量（Semantic Invariants of Unsafe Algorithms）](#不安全算法的语义不变量semantic-invariants-of-unsafe-algorithms)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 安全 API 与不安全实现之间的抽象屏障](#11-安全-api-与不安全实现之间的抽象屏障)
    - [1.2 指针与内存不变量](#12-指针与内存不变量)
    - [1.3 循环不变量与延迟初始化](#13-循环不变量与延迟初始化)
    - [1.4 别名与重叠不变量](#14-别名与重叠不变量)
  - [二、Rust 示例：契约的形式化表达](#二rust-示例契约的形式化表达)
    - [2.1 `swap_nonoverlapping` 的完整契约](#21-swap_nonoverlapping-的完整契约)
    - [2.2 手写 `memcpy` 的不变式](#22-手写-memcpy-的不变式)
    - [2.3 `Vec::set_len` 的循环不变量](#23-vecset_len-的循环不变量)
  - [三、反例与边界分析](#三反例与边界分析)
    - [3.1 反例：先 `set_len` 再写入元素](#31-反例先-set_len-再写入元素)
    - [3.2 边界：重叠缓冲区使用 `copy_nonoverlapping`](#32-边界重叠缓冲区使用-copy_nonoverlapping)
    - [3.3 边界：未对齐指针的读取](#33-边界未对齐指针的读取)
    - [3.4 抽象屏障必须在返回前恢复](#34-抽象屏障必须在返回前恢复)
  - [四、验证工具](#四验证工具)
  - [五、嵌入式测验（Embedded Quiz）](#五嵌入式测验embedded-quiz)
    - [测验 1：`unsafe` 算法的契约由谁负责？](#测验-1unsafe-算法的契约由谁负责)
    - [测验 2：以下循环中，`v.set_len(n)` 应该在何时调用？](#测验-2以下循环中vset_lenn-应该在何时调用)
    - [测验 3：`std::ptr::copy_nonoverlapping` 的“非重叠”条件是？](#测验-3stdptrcopy_nonoverlapping-的非重叠条件是)
    - [测验 4：下面哪个操作最可能导致未对齐读取？](#测验-4下面哪个操作最可能导致未对齐读取)
    - [测验 5：安全 API 返回时，下列哪项必须成立？](#测验-5安全-api-返回时下列哪项必须成立)
  - [六、相关概念](#六相关概念)
  - [七、🧭 思维导图（Mindmap）](#七-思维导图mindmap)

---

## 一、核心概念

### 1.1 安全 API 与不安全实现之间的抽象屏障

Rust 的 `unsafe` 算法通常呈现为一种**洋葱结构**：

```text
┌─────────────────────────────────────┐
│  公开安全 API                        │  ← 调用者无需 unsafe
│  fn foo(&mut self)                  │
├─────────────────────────────────────┤
│  内部 unsafe 实现                    │  ← 由实现者保证契约
│  unsafe { ... }                     │
├─────────────────────────────────────┤
│  平台/硬件原语                       │  ← 编译器无法验证
│  ptr::read / write / copy ...       │
└─────────────────────────────────────┘
```

用 [Hoare 逻辑](../03_operational_semantics/02_hoare_logic.md) 的语言描述：

```text
安全包装器:
  { P_safe } safe_api(input) { Q_safe }

内部 unsafe 实现:
  { P_unsafe } unsafe_impl { Q_unsafe }

抽象屏障要求:
  P_safe(input) ⇒ P_unsafe(prepare(input))
  Q_unsafe(result) ⇒ Q_safe(output)
```

也就是说，**安全函数负责在进入 unsafe 之前建立所有前置条件，并在返回之前确保后置条件成立**。unsafe 块内的临时违反（例如 `Vec::set_len` 后的未初始化间隙）必须在安全 API 返回前被修复。

### 1.2 指针与内存不变量

`unsafe` 算法最常见的错误来源是对**裸指针契约**的违反。下表总结了关键不变量：

| 不变量 | 含义 | 典型违反 | Rust 语义 |
|---|---|---|---|
| **有效性** | 指针指向已分配且未释放的内存 | 使用悬垂指针、空指针解引用 | `*ptr` 要求 `ptr` 非空且对齐 |
| **初始化** | 读取前内存已写入有效值 | 读取 `MaybeUninit::uninit()` | `ptr::read` 读取未初始化内存是 UB |
| **对齐** | 地址是 `align_of::<T>()` 的倍数 | 将 `u8` 指针强转为 `u32` 指针 | 未对齐读取/写入是 UB |
| **非重叠** | `copy_nonoverlapping` 的源与目标不重叠 | 同一缓冲区内向前/向后复制 | 重叠时必须使用 `ptr::copy` |
| **容量边界** | 写入不超出分配容量 | `set_len` 后越界写入 | 超出分配容量的写入是 UB |
| **别名隔离** | `&mut T` 与 `&T` 不共存 | 在持有 `&mut` 时创建 `&` | 违反借用规则是 UB |

> **认知功能**: 这些不变量不是“建议”，而是 `unsafe` 代码的**逻辑前置条件**。借用检查器在安全 Rust 中自动维护它们；进入 `unsafe` 后，维护责任完全落在开发者身上。

### 1.3 循环不变量与延迟初始化

在逐元素构建 `Vec<T>` 或 `MaybeUninit<T>` 的循环中，不变量必须同时跟踪**逻辑进度**和**内存状态**。

典型模式：

```text
let mut v: Vec<T> = Vec::with_capacity(n);
let ptr = v.as_mut_ptr();

for i in 0..n {
    // 循环不变量 I:
    //   1. v.capacity() >= n
    //   2. ptr.add(j) 在 [0, i) 范围内已初始化
    //   3. ptr.add(i..n) 未初始化
    unsafe { ptr.add(i).write(f(i)); }
}

// 终止时: [0, n) 全部初始化
unsafe { v.set_len(n); }
```

关键洞察：

- `Vec::set_len` 的后置条件是“前 `n` 个元素已初始化”；
- 如果提前调用 `set_len`，`Vec` 的 `Drop` 实现会在析构时尝试释放未初始化内存，导致 **use-after-free** 或 **未初始化读取**；
- 因此 `set_len` 的调用点本身就是**循环不变量成立的见证**。

### 1.4 别名与重叠不变量

`ptr::copy_nonoverlapping::<T>(src, dst, count)` 要求：

```text
1. src 与 dst 均有效，且各自覆盖 count * size_of::<T>() 字节
2. src 与 dst 指向的内存区域互不重叠
3. T 的对齐要求被满足
```

如果源与目标重叠，必须使用 `ptr::copy`，它会按正确方向逐元素复制。违反非重叠条件在某些平台可能只是得到错误结果，但在 Rust 语义中属于**未定义行为（UB）**，因为优化器可能据此假设两块内存独立。

---

## 二、Rust 示例：契约的形式化表达

### 2.1 `swap_nonoverlapping` 的完整契约

下面是一个手动实现的非重叠交换函数，展示了如何在注释中显式写出 Hoare 式契约：

```rust,ignore
/// 交换两个非重叠数组前缀的内容。
///
/// # Safety
/// - `a` 与 `b` 必须分别指向至少 `count` 个已初始化的 `T`。
/// - `a..a+count` 与 `b..b+count` 的内存区域不能重叠。
/// - `a` 与 `b` 必须满足 `T` 的对齐要求。
///
/// # Postcondition
/// - 调用后，`a[i]` 与 `b[i]` 的值被交换，其中 `0 <= i < count`。
unsafe fn swap_nonoverlapping<T>(a: *mut T, b: *mut T, count: usize) {
    // 前置条件：a、b 有效、已初始化、非重叠、对齐
    for i in 0..count {
        let ai = a.add(i);
        let bi = b.add(i);

        // 临时读取（要求源位置已初始化）
        let tmp = std::ptr::read(ai);
        std::ptr::copy(bi, ai, 1);
        std::ptr::write(bi, tmp);
    }
}
```

> 注意：真实标准库使用 `std::ptr::swap_nonoverlapping`，效率更高，但契约语义相同。

### 2.2 手写 `memcpy` 的不变式

```rust,ignore
/// 将 `count` 个 `T` 从 `src` 复制到 `dst`。
///
/// # Safety
/// - `src` 与 `dst` 均有效，且各自覆盖 `count * size_of::<T>()` 字节。
/// - `src` 与 `dst` 指向的内存区域**不重叠**。
/// - `src` 中前 `count` 个元素已初始化。
/// - `dst` 中前 `count` 个元素可以覆写（是否已初始化均可，因为会覆盖）。
unsafe fn memcpy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
    std::ptr::copy_nonoverlapping(src, dst, count);
}
```

不变量到 Rust 原语的映射：

| 契约项 | 代码/检查 |
|---|---|
| 源已初始化 | `ptr::read` / `copy_nonoverlapping` 读取前必须成立 |
| 目标有效 | `dst` 必须指向已分配且足够大的内存 |
| 非重叠 | 调用者负责；违反则使用 `ptr::copy` |
| 对齐 | `dst` 与 `src` 必须满足 `align_of::<T>()` |

### 2.3 `Vec::set_len` 的循环不变量

```rust,ignore
fn extend_from_generator<T, F>(n: usize, mut f: F) -> Vec<T>
where
    F: FnMut(usize) -> T,
{
    let mut v = Vec::with_capacity(n);
    let ptr = v.as_mut_ptr();

    for i in 0..n {
        // 不变量: ptr[0..i) 已初始化, ptr[i..n) 未初始化, capacity >= n
        unsafe {
            ptr.add(i).write(f(i));
        }
    }

    // 终止时: ptr[0..n) 全部初始化, set_len 的后置条件成立
    unsafe {
        v.set_len(n);
    }

    v
}
```

> **认知功能**: `set_len` 不是“调整长度”的普通 setter，而是对**循环不变量成立**的断言。它的前置条件是“前 `n` 个槽位已经包含合法值”。

---

## 三、反例与边界分析

### 3.1 反例：先 `set_len` 再写入元素

```rust,ignore
fn buggy_vec<T: Default>() -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(4);

    unsafe {
        // ❌ 错误: 先声明长度，但元素尚未初始化
        v.set_len(4);
    }

    // 此时 v[0..4] 的内容是未初始化内存。
    // 若 T 实现了 Drop，离开作用域时会调用 drop 垃圾指针 → use-after-free。
    // 若读取 v[0]，则是未初始化读取 → UB。

    v
}
```

正确顺序：先写入，再 `set_len`。

### 3.2 边界：重叠缓冲区使用 `copy_nonoverlapping`

```rust,ignore
fn buggy_shift<T: Copy>(buf: &mut [T]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        // ❌ 错误: src 与 dst 指向同一块缓冲区，区域重叠
        std::ptr::copy_nonoverlapping(ptr, ptr.add(1), buf.len() - 1);
    }
}
```

> 应使用 `std::ptr::copy`，它会处理重叠内存的正确复制方向。

### 3.3 边界：未对齐指针的读取

```rust,ignore
fn buggy_read_u32(bytes: &[u8]) -> u32 {
    assert!(bytes.len() >= 4);
    let ptr = bytes.as_ptr() as *const u32;
    unsafe {
        // ❌ 错误: bytes.as_ptr() 可能只按 1 字节对齐，而 u32 需要 4 字节对齐
        ptr.read()
    }
}
```

正确做法：使用 `ptr.read_unaligned()` 或先复制到对齐的局部变量。

### 3.4 抽象屏障必须在返回前恢复

```rust,ignore
struct Buffer<T> {
    inner: Vec<T>,
}

impl<T> Buffer<T> {
    /// 安全 API: 将元素追加到缓冲区。
    pub fn push(&mut self, value: T) {
        self.inner.push(value);
    }

    /// 安全 API: 将 inner 长度翻倍，未初始化部分由调用者后续填充。
    /// ❌ 错误: 公开安全函数将未初始化状态暴露给调用者，破坏了抽象屏障。
    pub fn reserve_doubled(&mut self) {
        let new_cap = self.inner.capacity() * 2;
        self.inner.reserve(new_cap);
        unsafe {
            self.inner.set_len(new_cap);
        }
    }
}
```

安全 API 返回时，`self.inner` 必须满足 `Vec<T>` 的所有不变量：每个在 `len` 范围内的元素都已初始化。

### 3.5 编译期捕捉：未对齐指针读取

`std::ptr::read` 要求指针对齐到 `align_of::<T>()`。下面用 `const` 断言形式化该对齐要求：从地址 `1` 读取 `u32` 违反了 4 字节对齐约束，对应现实中 `&[u8]` 强转为 `*const u32` 后直接使用 `ptr.read()` 的错误。

```rust,compile_fail
// 读取 T 要求指针按 align_of::<T>() 对齐
const fn require_aligned(addr: usize, align: usize) {
    assert!(addr % align == 0, "unaligned pointer read");
}

// 错误：地址 1 不是 u32（对齐 4）的合法起始地址
const _: () = require_aligned(1, 4);

fn main() {}
```

> **修正**: 对可能未对齐的内存使用 `std::ptr::read_unaligned()`，或先复制到对齐的局部变量。直接用 `ptr.read()` 读取未对齐地址是 UB。
> (Source: [The Rustonomicon — What is Undefined Behavior?](https://doc.rust-lang.org/nomicon/what-unsafe-does.html))

---

### 3.6 编译期捕捉：重叠缓冲区使用 `copy_nonoverlapping`

`std::ptr::copy_nonoverlapping` 要求源与目标内存区域互不重叠。下面用 `const` 断言形式化该非重叠条件：同一块缓冲区中 `src=0, dst=1, len=3` 的区域发生重叠，对应现实中 `copy_nonoverlapping(ptr, ptr.add(1), buf.len() - 1)` 的错误用法。

```rust,compile_fail
// copy_nonoverlapping 要求 [src, src+len) 与 [dst, dst+len) 不重叠
const fn require_non_overlapping(src_start: usize, dst_start: usize, len: usize) {
    assert!(
        dst_start >= src_start + len || src_start >= dst_start + len,
        "copy_nonoverlapping requires non-overlapping regions"
    );
}

// 错误：src=0, dst=1, len=3 在同一块缓冲区中重叠
const _: () = require_non_overlapping(0, 1, 3);

fn main() {}
```

> **修正**: 重叠内存复制必须使用 `std::ptr::copy`，它会按正确方向逐元素处理；`copy_nonoverlapping` 在重叠时产生 UB。
> (Source: [std::ptr::copy_nonoverlapping](https://doc.rust-lang.org/std/ptr/fn.copy_nonoverlapping.html))

---

### 3.7 编译期捕捉：先 `set_len` 再初始化元素

`Vec::set_len` 的前置条件是"新长度范围内的元素已经初始化"。下面用 `const` 断言形式化该循环不变量：已初始化元素数为 `0` 时却将长度设为 `4`，会把未初始化内存暴露为合法元素，导致 Drop 时释放垃圾指针。

```rust,compile_fail
// 循环不变量：set_len(new_len) 要求 [0, new_len) 已初始化
const fn set_len_requires_init(init_count: usize, new_len: usize) {
    assert!(
        init_count >= new_len,
        "set_len before initialization: uninitialized slots would be exposed"
    );
}

// 错误：已初始化 0 个元素，却设置 len 为 4
const _: () = set_len_requires_init(0, 4);

fn main() {}
```

> **修正**: 正确顺序是先通过 `ptr.add(i).write(...)` 写入全部元素，再统一调用 `v.set_len(n)`。`set_len` 的调用点是"初始化已完成"的见证，不可前置。
> (Source: [The Rustonomicon — Vec](https://doc.rust-lang.org/nomicon/vec.html))

---

## 四、验证工具

| 工具 | 检查方式 | 适用场景 |
|---|---|---|
| **Miri** | 动态解释执行，检测 UB | 指针有效性、别名规则、未初始化读取、数据竞争 |
| **Kani** | 有界模型检测 | 对给定 harness 验证 `unsafe` 块是否违反内存不变量 |
| **Prusti** | 分离逻辑 + SMT | 用 `#[requires]` / `#[ensures]` 显式写出前后置条件 |
| **Creusot** | Why3 / MLCFG | 对 Rust 子集进行精化/契约式验证 |
| **Aeneas** | 函数式翻译 + Coq/Lean | 手工形式化证明，适合关键算法 |

> **建议工作流**: 先用 Miri 在测试集上跑通，再用 Kani 对边界输入做有界验证，最后对核心路径补充 Prusti/Creusot 契约。Prusti 将 Rust 类型系统与 Viper 的权限模型结合，用于模块化规约与验证（Astrauskas et al., 2019）；Creusot 基于 Why3 / Coma 中间语言，将 Pearlite 规格翻译为最弱前置条件（Denis, 2021）；Viper 则是支撑 Prusti 等工具的中间验证语言和权限推理基础设施（Müller et al.）。这样能在工程成本与验证强度之间取得平衡。

---

## 五、嵌入式测验（Embedded Quiz）

### 测验 1：`unsafe` 算法的契约由谁负责？

```text
pub fn safe_api(x: &mut [u32]) { unsafe { raw_impl(x.as_mut_ptr(), x.len()); } }
```

如果 `raw_impl` 要求 `ptr` 非空且 `len > 0`，这个前置条件应由谁保证？

- A. `raw_impl` 的调用者，即 `safe_api`
- B. `safe_api` 的调用者
- C. Rust 编译器

<details>
<summary>✅ 答案</summary>

**A. `raw_impl` 的调用者，即 `safe_api`**。

安全包装器的职责是把公开接口的前置条件转换为 unsafe 实现所需的前置条件。只要 `safe_api` 返回时公开接口的后置条件成立，调用者就无需知道内部 unsafe 契约。

</details>

---

### 测验 2：以下循环中，`v.set_len(n)` 应该在何时调用？

```rust,ignore
let mut v = Vec::with_capacity(n);
let ptr = v.as_mut_ptr();
for i in 0..n {
    unsafe { ptr.add(i).write(f(i)); }
    // (A) 在这里调用 v.set_len(i + 1)
}
// (B) 在循环结束后调用 v.set_len(n)
```

- A. 每次迭代后都调用
- B. 循环结束后统一调用
- C. 两种写法等价

<details>
<summary>✅ 答案</summary>

**B. 循环结束后统一调用**（或在每次写入后逐步调用亦可，但需保证已写入部分连续）。

关键是 `set_len` 的前置条件：长度范围内的元素必须已初始化。如果只在循环结束后调用，整个 `[0, n)` 区间在调用时都已初始化；如果每次迭代后调用，也能维持不变量，但需注意 panic 安全。通常推荐在循环结束后统一调用，并配合 `AbortOnDrop` 等策略处理异常。

</details>

---

### 测验 3：`std::ptr::copy_nonoverlapping` 的“非重叠”条件是？

- A. 一种性能提示，违反后只是结果可能错误
- B. 一种安全要求，违反后是未定义行为
- C. 仅当 `T` 实现 `Copy` 时才需要

<details>
<summary>✅ 答案</summary>

**B. 一种安全要求，违反后是未定义行为**。

`copy_nonoverlapping` 向编译器承诺两块内存独立，优化器可能据此重排读写。重叠时应使用 `std::ptr::copy`。

</details>

---

### 测验 4：下面哪个操作最可能导致未对齐读取？

- A. `let x: u32 = *(ptr as *const u32);`，其中 `ptr` 来自 `&[u8]`
- B. `ptr::read(ptr as *const u8)`
- C. `std::ptr::copy_nonoverlapping(src, dst, 1)`，其中 `src` 与 `dst` 均为 `*mut u32`

<details>
<summary>✅ 答案</summary>

**A**。

`&[u8]` 的起始地址只保证 1 字节对齐，而 `*const u32` 要求 4 字节对齐。应使用 `read_unaligned` 或先复制到对齐的栈变量。

</details>

---

### 测验 5：安全 API 返回时，下列哪项必须成立？

- A. unsafe 块内部的临时不变量可以保留
- B. 公开类型的所有不变量必须恢复
- C. 只要没有 panic，临时违反无关紧要

<details>
<summary>✅ 答案</summary>

**B. 公开类型的所有不变量必须恢复**。

抽象屏障要求：安全函数返回后，调用者看到的 `Vec`、`Box` 等类型的内部不变量必须完整成立。unsafe 块内的临时违反（如未初始化长度）必须在返回前修复。

</details>

---

## 六、相关概念

- [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) — `unsafe` 关键字的能力与责任边界
- [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) — Rust 的内存模型、别名规则与 happens-before 关系
- [Hoare Logic](../03_operational_semantics/02_hoare_logic.md) — 前置/后置条件与循环不变量的形式化基础
- [Separation Logic](../02_separation_logic/02_separation_logic.md) — 指针程序的形式化推理
- [RustBelt](../02_separation_logic/01_rustbelt.md) — Rust 类型系统的 Iris 高阶分离逻辑证明
- [Iterator Correctness](03_iterator_correctness.md) — `Iterator` trait 的语义规范

---

> **权威来源**: [The Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html) ·
> [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [RustBelt](https://plv.mpi-sws.org/rustbelt/) ·
> [Miri](https://github.com/rust-lang/miri) ·
> [Kani](https://model-checking.github.io/kani/)
>
> **文档版本**: 1.1
> **最后更新**: 2026-07-30
> **状态**: ✅ 新建权威页

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [The Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html) | ✅ 一级 | `unsafe` 块与契约权威定义 |
| [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) | ✅ 一级 | Rust 不安全编程与 UB 边界 |
| [RustBelt](https://plv.mpi-sws.org/rustbelt/) | ✅ 一级 | Rust 类型系统的 Iris 高阶分离逻辑证明 |
| [Miri](https://github.com/rust-lang/miri) | ✅ 一级 | 动态检测 UB 的解释器 |
| [Kani](https://model-checking.github.io/kani/) | ✅ 一级 | Rust 有界模型检测器 |
| [Astrauskas et al. 2019 — Leveraging Rust Types for Modular Specification and Verification](https://doi.org/10.1145/3360573) | ✅ 一级 | Prusti 在 Rust 上的模块化验证方法 |
| [Denis 2021 — The Creusot Environment for the Deductive Verification of Rust Programs](https://hal-lara.archives-ouvertes.fr/hal-03526634/) | ✅ 一级 | Creusot 演绎验证环境技术报告 |
| [Müller et al. — Viper: A Verification Infrastructure for Permission-Based Reasoning](https://doi.org/10.3233/978-1-61499-810-5-104) | ✅ 一级 | Prusti 等工具依赖的权限推理中间语言 |

---

## 七、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((不安全算法的语义不变量))
    抽象屏障
      安全 API 包装
      unsafe 实现契约
      返回前恢复不变量
    内存不变量
      指针有效性
      初始化状态
      对齐要求
      容量边界
    别名与重叠
      copy_nonoverlapping
      重叠使用 ptr::copy
      &mut 独占借用
    循环不变量
      Vec::set_len 见证
      MaybeUninit 延迟初始化
      初始化区间追踪
    反例与边界
      先 set_len 后写入
      重叠缓冲区
      未对齐读取
    验证工具
      Miri 动态检查
      Kani 有界证明
      Prusti Creusot 契约
```

> **认知功能**: 本 mindmap 从「不安全算法的语义不变量」的章节结构提炼，一级分支对应核心主题，叶子节点为关键子概念，可作为本页的快速导航与复习索引。
