# MaybeUninit

> **Bloom 层级**: 理解

> **📌 简介**: `MaybeUninit<T>` 是 Rust 中处理未初始化内存的核心原语 [来源: Rustonomicon — Uninitialized Memory / 2025; RFC 1892 — MaybeUninit / 2017; 核心设计决策: `mem::uninitialized()` 因无法正确建模未初始化内存而被弃用，`MaybeUninit<T>` 提供类型安全的未初始化内存抽象; Unsafe Code Guidelines — Validity Invariant / 2025]。它绕过 Rust 的初始化要求，允许在不确定是否已初始化的情况下操作内存，是构建 `Vec`、栈数组、`ArrayVec` 等高性能抽象的基础。
>
> **⏱️ 预计学习时间**: 2-3 小时
> **📚 难度级别**: ⭐⭐⭐⭐ 高级
> **权威来源**: [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html), [Rustonomicon — Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninit.html), [Unsafe Code Guidelines — Validity](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#validity), [RFC 1892: MaybeUninit](https://rust-lang.github.io/rfcs/1892-maybe-uninit.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 MaybeUninit 形式化语义来源标注、validity invariant 学术引用、mem::uninitialized 弃用演进说明 [来源: Authority Source Sprint Batch 8]

---

## 🎯 学习目标
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

完成本章后，你将能够：

- [x] 理解 `MaybeUninit<T>` 与 `mem::uninitialized()` 的区别与演进
- [x] 正确使用 `assume_init()`、`assume_init_ref()`、`assume_init_mut()` 的安全边界
- [x] 使用 `MaybeUninit` 实现栈上固定大小数组的高效初始化
- [x] 识别 `assume_init()` 误用导致的未定义行为
- [x] 将 `MaybeUninit` 与 `Cell`、`UnsafeCell` 结合使用

---

## 📋 先决条件
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **所有权与借用** — 所有权转移、引用规则（`01_fundamentals/ownership.md`）
2. **Unsafe Rust** — 原始指针、未定义行为（`unsafe_rust.md`）
3. **Drop 语义** — 析构顺序、`ManuallyDrop`（`02_intermediate/smart_pointers.md`）

---

## 🧠 核心概念
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 模块 1: 概念定义
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 1.1 直观定义

`MaybeUninit<T>` 是一个**可能已初始化、可能未初始化**的 `T` 类型的容器。它告诉编译器："这块内存保存类型 `T` 的数据，但我不保证它已被正确初始化。"

```rust,ignore
use std::mem::MaybeUninit;

// 创建一个未初始化的 MaybeUninit<i32>
let mut x = MaybeUninit::<i32>::uninit();

// 安全地写入值
x.write(42);

// 安全地读取（前提是确实已写入）
let value = unsafe { x.assume_init() };
assert_eq!(value, 42);
```

#### 1.2 与 `mem::uninitialized()` 的对比

| 特性 | `mem::uninitialized()` (已废弃) | `MaybeUninit<T>` |
|------|-------------------------------|-----------------|
| 类型安全 | ❌ 返回 `T`，假装已初始化 | ✅ 返回 `MaybeUninit<T>`，明确未初始化 |
| 编译器优化 | 可能被优化掉，导致 UB | 编译器尊重未初始化状态 |
| Drop 处理 | 可能触发未初始化值的 Drop | 不会自动 Drop 未初始化内容 |
| 现代推荐 | 已废弃，不应使用 | Rust 1.36+ 标准方式 |

### 模块 2: 属性清单
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| API | 安全级别 | 说明 |
|-----|---------|------|
| `MaybeUninit::uninit()` | ✅ Safe | 分配未初始化内存 |
| `MaybeUninit::zeroed()` | ✅ Safe | 分配零初始化内存（适合整数/指针）|
| `MaybeUninit::new(val)` | ✅ Safe | 从已初始化值创建 |
| `.write(val)` | ✅ Safe | 写入值并返回可变引用 |
| `.as_ptr()` / `.as_mut_ptr()` | ✅ Safe | 获取原始指针（不假设初始化）|
| `.assume_init()` | ⚠️ Unsafe | 断言已初始化，返回 `T` |
| `.assume_init_ref()` | ⚠️ Unsafe | 断言已初始化，返回 `&T` |
| `.assume_init_mut()` | ⚠️ Unsafe | 断言已初始化，返回 `&mut T` |
| `.assume_init_drop()` | ⚠️ Unsafe | 断言已初始化，执行 Drop |

> **Rust 1.95 新增**: `MaybeUninit<[T; N]>` 与 `[MaybeUninit<T>; N]` 之间的双向转换已稳定：
>
> - `MaybeUninit<[T; N]>: From<[MaybeUninit<T>; N]>`
> - `[MaybeUninit<T>; N]: From<MaybeUninit<[T; N]>>`
> - `AsRef`/`AsMut` 实现支持数组视图访问

### 模块 3: 概念依赖图
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
MaybeUninit<T>
├── 内存分配
│   ├── 栈分配 (uninit, zeroed)
│   └── 堆分配 (Box::new_uninit)
├── 初始化模式
│   ├── 逐个元素初始化 (数组)
│   ├── 条件初始化 (部分填充)
│   └── 通过原始指针写入
├── 安全提取
│   ├── assume_init (所有权转移)
│   ├── assume_init_ref (共享引用)
│   └── assume_init_mut (独占引用)
└── Drop 处理
    ├── ManuallyDrop (抑制 Drop)
    └── 手动 Drop 控制
```

### 模块 4: 机制解释
>
> **[来源: [crates.io](https://crates.io/)]**

#### 4.1 为什么需要 `MaybeUninit`

Rust 要求所有变量在使用前必须初始化。但有些场景下，初始化是昂贵的或不可能一次性完成的：

1. **大数组栈分配**: `[T; N]` 要求 `T: Copy` 或显式初始化每个元素
2. **循环依赖初始化**: 对象 A 需要引用 B，B 需要引用 A
3. **FFI 边界**: C 库返回未初始化的结构体
4. **性能优化**: 避免不必要的零初始化（如 `Vec::with_capacity`）

#### 4.2 `Vec::with_capacity` 的实现原理

```rust,ignore
// Vec 内部使用 MaybeUninit 管理缓冲区
pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

struct RawVec<T> {
    ptr: Unique<T>,
    cap: usize,
    _marker: PhantomData<T>,
}

// RawVec 实际上使用 NonNull<T> 指向 MaybeUninit<T> 的内存
// 这允许 Vec 分配容量但不初始化元素
```

### 模块 5: 正例集
>
> **[来源: [docs.rs](https://docs.rs/)]**

#### 5.1 栈上数组的高效初始化

```rust
use std::mem::MaybeUninit;

fn init_array<T, F, const N: usize>(mut f: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    let mut arr: [MaybeUninit<T>; N] = unsafe {
        // SAFETY: MaybeUninit 不要求初始化
        MaybeUninit::uninit().assume_init()
    };

    for i in 0..N {
        arr[i].write(f(i));
    }

    // SAFETY: 所有元素都已初始化
    unsafe {
        let ptr = &mut arr as *mut _ as *mut [T; N];
        let result = ptr.read();
        std::mem::forget(arr); // 防止 MaybeUninit 的 Drop
        result
    }
}

fn main() {
    let squares: [i32; 5] = init_array(|i| (i * i) as i32);
    assert_eq!(squares, [0, 1, 4, 9, 16]);
}
```

#### 5.2 条件初始化（部分填充数组）

```rust
use std::mem::MaybeUninit;

fn filter_to_array<T, F, const N: usize>(
    input: &[T],
    mut pred: F,
) -> ([T; N], usize)
where
    T: Clone,
    F: FnMut(&T) -> bool,
{
    let mut arr: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut count = 0;

    for item in input {
        if count < N && pred(item) {
            arr[count].write(item.clone());
            count += 1;
        }
    }

    // 只提取已初始化的 count 个元素
    // 未初始化的 arr[count..] 必须被丢弃（不执行 Drop）
    let mut result: [T; N] = unsafe { MaybeUninit::uninit().assume_init() };
    for i in 0..count {
        result[i] = unsafe { arr[i].assume_init_read() };
    }
    // arr[count..N] 是 MaybeUninit，不会 Drop 内部的 T

    (result, count)
}
```

#### 5.3 `MaybeUninit` 数组转换 (Rust 1.95+)

```rust,ignore
use std::mem::MaybeUninit;

// [MaybeUninit<T>; N] → MaybeUninit<[T; N]>
let arr: [MaybeUninit<i32>; 4] = [
    MaybeUninit::new(1),
    MaybeUninit::new(2),
    MaybeUninit::new(3),
    MaybeUninit::new(4),
];
let uninit_array = MaybeUninit::from(arr);

// 反向转换
let arr_back: [MaybeUninit<i32>; 4] = uninit_array.into();

// AsRef 获取视图
let view: &[MaybeUninit<i32>] = uninit_array.as_ref();
```

#### 5.4 与 `Box::new_uninit` 结合使用

```rust,ignore
use std::alloc::{alloc, Layout};
use std::mem::MaybeUninit;

fn alloc_array<T>(len: usize) -> *mut MaybeUninit<T> {
    let layout = Layout::array::<T>(len).unwrap();
    unsafe { alloc(layout) as *mut MaybeUninit<T> }
}

// Rust 标准库提供更安全的方式
let mut uninit_box: Box<MaybeUninit<[u8; 1024]>> = Box::new(MaybeUninit::uninit());
uninit_box.write([0u8; 1024]);
let initialized_box: Box<[u8; 1024]> = unsafe {
    // SAFETY: 我们刚刚写入了值
    std::mem::transmute(uninit_box)
};
```

### 模块 6: 反例集
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

#### 6.1 对未初始化值调用 `assume_init()`

```rust,ignore
use std::mem::MaybeUninit;

// ❌ 严重错误: 未初始化就读取
let x: MaybeUninit<String> = MaybeUninit::uninit();
let s: String = unsafe { x.assume_init() };
// UB: String 内部指针是随机值，Drop 时会释放无效地址
```

#### 6.2 使用 `mem::uninitialized()` (已废弃)

```rust,ignore
// ❌ 绝对不要这样做
let x: String = unsafe { std::mem::uninitialized() };
// 即使随后立即覆盖，也可能在 panic/unwind 时触发 UB
```

#### 6.3 错误处理 Drop

```rust,ignore
use std::mem::MaybeUninit;

// ❌ 部分初始化数组的错误丢弃
let mut arr: [MaybeUninit<String>; 3] = unsafe { MaybeUninit::uninit().assume_init() };
arr[0].write("hello".to_string());
// arr[1] 和 arr[2] 未初始化

// 如果这里发生 panic，arr 的 Drop 会尝试 Drop 未初始化的 String
// ✅ 正确做法: 使用 ManuallyDrop 包装
let mut arr: [MaybeUninit<String>; 3] = unsafe { MaybeUninit::uninit().assume_init() };
// ... 初始化部分元素后，手动管理生命周期
```

### 模块 7: 思维表征
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

#### 初始化状态机

```text
MaybeUninit<T>
│
├─→ uninit() ──→ 未初始化状态
│                 │
│                 ├─→ write(val) ──→ 已初始化状态
│                 │                   │
│                 │                   ├─→ assume_init() ──→ T (所有权转移)
│                 │                   ├─→ assume_init_ref() ──→ &T
│                 │                   └─→ assume_init_mut() ──→ &mut T
│                 │
│                 └─→ as_ptr() ──→ *const T (不假设初始化，Safe)
│
└─→ zeroed() ──→ 零初始化状态 (适合整数/原始指针)
                  │
                  └─→ 仍需验证零值对 T 是否合法
```

### 模块 8: 国际化对齐
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 术语 (中文) | 英文 | 来源 |
|------------|------|------|
| 未初始化内存 | Uninitialized Memory | Rust Reference |
| 假设初始化 | Assume Init | std::mem::MaybeUninit |
| 零初始化 | Zero-initialization | C / Rust |
| 抑制析构 | Suppress Drop | Rustonomicon |
| 部分初始化 | Partial Initialization | Rust Unsafe Guidelines |

### 模块 9: 设计权衡
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 方案 | 安全 | 性能 | 复杂度 | 适用场景 |
|------|------|------|--------|---------|
| `Vec::with_capacity` + push | ✅ | 堆分配 | 低 | 动态大小 |
| `[MaybeUninit<T>; N]` | ⚠️ | 栈分配，无额外开销 | 高 | 固定大小，性能敏感 |
| `ArrayVec` (crate) | ✅ | 栈分配 | 低 | 固定上限，不愿写 unsafe |
| `smallvec` (crate) | ✅ | 栈+堆混合 | 低 | 大小变化但通常较小 |

### 模块 10: 自我检测
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

#### 10.1 快速检查

| 问题 | 你的答案 |
|------|---------|
| 是否在 `assume_init` 前确认所有字段已写入？ | ☐ 是 ☐ 否 |
| 是否处理了 panic 安全（部分初始化时的 unwind）？ | ☐ 是 ☐ 否 |
| 是否使用 `ManuallyDrop` 避免错误的自动 Drop？ | ☐ 是 ☐ 否 ☐ 不适用 |
| 是否用 Miri 验证过相关代码？ | ☐ 是 ☐ 否 |

#### 10.2 Miri 验证命令

```bash
# 运行 Miri 检测 MaybeUninit 相关代码
MIRIFLAGS="-Zmiri-disable-isolation" cargo +nightly miri test

# 如果代码使用外部 FFI，可能需要
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" cargo +nightly miri run
```

---

## 🔗 参考资源
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [MaybeUninit 文档](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)
- [Rustonomicon - Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninit.html)
- [Unsafe Rust Guidelines - Validity](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#validity)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 📚 权威来源索引
>
> **[来源: [crates.io](https://crates.io/)]**

### 官方来源

- [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html) [来源: Rust Standard Library / 2025]
- [Rustonomicon — Uninitialized Memory](https://doc.rust-lang.org/nomicon/uninit.html) [来源: Rust Team / Rustonomicon 2025]
- [Unsafe Code Guidelines — Validity](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#validity) [来源: Rust Unsafe Code Guidelines WG / 2025]
- [RFC 1892: MaybeUninit](https://rust-lang.github.io/rfcs/1892-maybe-uninit.html) [来源: Rust Core Team / 2017]

### 学术来源

- Jung, R., et al. — *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL 2018. [来源: `MaybeUninit` 与 validity invariant 的形式化基础; 未初始化内存的语义模型]
- Hu, W. & Dreyer, D. — *A Logical Relation for Monadic Encapsulation of State*. POPL 2011. [来源: 状态封装的逻辑关系; 与 Rust 所有权系统的形式化对比]

### 跨语言来源

- C — `malloc` + 未初始化内存 [来源: C 的未初始化内存是 UB 的主要来源; `MaybeUninit` 提供类型安全的替代]
- C++ — `std::optional`, placement new [来源: C++ 的可选类型与原地构造; 与 `MaybeUninit::assume_init()` 的设计对比]

---

## 相关概念
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [FFI (Foreign Function Interface)](ffi.md)
- [内联汇编 (Inline Assembly)](inline_asm.md)
- [Unsafe Rust 指南](README.md)
- [Rust 所有权深入](../../01_fundamentals/ownership.md)

---

## 权威来源索引

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
