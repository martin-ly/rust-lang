# Rust 对齐知识综合指南

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **文档定位**: 全面覆盖 Rust 中「对齐」相关的各类知识
> **关联**: [type_system.md](./quick_reference/type_system.md) | [strings_formatting_cheatsheet.md](./quick_reference/strings_formatting_cheatsheet.md)

---

## 📋 目录 {#-目录}

- [Rust 对齐知识综合指南](#rust-对齐知识综合指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [一、概念分类](#一概念分类)
  - [二、内存对齐（核心）](#二内存对齐核心)
    - [2.0 为何要对齐（Why Alignment Matters）](#20-为何要对齐why-alignment-matters)
    - [2.1 基本概念](#21-基本概念)
    - [2.2 常用 API](#22-常用-api)
    - [2.3 repr 与对齐（完整谱系）](#23-repr-与对齐完整谱系)
    - [2.4 字段重排序优化](#24-字段重排序优化)
    - [2.5 对齐计算（Rust 1.92+）](#25-对齐计算rust-192)
    - [2.6 Layout API（自定义分配）](#26-layout-api自定义分配)
    - [2.7 平台差异](#27-平台差异)
  - [三、格式化对齐](#三格式化对齐)
  - [四、unsafe 与对齐](#四unsafe-与对齐)
    - [4.1 裸指针解引用前提与 UB 情形](#41-裸指针解引用前提与-ub-情形)
    - [4.2 未对齐访问](#42-未对齐访问)
    - [4.3 transmute 对齐约束](#43-transmute-对齐约束)
  - [五、缓存行对齐与并发](#五缓存行对齐与并发)
    - [5.1 伪共享（False Sharing）](#51-伪共享false-sharing)
    - [5.2 数据局部性：AoS vs SoA](#52-数据局部性aos-vs-soa)
    - [5.3 工具验证与量化数据](#53-工具验证与量化数据)
  - [六、权威来源（非技术对齐）](#六权威来源非技术对齐)
  - [七、对齐选型决策树](#七对齐选型决策树)
  - [八、相关文档与示例](#八相关文档与示例)
    - [项目内文档](#项目内文档)
    - [代码示例](#代码示例)
    - [研究笔记](#研究笔记)

---

## 一、概念分类

Rust 项目中「对齐」一词在不同语境下有不同含义：

| 类型 | 含义 | 典型场景 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **格式化对齐** | 输出文本的左右/居中排版 | `{:>10}`、`{:<10}`、`{:^10}` |
| **权威来源对齐** | 项目文档与官方发布说明一致 | releases.rs、Rust Blog、版本追踪 |
| **类型对齐** | transmute/FFI 时类型大小与对齐兼容 | `mem::transmute`、`#[repr(C)]` |

---

## 二、内存对齐（核心）

### 2.0 为何要对齐（Why Alignment Matters）

**CPU 行为**：现代 CPU 按「对齐边界」加载数据。未对齐访问可能导致：

- **x86/x64**：可执行但慢（拆成多次加载、合并结果），或触发 fault（如 SSE/AVX 要求 16 字节对齐）
- **ARM**：未对齐访问可能直接 fault（取决于配置）
- **跨缓存行**：未对齐的 8 字节可能横跨两条 64 字节缓存行，导致两次加载

**结论**：对齐是正确性与性能的基础。Rust 默认保证所有安全访问都对齐；unsafe 代码必须自行保证。

*参考*: [Rust Reference - Type layout](https://doc.rust-lang.org/reference/type-layout.html)

---

### 2.1 基本概念

- **对齐**：类型 T 的实例地址必须是 `align_of::<T>()` 的整数倍
- **自然对齐**：标量类型的对齐通常等于其大小（如 `u64` 对齐 8 字节）
- **填充**：为满足对齐，编译器在字段间插入 padding

```rust
use std::mem::{size_of, align_of};

// u64 需 8 字节对齐
assert_eq!(align_of::<u64>(), 8);
assert_eq!(size_of::<u64>(), 8);

// 结构体对齐 = 各字段对齐的最大值
#[repr(C)]
struct Example {
    a: u8,   // 1 byte, 7 bytes padding
    b: u64,  // 8 bytes
    c: u8,   // 1 byte, 7 bytes padding
}
assert_eq!(align_of::<Example>(), 8);
assert_eq!(size_of::<Example>(), 24);
```

### 2.2 常用 API

| API | 用途 |
| :--- | :--- | :--- | :--- | :--- |
| `mem::size_of::<T>()` | 类型 T 的大小（含填充） |
| `mem::align_of_val(v)` | 值的实际对齐 |
| `ptr::read_unaligned` | 读取未对齐内存（较慢） |
| `Layout::from_size_align` | 构造自定义布局 |

### 2.3 repr 与对齐（完整谱系）

```rust
// 默认 #[repr(Rust)]：编译器可重排字段以优化
struct DefaultLayout { a: u8; b: u64; }

// #[repr(C)]：C 兼容，字段顺序固定，有填充
#[repr(C)]
struct CLayout { a: u8; b: u64; }

// #[repr(packed)]：无填充，所有字段 1 字节对齐（访问慢、FFI 慎用）
#[repr(packed)]
struct Packed { a: u8; b: u64; }

// #[repr(packed(N))]（Rust 1.90+）：N 字节对齐的紧凑布局
#[repr(packed(2))]
struct Packed2 { a: u8; b: u16; }  // b 至少 2 字节对齐

// #[repr(transparent)]：与单字段同大小、同对齐，用于 newtype
#[repr(transparent)]
struct Wrapper(u32);

// #[repr(align(N))]：强制 N 字节对齐（如缓存行）
#[repr(align(64))]
struct CacheAligned { data: [u8; 64]; }

// 组合：C 布局 + 自定义对齐
#[repr(C, align(32))]
struct CLayoutAligned { x: u64; y: u64; }
```

### 2.4 字段重排序优化

```rust
// ❌ 大字段后置导致多出填充
struct Bad { a: u8; b: u64; c: u8; }  // 24 bytes

// ✅ 大字段前置减少填充
struct Good { b: u64; a: u8; c: u8; } // 16 bytes
```

### 2.5 对齐计算（Rust 1.92+）

```rust
use std::num::NonZeroUsize;

/// 将 size 向上对齐到 alignment 的整数倍
fn align_up(size: usize, alignment: usize) -> usize {
    let nz = NonZeroUsize::new(alignment).unwrap();
    // 等价: (size + alignment - 1) / alignment * alignment
    (size + alignment - 1) / alignment * alignment
}

/// Rust 1.92+ 使用 div_ceil 的写法（需 size 已按 alignment 单位计算）
fn align_up_div_ceil(size: usize, alignment: NonZeroUsize) -> usize {
    size.div_ceil(alignment).get() * alignment.get()
}
```

### 2.6 Layout API（自定义分配）

`std::alloc::Layout` 描述内存块的大小与对齐，用于 `alloc`、`GlobalAlloc` 等。

```rust
use std::alloc::Layout;

// 构造布局：size 和 align 必须满足约束（align 为 2 的幂，size 为 align 的倍数等）
let layout = Layout::from_size_align(64, 8).unwrap();

// 计算为容纳 T 所需的对齐填充
let padding = layout.padding_needed_for(Layout::new::<u64>());

// 将布局对齐到更大边界
let aligned = layout.align_to(Layout::new::<u64>().align()).unwrap();
```

*参考*: [std::alloc::Layout](https://doc.rust-lang.org/std/alloc/struct.Layout.html)

### 2.7 平台差异

| 平台 | 未对齐访问 | 缓存行 | 备注 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| ARM (AArch64) | 可能 fault | 64 B | 取决于 MMU 配置 |
| WASM | 有对齐要求 | N/A | 见 [wasm 内存模型](https://webassembly.org/docs/semantics/) |

---

## 三、格式化对齐

输出文本的左右/居中排版，详见 [strings_formatting_cheatsheet.md](./quick_reference/strings_formatting_cheatsheet.md#对齐和填充)。

```rust
let x = 42;

println!("{:>10}", x);   // 右对齐，宽度 10
println!("{:<10}", x);   // 左对齐
println!("{:^10}", x);   // 居中对齐
println!("{:*>10}", x);  // 右对齐，* 填充
```

---

## 四、unsafe 与对齐

### 4.1 裸指针解引用前提与 UB 情形

[Rustonomicon](https://doc.rust-lang.org/nomicon/) 与 [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) 要求：

| 操作 | 未对齐时 | 说明 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `ptr::read(ptr)` | **UB** | 同上 |
| `ptr::write(ptr, v)` | **UB** | 同上 |
| `ptr::read_unaligned(ptr)` | ✅ 允许 | 显式未对齐读取，较慢 |
| `ptr::write_unaligned(ptr, v)` | ✅ 允许 | 显式未对齐写入 |

**原则**：凡未显式标注 `_unaligned` 的指针操作，均要求正确对齐。

### 4.2 未对齐访问

当指针可能未按类型对齐时（如从网络包、文件解析的字节流），必须用 `read_unaligned`/`write_unaligned`，否则 `*ptr` 或 `ptr::read` 会 UB。

```rust
use std::ptr;

// 场景：从 &[u8] 解析 u64，偏移可能不是 8 的倍数
fn parse_u64_unaligned(bytes: &[u8], offset: usize) -> u64 {
    assert!(offset + 8 <= bytes.len());
    let ptr = bytes[offset..].as_ptr() as *const u64;
    unsafe { ptr::read_unaligned(ptr) }  // 允许未对齐，比 read 慢
}
```

### 4.3 transmute 对齐约束

`mem::transmute::<A, B>(x)` 的约束（违反任一条为 UB）：

1. `size_of::<A>() == size_of::<B>()`
2. `align_of::<A>() <= align_of::<B>()`（目标对齐不能更严格）

```rust
// ✅ 合法：u32 与 u32 大小、对齐相同
let a: u32 = 0x1234_5678;
let b: u32 = unsafe { std::mem::transmute::<u32, u32>(a) };

// ❌ UB：align_of::<A>() > align_of::<B>() 时，B 的地址可能无法满足 A 的对齐
// 例：从 &[u8; 8] 取指针 transmute 成 &u64，若指针未 8 字节对齐则 UB

// 未对齐时用 read_unaligned，不要用 transmute
```

---

## 五、缓存行对齐与并发

### 5.1 伪共享（False Sharing）

多线程下，同一缓存行被不同核修改会导致缓存失效，性能可下降数倍。典型缓解：每线程数据单独占满缓存行。

```rust
// 单个 u64 需填充到 64 字节，避免与相邻数据共享缓存行
#[repr(align(64))]
struct CacheLinePadded {
    value: std::sync::atomic::AtomicU64,
    _pad: [u8; 56],  // 8 + 56 = 64 字节，占满缓存行
}
```

### 5.2 数据局部性：AoS vs SoA

与对齐相关：连续访问同类型数据时，缓存行利用率更高。

| 模式 | 说明 | 适用 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **SoA** (Structure of Arrays) | `positions_x: Vec<f32>`, `velocities_x: Vec<f32>` 等 | 批量处理单字段，通常快 2–4x |

*详见* [c01 09_性能优化参考](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/09_性能优化参考.md#32-缓存友好设计)

### 5.3 工具验证与量化数据

- **`cargo rustc -- -Z print-type-sizes`**：查看类型大小与对齐
- **perf**：`perf stat` 观测 cache-misses，伪共享时 L1-dcache-load-misses 显著升高
- **基准测试**：`cargo bench -p c05_threads --bench false_sharing_bench`

**实测数据**（x64，双线程各 10 万次 fetch_add）：

- 伪共享（BadCounters）：~1.55 ms
- 缓存行隔离（GoodCounters）：~465 µs
- **约 3.3x 加速**

---

## 六、权威来源（非技术对齐）

> **说明**：此处「对齐」指项目文档与官方发布的一致性，与内存对齐无技术关联。技术读者可跳过。

版本追踪与权威来源： [RUST_RELEASE_TRACKING_CHECKLIST](../07_project/RUST_RELEASE_TRACKING_CHECKLIST.md)、[INCREMENTAL_UPDATE_FLOW](../research_notes/INCREMENTAL_UPDATE_FLOW.md)。

---

## 七、对齐选型决策树

```text
需要控制内存布局？
├─ 否 → 使用默认 #[repr(Rust)]
└─ 是
   ├─ 与 C/FFI 交互？ → #[repr(C)]
   ├─ 需要紧凑无填充（如协议解析）？ → #[repr(packed)] 或 #[repr(packed(N))]
   ├─ 需要 newtype 与内层同布局？ → #[repr(transparent)]
   ├─ 多线程共享、避免伪共享？ → #[repr(align(64))] + 填充
   └─ 组合需求？ → #[repr(C, align(N))]
```

| 场景 | 推荐 |
| :--- | :--- | :--- | :--- | :--- |
| C 互操作、FFI | `#[repr(C)]` |
| 网络/二进制协议 | `#[repr(C)]` 或 `packed`，注意未对齐用 `read_unaligned` |
| 多线程原子计数器 | `#[repr(align(64))]` 每计数器独占缓存行 |
| 零成本 newtype | `#[repr(transparent)]` |

---

## 八、相关文档与示例

### 项目内文档

| 主题 | 路径 |
| :--- | :--- | :--- | :--- | :--- |
| 性能优化参考 | [c01/tier_03/09_性能优化参考](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/09_性能优化参考.md) |
| 内存安全参考 | [c01/tier_03/08_内存安全参考](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/08_内存安全参考.md) |
| 缓存行对齐 | [c05/02_系统编程优化](../../crates/c05_threads/docs/tier_04_advanced/02_系统编程优化.md#51-缓存行对齐) |
| 无锁编程 | [c05/04_lock_free_programming](../../crates/c05_threads/docs/04_lock_free_programming.md) |
| 格式化对齐 | [strings_formatting_cheatsheet](./quick_reference/strings_formatting_cheatsheet.md) |

### 代码示例

| 模块 | 示例 |
| :--- | :--- | :--- | :--- | :--- |
| c02 | `memory_safety_advanced`、`rust_192_features_demo` 对齐计算 |
| c04 | `rust_192_features_demo` 泛型对齐大小 |
| c05 | 并行算法中的缓存行对齐；`benches/false_sharing_bench` 伪共享基准 |
| c08 | `rust_192_features` align_size |

### 研究笔记

- [ownership_model](../research_notes/formal_methods/ownership_model.md) - transmute 形式化约束
- [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../research_notes/THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) - 指针有效性
- [memory_analysis](../research_notes/experiments/memory_analysis.md) - align_of 实验

---

**维护**: 对齐知识随 Rust 版本更新。新版本发布时检查 [Rust Reference - Type layout](https://doc.rust-lang.org/reference/type-layout.html)。发现错误或遗漏请提 issue。

**批判性评估与推进计划**: [ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md](../07_project/ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md)
