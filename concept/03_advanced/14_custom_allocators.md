# 自定义分配器与内存布局优化

> **Bloom 层级**: 应用 → 分析
> **定位**: 深入探讨 Rust 的**自定义分配器**机制——从 `GlobalAlloc` Trait 到 `allocator_api` 不稳定特性，分析内存布局对齐、分配策略与性能优化。
> **前置概念**: [Memory Management](../02_intermediate/03_memory_management.md) · [Type System](../01_foundation/04_type_system.md) · [Unsafe Rust](./03_unsafe.md)
> **后置概念**: [Performance Optimization](../06_ecosystem/15_performance_optimization.md) · [Embedded](../06_ecosystem/04_application_domains.md)

---

> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust Reference — Allocation](https://doc.rust-lang.org/reference/memory-allocation.html) · [RFC 1398 — Global Allocators](https://rust-lang.github.io/rfcs/1398-global_allocators.html) · [Wikipedia — Memory Management](https://en.wikipedia.org/wiki/Memory_management)

## 📑 目录

- [自定义分配器与内存布局优化](#自定义分配器与内存布局优化)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 GlobalAlloc Trait](#11-globalalloc-trait)
    - [1.2 分配器属性](#12-分配器属性)
  - [二、实践模式](#二实践模式)
    - [2.1 bumpalo — Bump 分配器](#21-bumpalo--bump-分配器)
    - [2.2 jemalloc / mimalloc](#22-jemalloc--mimalloc)
    - [2.3 arena 分配器](#23-arena-分配器)
  - [三、内存布局与对齐](#三内存布局与对齐)
    - [3.1 Layout](#31-layout)
    - [3.2 对齐约束](#32-对齐约束)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
    - [编译验证示例](#编译验证示例)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：自定义分配器的编译错误](#十边界测试自定义分配器的编译错误)
    - [10.1 边界测试：分配器布局不匹配（运行时 UB）](#101-边界测试分配器布局不匹配运行时-ub)
    - [10.2 边界测试：`Vec` 自定义分配器的泛型参数（编译错误）](#102-边界测试vec-自定义分配器的泛型参数编译错误)
    - [10.3 边界测试：全局分配器的 `#[global_allocator]` 重复定义（编译错误）](#103-边界测试全局分配器的-global_allocator-重复定义编译错误)
    - [10.4 边界测试：自定义分配器的 `Layout` 对齐要求（运行时 UB）](#104-边界测试自定义分配器的-layout-对齐要求运行时-ub)
    - [10.5 边界测试：分配器的 `dealloc` 与 `alloc` 的布局不匹配（运行时 UB）](#105-边界测试分配器的-dealloc-与-alloc-的布局不匹配运行时-ub)
    - [10.3 边界测试：全局分配器与 `#[global_allocator]` 重复定义（编译错误）](#103-边界测试全局分配器与-global_allocator-重复定义编译错误)
    - [10.4 边界测试：自定义分配器的 Layout 不匹配与内存安全（运行时 UB）](#104-边界测试自定义分配器的-layout-不匹配与内存安全运行时-ub)
    - [10.3 边界测试：函数重复定义](#103-边界测试函数重复定义)

---

## 一、核心概念
>
>

### 1.1 GlobalAlloc Trait
>

```text
GlobalAlloc:

  定义: Rust 的全局内存分配接口
  ├── alloc(layout: Layout) -> *mut u8
  ├── dealloc(ptr: *mut u8, layout: Layout)
  ├── realloc(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8
  └── alloc_zeroed(layout: Layout) -> *mut u8

  使用 #[global_allocator] 属性设置全局分配器:

  use std::alloc::{GlobalAlloc, Layout, System};

  struct MyAllocator;

  unsafe impl GlobalAlloc for MyAllocator {
      unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
          // 自定义分配逻辑
          System.alloc(layout)
      }

      unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
          System.dealloc(ptr, layout)
      }
  }

  #[global_allocator]
  static ALLOCATOR: MyAllocator = MyAllocator;

  关键约束:
  ├── alloc 返回的指针必须满足 Layout 的对齐要求
  ├── dealloc 必须使用与 alloc 相同的 Layout
  ├── realloc 保持原有数据不变
  └── 线程安全由实现保证
```

> **认知功能**: **GlobalAlloc 是 Rust 与操作系统内存管理的桥梁**——通过标准化接口允许替换底层分配策略。
> [来源: [std::alloc::GlobalAlloc](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)]

---

### 1.2 分配器属性
>

```text
分配器关键属性:

  碎片控制:
  ├── 内部碎片: 分配大小 > 实际请求大小
  ├── 外部碎片: 空闲空间分散，无法满足大请求
  └── 缓解: Bump 分配器、 slab 分配器

  并发性能:
  ├── 全局锁竞争
  ├── 线程本地缓存（TCMalloc, jemalloc）
  └── 无锁分配器（per-thread arenas）

  延迟特征:
  ├── 最坏情况分配时间
  ├── 实时系统的确定性需求
  └── 缓解: 预分配、内存池
```

> **性能洞察**: **分配器选择直接影响应用延迟分布**——jemalloc 适合通用场景，mimalloc 适合小对象高频分配。
> [来源: [Microsoft mimalloc](https://github.com/microsoft/mimalloc)]

---

## 二、实践模式

### 2.1 bumpalo — Bump 分配器
>

```text
Bump Allocation:

  原理: 单方向递增指针，批量释放
  ├── 分配: O(1) 指针递增
  ├── 释放: 不支持单独释放，只能重置整个 arena
  ├── 适用: 生命周期明确的批量对象
  └── 优势: 极致分配速度，无碎片

  代码示例:

  use bumpalo::Bump;

  let bump = Bump::new();
  let x: &mut i32 = bump.alloc(42);
  let vec: &mut Vec<i32> = bump.alloc_with(|| vec![1, 2, 3]);
  // 所有分配随 bump 一起释放

  使用场景:
  ├── 编译器（AST 节点分配）
  ├── 游戏引擎（帧临时对象）
  ├── 解析器（解析树构建）
  └── Web 渲染（DOM 节点）
```

> **实践洞察**: **Bump 分配器是 Rust 编译器的核心优化**——rustc 使用类似机制分配 AST/HIR/MIR 节点。
> [来源: [bumpalo crate](https://docs.rs/bumpalo/latest/bumpalo/)]

---

### 2.2 jemalloc / mimalloc
>

```text
高性能分配器对比:

  jemalloc:
  ├── Facebook 开发，Rust 曾默认使用
  ├── 线程本地 arena 减少竞争
  ├── 良好的大对象处理
  └── 配置丰富（通过 MALLOC_CONF）

  mimalloc:
  ├── Microsoft 开发，Rust 当前默认（部分平台）
  ├── 小对象分配极快
  ├── 安全的释放机制
  └── 内存安全设计（减少 Use-After-Free）

  snmalloc:
  ├── Microsoft Research
  ├── 消息传递架构
  ├── 极致并发性能
  └── 形式化验证的安全保证

  切换分配器:
  #[global_allocator]
  static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;
```

> **分配器洞察**: **Rust 的默认分配器选择是平台相关的工程决策**——Linux 通常为 glibc malloc，Windows 为 mimalloc。
> [来源: [jemalloc](http://jemalloc.net/)] · [来源: [mimalloc](https://github.com/microsoft/mimalloc)]

---

### 2.3 arena 分配器
>

```text
Arena 分配器模式:

  设计: 预分配大块内存，从中划分小对象
  ├── 减少系统调用次数
  ├── 批量释放提高效率
  ├── 消除单独跟踪开销
  └── 限制: 不支持单独释放

  Rust 中的 arena:
  ├── bumpalo::Bump
  ├── typed-arena::Arena<T>
  └── 自定义 arena（ unsafe 实现）

  代码示例:

  use typed_arena::Arena;

  let arena = Arena::new();
  let a = arena.alloc(Node { val: 1, children: vec![] });
  let b = arena.alloc(Node { val: 2, children: vec![] });
  // arena 内所有对象同生命周期
```

> **Arena 洞察**: **Arena 分配器是 Rust 零成本抽象的典范**——无运行时开销，纯编译期内存管理策略。
> [来源: [typed-arena](https://docs.rs/typed-arena/latest/typed_arena/)]

---

## 三、内存布局与对齐

### 3.1 Layout
>

```text
内存布局:

  Layout 结构:
  ├── size: usize — 分配大小
  ├── align: usize — 对齐要求（2的幂）
  └── padding: 填充字节

  创建 Layout:
  let layout = Layout::new::<MyStruct>();
  let layout = Layout::from_size_align(1024, 64).unwrap();

  布局组合:
  let (combined, offset_a) = Layout::new::<A>()
      .extend(Layout::new::<B>()).unwrap();

  对齐规则:
  ├── 基本类型: 大小即对齐
  ├── 结构体: 最大成员对齐
  ├── 元组: 类似结构体
  └── #[repr(align(N))]: 强制对齐

  #[repr(align(64))]
  struct CacheLineAligned {
      data: [u8; 64],
  }
```

> **布局洞察**: **内存对齐是缓存性能的关键**——缓存行通常为 64 字节，跨行访问可能触发两次缓存加载。
> [来源: [std::alloc::Layout](https://doc.rust-lang.org/std/alloc/struct.Layout.html)]

---

### 3.2 对齐约束
>

```text
对齐约束:

  #[repr(packed)]:
  ├── 移除填充，紧凑布局
  ├── 可能违反硬件对齐要求
  ├── 访问字段需要 unsafe
  └── 网络协议、硬件寄存器映射常用

  #[repr(C)]:
  ├── C 兼容布局
  ├── 字段按声明顺序
  ├── 可预测的对齐和偏移
  └── FFI 互操作必需

  #[repr(transparent)]:
  ├── 单字段新类型
  ├── 与底层类型相同布局
  └── 类型安全零成本抽象

  安全边界:
  ├── 未对齐指针解引用 → UB
  ├── packed 结构体的引用创建 → UB
  └── 需使用 ptr::read_unaligned / write_unaligned
```

> **对齐安全**: **Rust 的类型系统保证大部分对齐安全**——unsafe 代码中需手动维护 Layout 约束。
> [来源: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html)]

---

## 四、反命题与边界分析

### 4.1 反命题树
>

```mermaid
graph TD
    ROOT["命题: 自定义分配器总是提升性能"]
    ROOT --> Q1{"是否为小对象高频分配?"}
    Q1 -->|是| CUSTOM["✅ 自定义分配器有益"]
    Q1 -->|否| Q2{"是否需要单独释放?"}
    Q2 -->|是| DEFAULT["⚠️ 标准分配器更合适"]
    Q2 -->|否| Q3{"生命周期是否明确?"}
    Q3 -->|是| ARENA["✅ Arena/Bump 适合"]
    Q3 -->|否| DEFAULT

    style CUSTOM fill:#c8e6c9
    style ARENA fill:#c8e6c9
    style DEFAULT fill:#fff3e0
```

> **认知功能**: **分配器选择取决于分配模式**——没有 universally best 的分配器。
> [来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)]

---

### 4.2 边界极限

```text
边界 1: unsafe 风险
├── 错误实现 GlobalAlloc 导致内存损坏
├── Layout 不匹配导致未定义行为
└── 缓解: 充分测试，优先使用成熟 crate

边界 2: 生态系统兼容性
├── 第三方 crate 可能依赖特定分配器行为
├── #[global_allocator] 全局唯一
└── 缓解: 文档化分配器假设

边界 3: 平台差异
├── 不同 OS 的默认分配器不同
├── WASM 目标无系统分配器
└── 缓解: 条件编译 #[cfg(target_family = "wasm")]

边界 4: 调试难度
├── 自定义分配器增加内存调试复杂度
├── AddressSanitizer 集成可能受限
└── 缓解: 保持 alloc/dealloc 追踪日志
```

> **边界要点**: 自定义分配器的边界与**unsafe 风险**、**生态兼容性**、**平台差异**和**调试复杂度**相关。
> [来源: [Rustonomicon — Allocators](https://doc.rust-lang.org/nomicon/)]

---

## 五、常见陷阱

```text
陷阱 1: Layout 不匹配
  ❌ dealloc 使用与 alloc 不同的 Layout
     unsafe { dealloc(ptr, wrong_layout) }

  ✅ 始终保存并复用原始 Layout
     unsafe { dealloc(ptr, original_layout) }

陷阱 2: 零大小类型
  ❌ 假设 alloc(0) 返回非空指针
     // ZST 的 Layout::new::<()>().size() == 0

  ✅ 处理零大小类型的特殊情况
     // alloc 可能返回对齐的非空指针或 dangling

陷阱 3: 对齐假设错误
  ❌ 假设所有类型对齐到 8 字节
     // SIMD 类型可能需要 32/64 字节对齐

  ✅ 使用 Layout::new::<T>() 获取正确对齐
     let layout = Layout::new::<__m256i>(); // 32 字节对齐

陷阱 4: Arena 生命周期混淆
  ❌ 返回 arena 分配对象的引用超出 arena 生命周期
     fn bad<'a>(arena: &'a Arena<T>) -> &'a T { ... }

  ✅ 确保引用不超过 arena
     let arena = Arena::new();
     let x = arena.alloc(42);
     // x 不能存活超过 arena

陷阱 5: #[global_allocator] 重复定义
  ❌ 多个 crate 定义全局分配器
     // 链接错误

  ✅ 只在最终 binary crate 中定义
     // 或在 Cargo.toml 中选择特性
```

> **陷阱总结**: 自定义分配器的陷阱主要与**Layout 一致性**、**ZST 处理**、**对齐假设**、**生命周期**和**全局唯一性**相关。
> [来源: [Rust Reference — Global Allocators](https://doc.rust-lang.org/reference/memory-allocation.html)]

---

## 六、来源与延伸阅读
>

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference — Allocation](https://doc.rust-lang.org/reference/memory-allocation.html) | ✅ 一级 | 官方参考 |
| [std::alloc](https://doc.rust-lang.org/std/alloc/index.html) | ✅ 一级 | 标准库 API |
| [RFC 1398](https://rust-lang.github.io/rfcs/1398-global_allocators.html) | ✅ 一级 | 全局分配器 RFC |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | ✅ 一级 | unsafe 指南 |
| [jemalloc](http://jemalloc.net/) | ✅ 二级 | 高性能分配器 |
| [mimalloc](https://github.com/microsoft/mimalloc) | ✅ 二级 | 安全快速分配器 |
| [bumpalo](https://docs.rs/bumpalo/latest/bumpalo/) | ✅ 二级 | Bump 分配器 crate |

---

```rust
// 自定义分配器示例（需要 nightly）
use std::alloc::{GlobalAlloc, Layout, System};

struct MyAllocator;

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        System.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static ALLOCATOR: MyAllocator = MyAllocator;
```

```rust
fn main() {
    let v = vec![1, 2, 3];
    println!("capacity: {}", v.capacity());
}
```

### 编译验证示例

```rust
use std::alloc::Layout;

fn main() {
    let layout = Layout::new::<u64>();
    println!("size={}, align={}", layout.size(), layout.align());

    let combined = Layout::new::<u32>()
        .extend(Layout::new::<u64>()).unwrap()
        .0;
    println!("combined size={}", combined.size());
}
```

```rust
#[repr(C)]
struct Point {
    x: f64,
    y: f64,
}

fn main() {
    let p = Point { x: 1.0, y: 2.0 };
    println!("size_of Point = {}", std::mem::size_of_val(&p));
}
```

## 相关概念文件

- [Memory Management](../02_intermediate/03_memory_management.md) — 内存管理基础
- [Unsafe Rust](./03_unsafe.md) — unsafe Rust 基础
- [Type System](../01_foundation/04_type_system.md) — 类型系统
- [Performance Optimization](../06_ecosystem/15_performance_optimization.md) — 性能优化

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 11]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 权威来源索引

>
>
>
>
>

---

> **补充来源**

## 十、边界测试：自定义分配器的编译错误

### 10.1 边界测试：分配器布局不匹配（运行时 UB）

```rust
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    let layout = Layout::new::<u64>(); // 对齐 8，大小 8
    let ptr = unsafe { alloc(layout) };
    // ⚠️ 运行时 UB: 用错误的布局释放
    // let wrong_layout = Layout::new::<u8>(); // 对齐 1，大小 1
    // unsafe { dealloc(ptr, wrong_layout); } // 布局不匹配 = UB！
    unsafe { dealloc(ptr, layout); } // ✅ 使用相同布局
}
```

> **修正**: Rust 的全局分配器 API 要求 `alloc` 和 `dealloc` 使用**完全相同的布局**（大小和对齐）。使用错误布局释放内存是未定义行为，可能导致分配器元数据损坏、双重释放或内存泄漏。这与 C 的 `malloc`/`free`（只需配对）不同——Rust 的分配器可能使用大小类（size class）优化，`Layout` 信息对正确释放至关重要。自定义分配器实现必须严格遵守此契约。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]

### 10.2 边界测试：`Vec` 自定义分配器的泛型参数（编译错误）

```rust,compile_fail
use std::alloc::GlobalAlloc;

struct MyAlloc;

unsafe impl GlobalAlloc for MyAlloc {
    unsafe fn alloc(&self, _layout: std::alloc::Layout) -> *mut u8 {
        std::ptr::null_mut() // 简化实现
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: std::alloc::Layout) {}
}

fn main() {
    // ❌ 编译错误: Vec 的自定义分配器参数不稳定
    // Rust 1.95+ 中 Vec<T, A> 的分配器参数仍为 nightly 特性
    let _v: Vec<i32, MyAlloc> = Vec::new();
}

// 正确: 使用 nightly feature
#![feature(allocator_api)]

use std::alloc::Allocator;

fn fixed() {
    // let _v = Vec::new_in(MyAlloc); // nightly 支持
}
```

> **修正**: Rust 的自定义分配器 API（`Allocator` trait）截至 1.95+ 仍为**不稳定特性**（`#![feature(allocator_api)]`）。`Vec<T, A>`、`Box<T, A>` 等类型的第二个泛型参数只在 nightly 可用。稳定 Rust 中，自定义分配通常通过全局分配器替换（`#[global_allocator]`）实现，而非为单个集合指定分配器。这与 C++ 的 `std::allocator`（稳定且广泛使用）形成对比——Rust 的分配器设计更强调全局优化和安全性，牺牲了部分灵活性。[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]

### 10.3 边界测试：全局分配器的 `#[global_allocator]` 重复定义（编译错误）

```rust,ignore
use std::alloc::System;

#[global_allocator]
static A: System = System;

// ❌ 编译错误: 另一个 crate 也定义了全局分配器
// 例如 jemallocator 和 mimalloc 同时被依赖

fn main() {}
```

> **修正**: `#[global_allocator]` 属性将静态变量注册为进程的全局堆分配器。整个依赖树中只能有一个全局分配器——若两个 crate 都定义，链接器报告重复符号错误。解决方案：1) 仅在最终二进制 crate（`bin`）中定义全局分配器，不在库 crate 中定义；2) 使用 `cargo tree` 检查依赖中是否已有分配器；3) 通过 Cargo feature 控制（`jemalloc` feature 启用时定义分配器）。这与 C 的 `malloc` 替换（通过链接器弱符号或 `LD_PRELOAD`）或 C++ 的 `new`/`delete` 重载（类级别、全局级别）不同——Rust 的全局分配器是进程级别的，替换更彻底但冲突风险更高。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)] · [来源: [Rust Standard Library](https://doc.rust-lang.org/std/alloc/index.html)]

### 10.4 边界测试：自定义分配器的 `Layout` 对齐要求（运行时 UB）

```rust,compile_fail
use std::alloc::{Allocator, Layout, GlobalAlloc};

struct MyAlloc;

unsafe impl GlobalAlloc for MyAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // ❌ 运行时 UB: 若返回的指针未按 layout.align() 对齐
        std::alloc::System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // ❌ 运行时 UB: 若 layout 与 alloc 时的 layout 不匹配
        std::alloc::System.dealloc(ptr, layout);
    }
}
```

> **修正**: 自定义分配器必须严格遵守 `Layout` 契约：`alloc` 返回的指针必须按 `layout.align()` 对齐，`dealloc` 的 `layout` 必须与 `alloc` 时完全相同（大小和对齐）。违反这些契约是未定义行为：不对齐的指针导致 SIMD/原子指令失败，错误的 layout 导致分配器元数据损坏。Rust 的 `Allocator` trait（不稳定）比 `GlobalAlloc` 更安全：`Allocator::allocate` 返回 `NonNull<[u8]>`（包含长度验证），`deallocate` 要求 `NonNull<u8>` 和 `Layout`。但即使是安全的 `Allocator` API，底层实现仍需 unsafe 代码与操作系统分配器交互。这与 C 的 `malloc`/`free`（无对齐要求，由调用者保证）或 C++ 的 `std::allocator`（有 `allocate`/`deallocate` 但无运行时验证）不同——Rust 正在逐步增加分配器 API 的安全性。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)] · [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]

### 10.5 边界测试：分配器的 `dealloc` 与 `alloc` 的布局不匹配（运行时 UB）

```rust,ignore
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    unsafe {
        let layout = Layout::new::<[u8; 16]>();
        let ptr = alloc(layout);

        // ❌ 运行时 UB: dealloc 时使用不同布局
        let wrong_layout = Layout::new::<[u8; 8]>();
        dealloc(ptr, wrong_layout);
    }
}
```

> **修正**: `dealloc` 要求传入与 `alloc` 时**完全相同的 `Layout`**（大小和对齐）。大小不匹配导致分配器元数据损坏，对齐不匹配可能导致未对齐释放（某些分配器要求对齐一致）。这是分配器 API 的核心契约，违反即 UB。调试困难：错误可能在后续分配时才暴露（堆损坏的延迟效应）。安全模式：1) 始终保存 `alloc` 时的 `Layout`；2) 使用 `Box::from_raw` + `drop`（Rust 自动管理布局）；3) 使用 `Allocator` trait（不稳定，类型安全封装）。这与 C 的 `free`（只接受指针，无布局信息，依赖分配器内部追踪）或 C++ 的 `delete`（调用析构函数 + 释放，类型决定大小）不同——Rust 的 `GlobalAlloc` 要求显式布局，增加了安全性但也增加了出错机会。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)] · [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]

### 10.3 边界测试：全局分配器与 `#[global_allocator]` 重复定义（编译错误）

```rust,compile_fail
use std::alloc::{GlobalAlloc, Layout, System};

struct MyAlloc;

unsafe impl GlobalAlloc for MyAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 { std::ptr::null_mut() }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static A: MyAlloc = MyAlloc;

// ❌ 编译错误: 不能重复定义全局分配器
#[global_allocator]
static B: System = System;

fn main() {}
```

> **修正**: `#[global_allocator]` 将整个程序的**默认堆分配器**替换为自定义实现。限制：1) 整个 crate 图只能有一个全局分配器；2) 若依赖库也定义了全局分配器，链接错误；3) 分配器必须实现 `GlobalAlloc` trait（`alloc`/`dealloc`/`realloc`/`alloc_zeroed`）。常见自定义分配器：`jemallocator`（性能优化）、`mimalloc`（微软）、`dlmalloc`（嵌入式）。测试分配器：`std::alloc::alloc` + 泄漏检测。这与 C 的 `malloc` 重载（通过宏或链接器钩子）或 C++ 的 `operator new` 重载（类级别和全局级别）不同——Rust 的全局分配器替换是 crate 级别的，通过 trait 系统保证接口一致性。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)] · [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]

### 10.4 边界测试：自定义分配器的 Layout 不匹配与内存安全（运行时 UB）

```rust,ignore
use std::alloc::{alloc, dealloc, Layout};

fn main() {
    let layout = Layout::new::<u32>();
    let ptr = unsafe { alloc(layout) };

    // ❌ 运行时 UB: 使用错误的 Layout dealloc
    let wrong_layout = Layout::new::<u64>();
    unsafe { dealloc(ptr, wrong_layout); }
}
```

> **修正**: **`alloc`/`dealloc`** 的 **Layout 契约**：1) `alloc(layout)` 返回的指针必须用**相同 layout** 的 `dealloc` 释放；2) layout 的大小和对齐必须匹配；3) 重复释放（double free）→ UB；4) 释放未分配指针 → UB。`GlobalAlloc` trait 的要求：1) `alloc` 返回满足 layout.align 的指针；2) `dealloc` 的 ptr 和 layout 必须与 `alloc` 匹配；3) `realloc` 保持已有数据不变。调试工具：1) `#[cfg(debug_assertions)]` 使用检测分配器；2) Miri 检测 UB；3) AddressSanitizer / Valgrind（Linux）。这与 C 的 `malloc`/`free`（无 layout 概念，大小隐式存储）或 C++ 的 `new`/`delete`（调用析构函数 + 释放内存）不同——Rust 的分配器接口显式传递 layout，更灵活但更需小心。[来源: [GlobalAlloc](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)] · [来源: [Rust Allocator API](https://doc.rust-lang.org/std/alloc/index.html)]

### 10.3 边界测试：函数重复定义

```rust,compile_fail
fn duplicate() {}
fn duplicate() {}

fn main() {}
```

> **修正**: **名称唯一性**：1) 同一作用域内不能有两个同名函数；2) trait 方法可同名（通过 trait 区分）；3) 重载（overloading）不支持（除 trait 外）。

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
