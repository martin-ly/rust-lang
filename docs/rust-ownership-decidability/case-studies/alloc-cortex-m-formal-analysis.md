# alloc-cortex-m嵌入式堆分配器形式化分析

> **主题**: no_std环境下的堆分配
> **形式化框架**: 内存池 + 分配策略
> **参考**: cortex-m-alloc crate

---

## 目录

- [alloc-cortex-m嵌入式堆分配器形式化分析](#alloc-cortex-m嵌入式堆分配器形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 内存池形式化](#2-内存池形式化)
    - [定义 POOL-1 ( 内存池 )](#定义-pool-1--内存池-)
    - [定义 POOL-2 ( 块分配 )](#定义-pool-2--块分配-)
  - [3. 分配器接口](#3-分配器接口)
    - [定义 ALLOC-1 ( GlobalAlloc trait )](#定义-alloc-1--globalalloc-trait-)
    - [定理 ALLOC-T1 ( 分配器安全 )](#定理-alloc-t1--分配器安全-)
  - [4. 内存碎片分析](#4-内存碎片分析)
    - [定义 FRAG-1 ( 外部碎片 )](#定义-frag-1--外部碎片-)
    - [定理 FRAG-T1 ( 固定块无外部碎片 )](#定理-frag-t1--固定块无外部碎片-)
  - [5. 定理与证明](#5-定理与证明)
    - [定理 OOM-T1 ( OOM处理 )](#定理-oom-t1--oom处理-)
  - [6. 代码示例](#6-代码示例)
    - [示例1: 全局分配器配置](#示例1-全局分配器配置)
    - [示例2: 自定义分配器](#示例2-自定义分配器)
    - [示例3: 内存使用监控](#示例3-内存使用监控)

---

## 1. 引言

嵌入式系统中使用堆分配的挑战：

- 有限的RAM
- 确定性要求
- 碎片问题
- 分配失败处理

---

## 2. 内存池形式化

### 定义 POOL-1 ( 内存池 )

$$
\text{MemoryPool} = (\text{base} : *mut u8, \text{size} : usize, \text{used} : \text{Bitmap})
$$

### 定义 POOL-2 ( 块分配 )

```rust
// 固定大小的块分配
const BLOCK_SIZE: usize = 256;
const NUM_BLOCKS: usize = 16;
```

$$
\text{allocate}(n) = \begin{cases}
\text{Some}(ptr) & \text{if } \exists i.\ \neg\text{used}[i] \land \text{size} \leq \text{BLOCK\_SIZE} \\
\text{None} & \text{otherwise}
\end{cases}
$$

---

## 3. 分配器接口

### 定义 ALLOC-1 ( GlobalAlloc trait )

```rust
unsafe impl GlobalAlloc for CortexMAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8;
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout);
}
```

**形式化**:

$$
\text{alloc} : \text{Layout} \to \text{Option}<*mut u8> \\
\text{dealloc} : *mut u8 \times \text{Layout} \to ()
$$

### 定理 ALLOC-T1 ( 分配器安全 )

分配器满足Rust内存安全要求。

$$
\forall p = \text{alloc}(l).\ \text{valid}(p) \land \text{align}(p, l.\text{align})
$$

---

## 4. 内存碎片分析

### 定义 FRAG-1 ( 外部碎片 )

$$
\text{Fragmentation} = 1 - \frac{\max_{\text{contiguous}}}{\text{total\_free}}
$$

### 定理 FRAG-T1 ( 固定块无外部碎片 )

固定大小块分配器无外部碎片。

$$
\text{FixedBlockAllocator} \vdash \text{external\_fragmentation} = 0
$$

**证明**: 所有块大小相同，任何空闲块都可满足请求。$\square$

---

## 5. 定理与证明

### 定理 OOM-T1 ( OOM处理 )

嵌入式分配器必须处理分配失败。

$$
\forall \text{alloc}.\ \text{alloc}() = \text{None} \to \text{safe\_recovery}
$$

---

## 6. 代码示例

### 示例1: 全局分配器配置

```rust
use alloc_cortex_m::CortexMHeap;
use core::alloc::Layout;

#[global_allocator]
static ALLOCATOR: CortexMHeap = CortexMHeap::empty();

#[entry]
fn main() -> ! {
    // 初始化堆
    let start = cortex_m_rt::heap_start() as usize;
    let size = 1024; // 1KB堆
    unsafe { ALLOCATOR.init(start, size); }

    // 使用Vec
    let mut v = Vec::new();
    v.push(1);
    v.push(2);

    loop {}
}

#[alloc_error_handler]
fn alloc_error(_layout: Layout) -> ! {
    defmt::error!("Out of memory!");
    cortex_m::asm::bkpt();
    loop {}
}
```

### 示例2: 自定义分配器

```rust
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::NonNull;

struct FixedBlockAllocator<const N: usize, const SIZE: usize> {
    memory: [u8; N * SIZE],
    used: [bool; N],
}

impl<const N: usize, const SIZE: usize> FixedBlockAllocator<N, SIZE> {
    const fn new() -> Self {
        Self {
            memory: [0; N * SIZE],
            used: [false; N],
        }
    }

    fn allocate(&mut self) -> Option<NonNull<u8>> {
        for i in 0..N {
            if !self.used[i] {
                self.used[i] = true;
                let ptr = &mut self.memory[i * SIZE] as *mut u8;
                return Some(NonNull::new(ptr).unwrap());
            }
        }
        None
    }

    fn deallocate(&mut self, ptr: NonNull<u8>) {
        let offset = ptr.as_ptr() as usize - self.memory.as_ptr() as usize;
        let index = offset / SIZE;
        self.used[index] = false;
    }
}
```

### 示例3: 内存使用监控

```rust
struct InstrumentedAllocator<A> {
    inner: A,
    allocated: AtomicUsize,
    peak: AtomicUsize,
}

impl<A: GlobalAlloc> GlobalAlloc for InstrumentedAllocator<A> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = self.inner.alloc(layout);
        if !ptr.is_null() {
            let new_size = self.allocated.fetch_add(layout.size(), Ordering::SeqCst)
                          + layout.size();
            self.peak.fetch_max(new_size, Ordering::SeqCst);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.inner.dealloc(ptr, layout);
        self.allocated.fetch_sub(layout.size(), Ordering::SeqCst);
    }
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
