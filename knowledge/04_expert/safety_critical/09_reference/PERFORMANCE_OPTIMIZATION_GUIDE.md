# 性能优化指南

## 概述

本文档提供Rust安全关键系统的性能优化策略，在保证安全性的前提下实现最优运行时性能。

---

## 1. 零成本抽象

### 1.1 泛型单态化

```rust
/// 零成本泛型
/// 编译后为每个类型生成专用代码
pub fn process<T: Processor>(item: T) -> T::Output {
    item.process()
}

// 编译后等效于:
// fn process_i32(item: I32Processor) -> i32
// fn process_f64(item: F64Processor) -> f64
```

### 1.2 迭代器优化

```rust
/// 迭代器链零成本抽象
pub fn sum_of_squares(nums: &[i32]) -> i32 {
    nums.iter()
        .map(|x| x * x)           // 内联
        .filter(|x| *x > 100)     // 内联
        .sum()                     // 专用实现
}

// 编译后等效于手写循环，无函数调用开销
```

---

## 2. 内存布局优化

### 2.1 结构体布局

```rust
use std::mem::size_of;

/// 优化前: 24字节 (有填充)
#[repr(Rust)]
struct BadLayout {
    a: u8,      // 1字节 + 7字节填充
    b: u64,     // 8字节
    c: u8,      // 1字节 + 7字节填充
    d: u64,     // 8字节
}

/// 优化后: 17字节 (无填充)
#[repr(C)]
struct GoodLayout {
    b: u64,     // 8字节
    d: u64,     // 8字节
    a: u8,      // 1字节
    c: u8,      // 1字节
}

/// 或使用packed(注意性能影响)
#[repr(C, packed)]
struct PackedLayout {
    a: u8,
    b: u64,
    c: u8,
    d: u64,
}
```

### 2.2 缓存友好设计

```rust
/// SoA (Structure of Arrays) vs AoS (Array of Structures)

/// AoS - 缓存不友好 (用于随机访问)
struct ParticleAoS {
    position: [f32; 3],
    velocity: [f32; 3],
    mass: f32,
}

/// SoA - 缓存友好 (用于顺序处理)
struct ParticleSoA {
    positions: Vec<[f32; 3]>,
    velocities: Vec<[f32; 3]>,
    masses: Vec<f32>,
}

impl ParticleSoA {
    /// 向量化友好的批量更新
    pub fn update_positions(&mut self, dt: f32) {
        for i in 0..self.positions.len() {
            for j in 0..3 {
                self.positions[i][j] += self.velocities[i][j] * dt;
            }
        }
    }
}
```

---

## 3. 编译时计算

### 3.1 常量泛型

```rust
/// 编译时已知大小的数组
pub struct Buffer<T, const N: usize> {
    data: [T; N],
    len: usize,
}

impl<T: Default + Copy, const N: usize> Buffer<T, N> {
    pub const fn new() -> Self {
        Self {
            data: [T::default(); N],
            len: 0,
        }
    }

    /// 编译时边界检查
    pub fn push(&mut self, value: T) -> Result<(), BufferError> {
        if self.len >= N {
            return Err(BufferError::Full);
        }
        self.data[self.len] = value;
        self.len += 1;
        Ok(())
    }
}

/// 编译时查找表
const fn crc32_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        let mut c = i as u32;
        let mut j = 0;
        while j < 8 {
            if c & 1 != 0 {
                c = 0xEDB88320 ^ (c >> 1);
            } else {
                c >>= 1;
            }
            j += 1;
        }
        table[i] = c;
        i += 1;
    }
    table
}

static CRC32_TABLE: [u32; 256] = crc32_table();
```

### 3.2 常量求值

```rust
/// 编译时配置验证
const fn validate_config(max_size: usize, min_size: usize) -> usize {
    assert!(max_size > min_size, "max must be greater than min");
    assert!(max_size <= 1024, "max size exceeded");
    max_size
}

const MAX_BUFFER_SIZE: usize = validate_config(512, 16);
```

---

## 4. 运行时优化

### 4.1 分支预测提示

```rust
/// 使用likely/unlikely提示
#[cfg(feature = "nightly")]
use std::intrinsics::{likely, unlikely};

pub fn process_with_hint(value: Option<i32>) -> i32 {
    // 大多数情况下有值
    if unsafe { likely(value.is_some()) } {
        value.unwrap()
    } else {
        0
    }
}

/// 稳定版替代方案: 使用cold属性
#[cold]
fn handle_error() -> ! {
    panic!("Error occurred");
}

pub fn process_safe(value: Option<i32>) -> i32 {
    match value {
        Some(v) => v,
        None => handle_error(),
    }
}
```

### 4.2 SIMD向量化

```rust
/// 使用packed_simd或std::simd
#[cfg(feature = "simd")]
use std::simd::*;

/// SIMD数组加法
pub fn simd_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    const LANES: usize = 4;

    let chunks = a.len() / LANES;

    for i in 0..chunks {
        let offset = i * LANES;
        let va = f32x4::from_slice(&a[offset..offset + LANES]);
        let vb = f32x4::from_slice(&b[offset..offset + LANES]);
        let vr = va + vb;
        vr.copy_to_slice(&mut result[offset..offset + LANES]);
    }

    // 处理剩余元素
    for i in (chunks * LANES)..a.len() {
        result[i] = a[i] + b[i];
    }
}
```

---

## 5. 嵌入式特定优化

### 5.1 无分配设计

```rust
#![no_std]

/// 静态分配池
pub struct ObjectPool<T, const N: usize> {
    storage: [Option<T>; N],
    free_list: [bool; N],
}

impl<T, const N: usize> ObjectPool<T, N> {
    pub const fn new() -> Self {
        Self {
            storage: [None; N],
            free_list: [true; N],
        }
    }

    pub fn allocate(&mut self, value: T) -> Option<PoolRef<T>> {
        for i in 0..N {
            if self.free_list[i] {
                self.storage[i] = Some(value);
                self.free_list[i] = false;
                return Some(PoolRef { index: i, pool: self });
            }
        }
        None
    }
}

pub struct PoolRef<'a, T> {
    index: usize,
    pool: &'a mut ObjectPool<T>,
}

impl<'a, T> Drop for PoolRef<'a, T> {
    fn drop(&mut self) {
        self.pool.free_list[self.index] = true;
        self.pool.storage[self.index] = None;
    }
}
```

### 5.2 中断延迟优化

```rust
/// 最小化临界区
pub struct MinimalCriticalSection;

impl MinimalCriticalSection {
    /// 使用原子操作而非锁
    pub fn update_atomic(counter: &AtomicU32) {
        // 单条指令，无需禁用中断
        counter.fetch_add(1, Ordering::Relaxed);
    }

    /// 批量处理减少临界区
    pub fn process_batch(data: &mut [u8]) {
        // 准备工作(无需保护)
        let processed: Vec<u8> = data.iter().map(|x| x * 2).collect();

        // 临界区: 仅复制操作
        cortex_m::interrupt::free(|_| {
            data.copy_from_slice(&processed);
        });
    }
}
```

---

## 6. 性能测量

### 6.1 基准测试

```rust
/// 使用criterion进行基准测试
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

### 6.2 运行时性能监控

```rust
/// 性能计数器
pub struct PerformanceCounter {
    start: u64,
    name: &'static str,
}

impl PerformanceCounter {
    pub fn new(name: &'static str) -> Self {
        Self {
            start: Self::read_cycle_counter(),
            name,
        }
    }

    #[cfg(target_arch = "x86_64")]
    fn read_cycle_counter() -> u64 {
        unsafe { core::arch::x86_64::_rdtsc() }
    }

    #[cfg(target_arch = "arm")]
    fn read_cycle_counter() -> u64 {
        let cycles: u32;
        unsafe {
            asm!("mrc p15, 0, {}, c15, c12, 1", out(reg) cycles);
        }
        cycles as u64
    }
}

impl Drop for PerformanceCounter {
    fn drop(&mut self) {
        let elapsed = Self::read_cycle_counter() - self.start;
        log::debug!("{} took {} cycles", self.name, elapsed);
    }
}
```

---

## 7. 优化检查清单

### 编译时优化

- [ ] 使用release模式 (`--release`)
- [ ] 启用LTO (`lto = true`)
- [ ] 设置codegen-units = 1
- [ ] 使用适当的opt-level
- [ ] 启用panic = "abort"

### 代码优化

- [ ] 避免动态分配
- [ ] 使用迭代器而非循环
- [ ] 优化内存布局
- [ ] 使用const泛型
- [ ] 内联关键函数

### 嵌入式优化

- [ ] 使用no_std
- [ ] 静态分配
- [ ] 最小化中断延迟
- [ ] 使用合适的内存区域
- [ ] 禁用不需要的功能

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*性能优化应在保证安全性的前提下进行。*
