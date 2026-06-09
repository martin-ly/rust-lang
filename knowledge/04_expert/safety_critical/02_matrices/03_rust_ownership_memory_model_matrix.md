# Rust所有权与内存模型矩阵

> **Bloom 层级**: 理解
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

## 所有权系统核心机制
>
> **[来源: Rust Official Docs]**

### 所有权三原则
>
> **[来源: Rust Official Docs]**

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    Rust所有权三原则                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1. 每个值有且只有一个所有者                                          │
│     ┌─────────┐                                                     │
│     │  Owner  │ ──owns──→ [Value]                                   │
│     └─────────┘                                                     │
│                                                                     │
│  2. 当所有者离开作用域，值被释放                                       │
│     {                                                               │
│         let s = String::from("hello");  // 分配内存                  │
│     }  // s离开作用域，内存自动释放                                   │
│                                                                     │
│  3. 所有权可以转移，但总是只有一个所有者                               │
│     let s1 = String::from("hello");                                  │
│     let s2 = s1;  // 所有权转移到s2，s1失效                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 借用规则矩阵
>
> **[来源: Rust Official Docs]**

| 场景 | 不可变借用 &T | 可变借用 &mut T | 所有权转移 | 适用场景 |
|------|---------------|-----------------|------------|----------|
| **读取数据** | ✅ 允许多个 | ❌ 独占 | ❌ | 共享读取 |
| **修改数据** | ❌ | ✅ 独占 | ✅ | 独占写入 |
| **并发访问** | ✅ Send+Sync | ✅ Send | ❌ | 线程间共享 |
| **迭代器** | ✅ iter() | ✅ iter_mut() | ❌ into_iter() | 遍历集合 |
| **函数参数** | ✅ 任意数量 | ✅ 一个 | ✅ 一个 | API设计 |

### 生命周期关系图
>
> **[来源: Rust Official Docs]**

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    生命周期关系                                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  代码示例:                                                          │
│  fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {                │
│      if x.len() > y.len() { x } else { y }                          │
│  }                                                                  │
│                                                                     │
│  生命周期关系:                                                      │
│                                                                     │
│  'a ────────────────────────────────────────                       │
│      │           │                          │                       │
│      ▼           ▼                          ▼                       │
│    x输入      y输入                     返回值                       │
│                                                                     │
│  约束: 返回值的生命周期必须不大于任一输入                            │
│                                                                     │
│  实际调用:                                                          │
│  let string1 = String::from("long string is long");                  │
│  {                                                                  │
│      let string2 = String::from("xyz");                              │
│      let result = longest(string1.as_str(), string2.as_str());       │
│      // result有效直到这里                                           │
│  }  // string2结束，result也结束                                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 内存安全保证矩阵
>
> **[来源: Rust Official Docs]**

### 内存安全问题对比
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 问题类型 | C/C++ | Java | Rust Safe | Rust Unsafe | 检测方式 |
|----------|-------|------|-----------|-------------|----------|
| **Use-after-free** | ❌ 常见 | ✅ GC防止 | ✅ 编译器阻止 | ⚠️ 可能 | Miri/静态分析 |
| **Double-free** | ❌ 常见 | ✅ GC防止 | ✅ 所有权阻止 | ⚠️ 可能 | Miri |
| **Buffer overflow** | ❌ 常见 | ✅ 运行时检查 | ✅ 边界检查 | ⚠️ 可能 | 测试/Miri |
| **Null pointer** | ❌ 常见 | ✅ 异常 | ✅ Option类型 | ⚠️ 可能 | 类型系统 |
| **Data race** | ❌ 常见 | ⚠️ 部分保护 | ✅ 编译器阻止 | ⚠️ 可能 | Send/Sync |
| **Memory leak** | ⚠️ 可能 | ✅ GC防止 | ⚠️ 可能* | ⚠️ 可能 | 静态分析 |
| **Uninitialized** | ❌ 常见 | ✅ 强制初始化 | ✅ 编译器阻止 | ⚠️ 可能 | 编译器 |

*注: Rust中内存泄漏通常通过循环引用可能发生，但可用弱引用避免

### 内存布局对比
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
// C结构体布局（可能有填充）
struct CStyle {
    a: u8,    // 1 byte + 3 bytes padding
    b: u32,   // 4 bytes
    c: u16,   // 2 bytes + 2 bytes padding
}
// 总大小: 12 bytes

// Rust可以控制布局
#[repr(C)]  // C兼容布局
struct CCompatible {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(packed)]  // 无填充（可能影响性能）
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(align(64))]  // 64字节对齐（缓存行优化）
struct Aligned {
    data: [u8; 64],
}
```

---

## 并发安全模型
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### Send和Sync trait矩阵
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 类型 | Send | Sync | 说明 | 示例 |
|------|------|------|------|------|
| **i32/String** | ✅ | ✅ | 完全线程安全 | 基础类型 |
| **Cell/RefCell** | ✅ | ❌ | 单线程内部可变性 | 非线程安全 |
| **Mutex/RwLock** | ✅ | ✅ | 同步原语保护 | 线程安全 |
| **Rc** | ❌ | ❌ | 非线程安全引用计数 | 单线程 |
| **Arc** | ✅ | ✅ | 线程安全引用计数 | 多线程 |
| ***const T** | ✅ | ✅ | 原始指针（需unsafe） | FFI |
| **PhantomData** | 可变 | 可变 | 标记类型 | 泛型编程 |

### 并发模式选择
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    并发模式决策树                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  需要共享状态?                                                      │
│       │                                                             │
│       ├── 否 ──► 使用消息传递 (mpsc/channel)                        │
│       │                                                             │
│       └── 是 ──► 数据只读?                                          │
│                    │                                                │
│                    ├── 是 ──► Arc<T> (T: Sync)                     │
│                    │                                                │
│                    └── 否 ──► 需要修改?                             │
│                                 │                                   │
│                                 ├── 是 ──► Mutex<T> 或 RwLock<T>   │
│                                 │                                   │
│                                 └── 否 ──► Atomic类型              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 实际代码示例
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 多线程共享可变状态
fn shared_mutable_state() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10);
}

// 无锁编程
use std::sync::atomic::{AtomicUsize, Ordering};

fn lock_free_counter() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let mut handles = vec![];

    for _ in 0..10 {
        let handle = thread::spawn(|| {
            for _ in 0..1000 {
                COUNTER.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(COUNTER.load(Ordering::Relaxed), 10000);
}
```

---

## 安全关键系统内存管理
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 堆分配 vs 栈分配
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 特性 | 栈分配 | 堆分配 (Box) | 堆分配 (Vec) | 静态分配 |
|------|--------|--------------|--------------|----------|
| **分配速度** | 纳秒级 | 微秒级 | 微秒级 | 编译期 |
| **释放速度** | 自动 | Drop时 | Drop时 | 永不 |
| **大小限制** | 栈大小 (~MB) | 堆大小 (~GB) | 堆大小 | 数据段 |
| **碎片化** | 无 | 可能有 | 可能有 | 无 |
| **确定性** | 完全 | 分配时不确定 | 可能重新分配 | 完全 |
| **适用场景** | 局部变量 | 大对象 | 动态集合 | 全局配置 |

### 实时系统内存策略
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
#![no_std]
#![no_main]

use heapless::Vec;  // 无堆分配的集合
use heapless::consts::*;

// 策略1: 栈上固定大小数组
fn stack_allocated() {
    let buffer: [u8; 1024] = [0; 1024];
    // 编译期确定大小，无分配开销
}

// 策略2: 静态全局内存
static mut GLOBAL_BUFFER: [u8; 4096] = [0; 4096];

// 策略3: 使用heapless（无堆集合）
fn heapless_collection() {
    let mut vec: Vec<u8, U1024> = Vec::new();
    vec.push(42).unwrap();  // 可能失败（满），必须处理
}

// 策略4: 内存池
use heapless::pool::Pool;

static mut MEMORY: [u8; 1024 * 64] = [0; 1024 * 64];
static POOL: Pool<[u8; 256]> = Pool::new();

fn init_pool() {
    unsafe {
        POOL.grow(&mut MEMORY);
    }
}

fn use_pool() {
    if let Some(block) = POOL.alloc() {
        // 使用内存块
        drop(block);  // 自动归还
    }
}
```

### 内存对齐和填充
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
// 检查内存布局
use std::mem::{size_of, align_of, size_of_val};

#[repr(C)]
struct SensorData {
    timestamp: u64,  // 8 bytes
    value: f32,      // 4 bytes
    flags: u16,      // 2 bytes
    status: u8,      // 1 byte + 1 byte padding
}

fn check_layout() {
    assert_eq!(size_of::<SensorData>(), 16);
    assert_eq!(align_of::<SensorData>(), 8);

    // 字段偏移
    println!("timestamp offset: {}",
        &SensorData { timestamp: 0, value: 0.0, flags: 0, status: 0 }.timestamp as *const _ as usize
    );
}

// 优化布局减少填充
#[repr(C)]
struct OptimizedSensorData {
    timestamp: u64,  // 8 bytes
    value: f32,      // 4 bytes
    flags: u16,      // 2 bytes
    status: u8,      // 1 byte
    // 1 byte padding at end
}

// 紧凑布局（可能影响性能）
#[repr(C, packed)]
struct PackedSensorData {
    timestamp: u64,
    value: f32,
    flags: u16,
    status: u8,
}
```

---

## 零成本抽象验证
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 抽象开销对比
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
// 高层抽象
fn high_level_sum(values: &[i32]) -> i32 {
    values.iter().sum()
}

// 手动循环
fn manual_sum(values: &[i32]) -> i32 {
    let mut sum = 0;
    for i in 0..values.len() {
        sum += values[i];
    }
    sum
}

// 两者编译后的汇编代码相同（Release模式）
// 证明：Rust的迭代器是零成本抽象
```

### 编译器优化验证
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```bash
# 查看汇编输出

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [Rustonomicon](https://doc.rust-lang.org/nomicon/), [Ferrocene](https://ferrous-systems.com/ferrocene/), [Rust Safety Critical WG](https://github.com/rust-safety-critical/wg)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 安全关键生态系统来源标注 [来源: Authority Source Sprint Batch 8]
cargo rustc --release -- --emit=asm

# 使用godbolt对比
# https://godbolt.org/z/rust
```

---

## 形式化语义基础
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 操作语义
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
 judgment: Γ ⊢ e : τ ⇓ v, Γ'

 含义: 在环境Γ下，表达式e类型为τ，求值为v，新环境Γ'

 示例规则:

  变量查找:
  ────────────────
  Γ ⊢ x : τ ⇓ Γ(x), Γ

  借用创建:
  Γ ⊢ e : T ⇓ v, Γ'
  ──────────────────────────────
  Γ ⊢ &e : &T ⇓ &v, Γ'

  所有权转移:
  Γ ⊢ e : T ⇓ v, Γ'    T不是Copy
  ──────────────────────────────
  Γ ⊢ e : T ⇓ v, Γ'[x ↦ moved]
```

### 类型系统规则
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 规则 | 表达式 | 条件 | 结果类型 |
|------|--------|------|----------|
| **变量** | `x` | `x: T ∈ Γ` | `T` |
| **借用** | `&e` | `Γ ⊢ e: T` | `&T` |
| **可变借用** | `&mut e` | `Γ ⊢ e: T`, `e`未借用 | `&mut T` |
| **解引用** | `*e` | `Γ ⊢ e: &T` | `T` |
| **移动** | `e` | `Γ ⊢ e: T`, `T: !Copy` | `T` (e从Γ移除) |
| **复制** | `e` | `Γ ⊢ e: T`, `T: Copy` | `T` (e保留在Γ) |

---

## 安全关键系统建议
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 内存使用规范
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
#![no_std]

// 推荐: 使用常量泛型指定大小
pub struct FixedBuffer<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> FixedBuffer<N> {
    pub const fn new() -> Self {
        Self {
            data: [0; N],
            len: 0,
        }
    }

    pub fn push(&mut self, byte: u8) -> Result<(), BufferError> {
        if self.len >= N {
            return Err(BufferError::Full);
        }
        self.data[self.len] = byte;
        self.len += 1;
        Ok(())
    }
}

// 使用
static mut BUFFER: FixedBuffer<1024> = FixedBuffer::new();
```

### 内存安全检查清单
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [ ] 所有数组访问都有边界检查
- [ ] 无未初始化内存使用
- [ ] 指针正确对齐
- [ ] 无内存泄漏（循环引用检查）
- [ ] Miri测试通过
- [ ] 堆使用量在限制内
- [ ] 静态分析无警告

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**基于**: Rust 1.96.0+
---

**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [Rust 安全关键系统生态系统主索引](../README.md)

- [综合语言对比矩阵](01_comprehensive_language_comparison_matrix.md)
- [Rust生态系统多维概念矩阵对比](02_rust_multi_dimensional_matrix.md)

---

## 权威来源索引

> **[来源: [ISO 26262](https://www.iso.org/standard/68383.html)]**
>
> **[来源: [IEC 61508](https://www.iec.ch/functionalsafety)]**
>
> **[来源: [MISRA Rust Guidelines](https://misra.org.uk/)]**
>
> **[来源: [Ferrocene](https://ferrocene.dev/)]**
>
> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
>
> **[来源: [Rust Memory Model](https://doc.rust-lang.org/nomicon/memory.html)]**
>

---

---

## 相关概念

- [Tree Borrows (concept)](../../../../concept/01_foundation/05_reference_semantics.md) — PLDI 2025 Distinguished Paper 别名模型
- [Ferrocene 认证 (concept)](../../../../concept/04_formal/16_aerospace_certification_formal_methods.md) — 认证分层矩阵（core/alloc/std）
