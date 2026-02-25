# Unsafe Rust 专题指南

> **创建日期**: 2026-02-15
> **最后更新**: 2026-02-26
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [Unsafe Rust 专题指南](#unsafe-rust-专题指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [文档定位](#文档定位)
  - [🎯 何时使用 Unsafe {#-何时使用-unsafe}](#-何时使用-unsafe--何时使用-unsafe)
  - [📚 核心 Unsafe 操作 {#-核心-unsafe-操作}](#-核心-unsafe-操作--核心-unsafe-操作)
  - [💻 完整代码示例 {#-完整代码示例}](#-完整代码示例--完整代码示例)
    - [1. 原始指针操作](#1-原始指针操作)
    - [2. 调用外部函数 (FFI)](#2-调用外部函数-ffi)
    - [3. 实现 Send/Sync](#3-实现-sendsync)
    - [4. Union 访问](#4-union-访问)
    - [5. 内联汇编](#5-内联汇编)
    - [6. 自定义智能指针](#6-自定义智能指针)
  - [⚠️ 未定义行为 (UB) 案例 {#️-未定义行为-ub-案例}](#️-未定义行为-ub-案例-️-未定义行为-ub-案例)
    - [案例 1: 空指针解引用](#案例-1-空指针解引用)
    - [案例 2: 悬垂指针](#案例-2-悬垂指针)
    - [案例 3: 数据竞争](#案例-3-数据竞争)
    - [案例 4: 类型混淆](#案例-4-类型混淆)
    - [案例 5: 无效枚举值](#案例-5-无效枚举值)
    - [案例 6: 越界访问](#案例-6-越界访问)
    - [案例 7: 违反借用规则](#案例-7-违反借用规则)
    - [案例 8: 不恰当的 Drop 实现](#案例-8-不恰当的-drop-实现)
  - [🛡️ 安全抽象原则 {#️-安全抽象原则}](#️-安全抽象原则-️-安全抽象原则)
  - [🔬 Miri 检测工具 {#-miri-检测工具}](#-miri-检测工具--miri-检测工具)
  - [📖 形式化安全边界 {#-形式化安全边界}](#-形式化安全边界--形式化安全边界)
    - [安全/非安全边界分析](#安全非安全边界分析)
    - [形式化资源](#形式化资源)
  - [🔗 推荐学习路径 {#-推荐学习路径}](#-推荐学习路径--推荐学习路径)
  - [📖 Rustonomicon 逐章对标表 {#-rustonomicon-逐章对标表}](#-rustonomicon-逐章对标表--rustonomicon-逐章对标表)

---

## 文档定位

本指南为 **Rustonomicon** 的补充与项目内导航，帮助在系统学习 unsafe Rust 时快速定位到本项目的相关模块和示例。

**形式化引用**：T-OW3 (内存安全框架)、T-BR1 (数据竞争自由)。详见 [ownership_model](../research_notes/formal_methods/ownership_model.md)、[borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md)、[THEOREM_RUST_EXAMPLE_MAPPING](../research_notes/THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## 🎯 何时使用 Unsafe {#-何时使用-unsafe}

Rust 的 `unsafe` 关键字允许你执行以下五种操作：

1. **解引用原始指针** - `*const T` 和 `*mut T`
2. **调用 `unsafe` 函数** - 包括外部函数（FFI）
3. **实现 `unsafe` trait** - 主要是 `Send` 和 `Sync`
4. **访问 `union` 的字段**
5. **使用 `asm!` 内联汇编** (Rust 1.90+)

```rust
unsafe {
    // 在 unsafe 块中执行上述操作
}

unsafe fn dangerous_function() {
    // 整个函数体都是 unsafe 上下文
}

unsafe trait MyUnsafeTrait {
    // trait 定义
}

unsafe impl MyUnsafeTrait for MyType {
    // 实现
}
```

---

## 📚 核心 Unsafe 操作 {#-核心-unsafe-操作}

| 操作 | 说明 | 风险 |
| :--- | :--- | :--- |
| 原始指针 | `*const T`, `*mut T` | 悬垂指针、空指针 |
| FFI 调用 | `extern "C"` | ABI 不匹配、内存管理 |
| Send/Sync 实现 | `unsafe impl` | 数据竞争 |
| Union 访问 | `union` 字段 | 类型混淆 |
| 内联汇编 | `asm!` | 完全无保护 |

---

## 💻 完整代码示例 {#-完整代码示例}

### 1. 原始指针操作

```rust
use std::alloc::{alloc, dealloc, Layout};

/// 安全抽象的动态数组（简化版 Vec）
struct RawVec<T> {
    ptr: *mut T,
    cap: usize,
}

impl<T> RawVec<T> {
    fn new() -> Self {
        // 零大小类型的特殊处理
        let cap = if std::mem::size_of::<T>() == 0 { usize::MAX } else { 0 };
        Self {
            ptr: std::ptr::NonNull::dangling().as_ptr(),
            cap,
        }
    }

    fn with_capacity(cap: usize) -> Self {
        if cap == 0 || std::mem::size_of::<T>() == 0 {
            return Self::new();
        }

        // 计算布局
        let layout = Layout::array::<T>(cap).expect("容量溢出");

        // 分配内存 - unsafe!
        let ptr = unsafe { alloc(layout) } as *mut T;

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        Self { ptr, cap }
    }

    fn ptr(&self) -> *mut T {
        self.ptr
    }

    fn cap(&self) -> usize {
        self.cap
    }
}

impl<T> Drop for RawVec<T> {
    fn drop(&mut self) {
        if self.cap != 0 && std::mem::size_of::<T>() != 0 {
            let layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                dealloc(self.ptr as *mut u8, layout);
            }
        }
    }
}

// 使用示例
fn raw_pointer_demo() {
    let mut raw = RawVec::<i32>::with_capacity(10);

    // 安全地写入数据
    unsafe {
        for i in 0..10 {
            raw.ptr().add(i).write(i as i32 * 10);
        }

        // 安全地读取数据
        for i in 0..10 {
            let val = raw.ptr().add(i).read();
            println!("raw[{}] = {}", i, val);
        }
    }
} // 自动调用 Drop，释放内存
```

### 2. 调用外部函数 (FFI)

```rust
use std::os::raw::{c_char, c_int, c_void};
use std::ffi::{CStr, CString};

// 链接 C 标准库
extern "C" {
    fn strlen(s: *const c_char) -> usize;
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
    fn memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
}

/// 安全的 C 字符串包装
struct CStrings {
    ptr: *mut c_char,
}

impl CStrings {
    fn new(s: &str) -> Result<Self, std::ffi::NulError> {
        let c_string = CString::new(s)?;
        Ok(Self {
            ptr: c_string.into_raw(),
        })
    }

    fn len(&self) -> usize {
        unsafe { strlen(self.ptr) }
    }

    fn as_str(&self) -> &str {
        unsafe {
            CStr::from_ptr(self.ptr)
                .to_str()
                .expect("无效的 UTF-8")
        }
    }
}

impl Drop for CStrings {
    fn drop(&mut self) {
        unsafe {
            // 重新获取所有权并正确释放
            let _ = CString::from_raw(self.ptr);
        }
    }
}

/// 安全的内存复制
fn safe_memcpy<T: Copy>(src: &[T], dest: &mut [T]) {
    assert!(src.len() <= dest.len(), "目标缓冲区太小");

    unsafe {
        memcpy(
            dest.as_mut_ptr() as *mut c_void,
            src.as_ptr() as *const c_void,
            src.len() * std::mem::size_of::<T>(),
        );
    }
}

// 使用示例
fn ffi_demo() {
    let c_str = CStrings::new("Hello, FFI!").unwrap();
    println!("字符串长度: {}", c_str.len());
    println!("字符串内容: {}", c_str.as_str());

    let src = [1, 2, 3, 4, 5];
    let mut dest = [0; 5];
    safe_memcpy(&src, &mut dest);
    println!("复制结果: {:?}", dest);
}
```

### 3. 实现 Send/Sync

```rust
use std::sync::atomic::{AtomicPtr, Ordering};

/// 线程安全的原始指针包装
/// 注意：只有我们知道 T 是 Send + Sync 时才安全
struct SendPtr<T>(*const T);

// 标记为 Send - 只要 T 是 Send
unsafe impl<T: Send> Send for SendPtr<T> {}

// 标记为 Sync - 只要 T 是 Sync
unsafe impl<T: Sync> Sync for SendPtr<T> {}

/// 线程安全的堆栈（无锁）
struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

// 我们保证 Node<T> 的指针操作是线程安全的
unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send> Sync for LockFreeStack<T> {}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        Self {
            head: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: std::ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            match self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => continue, // 重试
            }
        }
    }

    fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            match self.head.compare_exchange_weak(
                head,
                next,
                Ordering::Relaxed,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // 成功获取所有权
                    let node = unsafe { Box::from_raw(head) };
                    return Some(node.data);
                }
                Err(_) => continue,
            }
        }
    }
}

impl<T> Drop for LockFreeStack<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}
```

### 4. Union 访问

```rust
/// FFI 中常见的联合类型
#[repr(C)]
union Value {
    int: i32,
    float: f32,
    bytes: [u8; 4],
}

/// 安全的 Value 包装
enum TypedValue {
    Int(i32),
    Float(f32),
    Bytes([u8; 4]),
}

impl Value {
    fn as_int(&self) -> i32 {
        unsafe { self.int }
    }

    fn as_float(&self) -> f32 {
        unsafe { self.float }
    }

    fn as_bytes(&self) -> [u8; 4] {
        unsafe { self.bytes }
    }

    fn from_int(i: i32) -> Self {
        Self { int: i }
    }
}

// 使用示例
fn union_demo() {
    let v = Value::from_int(0x3F800000); // f32 1.0 的二进制表示

    println!("As int: {}", v.as_int());
    println!("As float: {}", v.as_float());
    println!("As bytes: {:?}", v.as_bytes());
}
```

### 5. 内联汇编

```rust
// 需要 Rust 1.90+
#[cfg(target_arch = "x86_64")]
fn read_tsc() -> u64 {
    let low: u32;
    let high: u32;

    unsafe {
        std::arch::asm!(
            "rdtsc",
            out("eax") low,
            out("edx") high,
            options(nomem, nostack)
        );
    }

    ((high as u64) << 32) | (low as u64)
}

/// 安全的 CPU 周期计数器
pub fn cpu_cycles() -> u64 {
    #[cfg(target_arch = "x86_64")]
    return read_tsc();

    #[cfg(not(target_arch = "x86_64"))]
    compile_error!("不支持此架构");
}

/// 内存屏障
#[cfg(target_arch = "x86_64")]
pub fn memory_fence() {
    unsafe {
        std::arch::asm!("mfence", options(nomem, nostack));
    }
}
```

### 6. 自定义智能指针

```rust
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

/// 自定义 Box（教学用）
struct MyBox<T> {
    ptr: NonNull<T>,
}

impl<T> MyBox<T> {
    fn new(data: T) -> Self {
        let layout = std::alloc::Layout::new::<T>();

        unsafe {
            let ptr = std::alloc::alloc(layout) as *mut T;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // 写入数据
            ptr.write(data);

            Self {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    fn into_inner(self) -> T {
        unsafe {
            let data = self.ptr.as_ptr().read();
            std::mem::forget(self); // 防止 Drop 运行
            data
        }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe {
            // 调用析构函数
            self.ptr.as_ptr().drop_in_place();

            // 释放内存
            let layout = std::alloc::Layout::new::<T>();
            std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, layout);
        }
    }
}

// 确保线程安全
unsafe impl<T: Send> Send for MyBox<T> {}
unsafe impl<T: Sync> Sync for MyBox<T> {}
```

---

## ⚠️ 未定义行为 (UB) 案例 {#️-未定义行为-ub-案例}

### 案例 1: 空指针解引用

```rust
// ❌ UB: 解引用空指针
unsafe {
    let ptr: *const i32 = std::ptr::null();
    let _ = *ptr; // 立即 UB！
}

// ❌ UB: 使用未初始化的指针
unsafe {
    let ptr: *const i32;
    let _ = *ptr; // 未定义指针值
}

// ✅ 安全：检查后再解引用
unsafe {
    let ptr: *const i32 = some_source();
    if !ptr.is_null() {
        let val = *ptr; // 安全
    }
}
```

### 案例 2: 悬垂指针

```rust
// ❌ UB: 使用释放后的指针
unsafe {
    let ptr: *const i32 = {
        let x = 42;
        &x as *const i32 // x 在作用域结束时释放
    };
    let _ = *ptr; // UB: 悬垂指针！
}

// ❌ UB: Vec 重新分配后使用旧指针
unsafe {
    let mut v = vec![1, 2, 3];
    let ptr = v.as_ptr();
    v.push(4); // 可能重新分配
    let _ = *ptr; // UB: 可能指向已释放内存
}

// ✅ 安全：使用智能指针管理生命周期
let my_box = MyBox::new(42);
println!("{}", *my_box);
```

### 案例 3: 数据竞争

```rust
// ❌ UB: 多线程无同步访问
static mut COUNTER: i32 = 0;

fn increment() {
    unsafe {
        COUNTER += 1; // 多线程调用时是 UB！
    }
}

// ❌ UB: &mut T 和 &T 同时存在
unsafe {
    let mut x = 42;
    let r1 = &mut x;
    let r2 = &x; // 与 r1 重叠的生命周期
    println!("{} {}", r1, r2); // UB！
}

// ✅ 安全：使用原子类型
use std::sync::atomic::{AtomicI32, Ordering};
static COUNTER: AtomicI32 = AtomicI32::new(0);
COUNTER.fetch_add(1, Ordering::SeqCst);
```

### 案例 4: 类型混淆

```rust
// ❌ UB: 违反类型对齐
unsafe {
    let bytes: [u8; 8] = [0; 8];
    let ptr = bytes.as_ptr() as *const u64;
    let _ = *ptr; // 可能未对齐！
}

// ❌ UB: &mut 和 &mut 别名
unsafe {
    let mut x = 42;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;
    *r1 = 1;
    *r2 = 2; // 与 r1 重叠的写入
}

// ❌ UB: 错误的类型转换
unsafe {
    let x: f32 = 1.0;
    let ptr = &x as *const f32 as *const i32;
    let _ = *ptr; // UB: 非法的 "主动" 类型混淆
}

// ✅ 安全：使用 read_unaligned
unsafe {
    let bytes: [u8; 8] = [0; 8];
    let val = ptr.read_unaligned(); // 明确处理未对齐
}
```

### 案例 5: 无效枚举值

```rust
#[repr(u8)]
enum Color {
    Red = 0,
    Green = 1,
    Blue = 2,
}

// ❌ UB: 创建无效的枚举值
unsafe {
    let color: Color = std::mem::transmute(3u8); // 3 不是有效的变体！
    match color {
        Color::Red | Color::Green | Color::Blue => {}
    }
}

// ✅ 安全：检查有效性或使用 MaybeUninit
use std::mem::MaybeUninit;

let maybe_color: MaybeUninit<Color> = MaybeUninit::new(
    unsafe { std::mem::transmute(3u8) }
);
```

### 案例 6: 越界访问

```rust
// ❌ UB: 越界访问
unsafe {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    let _ = *ptr.add(100); // 越界！
}

// ❌ UB: 切片长度欺骗
unsafe {
    let arr = [1i32, 2, 3];
    let slice = std::slice::from_raw_parts(
        arr.as_ptr(),
        1000 // 错误的元素数量
    );
}

// ✅ 安全：正确的边界检查
unsafe {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    let idx = 1;
    assert!(idx < arr.len());
    let val = *ptr.add(idx);
}
```

### 案例 7: 违反借用规则

```rust
// ❌ UB: 同时存在可变和不可变借用
unsafe {
    let mut x = 42;
    let r1 = &x as *const i32;
    let r2 = &mut x as *mut i32;
    println!("{} {}", *r1, *r2); // 重叠的不变+可变
}

// ❌ UB: 多个可变借用重叠
unsafe {
    let mut x = [1, 2, 3, 4];
    let ptr = x.as_mut_ptr();
    let r1 = std::slice::from_raw_parts_mut(ptr, 3);
    let r2 = std::slice::from_raw_parts_mut(ptr.add(2), 2);
    // r1 和 r2 在索引 2 处重叠！
}

// ✅ 安全：确保借用不重叠
unsafe {
    let mut x = [1, 2, 3, 4];
    let ptr = x.as_mut_ptr();
    let r1 = std::slice::from_raw_parts_mut(ptr, 2);
    let r2 = std::slice::from_raw_parts_mut(ptr.add(2), 2);
    // r1: [1, 2], r2: [3, 4] - 不重叠
}
```

### 案例 8: 不恰当的 Drop 实现

```rust
// ❌ UB: 二次释放
struct BadDrop {
    ptr: *mut u8,
}

impl Drop for BadDrop {
    fn drop(&mut self) {
        unsafe {
            std::alloc::dealloc(self.ptr, std::alloc::Layout::new::<u8>());
        }
    }
}

fn bad() {
    let x = BadDrop { ptr: allocate() };
    let y = BadDrop { ptr: x.ptr }; // 共享指针
} // x 和 y 都释放同一块内存！UB！

// ❌ UB: use-after-free in Drop
impl Drop for BadDrop {
    fn drop(&mut self) {
        unsafe {
            let val = *self.ptr; // 读取
            dealloc(self.ptr);   // 释放
            println!("{}", val); // 释放后使用！
        }
    }
}

// ✅ 安全：使用 Unique 指针或封装所有权
struct SafeDrop {
    ptr: std::ptr::NonNull<u8>,
}

impl Drop for SafeDrop {
    fn drop(&mut self) {
        unsafe {
            std::alloc::dealloc(self.ptr.as_ptr(), std::alloc::Layout::new::<u8>());
        }
    }
}
```

---

## 🛡️ 安全抽象原则 {#️-安全抽象原则}

> **对应 Nomicon**: [Working with Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)

1. **封装 unsafe**: 将 `unsafe` 块封装在安全 API 内部

   ```rust
   // 安全的公开 API
   pub fn safe_api() -> Result<String, Error> {
       unsafe {
           // 内部使用 unsafe
           internal_unsafe_op()
       }
   }
   ```

2. **不变式文档化**: 明确写出 `unsafe` 依赖的前提条件

   ```rust
   /// # Safety
   /// `ptr` 必须是非空且正确对齐的有效指针
   unsafe fn dangerous(ptr: *const i32) -> i32 {
       *ptr
   }
   ```

3. **最小化范围**: 仅对必需的操作使用 `unsafe`

   ```rust
   // ❌ 不好的做法
   unsafe {
       let a = safe_op1();
       let b = dangerous_op();
       let c = safe_op2();
   }

   // ✅ 好的做法
   let a = safe_op1();
   let b = unsafe { dangerous_op() };
   let c = safe_op2();
   ```

4. **Miri 验证**: 使用 Miri 检测潜在的 UB

   ```bash
   cargo +nightly miri test
   ```

---

## 🔬 Miri 检测工具 {#-miri-检测工具}

Miri 是 Rust 的内存安全检测工具，可以检测大多数 UB。

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 运行特定程序
cargo miri run

# 检查环境变量影响
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

Miri 可以检测：

- 未对齐的内存访问
- 悬垂指针使用
- 数据竞争
- 无效的枚举值
- 越界访问
- 未初始化内存使用

---

## 📖 形式化安全边界 {#-形式化安全边界}

### 安全/非安全边界分析

| 层次 | 说明 | 文档链接 |
| :--- | :--- | :--- |
| **安全 API** | 完全由编译器保证安全 | Rust 标准库 |
| **安全抽象** | unsafe 内部实现，安全外部接口 | 本指南 |
| **unsafe 块** | 程序员负责安全 | [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
| **unsafe 函数** | 调用者负责前置条件 | [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
| **UB 边界** | 一旦违反，行为未定义 | 本指南 §UB 案例 |

### 形式化资源

- **理论体系与安全论证**: [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) - 安全与非安全边界、理论四层
- **借用检查器证明**: [borrow_checker_proof.md](../research_notes/formal_methods/borrow_checker_proof.md) - 形式化证明内存安全
- **所有权模型**: [ownership_model.md](../research_notes/formal_methods/ownership_model.md) - 所有权系统形式化
- **safe/unsafe 边界矩阵**: [safe_unsafe_matrix.md](../research_notes/software_design_theory/05_boundary_system/safe_unsafe_matrix.md)

---

## 🔗 推荐学习路径 {#-推荐学习路径}

> **对应 Nomicon 阅读顺序**: [Meet Safe and Unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) → [How Safe and Unsafe Interact](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) → [What Unsafe Rust Can Do](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) → [Working with Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)

1. **通读 Nomicon 前 4 节**（Meet Safe、Interact、What Unsafe Does、Working with Unsafe）
2. 学习 C01 的零成本抽象与高级所有权
3. 研究本项目 `formal_methods` 中的形式化证明
4. 实践：为现有安全 API 编写 `unsafe` 实现（如自定义集合）

---

## 📖 Rustonomicon 逐章对标表 {#-rustonomicon-逐章对标表}

| Nomicon 章节 | 官方链接 | 本指南对应小节 |
| :--- | :--- | :--- |
| **Meet Safe and Unsafe** | [meet-safe-and-unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) | § 文档定位、§ 何时使用 Unsafe |
| **How Safe and Unsafe Interact** | [safe-unsafe-meaning](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) | § 安全抽象原则 |
| **What Unsafe Can Do** | [what-unsafe-does](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | § 核心 Unsafe 操作、§ UB 案例 |
| **Working with Unsafe** | [working-with-unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) | § 安全抽象原则、§ 推荐学习路径 |
| **Data Layout** | [data](https://doc.rust-lang.org/nomicon/data.html) | 本项目 [type_system](../02_reference/quick_reference/type_system.md) |
| **Ownership** | [ownership](https://doc.rust-lang.org/nomicon/ownership.html) | [ownership_model](../research_notes/formal_methods/ownership_model.md)、[ownership_cheatsheet](../02_reference/quick_reference/ownership_cheatsheet.md) |
| **Subtyping and Variance** | [subtyping](https://doc.rust-lang.org/nomicon/subtyping.html) | [VARIANCE_CONCEPT_MINDMAP](../research_notes/formal_methods/VARIANCE_CONCEPT_MINDMAP.md) |
| **Type Conversions / Transmutes** | [transmutes](https://doc.rust-lang.org/nomicon/transmutes.html) | § UB 案例 4 类型混淆 |
| **Uninitialized Memory** | [uninitialized](https://doc.rust-lang.org/nomicon/uninitialized.html) | § UB 案例 6 越界、§ Miri |
| **Destructors / Drop** | [destructors](https://doc.rust-lang.org/nomicon/destructors.html) | § UB 案例 8 不恰当的 Drop |
| **Exception Safety** | [exception-safety](https://doc.rust-lang.org/nomicon/exception-safety.html) | [EDGE_CASES_AND_SPECIAL_CASES](../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) |
| **Concurrency / Send and Sync** | [send-and-sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | § 示例 3 实现 Send/Sync、[threads_concurrency_cheatsheet](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) |
| **Implementing Vec** | [vec](https://doc.rust-lang.org/nomicon/vec/vec.html) | § 示例 1 原始指针、§ 示例 6 自定义智能指针 |
| **Implementing Arc** | [arc](https://doc.rust-lang.org/nomicon/arc-mutex/arc.html) | [smart_pointers_cheatsheet](../02_reference/quick_reference/smart_pointers_cheatsheet.md) |
| **FFI** | [ffi](https://doc.rust-lang.org/nomicon/ffi.html) | § 示例 2 调用外部函数 |

> **官方入口**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/) · 与 Rust 1.93 对应见 [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-02-20
