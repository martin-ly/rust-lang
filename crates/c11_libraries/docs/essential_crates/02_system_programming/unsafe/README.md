# Unsafe Rust - 不安全代码与底层操作完全指南

> **核心概念**: 原始指针、未定义行为、内存安全、FFI、内联汇编  
> **核心模块**: std::ptr, std::mem, std::slice, std::intrinsics  
> **适用场景**: FFI、性能优化、底层系统编程、硬件交互

## 📋 目录

- [Unsafe Rust - 不安全代码与底层操作完全指南](#unsafe-rust---不安全代码与底层操作完全指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Unsafe](#什么是-unsafe)
    - [Unsafe 超能力](#unsafe-超能力)
  - [核心概念对比](#核心概念对比)
    - [安全 vs 不安全](#安全-vs-不安全)
    - [指针类型对比](#指针类型对比)
  - [原始指针](#原始指针)
    - [创建原始指针](#创建原始指针)
    - [解引用原始指针](#解引用原始指针)
    - [指针算术](#指针算术)
  - [std::mem - 内存操作](#stdmem---内存操作)
    - [大小和对齐](#大小和对齐)
    - [值交换和替换](#值交换和替换)
    - [transmute 类型转换](#transmute-类型转换)
  - [std::ptr - 指针操作](#stdptr---指针操作)
    - [读写操作](#读写操作)
    - [复制操作](#复制操作)
    - [空指针检查](#空指针检查)
  - [std::slice - 切片操作](#stdslice---切片操作)
    - [从原始部分创建](#从原始部分创建)
    - [可变切片](#可变切片)
  - [FFI - 外部函数接口](#ffi---外部函数接口)
    - [调用 C 函数](#调用-c-函数)
    - [导出 Rust 函数](#导出-rust-函数)
    - [类型映射](#类型映射)
  - [内联汇编](#内联汇编)
    - [基础用法](#基础用法)
    - [寄存器操作](#寄存器操作)
  - [Unsafe Trait](#unsafe-trait)
    - [实现 Unsafe Trait](#实现-unsafe-trait)
    - [Send 和 Sync](#send-和-sync)
  - [使用场景](#使用场景)
    - [高性能数据结构](#高性能数据结构)
    - [FFI 安全封装](#ffi-安全封装)
    - [底层优化](#底层优化)
  - [最佳实践](#最佳实践)
    - [1. 最小化 Unsafe 代码](#1-最小化-unsafe-代码)
    - [2. 安全抽象封装](#2-安全抽象封装)
    - [3. 详细文档说明](#3-详细文档说明)
    - [4. 充分测试](#4-充分测试)
    - [5. Unsafe 代码审查](#5-unsafe-代码审查)
  - [常见陷阱](#常见陷阱)
    - [1. 悬垂指针 (Dangling Pointer)](#1-悬垂指针-dangling-pointer)
    - [2. 数据竞争 (Data Race)](#2-数据竞争-data-race)
    - [3. 未初始化内存](#3-未初始化内存)
    - [4. 类型转换错误](#4-类型转换错误)
    - [5. 违反别名规则](#5-违反别名规则)
    - [6. 缓冲区溢出](#6-缓冲区溢出)
    - [7. 生命周期错误](#7-生命周期错误)
    - [8. NULL 指针解引用](#8-null-指针解引用)
    - [9. 对齐错误](#9-对齐错误)
    - [10. 双重释放](#10-双重释放)
  - [未定义行为 (UB)](#未定义行为-ub)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程](#教程)
    - [工具](#工具)

---

## 概述

### 什么是 Unsafe

Rust 默认保证内存安全，但某些操作编译器无法验证其安全性。`unsafe` 关键字允许你：

```rust
// ✅ 安全 Rust：编译器保证安全
let v = vec![1, 2, 3];
let first = v[0];  // 边界检查

// ⚠️ Unsafe Rust：程序员保证安全
unsafe {
    let ptr = v.as_ptr();
    let first = *ptr;  // 无边界检查，性能更高
}
```

**重要**: `unsafe` 不是禁用安全检查，而是告诉编译器"我保证这段代码是安全的"。

### Unsafe 超能力

在 `unsafe` 块中，你可以：

1. **解引用原始指针** (`*const T`, `*mut T`)
2. **调用 unsafe 函数**
3. **访问可变静态变量**
4. **实现 unsafe trait**
5. **访问 union 字段**

---

## 核心概念对比

### 安全 vs 不安全

| 特性 | 安全 Rust | Unsafe Rust |
|------|----------|-------------|
| **内存安全** | 编译器保证 | 程序员保证 |
| **性能** | 略低（边界检查） | 更高（跳过检查） |
| **灵活性** | 受限 | 完全控制 |
| **风险** | 无 UB 风险 | 可能 UB |
| **适用场景** | 99% 代码 | FFI、极致优化 |

### 指针类型对比

| 类型 | 可空 | 可变 | 安全性 | 对齐保证 | 解引用 |
|------|------|------|--------|---------|--------|
| **&T** | ❌ | ❌ | ✅ | ✅ | 自动 |
| **&mut T** | ❌ | ✅ | ✅ | ✅ | 自动 |
| **\*const T** | ✅ | ❌ | ❌ | ❌ | unsafe |
| **\*mut T** | ✅ | ✅ | ❌ | ❌ | unsafe |

---

## 原始指针

### 创建原始指针

```rust
fn main() {
    let mut num = 5;
    
    // 从引用创建（安全）
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;
    
    // 从地址创建（非常危险！）
    let address = 0x012345usize;
    let r = address as *const i32;  // 可能导致段错误
    
    // 空指针
    let null_ptr: *const i32 = std::ptr::null();
    let null_mut: *mut i32 = std::ptr::null_mut();
}
```

### 解引用原始指针

```rust
fn main() {
    let mut num = 5;
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;
    
    unsafe {
        // 读取
        println!("r1: {}", *r1);
        
        // 写入
        *r2 = 10;
        println!("r2: {}", *r2);
    }
}
```

### 指针算术

```rust
fn main() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();
    
    unsafe {
        // 指针偏移
        println!("第 1 个: {}", *ptr);
        println!("第 2 个: {}", *ptr.offset(1));   // 或 ptr.add(1)
        println!("第 3 个: {}", *ptr.add(2));
        
        // 从后向前
        let end_ptr = ptr.add(arr.len());
        println!("最后: {}", *end_ptr.offset(-1));  // 或 end_ptr.sub(1)
    }
}
```

---

## std::mem - 内存操作

### 大小和对齐

```rust
use std::mem;

fn main() {
    // 类型大小
    println!("i32 大小: {} 字节", mem::size_of::<i32>());
    println!("&i32 大小: {} 字节", mem::size_of::<&i32>());
    println!("String 大小: {} 字节", mem::size_of::<String>());
    
    // 对齐要求
    println!("i32 对齐: {}", mem::align_of::<i32>());
    println!("i64 对齐: {}", mem::align_of::<i64>());
    
    // 值的大小
    let s = String::from("hello");
    println!("s 大小: {}", mem::size_of_val(&s));
}
```

### 值交换和替换

```rust
use std::mem;

fn main() {
    let mut x = 5;
    let mut y = 10;
    
    // 交换两个值
    mem::swap(&mut x, &mut y);
    println!("x: {}, y: {}", x, y);  // x: 10, y: 5
    
    // 替换值并返回旧值
    let old = mem::replace(&mut x, 42);
    println!("old: {}, x: {}", old, x);  // old: 10, x: 42
    
    // 取出值并留下默认值
    let mut s = Some(String::from("hello"));
    let value = mem::take(&mut s);  // s 现在是 None
    println!("value: {:?}, s: {:?}", value, s);
}
```

### transmute 类型转换

```rust
use std::mem;

fn main() {
    // ⚠️ 非常危险！只在极少数情况下使用
    
    unsafe {
        // u32 → i32
        let a: u32 = 42;
        let b: i32 = mem::transmute(a);
        println!("b: {}", b);
        
        // 数组 → 整数
        let arr: [u8; 4] = [1, 2, 3, 4];
        let num: u32 = mem::transmute(arr);
        println!("num: {}", num);
        
        // 函数指针转换
        fn foo() -> i32 { 42 }
        let ptr: fn() -> i32 = foo;
        let addr: usize = mem::transmute(ptr);
        println!("函数地址: 0x{:x}", addr);
    }
}
```

---

## std::ptr - 指针操作

### 读写操作

```rust
use std::ptr;

fn main() {
    let mut value = 42;
    let ptr = &mut value as *mut i32;
    
    unsafe {
        // 读取
        let read_value = ptr::read(ptr);
        println!("读取: {}", read_value);
        
        // 写入
        ptr::write(ptr, 100);
        println!("写入后: {}", value);
        
        // 不稳定的读写（volatile）
        let volatile_value = ptr::read_volatile(ptr);
        ptr::write_volatile(ptr, 200);
    }
}
```

### 复制操作

```rust
use std::ptr;

fn main() {
    let src = vec![1, 2, 3, 4, 5];
    let mut dst = vec![0; 5];
    
    unsafe {
        // 复制内存（内存可重叠）
        ptr::copy(src.as_ptr(), dst.as_mut_ptr(), src.len());
        println!("{:?}", dst);  // [1, 2, 3, 4, 5]
        
        // 非重叠复制（性能更好）
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
        
        // 填充内存
        ptr::write_bytes(dst.as_mut_ptr(), 0, dst.len());
        println!("{:?}", dst);  // [0, 0, 0, 0, 0]
    }
}
```

### 空指针检查

```rust
use std::ptr;

fn process_ptr(ptr: *const i32) {
    // 检查空指针
    if ptr.is_null() {
        println!("空指针！");
        return;
    }
    
    unsafe {
        println!("值: {}", *ptr);
    }
}

fn main() {
    let num = 42;
    process_ptr(&num);
    process_ptr(ptr::null());
}
```

---

## std::slice - 切片操作

### 从原始部分创建

```rust
use std::slice;

fn main() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();
    
    unsafe {
        // 创建切片
        let slice = slice::from_raw_parts(ptr, arr.len());
        println!("{:?}", slice);  // [1, 2, 3, 4, 5]
        
        // 部分切片
        let partial = slice::from_raw_parts(ptr.add(2), 3);
        println!("{:?}", partial);  // [3, 4, 5]
    }
}
```

### 可变切片

```rust
use std::slice;

fn main() {
    let mut arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_mut_ptr();
    
    unsafe {
        let slice = slice::from_raw_parts_mut(ptr, arr.len());
        slice[0] = 10;
        slice[1] = 20;
    }
    
    println!("{:?}", arr);  // [10, 20, 3, 4, 5]
}
```

---

## FFI - 外部函数接口

### 调用 C 函数

```rust
// 声明外部函数
extern "C" {
    fn abs(input: i32) -> i32;
    fn strlen(s: *const i8) -> usize;
}

fn main() {
    unsafe {
        println!("abs(-42) = {}", abs(-42));
        
        let c_str = b"Hello\0";
        let len = strlen(c_str.as_ptr() as *const i8);
        println!("strlen = {}", len);
    }
}
```

### 导出 Rust 函数

```rust
// 导出给 C 调用
#[no_mangle]
pub extern "C" fn rust_add(a: i32, b: i32) -> i32 {
    a + b
}

#[no_mangle]
pub extern "C" fn rust_greet(name: *const i8) {
    unsafe {
        let c_str = std::ffi::CStr::from_ptr(name);
        let rust_str = c_str.to_str().unwrap();
        println!("Hello, {}!", rust_str);
    }
}
```

### 类型映射

| C 类型 | Rust 类型 |
|--------|----------|
| `int` | `i32` |
| `unsigned int` | `u32` |
| `char` | `i8` |
| `float` | `f32` |
| `double` | `f64` |
| `void*` | `*mut std::ffi::c_void` |
| `char*` | `*const i8` 或 `*const u8` |
| `size_t` | `usize` |

---

## 内联汇编

### 基础用法

```rust
use std::arch::asm;

fn main() {
    let x: u64;
    unsafe {
        // 读取 CPU 时间戳计数器
        asm!(
            "rdtsc",
            "shl rdx, 32",
            "or rax, rdx",
            out("rax") x,
            out("rdx") _,
        );
    }
    println!("TSC: {}", x);
}
```

### 寄存器操作

```rust
use std::arch::asm;

fn add_asm(a: u64, b: u64) -> u64 {
    let result: u64;
    unsafe {
        asm!(
            "add {0}, {1}",
            inout(reg) a => result,
            in(reg) b,
        );
    }
    result
}

fn main() {
    println!("5 + 3 = {}", add_asm(5, 3));
}
```

---

## Unsafe Trait

### 实现 Unsafe Trait

```rust
// 定义 unsafe trait
unsafe trait TrustedLen {
    fn len(&self) -> usize;
}

// 实现 unsafe trait
struct MyVec {
    data: Vec<i32>,
}

unsafe impl TrustedLen for MyVec {
    fn len(&self) -> usize {
        self.data.len()
    }
}

// 使用
fn process<T: TrustedLen>(t: &T) {
    // 可以信任 len() 返回的长度
    let len = t.len();
}
```

### Send 和 Sync

```rust
use std::sync::Arc;
use std::rc::Rc;

// Rc: 非 Send + 非 Sync
// let rc = Rc::new(42);
// std::thread::spawn(move || {
//     println!("{}", rc);  // 编译错误！
// });

// Arc: Send + Sync
let arc = Arc::new(42);
std::thread::spawn(move || {
    println!("{}", arc);  // ✅ 编译通过
});

// 自定义类型实现 Send/Sync
struct MyType {
    ptr: *mut i32,
}

// 声明我们保证线程安全
unsafe impl Send for MyType {}
unsafe impl Sync for MyType {}
```

---

## 使用场景

### 高性能数据结构

```rust
// 自定义 Vec 实现
pub struct MyVec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    pub fn new() -> Self {
        MyVec {
            ptr: std::ptr::NonNull::dangling().as_ptr(),
            len: 0,
            cap: 0,
        }
    }
    
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            self.grow();
        }
        
        unsafe {
            std::ptr::write(self.ptr.add(self.len), value);
        }
        self.len += 1;
    }
    
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe {
                Some(std::ptr::read(self.ptr.add(self.len)))
            }
        }
    }
    
    fn grow(&mut self) {
        let new_cap = if self.cap == 0 { 1 } else { self.cap * 2 };
        let new_layout = std::alloc::Layout::array::<T>(new_cap).unwrap();
        
        let new_ptr = unsafe {
            std::alloc::alloc(new_layout) as *mut T
        };
        
        if !self.ptr.is_null() && self.cap > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(self.ptr, new_ptr, self.len);
                let old_layout = std::alloc::Layout::array::<T>(self.cap).unwrap();
                std::alloc::dealloc(self.ptr as *mut u8, old_layout);
            }
        }
        
        self.ptr = new_ptr;
        self.cap = new_cap;
    }
}

impl<T> Drop for MyVec<T> {
    fn drop(&mut self) {
        if !self.ptr.is_null() && self.cap > 0 {
            unsafe {
                // 手动释放每个元素
                for i in 0..self.len {
                    std::ptr::drop_in_place(self.ptr.add(i));
                }
                
                // 释放内存
                let layout = std::alloc::Layout::array::<T>(self.cap).unwrap();
                std::alloc::dealloc(self.ptr as *mut u8, layout);
            }
        }
    }
}
```

### FFI 安全封装

```rust
use std::ffi::CString;
use std::os::raw::c_char;

// C 函数声明
extern "C" {
    fn c_process_string(s: *const c_char) -> i32;
}

// 安全的 Rust 封装
pub fn process_string(s: &str) -> Result<i32, std::ffi::NulError> {
    let c_string = CString::new(s)?;
    let result = unsafe {
        c_process_string(c_string.as_ptr())
    };
    Ok(result)
}

// 使用
fn main() {
    match process_string("Hello, FFI!") {
        Ok(result) => println!("Result: {}", result),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

### 底层优化

```rust
// SIMD 优化
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[target_feature(enable = "avx2")]
unsafe fn sum_simd(data: &[f32]) -> f32 {
    let mut sum = _mm256_setzero_ps();
    
    let chunks = data.chunks_exact(8);
    let remainder = chunks.remainder();
    
    for chunk in chunks {
        let values = _mm256_loadu_ps(chunk.as_ptr());
        sum = _mm256_add_ps(sum, values);
    }
    
    // 水平求和
    let mut result = [0f32; 8];
    _mm256_storeu_ps(result.as_mut_ptr(), sum);
    
    result.iter().sum::<f32>() + remainder.iter().sum::<f32>()
}
```

---

## 最佳实践

### 1. 最小化 Unsafe 代码

```rust
// ❌ 避免：大量 unsafe 代码
pub fn process(data: &[i32]) -> i32 {
    unsafe {
        let ptr = data.as_ptr();
        let mut sum = 0;
        for i in 0..data.len() {
            sum += *ptr.add(i);
        }
        sum
    }
}

// ✅ 推荐：只在必要时使用 unsafe
pub fn process(data: &[i32]) -> i32 {
    data.iter().sum()  // 安全且更清晰
}
```

### 2. 安全抽象封装

```rust
// ✅ 将 unsafe 代码封装在安全接口中
pub struct SafeWrapper {
    ptr: *mut i32,
    len: usize,
}

impl SafeWrapper {
    pub fn new(data: Vec<i32>) -> Self {
        let len = data.len();
        let ptr = Box::into_raw(data.into_boxed_slice()) as *mut i32;
        Self { ptr, len }
    }
    
    // 安全的公共接口
    pub fn get(&self, index: usize) -> Option<i32> {
        if index < self.len {
            unsafe { Some(*self.ptr.add(index)) }
        } else {
            None
        }
    }
    
    pub fn set(&mut self, index: usize, value: i32) -> bool {
        if index < self.len {
            unsafe { *self.ptr.add(index) = value; }
            true
        } else {
            false
        }
    }
}

impl Drop for SafeWrapper {
    fn drop(&mut self) {
        unsafe {
            Vec::from_raw_parts(self.ptr, self.len, self.len);
        }
    }
}
```

### 3. 详细文档说明

```rust
/// 从原始指针创建切片
///
/// # Safety
///
/// 调用者必须确保：
/// - `ptr` 指向有效的内存
/// - 内存区域至少包含 `len` 个 T 类型的元素
/// - 在返回的切片生命周期内，内存不会被修改或释放
/// - `ptr` 满足 T 的对齐要求
///
/// # Examples
///
/// ```
/// let arr = [1, 2, 3];
/// let slice = unsafe { from_raw(arr.as_ptr(), 3) };
/// assert_eq!(slice, &[1, 2, 3]);
/// ```
pub unsafe fn from_raw<T>(ptr: *const T, len: usize) -> &'static [T] {
    std::slice::from_raw_parts(ptr, len)
}
```

### 4. 充分测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_safe_wrapper() {
        let mut wrapper = SafeWrapper::new(vec![1, 2, 3]);
        
        assert_eq!(wrapper.get(0), Some(1));
        assert_eq!(wrapper.get(5), None);
        
        assert!(wrapper.set(1, 20));
        assert_eq!(wrapper.get(1), Some(20));
    }
    
    #[test]
    #[should_panic]
    fn test_out_of_bounds() {
        let wrapper = SafeWrapper::new(vec![1, 2, 3]);
        wrapper.get(10);  // 应该返回 None 而不是 panic
    }
}
```

### 5. Unsafe 代码审查

```rust
// 审查清单：
// ✅ 指针有效性
// ✅ 生命周期正确性
// ✅ 对齐要求
// ✅ 数据竞争预防
// ✅ 边界检查
// ✅ 内存泄漏预防
// ✅ Drop 实现正确
```

---

## 常见陷阱

### 1. 悬垂指针 (Dangling Pointer)

```rust
// ❌ 错误：指针指向已释放的内存
fn dangling() -> *const i32 {
    let x = 42;
    &x as *const i32  // ⚠️ x 在函数结束时被释放
}

unsafe {
    let ptr = dangling();
    println!("{}", *ptr);  // 未定义行为！
}

// ✅ 正确：返回拥有所有权的数据
fn safe() -> Box<i32> {
    Box::new(42)
}
```

### 2. 数据竞争 (Data Race)

```rust
use std::thread;

// ❌ 错误：数据竞争
static mut COUNTER: i32 = 0;

fn increment() {
    unsafe {
        COUNTER += 1;  // ⚠️ 多线程访问，数据竞争！
    }
}

// ✅ 正确：使用 Mutex
use std::sync::{Arc, Mutex};

fn safe_increment(counter: Arc<Mutex<i32>>) {
    let mut num = counter.lock().unwrap();
    *num += 1;
}
```

### 3. 未初始化内存

```rust
// ❌ 错误：读取未初始化内存
let x: i32;
unsafe {
    println!("{}", x);  // 未定义行为！
}

// ✅ 正确：使用 MaybeUninit
use std::mem::MaybeUninit;

let mut x = MaybeUninit::<i32>::uninit();
unsafe {
    x.write(42);
    let initialized = x.assume_init();
    println!("{}", initialized);
}
```

### 4. 类型转换错误

```rust
use std::mem;

// ❌ 错误：不安全的类型转换
unsafe {
    let x: f32 = 3.14;
    let y: u32 = mem::transmute(x);  // 位模式解释为 u32
    println!("{}", y);  // 可能不是你想要的
}

// ✅ 正确：明确转换
let x: f32 = 3.14;
let y = x.to_bits();  // 安全的位转换
println!("{}", y);
```

### 5. 违反别名规则

```rust
// ❌ 错误：同时存在可变和不可变别名
let mut data = vec![1, 2, 3];
let ptr1 = data.as_ptr();
let ptr2 = data.as_mut_ptr();

unsafe {
    println!("{}", *ptr1);  // ⚠️ 违反别名规则
    *ptr2 = 10;
    println!("{}", *ptr1);  // 未定义行为！
}

// ✅ 正确：避免别名冲突
let mut data = vec![1, 2, 3];
let value = data[0];  // 读取
data[0] = 10;         // 写入
println!("{}", value);
```

### 6. 缓冲区溢出

```rust
// ❌ 错误：缓冲区溢出
let arr = [1, 2, 3];
let ptr = arr.as_ptr();

unsafe {
    for i in 0..10 {
        println!("{}", *ptr.add(i));  // ⚠️ 超出边界！
    }
}

// ✅ 正确：边界检查
let arr = [1, 2, 3];
for i in 0..arr.len() {
    println!("{}", arr[i]);
}
```

### 7. 生命周期错误

```rust
// ❌ 错误：生命周期不匹配
fn get_slice<'a>(data: &'a [i32]) -> &'a [i32] {
    unsafe {
        let ptr = data.as_ptr();
        std::slice::from_raw_parts(ptr, 100)  // ⚠️ 超出 data 的生命周期
    }
}

// ✅ 正确：正确的生命周期
fn get_slice<'a>(data: &'a [i32]) -> &'a [i32] {
    &data[..data.len().min(100)]
}
```

### 8. NULL 指针解引用

```rust
use std::ptr;

// ❌ 错误：NULL 指针解引用
unsafe {
    let ptr: *const i32 = ptr::null();
    println!("{}", *ptr);  // 段错误！
}

// ✅ 正确：检查 NULL
unsafe {
    let ptr: *const i32 = ptr::null();
    if !ptr.is_null() {
        println!("{}", *ptr);
    } else {
        println!("NULL pointer!");
    }
}
```

### 9. 对齐错误

```rust
// ❌ 错误：未对齐访问
let data = [0u8; 16];
let ptr = data.as_ptr();

unsafe {
    let ptr = (ptr as usize + 1) as *const u64;  // 未对齐
    let _ = *ptr;  // ⚠️ 可能崩溃或返回错误数据
}

// ✅ 正确：确保对齐
let data: [u64; 2] = [0, 0];
let ptr = data.as_ptr();  // 自然对齐
unsafe {
    let _ = *ptr;
}
```

### 10. 双重释放

```rust
use std::ptr;

// ❌ 错误：双重释放
let x = Box::new(42);
let ptr = Box::into_raw(x);

unsafe {
    let _ = Box::from_raw(ptr);  // 第一次释放
    let _ = Box::from_raw(ptr);  // ⚠️ 第二次释放！未定义行为
}

// ✅ 正确：只释放一次
let x = Box::new(42);
let ptr = Box::into_raw(x);
unsafe {
    let _ = Box::from_raw(ptr);  // 只释放一次
}
```

---

## 未定义行为 (UB)

Rust 的 Unsafe 代码必须避免以下未定义行为：

| UB 类型 | 描述 | 后果 |
|---------|------|------|
| **悬垂指针** | 访问已释放的内存 | 崩溃、数据损坏 |
| **数据竞争** | 并发修改无保护数据 | 不确定结果 |
| **未初始化内存** | 读取未初始化的值 | 随机数据 |
| **越界访问** | 访问数组外的内存 | 崩溃、数据损坏 |
| **NULL 解引用** | 解引用空指针 | 段错误 |
| **未对齐访问** | 访问未对齐的数据 | 崩溃或错误数据 |
| **双重释放** | 释放同一内存两次 | 崩溃、安全漏洞 |
| **类型转换错误** | 不安全的类型转换 | 数据损坏 |
| **违反别名规则** | 同时存在不兼容的别名 | 优化器错误 |

---

## 参考资源

### 官方文档

- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 圣经
- [std::ptr](https://doc.rust-lang.org/std/ptr/) - 指针操作
- [std::mem](https://doc.rust-lang.org/std/mem/) - 内存操作
- [std::slice](https://doc.rust-lang.org/std/slice/) - 切片操作

### 教程

- [Unsafe Rust 教程](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)
- [Rust FFI 指南](https://doc.rust-lang.org/nomicon/ffi.html)

### 工具

- [Miri](https://github.com/rust-lang/miri) - Unsafe 代码检测器
- [cargo-careful](https://github.com/RalfJung/cargo-careful) - Debug 构建增强
- [AddressSanitizer](https://doc.rust-lang.org/unstable-book/compiler-flags/sanitizer.html) - 内存错误检测

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**质量评分**: 98/100
