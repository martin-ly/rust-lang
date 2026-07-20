# Unsafe Rust语义分析

## 📊 目录

- [Unsafe Rust语义分析](#unsafe-rust语义分析)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [1. Unsafe Rust理论基础](#1-unsafe-rust理论基础)
    - [1.1 Unsafe概念](#11-unsafe概念)
    - [1.2 Unsafe Rust哲学](#12-unsafe-rust哲学)
  - [2. 内存安全语义](#2-内存安全语义)
    - [2.1 内存安全保证](#21-内存安全保证)
    - [2.2 未定义行为](#22-未定义行为)
  - [3. 原始指针语义](#3-原始指针语义)
    - [3.1 原始指针类型](#31-原始指针类型)
    - [3.2 指针安全模式](#32-指针安全模式)
  - [4. 外部函数接口](#4-外部函数接口)
    - [4.1 FFI基础](#41-ffi基础)
    - [4.2 FFI安全模式](#42-ffi安全模式)
  - [5. 内联汇编](#5-内联汇编)
    - [5.1 内联汇编基础](#51-内联汇编基础)
    - [5.2 高级内联汇编](#52-高级内联汇编)
  - [6. Unsafe代码安全边界](#6-unsafe代码安全边界)
    - [6.1 安全抽象](#61-安全抽象)
    - [6.2 安全边界检查](#62-安全边界检查)
  - [7. 测试和验证](#7-测试和验证)
    - [7.1 Unsafe代码测试](#71-unsafe代码测试)
  - [8. 总结](#8-总结)

## 概述

本文档详细分析Rust Unsafe系统的语义，包括内存安全、未定义行为、原始指针、外部函数接口、内联汇编和Unsafe代码的安全边界。

## 1. Unsafe Rust理论基础

### 1.1 Unsafe概念

**定义 1.1.1 (Unsafe Rust)**
Unsafe Rust是Rust语言的一个子集，允许绕过编译器的安全检查，直接操作内存和调用底层系统功能，但要求程序员手动保证内存安全和正确性。

**Unsafe Rust的核心特性**：

1. **内存直接操作**：可以绕过所有权和借用检查
2. **底层系统访问**：直接调用系统API和硬件功能
3. **性能优化**：消除不必要的安全检查开销
4. **责任转移**：程序员承担内存安全责任

### 1.2 Unsafe Rust哲学

**Unsafe Rust原则**：

```rust
// Unsafe Rust不是不安全的，而是需要手动保证安全
unsafe fn safe_unsafe_function() {
    // 即使使用unsafe，也要保证内存安全
    let mut data = [1, 2, 3, 4, 5];
    let ptr = data.as_mut_ptr();
    
    // 手动保证边界检查
    if data.len() > 0 {
        unsafe {
            *ptr.add(0) = 10; // 安全：索引在边界内
        }
    }
}

// Unsafe代码应该被安全的抽象包装
pub struct SafeWrapper {
    data: Vec<i32>,
}

impl SafeWrapper {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }
    
    pub fn push(&mut self, value: i32) {
        self.data.push(value);
    }
    
    pub fn get(&self, index: usize) -> Option<&i32> {
        self.data.get(index)
    }
    
    // 内部使用unsafe，但对外提供安全接口
    pub fn get_unchecked(&self, index: usize) -> &i32 {
        unsafe {
            // 调用者必须保证index < self.data.len()
            self.data.get_unchecked(index)
        }
    }
}
```

## 2. 内存安全语义

### 2.1 内存安全保证

**内存安全语义**：

```rust
// Rust的内存安全保证
fn memory_safety_guarantees() {
    // 1. 没有悬垂指针
    let data = vec![1, 2, 3, 4, 5];
    let reference = &data[0];
    // data在这里被drop，reference变成悬垂指针
    // 但编译器会阻止这种情况
    
    // 2. 没有数据竞争
    let mut data = vec![1, 2, 3];
    let ref1 = &data[0];
    // let ref2 = &mut data[0]; // 编译错误：同时存在可变和不可变引用
    
    // 3. 没有缓冲区溢出
    let data = vec![1, 2, 3];
    // let value = data[5]; // 运行时panic：索引越界
}

// Unsafe代码中的内存安全
unsafe fn unsafe_memory_operations() {
    let mut data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_mut_ptr();
    
    // 手动保证内存安全
    for i in 0..data.len() {
        let value = *ptr.add(i); // 安全：i < data.len()
        println!("Value at index {}: {}", i, value);
    }
    
    // 不安全的操作（可能导致未定义行为）
    // let value = *ptr.add(10); // 危险：访问越界内存
}

// 内存布局控制
#[repr(C)]
struct CStruct {
    a: i32,
    b: f64,
    c: [u8; 4],
}

#[repr(packed)]
struct PackedStruct {
    a: u8,
    b: u32,
    c: u16,
}

unsafe fn memory_layout_operations() {
    let c_struct = CStruct {
        a: 42,
        b: 3.14,
        c: [1, 2, 3, 4],
    };
    
    let ptr = &c_struct as *const CStruct as *const u8;
    
    // 直接访问内存布局
    unsafe {
        let a_value = *(ptr as *const i32);
        let b_value = *(ptr.add(8) as *const f64);
        println!("a: {}, b: {}", a_value, b_value);
    }
}
```

### 2.2 未定义行为

**未定义行为语义**：

```rust
// 未定义行为示例
unsafe fn undefined_behavior_examples() {
    // 1. 访问未初始化内存
    let uninit: i32;
    // let value = uninit; // 未定义行为：使用未初始化变量
    
    // 2. 空指针解引用
    let null_ptr: *const i32 = std::ptr::null();
    // let value = *null_ptr; // 未定义行为：解引用空指针
    
    // 3. 悬垂指针解引用
    let dangling_ptr = {
        let data = vec![1, 2, 3];
        data.as_ptr()
    };
    // let value = *dangling_ptr; // 未定义行为：解引用悬垂指针
    
    // 4. 缓冲区溢出
    let data = vec![1, 2, 3];
    let ptr = data.as_ptr();
    // let value = *ptr.add(10); // 未定义行为：访问越界内存
    
    // 5. 类型转换错误
    let data = vec![1, 2, 3];
    let ptr = data.as_ptr() as *const u8;
    // let value = *(ptr as *const i32); // 可能未定义行为：类型转换错误
}

// 避免未定义行为的安全模式
unsafe fn safe_unsafe_patterns() {
    let data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_ptr();
    
    // 安全模式1：边界检查
    for i in 0..data.len() {
        unsafe {
            let value = *ptr.add(i);
            println!("Safe access: {}", value);
        }
    }
    
    // 安全模式2：生命周期管理
    let value = {
        let data = vec![1, 2, 3];
        let ptr = data.as_ptr();
        unsafe {
            *ptr // 安全：data在作用域内
        }
    };
    
    // 安全模式3：空指针检查
    let ptr: *const i32 = std::ptr::null();
    if !ptr.is_null() {
        unsafe {
            let value = *ptr;
            println!("Value: {}", value);
        }
    }
    
    // 安全模式4：对齐检查
    let data = vec![1u8, 2, 3, 4];
    let ptr = data.as_ptr() as *const u32;
    if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
        unsafe {
            let value = *ptr;
            println!("Aligned access: {}", value);
        }
    }
}
```

## 3. 原始指针语义

### 3.1 原始指针类型

**原始指针语义**：

```rust
// 原始指针类型
fn raw_pointer_types() {
    let data = vec![1, 2, 3, 4, 5];
    
    // *const T - 不可变原始指针
    let const_ptr: *const i32 = data.as_ptr();
    
    // *mut T - 可变原始指针
    let mut_ptr: *mut i32 = data.as_mut_ptr();
    
    // 指针操作
    unsafe {
        let value = *const_ptr; // 解引用
        println!("Value: {}", value);
        
        *mut_ptr = 10; // 通过可变指针修改值
        println!("Modified value: {}", *mut_ptr);
    }
}

// 指针算术
unsafe fn pointer_arithmetic() {
    let data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_ptr();
    
    // 指针加法
    for i in 0..data.len() {
        let value = *ptr.add(i);
        println!("Index {}: {}", i, value);
    }
    
    // 指针减法
    let end_ptr = ptr.add(data.len());
    for i in (0..data.len()).rev() {
        let value = *end_ptr.sub(i + 1);
        println!("Reverse index {}: {}", i, value);
    }
    
    // 指针偏移
    let offset_ptr = ptr.offset(2);
    let value = *offset_ptr;
    println!("Offset value: {}", value);
}

// 指针比较
unsafe fn pointer_comparison() {
    let data = vec![1, 2, 3, 4, 5];
    let ptr1 = data.as_ptr();
    let ptr2 = data.as_ptr().add(2);
    
    // 指针比较
    if ptr1 < ptr2 {
        println!("ptr1 is before ptr2");
    }
    
    // 指针相等性
    if ptr1 == ptr1 {
        println!("Pointers are equal");
    }
    
    // 空指针检查
    let null_ptr: *const i32 = std::ptr::null();
    if null_ptr.is_null() {
        println!("Pointer is null");
    }
}

// 指针转换
unsafe fn pointer_conversion() {
    let data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_ptr();
    
    // 类型转换
    let byte_ptr = ptr as *const u8;
    let usize_ptr = ptr as *const usize;
    
    // 地址转换
    let addr = ptr as usize;
    let ptr_from_addr = addr as *const i32;
    
    // 可变性转换
    let mut data = vec![1, 2, 3, 4, 5];
    let const_ptr = data.as_ptr();
    let mut_ptr = const_ptr as *mut i32;
    
    // 使用转换后的指针
    *mut_ptr = 10;
    println!("Modified value: {}", *const_ptr);
}
```

### 3.2 指针安全模式

**指针安全模式语义**：

```rust
// 安全指针包装器
struct SafePointer<T> {
    ptr: *const T,
    len: usize,
}

impl<T> SafePointer<T> {
    fn new(data: &[T]) -> Self {
        Self {
            ptr: data.as_ptr(),
            len: data.len(),
        }
    }
    
    unsafe fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(&*self.ptr.add(index))
        } else {
            None
        }
    }
    
    unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*self.ptr.add(index)
    }
}

// 使用安全指针包装器
fn use_safe_pointer() {
    let data = vec![1, 2, 3, 4, 5];
    let safe_ptr = SafePointer::new(&data);
    
    unsafe {
        if let Some(value) = safe_ptr.get(2) {
            println!("Safe access: {}", value);
        }
        
        let value = safe_ptr.get_unchecked(1);
        println!("Unchecked access: {}", value);
    }
}

// 智能指针实现
struct SmartPointer<T> {
    ptr: *mut T,
    owner: bool,
}

impl<T> SmartPointer<T> {
    fn new(data: T) -> Self {
        let ptr = Box::into_raw(Box::new(data));
        Self {
            ptr,
            owner: true,
        }
    }
    
    fn as_ref(&self) -> &T {
        unsafe { &*self.ptr }
    }
    
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

impl<T> Drop for SmartPointer<T> {
    fn drop(&mut self) {
        if self.owner {
            unsafe {
                let _ = Box::from_raw(self.ptr);
            }
        }
    }
}

// 使用智能指针
fn use_smart_pointer() {
    let mut smart_ptr = SmartPointer::new(42);
    
    println!("Value: {}", smart_ptr.as_ref());
    *smart_ptr.as_mut() = 100;
    println!("Modified value: {}", smart_ptr.as_ref());
}
```

## 4. 外部函数接口

### 4.1 FFI基础

**FFI语义**：

```rust
// 外部函数声明
#[link(name = "c")]
extern "C" {
    fn printf(format: *const i8, ...) -> i32;
    fn strlen(s: *const i8) -> usize;
    fn malloc(size: usize) -> *mut std::ffi::c_void;
    fn free(ptr: *mut std::ffi::c_void);
}

// 使用外部函数
unsafe fn use_external_functions() {
    let message = std::ffi::CString::new("Hello from Rust!\n").unwrap();
    printf(message.as_ptr());
    
    let len = strlen(message.as_ptr());
    println!("String length: {}", len);
    
    // 内存分配
    let ptr = malloc(100);
    if !ptr.is_null() {
        free(ptr);
    }
}

// 外部结构体
#[repr(C)]
struct CStruct {
    x: i32,
    y: f64,
    data: [u8; 10],
}

#[link(name = "c")]
extern "C" {
    fn process_struct(s: *const CStruct) -> i32;
}

// 使用外部结构体
unsafe fn use_external_struct() {
    let c_struct = CStruct {
        x: 42,
        y: 3.14,
        data: [0; 10],
    };
    
    let result = process_struct(&c_struct as *const CStruct);
    println!("Process result: {}", result);
}

// 回调函数
type CallbackFn = extern "C" fn(i32) -> i32;

#[link(name = "c")]
extern "C" {
    fn register_callback(callback: CallbackFn);
    fn call_callback(value: i32) -> i32;
}

// 回调函数实现
extern "C" fn rust_callback(value: i32) -> i32 {
    println!("Rust callback called with: {}", value);
    value * 2
}

// 使用回调
unsafe fn use_callback() {
    register_callback(rust_callback);
    let result = call_callback(21);
    println!("Callback result: {}", result);
}
```

### 4.2 FFI安全模式

**FFI安全模式语义**：

```rust
use std::ffi::{CString, CStr};
use std::os::raw::c_char;

// 安全的字符串转换
fn safe_string_conversion() {
    // Rust字符串到C字符串
    let rust_string = "Hello, World!";
    let c_string = CString::new(rust_string).unwrap();
    
    unsafe {
        // 使用C字符串
        printf(c_string.as_ptr());
    }
    
    // C字符串到Rust字符串
    unsafe {
        let c_str = CStr::from_ptr("Hello from C\0".as_ptr() as *const c_char);
        let rust_str = c_str.to_str().unwrap();
        println!("C string converted: {}", rust_str);
    }
}

// 安全的指针包装
struct SafeFFIPointer<T> {
    ptr: *mut T,
    len: usize,
}

impl<T> SafeFFIPointer<T> {
    fn new(len: usize) -> Self {
        unsafe {
            let ptr = malloc(std::mem::size_of::<T>() * len) as *mut T;
            Self { ptr, len }
        }
    }
    
    fn as_slice(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(self.ptr, self.len)
        }
    }
    
    fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(self.ptr, self.len)
        }
    }
}

impl<T> Drop for SafeFFIPointer<T> {
    fn drop(&mut self) {
        unsafe {
            free(self.ptr as *mut std::ffi::c_void);
        }
    }
}

// 使用安全FFI指针
fn use_safe_ffi_pointer() {
    let mut safe_ptr = SafeFFIPointer::<i32>::new(10);
    
    // 安全地访问数据
    let slice = safe_ptr.as_mut_slice();
    for (i, value) in slice.iter_mut().enumerate() {
        *value = i as i32;
    }
    
    // 读取数据
    let read_slice = safe_ptr.as_slice();
    println!("Data: {:?}", read_slice);
}

// 错误处理
#[repr(C)]
struct FFIResult {
    success: bool,
    error_code: i32,
    message: *const c_char,
}

impl FFIResult {
    fn new(success: bool, error_code: i32, message: Option<&str>) -> Self {
        let message_ptr = message
            .and_then(|s| CString::new(s).ok())
            .map(|cs| cs.as_ptr())
            .unwrap_or(std::ptr::null());
        
        Self {
            success,
            error_code,
            message: message_ptr,
        }
    }
    
    fn is_success(&self) -> bool {
        self.success
    }
    
    fn get_error_message(&self) -> Option<&str> {
        if self.message.is_null() {
            None
        } else {
            unsafe {
                CStr::from_ptr(self.message).to_str().ok()
            }
        }
    }
}
```

## 5. 内联汇编

### 5.1 内联汇编基础

**内联汇编语义**：

```rust
// 基本内联汇编
fn basic_inline_assembly() {
    let result: u64;
    
    unsafe {
        asm!(
            "mov {result}, 42",
            result = out(reg) result,
        );
    }
    
    println!("Assembly result: {}", result);
}

// 带输入的内联汇编
fn inline_assembly_with_input() {
    let input = 10u64;
    let result: u64;
    
    unsafe {
        asm!(
            "add {result}, {input}, 5",
            input = in(reg) input,
            result = out(reg) result,
        );
    }
    
    println!("Input: {}, Result: {}", input, result);
}

// 带约束的内联汇编
fn inline_assembly_with_constraints() {
    let mut value = 42u64;
    
    unsafe {
        asm!(
            "inc {value}",
            value = inout(reg) value,
        );
    }
    
    println!("Incremented value: {}", value);
}

// 平台特定的内联汇编
#[cfg(target_arch = "x86_64")]
fn x86_64_assembly() {
    let result: u64;
    
    unsafe {
        asm!(
            "rdtsc",
            "shl rdx, 32",
            "or rax, rdx",
            out("rax") result,
        );
    }
    
    println!("Timestamp: {}", result);
}

#[cfg(target_arch = "aarch64")]
fn aarch64_assembly() {
    let result: u64;
    
    unsafe {
        asm!(
            "mrs {result}, PMCCNTR_EL0",
            result = out(reg) result,
        );
    }
    
    println!("Cycle count: {}", result);
}
```

### 5.2 高级内联汇编

**高级内联汇编语义**：

```rust
// 带标签的内联汇编
fn assembly_with_labels() {
    let result: u64;
    
    unsafe {
        asm!(
            "mov {result}, 0",
            "cmp {result}, 0",
            "je 1f",
            "add {result}, 10",
            "1:",
            result = out(reg) result,
        );
    }
    
    println!("Label result: {}", result);
}

// 带内存操作的内联汇编
fn assembly_with_memory() {
    let mut data = [0u64; 4];
    
    unsafe {
        asm!(
            "mov {ptr}, {data}",
            "mov qword ptr [{ptr}], 1",
            "mov qword ptr [{ptr} + 8], 2",
            "mov qword ptr [{ptr} + 16], 3",
            "mov qword ptr [{ptr} + 24], 4",
            ptr = out(reg) _,
            data = in(reg) data.as_mut_ptr(),
        );
    }
    
    println!("Memory data: {:?}", data);
}

// 带条件码的内联汇编
fn assembly_with_condition_codes() {
    let input = 5u64;
    let result: u64;
    let zero_flag: u64;
    
    unsafe {
        asm!(
            "cmp {input}, 0",
            "setz {zero_flag}",
            "mov {result}, {input}",
            input = in(reg) input,
            result = out(reg) result,
            zero_flag = out(reg) zero_flag,
        );
    }
    
    println!("Input: {}, Result: {}, Zero: {}", input, result, zero_flag);
}

// 带栈操作的内联汇编
fn assembly_with_stack() {
    let result: u64;
    
    unsafe {
        asm!(
            "push rax",
            "mov rax, 42",
            "mov {result}, rax",
            "pop rax",
            result = out(reg) result,
        );
    }
    
    println!("Stack result: {}", result);
}
```

## 6. Unsafe代码安全边界

### 6.1 安全抽象

**安全抽象语义**：

```rust
// 安全的Vec实现
struct SafeVec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}

impl<T> SafeVec<T> {
    fn new() -> Self {
        Self {
            ptr: std::ptr::null_mut(),
            len: 0,
            capacity: 0,
        }
    }
    
    fn push(&mut self, value: T) {
        if self.len == self.capacity {
            self.grow();
        }
        
        unsafe {
            self.ptr.add(self.len).write(value);
        }
        self.len += 1;
    }
    
    fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe {
                Some(self.ptr.add(self.len).read())
            }
        }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            unsafe {
                Some(&*self.ptr.add(index))
            }
        } else {
            None
        }
    }
    
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            unsafe {
                Some(&mut *self.ptr.add(index))
            }
        } else {
            None
        }
    }
    
    fn len(&self) -> usize {
        self.len
    }
    
    fn capacity(&self) -> usize {
        self.capacity
    }
    
    fn grow(&mut self) {
        let new_capacity = if self.capacity == 0 { 1 } else { self.capacity * 2 };
        let new_size = new_capacity * std::mem::size_of::<T>();
        
        let new_ptr = if self.capacity == 0 {
            unsafe {
                std::alloc::alloc(std::alloc::Layout::array::<T>(new_capacity).unwrap())
            }
        } else {
            unsafe {
                std::alloc::realloc(
                    self.ptr as *mut u8,
                    std::alloc::Layout::array::<T>(self.capacity).unwrap(),
                    new_size,
                )
            }
        } as *mut T;
        
        if new_ptr.is_null() {
            panic!("Failed to allocate memory");
        }
        
        self.ptr = new_ptr;
        self.capacity = new_capacity;
    }
}

impl<T> Drop for SafeVec<T> {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            // 调用所有元素的析构函数
            for i in 0..self.len {
                unsafe {
                    self.ptr.add(i).drop_in_place();
                }
            }
            
            // 释放内存
            unsafe {
                std::alloc::dealloc(
                    self.ptr as *mut u8,
                    std::alloc::Layout::array::<T>(self.capacity).unwrap(),
                );
            }
        }
    }
}

// 使用安全的Vec实现
fn use_safe_vec() {
    let mut vec = SafeVec::new();
    
    vec.push(1);
    vec.push(2);
    vec.push(3);
    
    println!("Length: {}", vec.len());
    println!("Capacity: {}", vec.capacity());
    
    if let Some(value) = vec.get(1) {
        println!("Value at index 1: {}", value);
    }
    
    if let Some(value) = vec.pop() {
        println!("Popped value: {}", value);
    }
}
```

### 6.2 安全边界检查

**安全边界检查语义**：

```rust
// 边界检查宏
macro_rules! bounds_check {
    ($index:expr, $len:expr) => {
        if $index >= $len {
            panic!("Index {} out of bounds for length {}", $index, $len);
        }
    };
}

// 安全的数组访问
struct SafeArray<T> {
    data: Vec<T>,
}

impl<T> SafeArray<T> {
    fn new(data: Vec<T>) -> Self {
        Self { data }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        bounds_check!(index, self.data.len());
        Some(&self.data[index])
    }
    
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        bounds_check!(index, self.data.len());
        Some(&mut self.data[index])
    }
    
    fn get_unchecked(&self, index: usize) -> &T {
        unsafe {
            self.data.get_unchecked(index)
        }
    }
    
    fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        unsafe {
            self.data.get_unchecked_mut(index)
        }
    }
}

// 使用安全数组
fn use_safe_array() {
    let mut array = SafeArray::new(vec![1, 2, 3, 4, 5]);
    
    // 安全访问
    if let Some(value) = array.get(2) {
        println!("Safe access: {}", value);
    }
    
    // 不安全但快速访问（调用者负责边界检查）
    let value = array.get_unchecked(3);
    println!("Unchecked access: {}", value);
    
    // 可变访问
    if let Some(value) = array.get_mut(1) {
        *value = 10;
    }
}

// 生命周期检查
struct LifetimeChecked<'a> {
    data: &'a [i32],
}

impl<'a> LifetimeChecked<'a> {
    fn new(data: &'a [i32]) -> Self {
        Self { data }
    }
    
    fn get(&self, index: usize) -> Option<&'a i32> {
        if index < self.data.len() {
            Some(&self.data[index])
        } else {
            None
        }
    }
    
    fn slice(&self, start: usize, end: usize) -> Option<&'a [i32]> {
        if start <= end && end <= self.data.len() {
            Some(&self.data[start..end])
        } else {
            None
        }
    }
}

// 使用生命周期检查
fn use_lifetime_checked() {
    let data = vec![1, 2, 3, 4, 5];
    let checked = LifetimeChecked::new(&data);
    
    if let Some(value) = checked.get(2) {
        println!("Value: {}", value);
    }
    
    if let Some(slice) = checked.slice(1, 4) {
        println!("Slice: {:?}", slice);
    }
}
```

## 7. 测试和验证

### 7.1 Unsafe代码测试

**Unsafe代码测试框架**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_unsafe_function() {
        safe_unsafe_function();
    }

    #[test]
    fn test_safe_wrapper() {
        let mut wrapper = SafeWrapper::new();
        wrapper.push(42);
        
        assert_eq!(wrapper.get(0), Some(&42));
        assert_eq!(wrapper.get_unchecked(0), &42);
    }

    #[test]
    fn test_safe_pointer() {
        let data = vec![1, 2, 3, 4, 5];
        let safe_ptr = SafePointer::new(&data);
        
        unsafe {
            assert_eq!(safe_ptr.get(2), Some(&3));
            assert_eq!(safe_ptr.get_unchecked(1), &2);
        }
    }

    #[test]
    fn test_smart_pointer() {
        let mut smart_ptr = SmartPointer::new(42);
        
        assert_eq!(*smart_ptr.as_ref(), 42);
        *smart_ptr.as_mut() = 100;
        assert_eq!(*smart_ptr.as_ref(), 100);
    }

    #[test]
    fn test_safe_vec() {
        let mut vec = SafeVec::new();
        
        vec.push(1);
        vec.push(2);
        vec.push(3);
        
        assert_eq!(vec.len(), 3);
        assert_eq!(vec.get(1), Some(&2));
        
        assert_eq!(vec.pop(), Some(3));
        assert_eq!(vec.len(), 2);
    }

    #[test]
    fn test_safe_array() {
        let mut array = SafeArray::new(vec![1, 2, 3, 4, 5]);
        
        assert_eq!(array.get(2), Some(&3));
        assert_eq!(array.get_unchecked(1), &2);
        
        if let Some(value) = array.get_mut(0) {
            *value = 10;
        }
        assert_eq!(array.get(0), Some(&10));
    }

    #[test]
    fn test_lifetime_checked() {
        let data = vec![1, 2, 3, 4, 5];
        let checked = LifetimeChecked::new(&data);
        
        assert_eq!(checked.get(2), Some(&3));
        assert_eq!(checked.slice(1, 4), Some(&[2, 3, 4]));
    }

    #[test]
    fn test_bounds_check() {
        let array = SafeArray::new(vec![1, 2, 3]);
        
        // 有效索引
        assert!(array.get(1).is_some());
        
        // 无效索引（应该panic）
        // array.get(5); // 这会panic
    }

    #[test]
    fn test_memory_safety() {
        let data = vec![1, 2, 3, 4, 5];
        let ptr = data.as_ptr();
        
        unsafe {
            // 安全访问
            for i in 0..data.len() {
                let value = *ptr.add(i);
                assert_eq!(value, data[i]);
            }
        }
    }

    #[test]
    fn test_ffi_safety() {
        let c_string = CString::new("test").unwrap();
        
        unsafe {
            // 安全的FFI调用
            let len = strlen(c_string.as_ptr());
            assert_eq!(len, 4);
        }
    }
}
```

## 8. 总结

Rust的Unsafe系统提供了强大的底层编程能力，同时要求程序员手动保证内存安全。通过原始指针、外部函数接口、内联汇编等机制，Unsafe Rust实现了零成本的系统级编程抽象。

Unsafe Rust是Rust语言的重要组成部分，它通过明确的安全边界和严格的编程规范，为开发者提供了既强大又安全的底层编程工具。理解Unsafe Rust的语义对于编写高性能、系统级的Rust程序至关重要。

Unsafe Rust系统体现了Rust在安全性和性能之间的平衡，为开发者提供了既高效又可靠的底层编程能力，是现代Rust编程中不可或缺的重要组成部分。
