# Unsafe Rust 模式

Unsafe Rust 为系统级编程提供了必要的底层控制能力。
本章节深入探讨原始指针、联合体、内联汇编等高级特性的正确使用方式，以及如何在保持安全性的前提下发挥 Rust 的底层能力。

## 目录

- [Unsafe Rust 模式](#unsafe-rust-模式)
  - [目录](#目录)
  - [Unsafe 基础](#unsafe-基础)
    - [Unsafe 的能力范围](#unsafe-的能力范围)
    - [Unsafe 函数契约](#unsafe-函数契约)
    - [安全的抽象包装](#安全的抽象包装)
  - [原始指针操作](#原始指针操作)
    - [指针算术和内存操作](#指针算术和内存操作)
    - [类型转换和指针转换](#类型转换和指针转换)
    - [指针别名和内存屏障](#指针别名和内存屏障)
  - [Union 类型](#union-类型)
    - [基础 Union 用法](#基础-union-用法)
    - [MaybeUninit 模式](#maybeuninit-模式)
  - [内联汇编](#内联汇编)
    - [基础汇编语法](#基础汇编语法)
    - [系统调用](#系统调用)
    - [裸函数](#裸函数)
  - [FFI 边界安全](#ffi-边界安全)
    - [C 字符串处理](#c-字符串处理)
    - [不透明类型处理](#不透明类型处理)
  - [裸机编程](#裸机编程)
    - [内存映射 I/O](#内存映射-io)
    - [中断处理](#中断处理)
  - [性能优化](#性能优化)
    - [SIMD 操作](#simd-操作)
    - [零拷贝解析](#零拷贝解析)
    - [内存池实现](#内存池实现)

## Unsafe 基础

### Unsafe 的能力范围

`unsafe` 关键字允许你执行以下五种操作：

1. 解引用原始指针
2. 调用 `unsafe` 函数或方法
3. 访问或修改可变静态变量
4. 实现 `unsafe` trait
5. 访问 `union` 的字段

```rust
// 原始指针创建（安全的）
let x = 5;
let raw_ptr = &x as *const i32;

// 原始指针解引用（需要 unsafe）
unsafe {
    println!("Value: {}", *raw_ptr);
}
```

### Unsafe 函数契约

每个 unsafe 函数都应该有明确的安全契约：

```rust
/// # Safety
///
/// - `ptr` 必须是非空且正确对齐的指针
/// - `ptr` 必须指向有效的 `T` 实例
/// - `ptr` 在函数执行期间必须保持有效
/// - 调用者必须拥有对 `ptr` 指向数据的独占访问权（如果 `T` 包含内部可变性）
pub unsafe fn dangerous_operation<T>(ptr: *mut T) -> T {
    std::ptr::read(ptr)
}
```

### 安全的抽象包装

将 unsafe 代码包装在 safe API 中：

```rust
pub struct SafeBuffer<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}

impl<T> SafeBuffer<T> {
    pub fn new(capacity: usize) -> Self {
        let layout = std::alloc::Layout::array::<T>(capacity).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) as *mut T };

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        SafeBuffer { ptr, len: 0, capacity }
    }

    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.len >= self.capacity {
            return Err(value);
        }

        unsafe {
            std::ptr::write(self.ptr.add(self.len), value);
        }
        self.len += 1;
        Ok(())
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        unsafe {
            Some(&*self.ptr.add(index))
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len {
            return None;
        }

        unsafe {
            Some(&mut *self.ptr.add(index))
        }
    }
}

impl<T> Drop for SafeBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            // 先 drop 所有元素
            for i in 0..self.len {
                std::ptr::drop_in_place(self.ptr.add(i));
            }

            // 释放内存
            let layout = std::alloc::Layout::array::<T>(self.capacity).unwrap();
            std::alloc::dealloc(self.ptr as *mut u8, layout);
        }
    }
}

// 实现 Send 和 Sync（前提是 T 是 Send 和 Sync）
unsafe impl<T: Send> Send for SafeBuffer<T> {}
unsafe impl<T: Sync> Sync for SafeBuffer<T> {}
```

## 原始指针操作

### 指针算术和内存操作

```rust
use std::ptr;

/// 实现一个轻量化的 Vec
pub struct RawVec<T> {
    ptr: ptr::Unique<T>,
    cap: usize,
}

impl<T> RawVec<T> {
    pub fn new() -> Self {
        let cap = if std::mem::size_of::<T>() == 0 { usize::MAX } else { 0 };
        RawVec {
            ptr: ptr::Unique::empty(),
            cap,
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        if cap == 0 || std::mem::size_of::<T>() == 0 {
            return Self::new();
        }

        let layout = std::alloc::Layout::array::<T>(cap).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        RawVec {
            ptr: unsafe { ptr::Unique::new_unchecked(ptr as *mut T) },
            cap,
        }
    }

    pub fn grow(&mut self) {
        assert!(std::mem::size_of::<T>() != 0, "capacity overflow");

        let (new_cap, new_layout) = if self.cap == 0 {
            (1, std::alloc::Layout::array::<T>(1).unwrap())
        } else {
            let new_cap = 2 * self.cap;
            let new_layout = std::alloc::Layout::array::<T>(new_cap).unwrap();
            (new_cap, new_layout)
        };

        assert!(new_layout.size() <= isize::MAX as usize, "Allocation too large");

        let new_ptr = if self.cap == 0 {
            unsafe { std::alloc::alloc(new_layout) }
        } else {
            let old_layout = std::alloc::Layout::array::<T>(self.cap).unwrap();
            let old_ptr = self.ptr.as_ptr() as *mut u8;
            unsafe { std::alloc::realloc(old_ptr, old_layout, new_layout.size()) }
        };

        if new_ptr.is_null() {
            std::alloc::handle_alloc_error(new_layout);
        }

        self.ptr = unsafe { ptr::Unique::new_unchecked(new_ptr as *mut T) };
        self.cap = new_cap;
    }

    pub fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    pub fn cap(&self) -> usize {
        self.cap
    }
}

impl<T> Drop for RawVec<T> {
    fn drop(&mut self) {
        if self.cap != 0 && std::mem::size_of::<T>() != 0 {
            let layout = std::alloc::Layout::array::<T>(self.cap).unwrap();
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, layout);
            }
        }
    }
}
```

### 类型转换和指针转换

```rust
/// 安全的类型转换工具
pub struct Transmuter;

impl Transmuter {
    /// 将 &[u8] 安全地转换为 &[T]
    ///
    /// # Safety
    /// - bytes 的长度必须是 std::mem::size_of::<T>() 的倍数
    /// - bytes 必须正确对齐到 T 的对齐要求
    pub unsafe fn bytes_to_slice<T>(bytes: &[u8]) -> &[T] {
        let size = std::mem::size_of::<T>();
        assert!(bytes.len() % size == 0, "Length not aligned");

        let ptr = bytes.as_ptr() as *const T;
        assert!(ptr.align_offset(std::mem::align_of::<T>()) == 0, "Pointer not aligned");

        let len = bytes.len() / size;
        std::slice::from_raw_parts(ptr, len)
    }

    /// 将 T 转换为字节表示
    pub fn value_to_bytes<T: Copy>(value: &T) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(
                (value as *const T) as *const u8,
                std::mem::size_of::<T>()
            )
        }
    }

    /// 读取未对齐的数据
    pub unsafe fn read_unaligned<T: Copy>(ptr: *const u8) -> T {
        ptr.cast::<T>().read_unaligned()
    }

    /// 写入未对齐的数据
    pub unsafe fn write_unaligned<T: Copy>(ptr: *mut u8, value: T) {
        ptr.cast::<T>().write_unaligned(value);
    }
}
```

### 指针别名和内存屏障

```rust
use std::sync::atomic::{fence, Ordering};

/// 实现一个无锁的单生产者单消费者队列
pub struct SpscQueue<T> {
    buffer: *mut T,
    capacity: usize,
    head: std::sync::atomic::AtomicUsize,
    tail: std::sync::atomic::AtomicUsize,
}

impl<T> SpscQueue<T> {
    pub fn new(capacity: usize) -> Self {
        let layout = std::alloc::Layout::array::<T>(capacity).unwrap();
        let buffer = unsafe { std::alloc::alloc(layout) as *mut T };

        if buffer.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        SpscQueue {
            buffer,
            capacity,
            head: std::sync::atomic::AtomicUsize::new(0),
            tail: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// 生产者调用（单线程）
    pub fn push(&self, value: T) -> Result<(), T> {
        let tail = self.tail.load(Ordering::Relaxed);
        let next_tail = (tail + 1) % self.capacity;

        // 检查队列是否已满
        if next_tail == self.head.load(Ordering::Acquire) {
            return Err(value);
        }

        unsafe {
            std::ptr::write(self.buffer.add(tail), value);
        }

        // 内存屏障：确保写入在更新 tail 之前完成
        fence(Ordering::Release);
        self.tail.store(next_tail, Ordering::Relaxed);

        Ok(())
    }

    /// 消费者调用（单线程）
    pub fn pop(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);

        // 检查队列是否为空
        if head == self.tail.load(Ordering::Acquire) {
            return None;
        }

        let value = unsafe {
            std::ptr::read(self.buffer.add(head))
        };

        // 内存屏障
        fence(Ordering::Release);
        self.head.store((head + 1) % self.capacity, Ordering::Relaxed);

        Some(value)
    }
}

unsafe impl<T: Send> Send for SpscQueue<T> {}
unsafe impl<T: Send> Sync for SpscQueue<T> {}
```

## Union 类型

### 基础 Union 用法

```rust
use std::mem::{size_of, transmute};

/// 用于解析二进制协议的 Union
#[repr(C)]
union PacketData {
    bytes: [u8; 16],
    header: PacketHeader,
    int_values: [u32; 4],
    float_values: [f32; 4],
}

#[repr(C)]
#[derive(Copy, Clone)]
struct PacketHeader {
    version: u16,
    flags: u16,
    length: u32,
    checksum: u32,
    reserved: u32,
}

impl PacketData {
    pub fn from_bytes(bytes: [u8; 16]) -> Self {
        PacketData { bytes }
    }

    /// # Safety
    /// 调用者必须确保 bytes 包含有效的 PacketHeader
    pub unsafe fn header(&self) -> PacketHeader {
        self.header
    }

    pub fn as_bytes(&self) -> [u8; 16] {
        unsafe { self.bytes }
    }

    /// 安全地获取版本号（已知布局的字段）
    pub fn version(&self) -> u16 {
        unsafe { u16::from_le(self.header.version) }
    }
}

/// 用于 FFI 的 Union
#[repr(C)]
pub union Value {
    pub int_val: i64,
    pub float_val: f64,
    pub bool_val: bool,
    pub ptr_val: *mut std::ffi::c_void,
}

#[repr(C)]
pub struct TaggedValue {
    pub tag: ValueType,
    pub value: Value,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub enum ValueType {
    Int = 0,
    Float = 1,
    Bool = 2,
    Pointer = 3,
}

impl TaggedValue {
    pub fn new_int(val: i64) -> Self {
        TaggedValue {
            tag: ValueType::Int,
            value: Value { int_val: val },
        }
    }

    pub fn new_float(val: f64) -> Self {
        TaggedValue {
            tag: ValueType::Float,
            value: Value { float_val: val },
        }
    }

    /// # Safety
    /// 调用者必须确保 tag 与实际的 value 类型匹配
    pub unsafe fn as_int(&self) -> Option<i64> {
        if self.tag == ValueType::Int {
            Some(self.value.int_val)
        } else {
            None
        }
    }

    /// # Safety
    /// 调用者必须确保 tag 与实际的 value 类型匹配
    pub unsafe fn as_float(&self) -> Option<f64> {
        if self.tag == ValueType::Float {
            Some(self.value.float_val)
        } else {
            None
        }
    }
}
```

### MaybeUninit 模式

```rust
use std::mem::MaybeUninit;

/// 高效的数组初始化
pub struct ArrayVec<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    len: usize,
}

impl<T, const N: usize> ArrayVec<T, N> {
    pub fn new() -> Self {
        ArrayVec {
            data: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), T> {
        if self.len >= N {
            return Err(value);
        }

        self.data[self.len].write(value);
        self.len += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        Some(unsafe { self.data[self.len].assume_init_read() })
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        Some(unsafe { self.data[index].assume_init_ref() })
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                self.data.as_ptr() as *const T,
                self.len
            )
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(
                self.data.as_mut_ptr() as *mut T,
                self.len
            )
        }
    }
}

impl<T, const N: usize> Drop for ArrayVec<T, N> {
    fn drop(&mut self) {
        for i in 0..self.len {
            unsafe {
                self.data[i].assume_init_drop();
            }
        }
    }
}
```

## 内联汇编

### 基础汇编语法

```rust
use std::arch::asm;

/// 使用内联汇编读取 CPU 时间戳计数器
#[cfg(target_arch = "x86_64")]
pub fn rdtsc() -> u64 {
    let low: u32;
    let high: u32;

    unsafe {
        asm!(
            "rdtsc",
            lateout("eax") low,
            lateout("edx") high,
            options(nomem, nostack)
        );
    }

    ((high as u64) << 32) | (low as u64)
}

/// 使用 cpuid 获取 CPU 信息
#[cfg(target_arch = "x86_64")]
pub fn cpuid(leaf: u32, subleaf: u32) -> (u32, u32, u32, u32) {
    let eax: u32;
    let ebx: u32;
    let ecx: u32;
    let edx: u32;

    unsafe {
        asm!(
            "cpuid",
            inout("eax") leaf => eax,
            lateout("ebx") ebx,
            inout("ecx") subleaf => ecx,
            lateout("edx") edx,
        );
    }

    (eax, ebx, ecx, edx)
}

/// 内存屏障
#[cfg(target_arch = "x86_64")]
pub fn memory_fence() {
    unsafe {
        asm!("mfence", options(nostack, preserves_flags));
    }
}
```

### 系统调用

```rust
/// Linux x86_64 系统调用
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub unsafe fn syscall1(n: usize, a1: usize) -> usize {
    let result: usize;
    asm!(
        "syscall",
        inlateout("rax") n => result,
        in("rdi") a1,
        out("rcx") _,
        out("r11") _,
        options(nostack, preserves_flags)
    );
    result
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub unsafe fn syscall3(n: usize, a1: usize, a2: usize, a3: usize) -> usize {
    let result: usize;
    asm!(
        "syscall",
        inlateout("rax") n => result,
        in("rdi") a1,
        in("rsi") a2,
        in("rdx") a3,
        out("rcx") _,
        out("r11") _,
        options(nostack, preserves_flags)
    );
    result
}

/// 安全的系统调用包装
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub fn sys_write(fd: usize, buf: &[u8]) -> isize {
    unsafe {
        let result = syscall3(
            1,  // SYS_write
            fd,
            buf.as_ptr() as usize,
            buf.len()
        );
        result as isize
    }
}
```

### 裸函数

```rust
use std::arch::naked_asm;

/// 裸函数用于实现上下文切换
#[cfg(target_arch = "x86_64")]
#[naked]
pub unsafe extern "C" fn context_switch(from: *mut *mut u8, to: *mut u8) {
    naked_asm!(
        // 保存当前上下文
        "push rbp",
        "push rbx",
        "push r12",
        "push r13",
        "push r14",
        "push r15",

        // 保存栈指针到 from
        "mov [rdi], rsp",

        // 恢复新上下文
        "mov rsp, rsi",

        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",

        "ret",
    );
}
```

## FFI 边界安全

### C 字符串处理

```rust
use std::ffi::{CStr, CString, OsStr, OsString};
use std::os::raw::c_char;

/// 安全的 C 字符串包装器
pub struct CStringRef<'a> {
    inner: &'a CStr,
    owned: Option<CString>,
}

impl<'a> CStringRef<'a> {
    /// 从 Rust 字符串创建
    pub fn from_str(s: &str) -> Result<Self, std::ffi::NulError> {
        let owned = CString::new(s)?;
        Ok(CStringRef {
            inner: unsafe { CStr::from_ptr(owned.as_ptr()) },
            owned: Some(owned),
        })
    }

    /// 从 C 字符串指针创建（unsafe）
    ///
    /// # Safety
    /// - ptr 必须指向有效的 null 终止字符串
    /// - 字符串必须在 'a 生命周期内保持有效
    pub unsafe fn from_ptr<'b>(ptr: *const c_char) -> CStringRef<'b> {
        CStringRef {
            inner: CStr::from_ptr(ptr),
            owned: None,
        }
    }

    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }

    pub fn to_str(&self) -> Result<&str, std::str::Utf8Error> {
        self.inner.to_str()
    }
}

/// C 字符串列表管理
pub struct CStringList {
    strings: Vec<CString>,
    ptrs: Vec<*const c_char>,
}

impl CStringList {
    pub fn new() -> Self {
        CStringList {
            strings: Vec::new(),
            ptrs: Vec::new(),
        }
    }

    pub fn push(&mut self, s: &str) -> Result<(), std::ffi::NulError> {
        let cstring = CString::new(s)?;
        self.ptrs.push(cstring.as_ptr());
        self.strings.push(cstring);
        Ok(())
    }

    pub fn as_ptr(&self) -> *const *const c_char {
        self.ptrs.as_ptr()
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }
}
```

### 不透明类型处理

```rust
/// 表示 C 库中的不透明类型
#[repr(C)]
pub struct OpaqueContext {
    _private: [u8; 0],
}

pub struct ContextHandle {
    ptr: *mut OpaqueContext,
    // 标记以确保 Send/Sync 的正确性
    _marker: std::marker::PhantomData<std::sync::Mutex<()>>,
}

#[link(name = "context_lib")]
extern "C" {
    fn context_create() -> *mut OpaqueContext;
    fn context_destroy(ctx: *mut OpaqueContext);
    fn context_process(ctx: *mut OpaqueContext, data: *const u8, len: usize) -> i32;
}

impl ContextHandle {
    pub fn new() -> Option<Self> {
        unsafe {
            let ptr = context_create();
            if ptr.is_null() {
                None
            } else {
                Some(ContextHandle {
                    ptr,
                    _marker: std::marker::PhantomData,
                })
            }
        }
    }

    pub fn process(&mut self, data: &[u8]) -> Result<(), i32> {
        unsafe {
            let result = context_process(self.ptr, data.as_ptr(), data.len());
            if result == 0 {
                Ok(())
            } else {
                Err(result)
            }
        }
    }
}

impl Drop for ContextHandle {
    fn drop(&mut self) {
        unsafe {
            context_destroy(self.ptr);
        }
    }
}

// 如果底层 C 库是线程安全的，可以实现 Send 和 Sync
unsafe impl Send for ContextHandle {}
unsafe impl Sync for ContextHandle {}
```

## 裸机编程

### 内存映射 I/O

```rust
use core::ptr::{read_volatile, write_volatile};

/// 内存映射寄存器
#[repr(C)]
pub struct MmioRegisters {
    control: u32,
    status: u32,
    data: u32,
    interrupt_mask: u32,
}

pub struct MmioDevice {
    base: *mut MmioRegisters,
}

impl MmioDevice {
    /// # Safety
    /// - base 必须是有效的内存映射寄存器地址
    /// - 地址必须正确对齐
    pub unsafe fn new(base: usize) -> Self {
        MmioDevice {
            base: base as *mut MmioRegisters,
        }
    }

    pub fn read_status(&self) -> u32 {
        unsafe { read_volatile(&(*self.base).status) }
    }

    pub fn write_control(&mut self, value: u32) {
        unsafe { write_volatile(&mut (*self.base).control, value) }
    }

    pub fn read_data(&self) -> u32 {
        unsafe { read_volatile(&(*self.base).data) }
    }

    pub fn write_data(&mut self, value: u32) {
        unsafe { write_volatile(&mut (*self.base).data, value) }
    }

    pub fn enable_interrupt(&mut self, mask: u32) {
        let current = unsafe { read_volatile(&(*self.base).interrupt_mask) };
        unsafe { write_volatile(&mut (*self.base).interrupt_mask, current | mask) }
    }
}

// 针对特定平台的 UART 实现
pub struct Uart16550 {
    data: *mut u8,
    interrupt_enable: *mut u8,
    fifo_control: *mut u8,
    line_control: *mut u8,
    modem_control: *mut u8,
    line_status: *mut u8,
}

impl Uart16550 {
    pub const fn new(base: usize) -> Self {
        Uart16550 {
            data: base as *mut u8,
            interrupt_enable: (base + 1) as *mut u8,
            fifo_control: (base + 2) as *mut u8,
            line_control: (base + 3) as *mut u8,
            modem_control: (base + 4) as *mut u8,
            line_status: (base + 5) as *mut u8,
        }
    }

    pub fn init(&mut self) {
        unsafe {
            // 禁用中断
            write_volatile(self.interrupt_enable, 0x00);

            // 启用 DLAB
            write_volatile(self.line_control, 0x80);

            // 设置波特率除数（115200）
            write_volatile(self.data, 0x01);
            write_volatile(self.interrupt_enable, 0x00);

            // 禁用 DLAB，8 位数据，无校验，1 停止位
            write_volatile(self.line_control, 0x03);

            // 启用 FIFO
            write_volatile(self.fifo_control, 0xC7);

            // 启用 IRQ，设置 RTS/DSR
            write_volatile(self.modem_control, 0x0B);
        }
    }

    fn line_status(&self) -> u8 {
        unsafe { read_volatile(self.line_status) }
    }

    pub fn write_byte(&mut self, byte: u8) {
        // 等待发送缓冲区为空
        while self.line_status() & 0x20 == 0 {}

        unsafe {
            write_volatile(self.data, byte);
        }
    }

    pub fn read_byte(&self) -> Option<u8> {
        // 检查接收缓冲区是否有数据
        if self.line_status() & 0x01 == 0 {
            return None;
        }

        unsafe { Some(read_volatile(self.data)) }
    }
}
```

### 中断处理

```rust
use core::arch::global_asm;

/// 中断描述符表项
#[repr(C, packed)]
struct IdtEntry {
    offset_low: u16,
    selector: u16,
    ist: u8,
    type_attr: u8,
    offset_mid: u16,
    offset_high: u32,
    zero: u32,
}

impl IdtEntry {
    fn new(handler: u64, selector: u16, flags: u8) -> Self {
        IdtEntry {
            offset_low: handler as u16,
            selector,
            ist: 0,
            type_attr: flags,
            offset_mid: (handler >> 16) as u16,
            offset_high: (handler >> 32) as u32,
            zero: 0,
        }
    }
}

/// IDT 描述符
#[repr(C, packed)]
struct IdtDescriptor {
    limit: u16,
    base: u64,
}

static mut IDT: [IdtEntry; 256] = [IdtEntry {
    offset_low: 0,
    selector: 0,
    ist: 0,
    type_attr: 0,
    offset_mid: 0,
    offset_high: 0,
    zero: 0,
}; 256];

/// 加载 IDT
///
/// # Safety
/// IDT 必须正确初始化，且在中断关闭时调用
pub unsafe fn load_idt() {
    let idt_desc = IdtDescriptor {
        limit: (core::mem::size_of::<[IdtEntry; 256]>() - 1) as u16,
        base: IDT.as_ptr() as u64,
    };

    core::arch::asm!(
        "lidt [{}]",
        in(reg) &idt_desc,
        options(nostack, preserves_flags)
    );
}

/// 设置中断处理程序
///
/// # Safety
/// handler 必须是有效的中断处理函数入口
pub unsafe fn set_handler(index: u8, handler: u64) {
    IDT[index as usize] = IdtEntry::new(
        handler,
        0x08,  // 内核代码段
        0x8E,  // 中断门，DPL=0
    );
}
```

## 性能优化

### SIMD 操作

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

/// 使用 SIMD 进行向量加法
#[cfg(target_arch = "x86_64")]
pub fn simd_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), result.len());

    let len = a.len();
    let mut i = 0;

    unsafe {
        // 每次处理 8 个 f32（256 位 AVX）
        while i + 8 <= len {
            let va = _mm256_loadu_ps(a.as_ptr().add(i));
            let vb = _mm256_loadu_ps(b.as_ptr().add(i));
            let vr = _mm256_add_ps(va, vb);
            _mm256_storeu_ps(result.as_mut_ptr().add(i), vr);
            i += 8;
        }

        // 处理剩余元素（128 位 SSE）
        while i + 4 <= len {
            let va = _mm_loadu_ps(a.as_ptr().add(i));
            let vb = _mm_loadu_ps(b.as_ptr().add(i));
            let vr = _mm_add_ps(va, vb);
            _mm_storeu_ps(result.as_mut_ptr().add(i), vr);
            i += 4;
        }
    }

    // 处理尾部
    while i < len {
        result[i] = a[i] + b[i];
        i += 1;
    }
}

/// SIMD 点积计算
#[cfg(target_arch = "x86_64")]
pub fn simd_dot_product(a: &[f32], b: &[f32]) -> f32 {
    assert_eq!(a.len(), b.len());

    let len = a.len();
    let mut sum = 0.0f32;
    let mut i = 0;

    unsafe {
        let mut acc = _mm256_setzero_ps();

        while i + 8 <= len {
            let va = _mm256_loadu_ps(a.as_ptr().add(i));
            let vb = _mm256_loadu_ps(b.as_ptr().add(i));
            acc = _mm256_fmadd_ps(va, vb, acc);
            i += 8;
        }

        // 水平求和
        let sum256 = _mm256_hadd_ps(acc, acc);
        let sum256 = _mm256_hadd_ps(sum256, sum256);
        let low = _mm256_castps256_ps128(sum256);
        let high = _mm256_extractf128_ps(sum256, 1);
        let result = _mm_add_ps(low, high);
        sum = _mm_cvtss_f32(result);
    }

    // 处理尾部
    while i < len {
        sum += a[i] * b[i];
        i += 1;
    }

    sum
}
```

### 零拷贝解析

```rust
/// 零拷贝的二进制协议解析
pub struct ZeroCopyParser<'a> {
    data: &'a [u8],
    position: usize,
}

impl<'a> ZeroCopyParser<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        ZeroCopyParser { data, position: 0 }
    }

    /// 读取定长字段（复制）
    pub fn read_u32(&mut self) -> Option<u32> {
        if self.position + 4 > self.data.len() {
            return None;
        }

        let value = u32::from_le_bytes([
            self.data[self.position],
            self.data[self.position + 1],
            self.data[self.position + 2],
            self.data[self.position + 3],
        ]);

        self.position += 4;
        Some(value)
    }

    /// 读取变长字符串（零拷贝）
    pub fn read_str(&mut self, len: usize) -> Option<&'a str> {
        if self.position + len > self.data.len() {
            return None;
        }

        let bytes = &self.data[self.position..self.position + len];
        self.position += len;

        std::str::from_utf8(bytes).ok()
    }

    /// 读取字节数组（零拷贝）
    pub fn read_bytes(&mut self, len: usize) -> Option<&'a [u8]> {
        if self.position + len > self.data.len() {
            return None;
        }

        let bytes = &self.data[self.position..self.position + len];
        self.position += len;
        Some(bytes)
    }

    /// 读取剩余所有数据
    pub fn read_remaining(&mut self) -> &'a [u8] {
        let bytes = &self.data[self.position..];
        self.position = self.data.len();
        bytes
    }
}

/// 示例：解析网络包头部
#[repr(C, packed)]
#[derive(Debug)]
pub struct PacketHeader {
    pub version: u8,
    pub flags: u8,
    pub length: u16,
    pub checksum: u32,
}

impl PacketHeader {
    /// 从字节切片解析（避免复制）
    pub fn from_bytes(data: &[u8]) -> Option<&PacketHeader> {
        if data.len() < std::mem::size_of::<PacketHeader>() {
            return None;
        }

        unsafe {
            Some(&*(data.as_ptr() as *const PacketHeader))
        }
    }

    pub fn version(&self) -> u8 {
        self.version
    }

    pub fn length(&self) -> u16 {
        u16::from_be(self.length)
    }
}
```

### 内存池实现

```rust
use std::cell::RefCell;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

/// 固定大小的内存池
pub struct ObjectPool<T> {
    chunks: Vec<Box<[T]>>,
    free_list: RefCell<Vec<NonNull<T>>>,
    chunk_size: usize,
}

impl<T> ObjectPool<T> {
    pub fn new(chunk_size: usize) -> Self {
        ObjectPool {
            chunks: Vec::new(),
            free_list: RefCell::new(Vec::new()),
            chunk_size,
        }
    }

    fn allocate_chunk(&mut self) {
        let mut chunk = Vec::with_capacity(self.chunk_size);

        unsafe {
            chunk.set_len(self.chunk_size);

            // 将所有元素加入空闲列表
            for item in chunk.iter_mut() {
                self.free_list.borrow_mut().push(NonNull::new(item).unwrap());
            }
        }

        self.chunks.push(chunk.into_boxed_slice());
    }

    pub fn acquire(&mut self) -> Option<PoolBox<T>> {
        if self.free_list.borrow().is_empty() {
            self.allocate_chunk();
        }

        self.free_list.borrow_mut().pop().map(|ptr| {
            PoolBox {
                ptr,
                pool: self,
            }
        })
    }

    fn release(&self, ptr: NonNull<T>) {
        self.free_list.borrow_mut().push(ptr);
    }
}

pub struct PoolBox<'a, T> {
    ptr: NonNull<T>,
    pool: &'a ObjectPool<T>,
}

impl<'a, T> std::ops::Deref for PoolBox<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a, T> std::ops::DerefMut for PoolBox<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<'a, T> Drop for PoolBox<'a, T> {
    fn drop(&mut self) {
        self.pool.release(self.ptr);
    }
}

/// 线程安全的内存池
pub struct ConcurrentPool<T> {
    local_pools: Vec<RefCell<ObjectPool<T>>>,
    global_free: crossbeam::queue::SegQueue<NonNull<T>>,
}

impl<T: Send> ConcurrentPool<T> {
    pub fn new(num_threads: usize, chunk_size: usize) -> Self {
        ConcurrentPool {
            local_pools: (0..num_threads)
                .map(|_| RefCell::new(ObjectPool::new(chunk_size)))
                .collect(),
            global_free: crossbeam::queue::SegQueue::new(),
        }
    }
}
```

---

掌握 Unsafe Rust 需要深入理解内存模型、并发安全性和平台特定细节。始终遵循以下原则：

1. **最小化 unsafe 代码块**：将 unsafe 操作封装在安全的 API 中
2. **文档化安全契约**：清晰地说明每个 unsafe 函数的前置条件
3. **使用 Miri 测试**：利用 Miri 检测未定义行为
4. **代码审查**：unsafe 代码应该经过额外的审查
5. **优先使用标准库**：标准库通常已经提供了安全的抽象

通过这些模式和最佳实践，你可以在保持 Rust 安全保证的同时，获得底层编程的全部能力。
