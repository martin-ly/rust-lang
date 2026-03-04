# FFI模式与C互操作

> **权威来源**: The Rustonomicon, FFI chapter; bindgen documentation; libc crate documentation

## 目录

- [FFI模式与C互操作](#ffi模式与c互操作)
  - [目录](#目录)
  - [1. FFI基础](#1-ffi基础)
    - [1.1 为什么需要FFI](#11-为什么需要ffi)
    - [1.2 调用约定](#12-调用约定)
    - [1.3 链接配置](#13-链接配置)
  - [2. 类型映射与内存布局](#2-类型映射与内存布局)
    - [2.1 基本类型映射](#21-基本类型映射)
    - [2.2 内存布局控制](#22-内存布局控制)
    - [2.3 复杂类型映射](#23-复杂类型映射)
  - [3. 所有权与生命周期](#3-所有权与生命周期)
    - [3.1 跨边界的所有权规则](#31-跨边界的所有权规则)
    - [3.2 不透明指针模式](#32-不透明指针模式)
    - [3.3 生命周期管理策略](#33-生命周期管理策略)
  - [4. 高级FFI模式](#4-高级ffi模式)
    - [4.1 回调与闭包](#41-回调与闭包)
    - [4.2 异步 FFI](#42-异步-ffi)
    - [4.3 泛型 FFI 接口](#43-泛型-ffi-接口)
  - [5. 错误处理与panic安全](#5-错误处理与panic安全)
    - [5.1 错误码转换](#51-错误码转换)
    - [5.2 Panic安全](#52-panic安全)
    - [5.3 异常安全策略](#53-异常安全策略)
  - [6. 工具链使用](#6-工具链使用)
    - [6.1 bindgen](#61-bindgen)
    - [6.2 cbindgen](#62-cbindgen)
    - [6.3 调试与测试](#63-调试与测试)
  - [7. 实际案例](#7-实际案例)
    - [7.1 图像处理库包装](#71-图像处理库包装)
    - [7.2 数据库驱动实现](#72-数据库驱动实现)
    - [7.3 硬件抽象层](#73-硬件抽象层)
  - [总结](#总结)
  - [参考资源](#参考资源)

---

## 1. FFI基础

### 1.1 为什么需要FFI

Rust 的 FFI（Foreign Function Interface）允许 Rust 代码与其他语言（主要是 C）进行互操作。这在以下场景中是必需的：

- 复用现有的 C/C++ 库
- 与操作系统 API 交互
- 嵌入式系统开发
- 跨语言插件系统
- 性能关键路径调用手写汇编

```rust
// 最基本的 FFI 示例
use std::os::raw::{c_int, c_char};
use std::ffi::CString;

// 声明外部函数
extern "C" {
    // 调用 C 标准库的 strlen
    fn strlen(s: *const c_char) -> usize;

    // 调用 C 标准库的 malloc/free
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
}

// 在 Rust 中调用 C 函数
fn use_c_strlen() {
    let s = CString::new("Hello, FFI!").unwrap();
    let len = unsafe { strlen(s.as_ptr()) };
    println!("Length: {}", len);  // 输出: 11
}
```

### 1.2 调用约定

Rust 支持多种调用约定：

```rust
// 不同调用约定示例
extern "C" fn c_calling_convention() {}      // C 调用约定（默认）
extern "system" fn system_calling_convention() {}  // 系统调用约定（Windows）
extern "stdcall" fn stdcall_convention() {}   // Windows API 调用约定
extern "fastcall" fn fastcall_convention() {} // 寄存器传递参数
extern "cdecl" fn cdecl_convention() {}       // C 声明调用约定
extern "win64" fn win64_convention() {}       // Windows x64 调用约定
extern "sysv64" fn sysv64_convention() {}     // System V AMD64 ABI

// 调用约定对 ABI 的影响
#[cfg(target_os = "windows")]
extern "system" {
    // Windows 上使用 stdcall，其他平台使用 C
    fn some_system_function();
}
```

### 1.3 链接配置

```rust
// Cargo.toml 中的链接配置
// [package]
// name = "my-ffi-lib"
// version = "0.1.0"
// edition = "2021"
//
// [dependencies]
// libc = "0.2"
//
// [build-dependencies]
// cc = "1.0"

// build.rs - 构建脚本示例
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉 Cargo 链接系统库
    println!("cargo:rustc-link-lib=ssl");
    println!("cargo:rustc-link-lib=crypto");

    // 指定库搜索路径
    println!("cargo:rustc-link-search=/usr/local/lib");

    // 编译 C 代码
    cc::Build::new()
        .file("src/native/mylib.c")
        .include("src/native")
        .compile("mylib");

    // 重新运行条件
    println!("cargo:rerun-if-changed=src/native/mylib.c");
}
```

---

## 2. 类型映射与内存布局

### 2.1 基本类型映射

```rust
use std::os::raw::*;
use libc;

// Rust 与 C 类型的对应关系
fn type_mappings() {
    // 整数类型
    let c_char: c_char = 0;           // char (有符号或无符号，平台相关)
    let c_schar: c_schar = 0;         // signed char
    let c_uchar: c_uchar = 0;         // unsigned char
    let c_short: c_short = 0;         // short
    let c_ushort: c_ushort = 0;       // unsigned short
    let c_int: c_int = 0;             // int
    let c_uint: c_uint = 0;           // unsigned int
    let c_long: c_long = 0;           // long
    let c_ulong: c_ulong = 0;         // unsigned long
    let c_longlong: c_longlong = 0;   // long long
    let c_ulonglong: c_ulonglong = 0; // unsigned long long

    // 浮点类型
    let c_float: c_float = 0.0;       // float
    let c_double: c_double = 0.0;     // double

    // 指针类型
    let c_void_ptr: *mut c_void = std::ptr::null_mut();

    // 使用 libc crate（推荐）
    let libc_size_t: libc::size_t = 0;
    let libc_ssize_t: libc::ssize_t = 0;
    let libc_pid_t: libc::pid_t = 0;
    let libc_off_t: libc::off_t = 0;
    let libc_mode_t: libc::mode_t = 0;
}

// 固定大小整数（推荐用于可移植性）
fn fixed_size_types() {
    use std::ffi::*;

    // C 的 uint32_t -> Rust 的 u32
    let exact_u32: u32 = 0;

    // C 的 int64_t -> Rust 的 i64
    let exact_i64: i64 = 0;

    // 指针大小的整数
    let usize_val: usize = 0;  // uintptr_t
    let isize_val: isize = 0;  // intptr_t
}
```

### 2.2 内存布局控制

```rust
// 控制结构体内存布局

// #[repr(C)] - C 兼容布局
#[repr(C)]
struct CCompatible {
    a: u8,   // 偏移 0
    b: u32,  // 偏移 4 (对齐到 4 字节)
    c: u16,  // 偏移 8
}  // 总大小 12 字节（包含填充）

// #[repr(packed)] - 紧凑布局（无填充）
#[repr(C, packed)]
struct Packed {
    a: u8,   // 偏移 0
    b: u32,  // 偏移 1 (无填充)
    c: u16,  // 偏移 5
}  // 总大小 7 字节

// 注意：packed 结构体需要小心未对齐访问
impl Packed {
    fn get_b(&self) -> u32 {
        // SAFETY: 需要处理可能的未对齐访问
        unsafe { std::ptr::addr_of!(self.b).read_unaligned() }
    }
}

// #[repr(align(n))] - 指定对齐
#[repr(C, align(16))]
struct Aligned16 {
    data: [u8; 16],
}  // 对齐到 16 字节边界

// #[repr(transparent)] - 单字段包装器的透明布局
#[repr(transparent)]
struct Handle(*mut c_void);

// C 联合体
#[repr(C)]
union MyUnion {
    i: i32,
    f: f32,
    bytes: [u8; 4],
}

// C 枚举（带值）
#[repr(C)]
#[derive(Debug, Copy, Clone)]
enum CEnum {
    A = 0,
    B = 1,
    C = 42,
}
```

### 2.3 复杂类型映射

```rust
use std::ffi::{CStr, CString, OsStr, OsString};
use std::os::raw::c_char;

// 字符串处理
fn string_conversions() {
    // Rust String -> C 字符串
    let rust_string = String::from("Hello");
    let c_string = CString::new(rust_string).unwrap();
    let c_ptr: *const c_char = c_string.as_ptr();

    // C 字符串 -> Rust &str（不安全）
    let c_ptr: *const c_char = ...;
    let c_str = unsafe { CStr::from_ptr(c_ptr) };
    let rust_str = c_str.to_str().unwrap();

    // 注意：CStr 的生命周期与指针相同
}

// 数组与切片
#[repr(C)]
struct ArrayWrapper {
    data: *const u8,
    len: usize,
}

impl ArrayWrapper {
    // SAFETY: data 必须指向至少 len 个有效字节
    unsafe fn as_slice(&self) -> &[u8] {
        std::slice::from_raw_parts(self.data, self.len)
    }
}

// 变长结构体（C 柔性数组）
#[repr(C)]
struct FlexibleArray {
    count: usize,
    // data: [u8; 0],  // C 方式
}

impl FlexibleArray {
    fn data_ptr(&self) -> *const u8 {
        // 计算 data 字段的偏移
        unsafe { (self as *const Self).add(1) as *const u8 }
    }

    // SAFETY: 调用者必须确保内存布局正确
    unsafe fn as_slice(&self) -> &[u8] {
        std::slice::from_raw_parts(self.data_ptr(), self.count)
    }
}
```

---

## 3. 所有权与生命周期

### 3.1 跨边界的所有权规则

```rust
// FFI 所有权约定

// 情况1：Rust 分配，Rust 释放
pub struct RustBox<T> {
    ptr: *mut T,
}

impl<T> RustBox<T> {
    pub fn new(value: T) -> Self {
        Self {
            ptr: Box::into_raw(Box::new(value)),
        }
    }

    // 导出到 C，但不转移所有权
    pub fn as_ptr(&self) -> *const T {
        self.ptr
    }

    // 重新获取所有权
    pub fn into_inner(self) -> T {
        unsafe { *Box::from_raw(self.ptr) }
    }
}

impl<T> Drop for RustBox<T> {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe { drop(Box::from_raw(self.ptr)) }
        }
    }
}

// 情况2：C 分配，C 释放
pub struct CBox<T> {
    ptr: *mut T,
    free_fn: unsafe extern "C" fn(*mut T),
}

impl<T> Drop for CBox<T> {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe { (self.free_fn)(self.ptr) }
        }
    }
}

// 情况3：C 分配，Rust 释放（需要自定义分配器）
#[repr(C)]
pub struct CStringWrapper {
    data: *mut c_char,
    len: usize,
    capacity: usize,
}

impl Drop for CStringWrapper {
    fn drop(&mut self) {
        if !self.data.is_null() {
            unsafe {
                // 使用 C 的 free 释放
                libc::free(self.data as *mut c_void);
            }
        }
    }
}
```

### 3.2 不透明指针模式

```rust
// 向 C 隐藏 Rust 类型细节

// Rust 实现
pub struct InternalState {
    data: Vec<u8>,
    counter: AtomicU64,
    name: String,
}

// 导出到 C 的不透明指针
pub type Context = c_void;

// 构造函数
#[no_mangle]
pub extern "C" fn context_new() -> *mut Context {
    let state = Box::new(InternalState {
        data: Vec::new(),
        counter: AtomicU64::new(0),
        name: String::new(),
    });
    Box::into_raw(state) as *mut Context
}

// 析构函数
#[no_mangle]
pub extern "C" fn context_free(ctx: *mut Context) {
    if !ctx.is_null() {
        unsafe {
            drop(Box::from_raw(ctx as *mut InternalState));
        }
    }
}

// 操作函数
#[no_mangle]
pub extern "C" fn context_increment(ctx: *mut Context) -> u64 {
    let state = unsafe { &*(ctx as *mut InternalState) };
    state.counter.fetch_add(1, Ordering::SeqCst) + 1
}

// C 头文件示例：
// typedef void* Context;
// Context context_new(void);
// void context_free(Context ctx);
// uint64_t context_increment(Context ctx);
```

### 3.3 生命周期管理策略

```rust
use std::marker::PhantomData;
use std::sync::Arc;

// 借用检查器友好的 FFI 包装器

// 策略1：引用计数
pub struct SharedResource {
    inner: Arc<InnerResource>,
}

impl SharedResource {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(InnerResource::new()),
        }
    }

    pub fn share_for_ffi(&self) -> FfiResourceHandle {
        let ptr = Arc::into_raw(Arc::clone(&self.inner));
        FfiResourceHandle { ptr }
    }
}

pub struct FfiResourceHandle {
    ptr: *const InnerResource,
}

impl FfiResourceHandle {
    // SAFETY: 必须在使用后调用 release
    pub unsafe fn as_ref(&self) -> &InnerResource {
        &*self.ptr
    }

    pub unsafe fn release(self) {
        drop(Arc::from_raw(self.ptr));
    }
}

// 策略2：显式生命周期标记
pub struct BorrowedBuffer<'a> {
    ptr: *const u8,
    len: usize,
    _phantom: PhantomData<&'a [u8]>,
}

impl<'a> BorrowedBuffer<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self {
            ptr: data.as_ptr(),
            len: data.len(),
            _phantom: PhantomData,
        }
    }

    // 导出到 C，但借用检查器知道生命周期
    pub fn as_raw_parts(&self) -> (*const u8, usize) {
        (self.ptr, self.len)
    }
}

// 策略3：回调中的生命周期
pub unsafe extern "C" fn with_temporary_buffer<F>(
    size: usize,
    callback: F,
) where
    F: FnOnce(*mut u8, usize),
{
    let mut buffer = vec![0u8; size];
    callback(buffer.as_mut_ptr(), buffer.len());
    // buffer 在这里被释放，防止 C 代码持有野指针
}
```

---

## 4. 高级FFI模式

### 4.1 回调与闭包

```rust
use std::ffi::c_void;
use std::sync::Mutex;
use std::collections::HashMap;

// 类型擦除的回调系统
type CallbackId = u64;
static CALLBACK_REGISTRY: Mutex<HashMap<CallbackId, Box<dyn FnMut(i32)>>> =
    Mutex::new(HashMap::new());

// 注册 Rust 闭包作为 C 回调
pub fn register_callback<F>(callback: F) -> CallbackId
where
    F: FnMut(i32) + 'static,
{
    static NEXT_ID: AtomicU64 = AtomicU64::new(1);

    let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
    CALLBACK_REGISTRY.lock().unwrap().insert(id, Box::new(callback));
    id
}

// C 调用的统一入口
#[no_mangle]
pub extern "C" fn invoke_callback(id: CallbackId, value: i32) {
    if let Some(callback) = CALLBACK_REGISTRY.lock().unwrap().get_mut(&id) {
        callback(value);
    }
}

// 带用户数据的回调（传统 C 方式）
#[repr(C)]
pub struct CallbackWithData {
    callback: Option<extern "C" fn(*mut c_void, i32)>,
    user_data: *mut c_void,
}

impl CallbackWithData {
    pub fn call(&self, value: i32) {
        if let Some(cb) = self.callback {
            unsafe { cb(self.user_data, value) }
        }
    }
}

// Rust 闭包转换为 C 回调（使用 trampoline）
pub struct RustClosureWrapper<F> {
    closure: F,
}

impl<F: FnMut(i32)> RustClosureWrapper<F> {
    pub extern "C" fn trampoline(
        user_data: *mut c_void,
        value: i32,
    ) {
        let wrapper = unsafe { &mut *(user_data as *mut Self) };
        (wrapper.closure)(value);
    }
}
```

### 4.2 异步 FFI

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::os::raw::c_void;

// 异步 FFI 模式

// 回调风格的异步操作
#[repr(C)]
pub struct AsyncOperation {
    handle: *mut c_void,
    complete_callback: Option<extern "C" fn(*mut c_void, i32)>,
    user_data: *mut c_void,
}

impl AsyncOperation {
    pub fn poll(&self) -> Poll<i32> {
        // 检查操作是否完成
        unsafe {
            let status = check_operation_status(self.handle);
            match status {
                Status::Pending => Poll::Pending,
                Status::Complete(result) => Poll::Ready(result),
                Status::Error(code) => panic!("Async operation failed: {}", code),
            }
        }
    }
}

impl Future for AsyncOperation {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.poll() {
            Poll::Pending => {
                // 注册唤醒回调
                register_wake_callback(self.handle, cx.waker());
                Poll::Pending
            }
            Poll::Ready(result) => Poll::Ready(result),
        }
    }
}

// 使用示例
pub async fn async_ffi_call() -> i32 {
    let op = unsafe { start_async_operation() };
    op.await
}

// 将 C 的异步 API 包装为 Rust Future
pub struct CFuture {
    state: Arc<Mutex<CFutureState>>,
}

enum CFutureState {
    Pending,
    Waker(Option<Waker>),
    Complete(i32),
}

impl Future for CFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.state.lock().unwrap();
        match *state {
            CFutureState::Complete(result) => Poll::Ready(result),
            _ => {
                *state = CFutureState::Waker(Some(cx.waker().clone()));
                Poll::Pending
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn c_future_callback(state: *mut c_void, result: i32) {
    let state = unsafe { Arc::from_raw(state as *const Mutex<CFutureState>) };
    let mut guard = state.lock().unwrap();

    if let CFutureState::Waker(Some(waker)) = &*guard {
        waker.wake_by_ref();
    }

    *guard = CFutureState::Complete(result);
}
```

### 4.3 泛型 FFI 接口

```rust
use std::any::{Any, TypeId};
use std::collections::HashMap;

// 类型安全的泛型 FFI

// vtable 模式
#[repr(C)]
pub struct VTable<T> {
    pub drop: unsafe extern "C" fn(*mut T),
    pub clone: unsafe extern "C" fn(*const T) -> *mut T,
    pub eq: unsafe extern "C" fn(*const T, *const T) -> bool,
}

pub struct TypeErasedBox {
    ptr: *mut c_void,
    vtable: *const VTable<c_void>,
    type_id: TypeId,
}

impl TypeErasedBox {
    pub fn new<T: Any + Clone + PartialEq>(value: T) -> Self {
        lazy_static! {
            static ref VTABLES: Mutex<HashMap<TypeId, *const VTable<c_void>>> =
                Mutex::new(HashMap::new());
        }

        let type_id = TypeId::of::<T>();

        // 获取或创建 vtable
        let vtable = VTABLES.lock().unwrap()
            .entry(type_id)
            .or_insert_with(|| {
                let vt = Box::new(VTable::<T> {
                    drop: |ptr| unsafe { drop(Box::from_raw(ptr as *mut T)) },
                    clone: |ptr| unsafe {
                        Box::into_raw(Box::new((*(ptr as *const T)).clone())) as *mut c_void
                    },
                    eq: |a, b| unsafe {
                        *(a as *const T) == *(b as *const T)
                    },
                });
                Box::into_raw(vt) as *const VTable<c_void>
            });

        Self {
            ptr: Box::into_raw(Box::new(value)) as *mut c_void,
            vtable: *vtable,
            type_id,
        }
    }

    pub fn is<T: Any>(&self) -> bool {
        self.type_id == TypeId::of::<T>()
    }

    pub unsafe fn downcast_ref<T: Any>(&self) -> Option<&T> {
        if self.is::<T>() {
            Some(&*(self.ptr as *const T))
        } else {
            None
        }
    }
}

impl Clone for TypeErasedBox {
    fn clone(&self) -> Self {
        let new_ptr = unsafe { ((*self.vtable).clone)(self.ptr) };
        Self {
            ptr: new_ptr,
            vtable: self.vtable,
            type_id: self.type_id,
        }
    }
}

impl Drop for TypeErasedBox {
    fn drop(&mut self) {
        unsafe { ((*self.vtable).drop)(self.ptr) }
    }
}
```

---

## 5. 错误处理与panic安全

### 5.1 错误码转换

```rust
use std::ffi::c_int;
use std::ptr;

// 系统错误码定义
pub const SUCCESS: c_int = 0;
pub const ERROR_INVALID_PARAM: c_int = -1;
pub const ERROR_OUT_OF_MEMORY: c_int = -2;
pub const ERROR_NOT_FOUND: c_int = -3;
pub const ERROR_IO: c_int = -4;

// 结果类型转换
pub type CResult<T> = Result<T, CError>;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct CError {
    pub code: c_int,
    pub message: *const c_char,
}

impl CError {
    pub fn new(code: c_int, message: &str) -> Self {
        let c_string = CString::new(message).unwrap();
        // 注意：这里需要持久化字符串或使用静态字符串
        Self {
            code,
            message: c_string.into_raw(),
        }
    }

    pub fn ok() -> Self {
        Self {
            code: SUCCESS,
            message: ptr::null(),
        }
    }
}

// 错误转换宏
#[macro_export]
macro_rules! c_try {
    ($expr:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => return $crate::to_c_error(e),
        }
    };
}

// Rust 错误到 C 错误的转换
pub fn to_c_error<E: std::error::Error>(err: E) -> CError {
    let code = match err.downcast_ref::<std::io::Error>() {
        Some(io_err) if io_err.kind() == std::io::ErrorKind::NotFound => ERROR_NOT_FOUND,
        Some(_) => ERROR_IO,
        None => ERROR_INVALID_PARAM,
    };

    CError::new(code, &err.to_string())
}

// 使用示例
#[no_mangle]
pub extern "C" fn do_something(input: *const c_char, result: *mut *mut c_char) -> CError {
    if input.is_null() || result.is_null() {
        return CError::new(ERROR_INVALID_PARAM, "Null pointer");
    }

    let input_str = c_try!(unsafe { CStr::from_ptr(input) }.to_str());
    let output = c_try!(process_string(input_str));

    let c_output = c_try!(CString::new(output));
    unsafe { *result = c_output.into_raw() }

    CError::ok()
}

#[no_mangle]
pub extern "C" fn free_string(s: *mut c_char) {
    if !s.is_null() {
        unsafe { drop(CString::from_raw(s)) }
    }
}
```

### 5.2 Panic安全

```rust
use std::panic::{self, AssertUnwindSafe};

// 必须捕获所有 panic，防止跨 FFI 边界传播

#[no_mangle]
pub extern "C" fn panic_safe_function(input: *const c_char) -> *mut c_char {
    // 使用 catch_unwind 捕获 panic
    let result = panic::catch_unwind(AssertUnwindSafe(|| {
        unsafe {
            if input.is_null() {
                return ptr::null_mut();
            }

            let c_str = CStr::from_ptr(input)?;
            let rust_str = c_str.to_str()?;

            // 可能 panic 的操作
            let result = process_data(rust_str)?;

            CString::new(result).map(|c| c.into_raw()).unwrap_or(ptr::null_mut())
        }
    }));

    match result {
        Ok(ptr) => ptr,
        Err(_) => {
            // 记录 panic 信息，返回空指针或错误码
            eprintln!("Panic caught in FFI function");
            ptr::null_mut()
        }
    }
}

// 使用 abort-on-panic 策略的替代方案
// Cargo.toml:
// [profile.release]
// panic = "abort"

// FFI 边界的安全包装器
pub struct PanicGuard;

impl PanicGuard {
    pub fn new() -> Self {
        Self
    }

    pub fn run<F, R>(&self, f: F) -> Option<R>
    where
        F: FnOnce() -> R + std::panic::UnwindSafe,
    {
        panic::catch_unwind(f).ok()
    }
}

impl Drop for PanicGuard {
    fn drop(&mut self) {
        // 确保清理资源，即使在 panic 时
    }
}
```

### 5.3 异常安全策略

```rust
use std::sync::atomic::{AtomicBool, Ordering};

// RAII 风格的资源管理

pub struct FfiGuard {
    completed: AtomicBool,
    cleanup: Box<dyn FnOnce()>,
}

impl FfiGuard {
    pub fn new<F: FnOnce() + 'static>(cleanup: F) -> Self {
        Self {
            completed: AtomicBool::new(false),
            cleanup: Box::new(cleanup),
        }
    }

    pub fn complete(&self) {
        self.completed.store(true, Ordering::SeqCst);
    }
}

impl Drop for FfiGuard {
    fn drop(&mut self) {
        if !self.completed.load(Ordering::SeqCst) {
            // 操作未完成，执行清理
            let cleanup = unsafe {
                std::ptr::read(&self.cleanup)
            };
            cleanup();
        }
    }
}

// 事务风格的 FFI 操作
#[no_mangle]
pub extern "C" fn transactional_operation() -> c_int {
    let guard = FfiGuard::new(|| {
        // 回滚操作
        rollback_changes();
    });

    // 步骤1
    if !step1() {
        return ERROR_STEP1;
    }

    // 步骤2
    if !step2() {
        return ERROR_STEP2;
    }

    // 所有步骤成功
    guard.complete();
    SUCCESS
}
```

---

## 6. 工具链使用

### 6.1 bindgen

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉 cargo 链接系统库
    println!("cargo:rustc-link-lib=mylib");

    // 生成绑定
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg("-I/usr/local/include")
        .clang_arg("-I./include")
        // 白名单配置
        .whitelist_type("MyStruct")
        .whitelist_function("mylib_.*")
        .whitelist_var("MYLIB_.*")
        // 黑名单
        .blacklist_type("__.*")
        // 选项
        .derive_default(true)
        .derive_debug(true)
        .impl_debug(true)
        .generate_comments(true)
        // 布局测试
        .layout_tests(true)
        // 生成
        .generate()
        .expect("Unable to generate bindings");

    // 写入文件
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // 重新运行条件
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=build.rs");
}

// wrapper.h
// #include <mylib.h>
// #include "custom_types.h"

// 使用生成的绑定
// include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
```

### 6.2 cbindgen

```toml
# cbindgen.toml
language = "C"
cpp_compat = true
include_guard = "MYLIB_H"
sys_includes = ["stdint.h", "stdbool.h"]

[export]
include = ["MyStruct", "my_function"]
exclude = ["PrivateType"]

[fn]
rename_types = "SnakeCase"

[struct]
rename_fields = "SnakeCase"
```

```rust
// lib.rs
/// FFI 安全的结构体
#[repr(C)]
#[derive(Debug, Clone)]
pub struct MyStruct {
    pub field1: i32,
    pub field2: *const c_char,
}

/// 导出函数
///
/// # Safety
/// `data` must be a valid pointer
#[no_mangle]
pub unsafe extern "C" fn my_function(data: *const MyStruct) -> i32 {
    if data.is_null() {
        return -1;
    }
    (*data).field1
}
```

### 6.3 调试与测试

```rust
// FFI 测试策略

#[cfg(test)]
mod tests {
    use super::*;

    // 测试内存布局
    #[test]
    fn test_struct_layout() {
        assert_eq!(
            std::mem::size_of::<MyStruct>(),
            std::mem::size_of::<std::os::raw::c_int>() + std::mem::size_of::<*const c_char>()
        );

        assert_eq!(
            std::mem::align_of::<MyStruct>(),
            std::mem::align_of::<*const c_char>()
        );
    }

    // 使用 libc 测试
    #[test]
    fn test_c_interop() {
        let c_string = CString::new("test").unwrap();
        let ptr = c_string.as_ptr();

        unsafe {
            let len = libc::strlen(ptr);
            assert_eq!(len, 4);
        }
    }

    // 使用 Miri 测试未定义行为
    // cargo +nightly miri test

    // Valgrind 测试
    // valgrind --leak-check=full ./target/debug/mytest
}

// 集成测试
#[test]
fn test_round_trip() {
    // Rust -> C -> Rust
    let original = MyStruct {
        field1: 42,
        field2: CString::new("hello").unwrap().into_raw(),
    };

    let ptr = &original as *const MyStruct;
    let result = unsafe { my_function(ptr) };

    assert_eq!(result, 42);

    // 清理
    unsafe { drop(CString::from_raw(original.field2 as *mut c_char)) };
}
```

---

## 7. 实际案例

### 7.1 图像处理库包装

```rust
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int, c_void};

// 假设这是 C 库的接口
extern "C" {
    fn image_load(path: *const c_char, width: *mut c_int, height: *mut c_int) -> *mut c_void;
    fn image_save(path: *const c_char, data: *const c_void, width: c_int, height: c_int) -> c_int;
    fn image_free(data: *mut c_void);
    fn image_resize(src: *const c_void, dst: *mut c_void, src_w: c_int, src_h: c_int, dst_w: c_int, dst_h: c_int);
}

// Rust 友好的包装器
pub struct Image {
    data: *mut c_void,
    width: i32,
    height: i32,
}

impl Image {
    pub fn load<P: AsRef<std::path::Path>>(path: P) -> Result<Self, ImageError> {
        let path_str = CString::new(path.as_ref().to_str().ok_or(ImageError::InvalidPath)?)?;

        let mut width = 0;
        let mut height = 0;

        let data = unsafe { image_load(path_str.as_ptr(), &mut width, &mut height) };

        if data.is_null() {
            return Err(ImageError::LoadFailed);
        }

        Ok(Self {
            data,
            width,
            height,
        })
    }

    pub fn save<P: AsRef<std::path::Path>>(&self, path: P) -> Result<(), ImageError> {
        let path_str = CString::new(path.as_ref().to_str().ok_or(ImageError::InvalidPath)?)?;

        let result = unsafe {
            image_save(path_str.as_ptr(), self.data, self.width, self.height)
        };

        if result != 0 {
            Err(ImageError::SaveFailed)
        } else {
            Ok(())
        }
    }

    pub fn resize(&self, new_width: i32, new_height: i32) -> Result<Image, ImageError> {
        let new_data = unsafe { libc::malloc((new_width * new_height * 4) as usize) };

        if new_data.is_null() {
            return Err(ImageError::OutOfMemory);
        }

        unsafe {
            image_resize(
                self.data,
                new_data,
                self.width,
                self.height,
                new_width,
                new_height,
            );
        }

        Ok(Image {
            data: new_data,
            width: new_width,
            height: new_height,
        })
    }

    pub fn width(&self) -> i32 { self.width }
    pub fn height(&self) -> i32 { self.height }
}

impl Drop for Image {
    fn drop(&mut self) {
        if !self.data.is_null() {
            unsafe { image_free(self.data) }
        }
    }
}

#[derive(Debug)]
pub enum ImageError {
    InvalidPath,
    LoadFailed,
    SaveFailed,
    OutOfMemory,
}

impl std::fmt::Display for ImageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImageError::InvalidPath => write!(f, "Invalid file path"),
            ImageError::LoadFailed => write!(f, "Failed to load image"),
            ImageError::SaveFailed => write!(f, "Failed to save image"),
            ImageError::OutOfMemory => write!(f, "Out of memory"),
        }
    }
}

impl std::error::Error for ImageError {}
```

### 7.2 数据库驱动实现

```rust
use std::ffi::{CStr, CString, c_void};
use std::os::raw::{c_char, c_int};
use std::sync::Arc;

// C 数据库 API
extern "C" {
    fn db_connect(conn_str: *const c_char) -> *mut c_void;
    fn db_disconnect(conn: *mut c_void);
    fn db_query(conn: *mut c_void, sql: *const c_char) -> *mut c_void;
    fn db_fetch_row(result: *mut c_void) -> *mut c_void;
    fn db_get_column(row: *mut c_void, col: c_int) -> *const c_char;
    fn db_free_result(result: *mut c_void);
    fn db_error(conn: *mut c_void) -> *const c_char;
}

// Rust 包装器
pub struct Connection {
    raw: *mut c_void,
}

unsafe impl Send for Connection {}
unsafe impl Sync for Connection {}

impl Connection {
    pub fn new(conn_str: &str) -> Result<Self, DbError> {
        let c_conn_str = CString::new(conn_str)?;
        let raw = unsafe { db_connect(c_conn_str.as_ptr()) };

        if raw.is_null() {
            return Err(DbError::ConnectionFailed);
        }

        Ok(Self { raw })
    }

    pub fn query(&self, sql: &str) -> Result<QueryResult, DbError> {
        let c_sql = CString::new(sql)?;
        let result = unsafe { db_query(self.raw, c_sql.as_ptr()) };

        if result.is_null() {
            let err = unsafe {
                CStr::from_ptr(db_error(self.raw))
                    .to_string_lossy()
                    .into_owned()
            };
            return Err(DbError::QueryFailed(err));
        }

        Ok(QueryResult {
            raw: result,
            _conn: PhantomData,
        })
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        if !self.raw.is_null() {
            unsafe { db_disconnect(self.raw) }
        }
    }
}

pub struct QueryResult<'a> {
    raw: *mut c_void,
    _conn: PhantomData<&'a Connection>,
}

impl<'a> QueryResult<'a> {
    pub fn iter(&self) -> RowIter<'a> {
        RowIter {
            result: self,
            current: ptr::null_mut(),
        }
    }
}

impl<'a> Drop for QueryResult<'a> {
    fn drop(&mut self) {
        if !self.raw.is_null() {
            unsafe { db_free_result(self.raw) }
        }
    }
}

pub struct RowIter<'a> {
    result: &'a QueryResult<'a>,
    current: *mut c_void,
}

impl<'a> Iterator for RowIter<'a> {
    type Item = Row<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current = unsafe { db_fetch_row(self.result.raw) };

        if self.current.is_null() {
            None
        } else {
            Some(Row { raw: self.current })
        }
    }
}

pub struct Row<'a> {
    raw: *mut c_void,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> Row<'a> {
    pub fn get(&self, col: i32) -> Option<&str> {
        unsafe {
            let val = db_get_column(self.raw, col);
            if val.is_null() {
                None
            } else {
                CStr::from_ptr(val).to_str().ok()
            }
        }
    }
}

#[derive(Debug)]
pub enum DbError {
    ConnectionFailed,
    QueryFailed(String),
    InvalidString,
}

impl From<std::ffi::NulError> for DbError {
    fn from(_: std::ffi::NulError) -> Self {
        DbError::InvalidString
    }
}
```

### 7.3 硬件抽象层

```rust
use std::os::raw::{c_uint, c_void};
use std::sync::atomic::{AtomicU32, Ordering};

// 嵌入式硬件寄存器定义
#[repr(C)]
struct GpioRegisters {
    moder: AtomicU32,    // Mode register
    otyper: AtomicU32,   // Output type register
    ospeedr: AtomicU32,  // Output speed register
    pupdr: AtomicU32,    // Pull-up/pull-down register
    idr: AtomicU32,      // Input data register
    odr: AtomicU32,      // Output data register
    bsrr: AtomicU32,     // Bit set/reset register
    lckr: AtomicU32,     // Configuration lock register
}

// 安全的 GPIO 包装器
pub struct GpioPort {
    registers: *mut GpioRegisters,
    clock: ClockManager,
}

impl GpioPort {
    /// SAFETY: `base_addr` 必须是有效的 GPIO 寄存器基地址
    pub unsafe fn new(base_addr: usize, clock: ClockManager) -> Self {
        // 启用时钟
        clock.enable_gpio();

        Self {
            registers: base_addr as *mut GpioRegisters,
            clock,
        }
    }

    pub fn configure_pin(&self, pin: u8, config: PinConfig) {
        assert!(pin < 16, "Invalid pin number");

        let regs = unsafe { &*self.registers };
        let pin = pin as u32;

        // 配置模式
        regs.moder.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |mut v| {
            v &= !(0b11 << (pin * 2));  // 清除原有配置
            v |= (config.mode as u32) << (pin * 2);
            Some(v)
        }).unwrap();

        // 配置输出类型
        if config.mode == PinMode::Output {
            regs.otyper.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |mut v| {
                v &= !(1 << pin);
                v |= (config.output_type as u32) << pin;
                Some(v)
            }).unwrap();
        }

        // 配置上拉/下拉
        regs.pupdr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |mut v| {
            v &= !(0b11 << (pin * 2));
            v |= (config.pull as u32) << (pin * 2);
            Some(v)
        }).unwrap();
    }

    pub fn set_pin(&self, pin: u8) {
        assert!(pin < 16);
        let regs = unsafe { &*self.registers };
        regs.bsrr.store(1 << pin, Ordering::SeqCst);
    }

    pub fn clear_pin(&self, pin: u8) {
        assert!(pin < 16);
        let regs = unsafe { &*self.registers };
        regs.bsrr.store(1 << (pin + 16), Ordering::SeqCst);
    }

    pub fn read_pin(&self, pin: u8) -> bool {
        assert!(pin < 16);
        let regs = unsafe { &*self.registers };
        (regs.idr.load(Ordering::SeqCst) & (1 << pin)) != 0
    }

    pub fn write_pin(&self, pin: u8, value: bool) {
        if value {
            self.set_pin(pin);
        } else {
            self.clear_pin(pin);
        }
    }
}

#[derive(Clone, Copy)]
pub enum PinMode {
    Input = 0b00,
    Output = 0b01,
    AlternateFunction = 0b10,
    Analog = 0b11,
}

#[derive(Clone, Copy)]
pub enum OutputType {
    PushPull = 0,
    OpenDrain = 1,
}

#[derive(Clone, Copy)]
pub enum PullType {
    None = 0b00,
    PullUp = 0b01,
    PullDown = 0b10,
}

pub struct PinConfig {
    pub mode: PinMode,
    pub output_type: OutputType,
    pub pull: PullType,
}

impl Default for PinConfig {
    fn default() -> Self {
        Self {
            mode: PinMode::Input,
            output_type: OutputType::PushPull,
            pull: PullType::None,
        }
    }
}
```

---

## 总结

FFI 编程是 Rust 与其他语言互操作的核心能力，但也引入了安全挑战。关键要点：

1. **类型安全**: 仔细匹配 Rust 与 C 的类型，使用 `#[repr(C)]` 控制布局
2. **所有权管理**: 明确跨边界的数据所有权，使用不透明指针模式
3. **错误处理**: 转换错误码，捕获 panic，确保异常安全
4. **工具使用**: bindgen 和 cbindgen 可以自动生成大部分绑定代码
5. **测试**: 使用 Miri、Valgrind 等工具检测未定义行为和内存泄漏

---

## 参考资源

- [The Rustonomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html)
- [bindgen User Guide](https://rust-lang.github.io/rust-bindgen/)
- [cbindgen Documentation](https://docs.rs/cbindgen/)
- [libc crate](https://docs.rs/libc/)
- [Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/)
