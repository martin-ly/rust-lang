# FFI集成指南 - 安全关键系统

## 概述

本指南提供在安全关键系统中安全地使用Rust FFI(外部函数接口)与C/C++代码集成的最佳实践，确保跨语言边界的安全性。

---

## FFI安全风险

### 风险矩阵

| 风险 | 严重性 | 可能性 | 缓解复杂度 | Rust防护 |
|------|--------|--------|------------|----------|
| 空指针解引用 | 高 | 高 | 中 | Option/ptr::NonNull |
| 缓冲区溢出 | 高 | 高 | 高 | 切片边界检查 |
| 内存泄漏 | 中 | 中 | 低 | Drop实现 |
| 数据竞争 | 高 | 中 | 高 | Send/Sync |
| ABI不匹配 | 高 | 低 | 低 | bindgen/cbindgen |

---

## 基础FFI模式

### 1. 安全包装器模式

```rust
//! 安全的C库包装器

use std::ffi::{c_char, c_int, CStr, CString};
use std::ptr::NonNull;

/// C库不透明句柄
pub struct NativeHandle {
    ptr: NonNull<NativeContext>,
}

/// 安全包装器
impl NativeHandle {
    /// 创建新实例
    ///
    /// # Safety
    /// 底层C库必须已正确初始化
    pub unsafe fn new() -> Result<Self, FfiError> {
        let ptr = native_create();
        if ptr.is_null() {
            return Err(FfiError::InitializationFailed);
        }

        Ok(Self {
            ptr: NonNull::new_unchecked(ptr),
        })
    }

    /// 安全操作
    pub fn process(&mut self, data: &[u8]) -> Result<Vec<u8>, FfiError> {
        // 边界检查
        if data.len() > MAX_BUFFER_SIZE {
            return Err(FfiError::BufferTooLarge);
        }

        let mut output = vec![0u8; MAX_BUFFER_SIZE];
        let mut output_len = 0usize;

        // SAFETY: 指针有效，边界已检查
        let result = unsafe {
            native_process(
                self.ptr.as_ptr(),
                data.as_ptr(),
                data.len(),
                output.as_mut_ptr(),
                output.len(),
                &mut output_len,
            )
        };

        if result != 0 {
            return Err(FfiError::ProcessingFailed(result));
        }

        output.truncate(output_len);
        Ok(output)
    }
}

impl Drop for NativeHandle {
    fn drop(&mut self) {
        // SAFETY: 指针有效且不再使用
        unsafe {
            native_destroy(self.ptr.as_ptr());
        }
    }
}

// 外部C函数声明
extern "C" {
    fn native_create() -> *mut NativeContext;
    fn native_destroy(ctx: *mut NativeContext);
    fn native_process(
        ctx: *mut NativeContext,
        input: *const u8,
        input_len: usize,
        output: *mut u8,
        output_capacity: usize,
        output_len: *mut usize,
    ) -> c_int;
}

#[repr(C)]
pub struct NativeContext {
    _opaque: [u8; 0],
}

const MAX_BUFFER_SIZE: usize = 1024 * 1024; // 1MB

#[derive(Debug)]
pub enum FfiError {
    InitializationFailed,
    BufferTooLarge,
    ProcessingFailed(c_int),
}
```

### 2. 类型转换安全

```rust
//! 类型转换安全

use std::ffi::{c_char, c_int, c_uint};

/// 安全的C字符串处理
pub struct SafeCString {
    inner: CString,
}

impl SafeCString {
    pub fn new(s: &str) -> Result<Self, FfiError> {
        let inner = CString::new(s)
            .map_err(|_| FfiError::NullByteInString)?;
        Ok(Self { inner })
    }

    /// 获取C字符串指针
    ///
    /// 注意: 返回的指针只在self生命周期内有效
    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }
}

/// 整数边界检查
pub fn safe_int_conversion(value: u64) -> Result<c_uint, FfiError> {
    if value > c_uint::MAX as u64 {
        return Err(FfiError::IntegerOverflow);
    }
    Ok(value as c_uint)
}

/// 枚举映射
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NativeStatus {
    Ok = 0,
    Error = 1,
    InvalidParam = 2,
    NoMemory = 3,
}

impl TryFrom<c_int> for NativeStatus {
    type Error = FfiError;

    fn try_from(value: c_int) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Ok),
            1 => Ok(Self::Error),
            2 => Ok(Self::InvalidParam),
            3 => Ok(Self::NoMemory),
            _ => Err(FfiError::UnknownStatus(value)),
        }
    }
}

#[derive(Debug)]
pub enum FfiError {
    NullByteInString,
    IntegerOverflow,
    UnknownStatus(c_int),
}
```

### 3. 回调安全

```rust
//! 安全的回调机制

use std::ffi::c_void;
use std::panic::catch_unwind;
use std::sync::Mutex;

/// 线程安全的回调注册
pub struct CallbackRegistry {
    callback: Mutex<Option<Box<dyn FnMut(Event) + Send>>>,
}

impl CallbackRegistry {
    pub fn new() -> Self {
        Self {
            callback: Mutex::new(None),
        }
    }

    /// 注册回调
    pub fn register<F>(&self, callback: F)
    where
        F: FnMut(Event) + Send + 'static,
    {
        *self.callback.lock().unwrap() = Some(Box::new(callback));
    }

    /// 触发回调 (从C调用)
    ///
    /// # Safety
    /// 此函数由C代码调用，必须处理panic
    pub unsafe extern "C" fn trampoline(
        event_type: c_int,
        data: *const c_void,
        user_data: *mut c_void,
    ) {
        // 捕获panic防止跨FFI边界传播
        let result = catch_unwind(|| {
            let registry = &*(user_data as *const CallbackRegistry);

            if let Some(callback) = registry.callback.lock().unwrap().as_mut() {
                let event = Event::from_native(event_type, data);
                callback(event);
            }
        });

        if result.is_err() {
            // 记录panic，但不传播到C代码
            eprintln!("Callback panicked!");
        }
    }
}

#[derive(Debug)]
pub struct Event {
    pub event_type: EventType,
    pub data: Vec<u8>,
}

impl Event {
    unsafe fn from_native(event_type: c_int, data: *const c_void) -> Self {
        // 转换实现...
        Self {
            event_type: EventType::Data,
            data: vec![],
        }
    }
}

#[derive(Debug)]
pub enum EventType {
    Data,
    Error,
    Complete,
}
```

---

## 安全关键FFI模式

### 1. 内存管理

```rust
//! FFI内存管理安全

use std::alloc::{self, Layout};
use std::ptr::NonNull;

/// 安全的C内存分配器包装
pub struct CAllocator;

impl CAllocator {
    /// 分配对齐内存
    pub unsafe fn alloc(size: usize, align: usize) -> Option<NonNull<u8>> {
        let layout = Layout::from_size_align(size, align).ok()?;
        let ptr = alloc::alloc(layout);
        NonNull::new(ptr)
    }

    /// 释放内存
    pub unsafe fn dealloc(ptr: NonNull<u8>, size: usize, align: usize) {
        let layout = Layout::from_size_align(size, align).unwrap();
        alloc::dealloc(ptr.as_ptr(), layout);
    }
}

/// Vec与C数组的安全转换
pub struct CVec<T> {
    ptr: NonNull<T>,
    len: usize,
    capacity: usize,
}

impl<T> CVec<T> {
    /// 从Rust Vec创建
    pub fn from_vec(mut vec: Vec<T>) -> Self {
        let ptr = NonNull::new(vec.as_mut_ptr()).unwrap();
        let len = vec.len();
        let capacity = vec.capacity();
        std::mem::forget(vec); // 防止Rust释放

        Self { ptr, len, capacity }
    }

    /// 转换为C指针
    pub fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    /// 获取长度
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T> Drop for CVec<T> {
    fn drop(&mut self) {
        // SAFETY: 重新构造Vec并正常释放
        unsafe {
            let _ = Vec::from_raw_parts(
                self.ptr.as_ptr(),
                self.len,
                self.capacity,
            );
        }
    }
}
```

### 2. 并发FFI

```rust
//! 并发FFI安全

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, Thread};

/// 线程安全的FFI上下文
pub struct ThreadSafeContext {
    inner: Arc<NativeContextWrapper>,
}

unsafe impl Send for ThreadSafeContext {}
unsafe impl Sync for ThreadSafeContext {}

impl ThreadSafeContext {
    pub fn new() -> Result<Self, FfiError> {
        // SAFETY: 单线程创建
        let inner = unsafe { NativeContextWrapper::new()? };
        Ok(Self {
            inner: Arc::new(inner),
        })
    }

    pub fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

struct NativeContextWrapper {
    ptr: *mut NativeContext,
    is_thread_safe: AtomicBool,
}

unsafe impl Send for NativeContextWrapper {}

impl NativeContextWrapper {
    unsafe fn new() -> Result<Self, FfiError> {
        let ptr = native_create();
        if ptr.is_null() {
            return Err(FfiError::CreationFailed);
        }

        Ok(Self {
            ptr,
            is_thread_safe: AtomicBool::new(false),
        })
    }

    fn mark_thread_safe(&self) {
        self.is_thread_safe.store(true, Ordering::Release);
    }
}

impl Drop for NativeContextWrapper {
    fn drop(&mut self) {
        unsafe {
            native_destroy(self.ptr);
        }
    }
}
```

---

## 自动生成工具

### bindgen配置

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉cargo在头文件变化时重新生成
    println!("cargo:rerun-if-changed=wrapper.h");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // 使用core而不是std
        .use_core()
        // 整数类型使用固定大小
        .ctypes_prefix("cty")
        // 生成注释
        .generate_comments(true)
        // 布局测试
        .layout_tests(true)
        // 派生特征
        .derive_default(true)
        .derive_debug(true)
        .derive_partialeq(true)
        // 安全注解
        .enable_cxx_namespaces()
        // 完成构建
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

### cbindgen配置

```toml
# cbindgen.toml
[parse]
parse_deps = true
include = ["my-crate"]

[export]
include = ["MyStruct", "my_function"]
prefix = "MY_"

[fn]
args = "horizontal"
rename_types = "PascalCase"

[struct]
rename_types = "PascalCase"
```

---

## 验证与测试

### FFI测试模式

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// 测试空指针处理
    #[test]
    fn test_null_pointer_handling() {
        let result = unsafe { process_with_null() };
        assert!(result.is_err());
    }

    /// 测试缓冲区边界
    #[test]
    fn test_buffer_boundaries() {
        let data = vec![0u8; MAX_BUFFER_SIZE + 1];
        let handle = unsafe { NativeHandle::new().unwrap() };

        let result = handle.process(&data);
        assert!(matches!(result, Err(FfiError::BufferTooLarge)));
    }

    /// 测试内存泄漏
    #[test]
    fn test_no_memory_leaks() {
        for _ in 0..10000 {
            let _ = unsafe { NativeHandle::new() };
            // Drop会自动释放
        }
        // 使用valgrind或miri检查泄漏
    }

    /// Miri测试FFI安全性
    #[test]
    #[cfg(miri)]
    fn test_ffi_under_miri() {
        // Miri可以检测FFI边界的不安全操作
    }
}
```

---

## 最佳实践检查表

### 设计阶段

- [ ] 最小化FFI边界
- [ ] 定义清晰的类型映射
- [ ] 错误处理策略确定
- [ ] 内存所有权规则定义
- [ ] 线程安全模型确定

### 实现阶段

- [ ] 所有unsafe代码有SAFETY注释
- [ ] 空指针检查完整
- [ ] 边界检查完整
- [ ] Drop实现正确
- [ ] 线程安全标记正确

### 测试阶段

- [ ] 异常输入测试
- [ ] 边界条件测试
- [ ] 并发测试
- [ ] Miri测试
- [ ] Valgrind/ASan测试

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用范围**: ASIL D/SIL 4级FFI集成

---

*FFI是安全关键系统中的高风险区域，必须经过严格审查。*
