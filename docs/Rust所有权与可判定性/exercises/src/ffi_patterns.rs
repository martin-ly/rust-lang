//! FFI模式
//!
//! Rust与外部代码的安全交互

use std::ffi::{CString, CStr, c_char, c_int};
use std::os::raw::c_void;

// ============================================
// C字符串处理
// ============================================

/// Rust String -> C字符串
pub fn rust_to_c_string(s: String) -> Result<CString, String> {
    CString::new(s).map_err(|e| format!("Null byte in string: {:?}", e))
}

/// C字符串 -> Rust &str
/// 
/// # Safety
/// ptr必须指向有效的C字符串
pub unsafe fn c_to_rust_str(ptr: *const c_char) -> Option<&'static str> {
    if ptr.is_null() {
        return None;
    }
    CStr::from_ptr(ptr).to_str().ok()
}

// ============================================
// 不透明指针模式
// ============================================

pub struct ExternalHandle {
    _opaque: [u8; 0], // ZST，确保不透明
}

/// 外部库上下文的安全封装
pub struct SafeContext {
    raw: *mut ExternalHandle,
}

impl SafeContext {
    /// # Safety
    /// raw必须是有效的上下文指针
    pub unsafe fn from_raw(raw: *mut ExternalHandle) -> Option<Self> {
        if raw.is_null() {
            None
        } else {
            Some(Self { raw })
        }
    }
    
    pub fn as_ptr(&self) -> *mut ExternalHandle {
        self.raw
    }
}

impl Drop for SafeContext {
    fn drop(&mut self) {
        // 假设有外部释放函数
        // 注意：实际项目中需要链接对应的外部库
        // 这里使用条件编译避免测试时的链接问题
        if !self.raw.is_null() {
            // 实际调用外部释放函数的地方
            // unsafe { external_free(self.raw) }
            // 标记为已释放
            let _ = self.raw;
        }
    }
}

// 外部函数声明示例（实际使用时需要链接对应库）
// unsafe extern "C" {
//     fn external_free(handle: *mut ExternalHandle);
// }

// ============================================
// 回调模式
// ============================================

/// 将Rust闭包传递给C的trampoline
/// 
/// # Safety
/// user_data必须是有效的Box<FnMut>指针
pub unsafe extern "C" fn rust_callback_trampoline<F>(
    user_data: *mut c_void,
    value: c_int,
) where F: FnMut(c_int) {
    let closure: &mut F = &mut *(user_data as *mut F);
    closure(value);
}

/// 类型安全的回调设置
pub fn with_callback<F, R>(mut callback: F, f: impl FnOnce(*mut c_void) -> R) -> R
where
    F: FnMut(c_int),
{
    let ptr = &mut callback as *mut F as *mut c_void;
    f(ptr)
}

// ============================================
// 结构体布局
// ============================================

/// 与C兼容的结构体
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

/// 带有变长数组的C结构体
#[repr(C)]
pub struct Buffer {
    pub len: usize,
    pub data: [u8; 0], // FAM - Flexible Array Member
}

impl Buffer {
    /// # Safety
    /// ptr必须指向有效的Buffer
    pub unsafe fn data_slice(&self) -> &[u8] {
        std::slice::from_raw_parts(self.data.as_ptr(), self.len)
    }
}

// ============================================
// 错误处理
// ============================================

/// FFI错误码
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub enum FfiError {
    Success = 0,
    InvalidArg = -1,
    NullPointer = -2,
    BufferTooSmall = -3,
}

/// 结果类型转换
pub fn check_result(code: c_int) -> Result<(), FfiError> {
    match code {
        0 => Ok(()),
        -1 => Err(FfiError::InvalidArg),
        -2 => Err(FfiError::NullPointer),
        -3 => Err(FfiError::BufferTooSmall),
        _ => panic!("Unknown error code: {}", code),
    }
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_c_string_roundtrip() {
        let original = "Hello, FFI!".to_string();
        let c_str = rust_to_c_string(original.clone()).unwrap();
        let roundtrip = unsafe { c_to_rust_str(c_str.as_ptr()) }.unwrap();
        assert_eq!(original, roundtrip);
    }
    
    #[test]
    fn test_error_codes() {
        assert!(check_result(0).is_ok());
        assert!(matches!(check_result(-1), Err(FfiError::InvalidArg)));
    }
}
