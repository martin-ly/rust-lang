//! FFI 高级用法
//! FFI high usage
//! FFI
//! 对照 The Rustonomicon 中 FFI 相关章节。
//! to照 The Rustonomicon in FFI 相关章节。
//! 涵盖：
//! cover ：
//! ：
//! - 不透明结构体（Opaque Structs）
//! - 不透明struct（Opaque Structs）
//! - 回调函数与生命周期
//! - function and lifetime
//! - 回调functionandlifetime
//! - 可变参数函数封装概念
//! - parameter function concept
//! - 动态库加载（dlopen 概念）
//! - library （dlopen concept ）

/// 不透明结构体封装
/// struct
#[repr(C)]
pub struct OpaqueContext {
    _private: [u8; 0],
}

/// 外部 C 函数声明（概念演示）
/// outside C function （concept demonstration ）
/// 真实场景需要 `extern "C"` 块和 `#[link]` 属性。
/// real scenario `extern "C"` and `#[link]` attribute 。
pub mod c_api_concepts {
    use super::OpaqueContext;
    use std::ffi::{c_char, c_void};

    /// 创建上下文（由 C 库实现）
    /// on under （ C library ）
    pub type CreateFn = unsafe extern "C" fn() -> *mut OpaqueContext;

    /// 销毁上下文
    /// on under
    pub type DestroyFn = unsafe extern "C" fn(*mut OpaqueContext);

    /// 回调函数类型：Rust 被 C 调用
    /// function type ：Rust is C
    /// 回调functiontype：Rust is C Call
    pub type CallbackFn = unsafe extern "C" fn(user_data: *mut c_void, result: i32);

    /// 带可变参数的 C 函数签名概念
    /// parameter C function concept
    pub type VarargsFn = unsafe extern "C" fn(fmt: *const c_char, ...);
}

pub struct ContextHandle {
    ptr: *mut OpaqueContext,
    destroy: unsafe extern "C" fn(*mut OpaqueContext),
}

impl ContextHandle {
    /// # Safety
    ///
    pub unsafe fn new(
        ptr: *mut OpaqueContext,
        destroy: unsafe extern "C" fn(*mut OpaqueContext),
    ) -> Self {
        Self { ptr, destroy }
    }
}

impl Drop for ContextHandle {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe {
                (self.destroy)(self.ptr);
            }
        }
    }
}

// Send + Sync 标记：如果 C 库保证线程安全
unsafe impl Send for ContextHandle {}
unsafe impl Sync for ContextHandle {}

pub struct CallbackWrapper<F> {
    closure: F,
}

impl<F: FnMut(i32)> CallbackWrapper<F> {
    /// 创建新包装器
    pub fn new(closure: F) -> Self {
        Self { closure }
    }

    /// Get C 可Callfunction pointerand user_data
    ///
    pub unsafe fn into_raw(
        self,
    ) -> (
        *const std::ffi::c_void,
        unsafe extern "C" fn(*mut std::ffi::c_void, i32),
    ) {
        let boxed = Box::into_raw(Box::new(self));
        (boxed.cast::<std::ffi::c_void>(), trampoline::<F>)
    }
}

unsafe extern "C" fn trampoline<F: FnMut(i32)>(user_data: *mut std::ffi::c_void, result: i32) {
    let wrapper = unsafe { &mut *user_data.cast::<CallbackWrapper<F>>() };
    (wrapper.closure)(result);
}

pub mod dynamic_loading_concept {
    /// 动态库加载步骤
    /// library step
    pub fn loading_steps() -> &'static str {
        r#"动态库加载流程:
1. 调用 dlopen (Linux) / LoadLibrary (Windows) 加载共享库
2. 使用 dlsym / GetProcAddress 获取函数指针
3. 将函数指针转换为 Rust extern "C" 函数类型
4. 使用完毕后调用 dlclose / FreeLibrary 卸载
"#
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opaque_context_size() {
        assert_eq!(size_of::<OpaqueContext>(), 0);
    }

    #[test]
    fn test_callback_wrapper_creation() {
        let mut received = 0;
        let wrapper = CallbackWrapper::new(|v: i32| received = v);
        let _ = wrapper;
        assert_eq!(received, 0);
    }

    #[test]
    fn test_dynamic_loading_concept() {
        assert!(dynamic_loading_concept::loading_steps().contains("dlopen"));
    }
}
