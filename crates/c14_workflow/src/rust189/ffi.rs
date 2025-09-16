//! # FFI 改进 / FFI Improvements
//!
//! Rust 1.89 在 FFI (Foreign Function Interface) 方面进行了重要改进，
//! 包括 `i128`/`u128` 类型在 `extern "C"` 中的安全使用。
//!
//! Rust 1.89 has made important improvements in FFI (Foreign Function Interface),
//! including safe usage of `i128`/`u128` types in `extern "C"`.

use std::ffi::{CStr, CString};
use std::mem;
use std::os::raw::c_char;

/// FFI 128位类型 / FFI 128-bit Type
///
/// 用于 FFI 的 128位整数类型。
/// 128-bit integer type for FFI.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FFI128Bit {
    pub i128_value: i128,
    pub u128_value: u128,
}

impl FFI128Bit {
    /// 创建新的 FFI128Bit 实例 / Create new FFI128Bit instance
    pub fn new(i128_value: i128, u128_value: u128) -> Self {
        Self {
            i128_value,
            u128_value,
        }
    }

    /// 从 C 结构转换 / Convert from C structure
    pub unsafe fn from_c_struct(ptr: *const Self) -> Option<Self> {
        if ptr.is_null() {
            return None;
        }
        unsafe { Some(*ptr) }
    }

    /// 转换为 C 结构 / Convert to C structure
    pub fn to_c_struct(&self) -> Self {
        *self
    }
}

/// FFI 类型定义 / FFI Type Definitions
pub mod types {

    /// 128位有符号整数 / 128-bit signed integer
    #[repr(C)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct i128_ffi {
        pub low: u64,
        pub high: i64,
    }

    /// 128位无符号整数 / 128-bit unsigned integer
    #[repr(C)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct u128_ffi {
        pub low: u64,
        pub high: u64,
    }

    /// 复数类型 / Complex number type
    #[repr(C)]
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub struct Complex {
        pub real: f64,
        pub imag: f64,
    }

    /// 向量类型 / Vector type
    #[repr(C)]
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub struct Vector3 {
        pub x: f32,
        pub y: f32,
        pub z: f32,
    }
}

/// FFI 转换器 / FFI Converter
pub struct FFIConverter;

impl FFIConverter {
    /// 将 Rust i128 转换为 FFI i128 / Convert Rust i128 to FFI i128
    pub fn i128_to_ffi(value: i128) -> types::i128_ffi {
        types::i128_ffi {
            low: (value as u64),
            high: ((value >> 64) as i64),
        }
    }

    /// 将 FFI i128 转换为 Rust i128 / Convert FFI i128 to Rust i128
    pub fn ffi_to_i128(value: types::i128_ffi) -> i128 {
        ((value.high as i128) << 64) | (value.low as i128)
    }

    /// 将 Rust u128 转换为 FFI u128 / Convert Rust u128 to FFI u128
    pub fn u128_to_ffi(value: u128) -> types::u128_ffi {
        types::u128_ffi {
            low: (value as u64),
            high: ((value >> 64) as u64),
        }
    }

    /// 将 FFI u128 转换为 Rust u128 / Convert FFI u128 to Rust u128
    pub fn ffi_to_u128(value: types::u128_ffi) -> u128 {
        ((value.high as u128) << 64) | (value.low as u128)
    }

    /// 将 Rust 字符串转换为 C 字符串 / Convert Rust string to C string
    pub fn string_to_cstring(s: &str) -> Result<CString, FFIError> {
        CString::new(s).map_err(|_| FFIError::StringConversionFailed)
    }

    /// 将 C 字符串转换为 Rust 字符串 / Convert C string to Rust string
    pub fn cstring_to_string(c_str: *const c_char) -> Result<String, FFIError> {
        if c_str.is_null() {
            return Err(FFIError::NullPointer);
        }

        unsafe {
            CStr::from_ptr(c_str)
                .to_str()
                .map(|s| s.to_string())
                .map_err(|_| FFIError::StringConversionFailed)
        }
    }
}

/// FFI 绑定生成器 / FFI Binding Generator
pub struct FFIBindingGenerator {
    bindings: Vec<FFIBinding>,
}

/// FFI 绑定 / FFI Binding
#[derive(Debug, Clone)]
pub struct FFIBinding {
    pub name: String,
    pub function_type: FFIFunctionType,
    pub parameters: Vec<FFIParameter>,
    pub return_type: FFIType,
    pub calling_convention: CallingConvention,
}

/// FFI 函数类型 / FFI Function Type
#[derive(Debug, Clone, PartialEq)]
pub enum FFIFunctionType {
    Function,
    Method,
    StaticMethod,
    Constructor,
    Destructor,
}

/// FFI 参数 / FFI Parameter
#[derive(Debug, Clone)]
pub struct FFIParameter {
    pub name: String,
    pub param_type: FFIType,
    pub is_optional: bool,
    pub is_output: bool,
}

/// FFI 类型 / FFI Type
#[derive(Debug, Clone, PartialEq)]
pub enum FFIType {
    Void,
    Bool,
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F32,
    F64,
    String,
    CString,
    Pointer(Box<FFIType>),
    Array(Box<FFIType>, usize),
    Struct(String),
    Enum(String),
}

/// 调用约定 / Calling Convention
#[derive(Debug, Clone, PartialEq)]
pub enum CallingConvention {
    C,
    StdCall,
    FastCall,
    ThisCall,
    VectorCall,
}

impl FFIBindingGenerator {
    /// 创建新的绑定生成器 / Create new binding generator
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// 添加绑定 / Add binding
    pub fn add_binding(&mut self, binding: FFIBinding) {
        self.bindings.push(binding);
    }

    /// 生成 Rust 绑定代码 / Generate Rust binding code
    pub fn generate_rust_bindings(&self) -> String {
        let mut code = String::new();

        code.push_str("//! 自动生成的 FFI 绑定 / Auto-generated FFI bindings\n");
        code.push_str("use std::ffi::{CStr, CString};\n");
        code.push_str("use std::os::raw::*;\n\n");

        for binding in &self.bindings {
            code.push_str(&self.generate_function_binding(binding));
            code.push_str("\n");
        }

        code
    }

    /// 生成函数绑定 / Generate function binding
    fn generate_function_binding(&self, binding: &FFIBinding) -> String {
        let mut code = String::new();

        // 函数签名 / Function signature
        code.push_str(&format!(
            "extern \"{}\" {{\n",
            self.calling_convention_to_str(&binding.calling_convention)
        ));
        code.push_str(&format!("    pub fn {}(\n", binding.name));

        // 参数 / Parameters
        for (i, param) in binding.parameters.iter().enumerate() {
            if i > 0 {
                code.push_str(",\n");
            }
            code.push_str(&format!(
                "        {}: {}",
                param.name,
                self.ffi_type_to_str(&param.param_type)
            ));
        }

        code.push_str("\n    ) -> ");
        code.push_str(&self.ffi_type_to_str(&binding.return_type));
        code.push_str(";\n");
        code.push_str("}\n");

        code
    }

    /// 调用约定转字符串 / Calling convention to string
    fn calling_convention_to_str(&self, convention: &CallingConvention) -> &'static str {
        match convention {
            CallingConvention::C => "C",
            CallingConvention::StdCall => "stdcall",
            CallingConvention::FastCall => "fastcall",
            CallingConvention::ThisCall => "thiscall",
            CallingConvention::VectorCall => "vectorcall",
        }
    }

    /// FFI 类型转字符串 / FFI type to string
    fn ffi_type_to_str(&self, ffi_type: &FFIType) -> String {
        match ffi_type {
            FFIType::Void => "()".to_string(),
            FFIType::Bool => "bool".to_string(),
            FFIType::I8 => "i8".to_string(),
            FFIType::I16 => "i16".to_string(),
            FFIType::I32 => "i32".to_string(),
            FFIType::I64 => "i64".to_string(),
            FFIType::I128 => "i128".to_string(),
            FFIType::U8 => "u8".to_string(),
            FFIType::U16 => "u16".to_string(),
            FFIType::U32 => "u32".to_string(),
            FFIType::U64 => "u64".to_string(),
            FFIType::U128 => "u128".to_string(),
            FFIType::F32 => "f32".to_string(),
            FFIType::F64 => "f64".to_string(),
            FFIType::String => "String".to_string(),
            FFIType::CString => "*const c_char".to_string(),
            FFIType::Pointer(inner) => format!("*mut {}", self.ffi_type_to_str(inner)),
            FFIType::Array(inner, size) => format!("[{}; {}]", self.ffi_type_to_str(inner), size),
            FFIType::Struct(name) => name.clone(),
            FFIType::Enum(name) => name.clone(),
        }
    }
}

/// FFI 错误 / FFI Error
#[derive(Debug, thiserror::Error)]
pub enum FFIError {
    #[error("字符串转换失败 / String conversion failed")]
    StringConversionFailed,

    #[error("空指针 / Null pointer")]
    NullPointer,

    #[error("类型转换失败 / Type conversion failed")]
    TypeConversionFailed,

    #[error("内存分配失败 / Memory allocation failed")]
    MemoryAllocationFailed,

    #[error("FFI 调用失败 / FFI call failed")]
    FFICallFailed(String),
}

/// FFI 安全包装器 / FFI Safe Wrapper
pub struct FFISafeWrapper<T> {
    data: T,
    is_valid: bool,
}

impl<T> FFISafeWrapper<T> {
    /// 创建新的安全包装器 / Create new safe wrapper
    pub fn new(data: T) -> Self {
        Self {
            data,
            is_valid: true,
        }
    }

    /// 获取数据 / Get data
    pub fn get_data(&self) -> Result<&T, FFIError> {
        if self.is_valid {
            Ok(&self.data)
        } else {
            Err(FFIError::TypeConversionFailed)
        }
    }

    /// 获取可变数据 / Get mutable data
    pub fn get_data_mut(&mut self) -> Result<&mut T, FFIError> {
        if self.is_valid {
            Ok(&mut self.data)
        } else {
            Err(FFIError::TypeConversionFailed)
        }
    }

    /// 标记为无效 / Mark as invalid
    pub fn invalidate(&mut self) {
        self.is_valid = false;
    }

    /// 检查是否有效 / Check if valid
    pub fn is_valid(&self) -> bool {
        self.is_valid
    }
}

/// FFI 工具函数 / FFI Utility Functions
pub mod utils {
    use super::*;

    /// 安全的内存复制 / Safe memory copy
    pub unsafe fn safe_memcpy<T>(dst: *mut T, src: *const T, count: usize) -> Result<(), FFIError> {
        if dst.is_null() || src.is_null() {
            return Err(FFIError::NullPointer);
        }

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, count);
        }
        Ok(())
    }

    /// 安全的内存移动 / Safe memory move
    pub unsafe fn safe_memmove<T>(dst: *mut T, src: *mut T, count: usize) -> Result<(), FFIError> {
        if dst.is_null() || src.is_null() {
            return Err(FFIError::NullPointer);
        }

        unsafe {
            std::ptr::copy(src, dst, count);
        }
        Ok(())
    }

    /// 安全的内存设置 / Safe memory set
    pub unsafe fn safe_memset<T>(dst: *mut T, value: u8, count: usize) -> Result<(), FFIError> {
        if dst.is_null() {
            return Err(FFIError::NullPointer);
        }

        unsafe {
            std::ptr::write_bytes(dst, value, count);
        }
        Ok(())
    }

    /// 检查内存对齐 / Check memory alignment
    pub fn check_alignment<T>(ptr: *const T) -> bool {
        let align = mem::align_of::<T>();
        (ptr as usize) % align == 0
    }

    /// 获取类型大小 / Get type size
    pub fn get_type_size<T>() -> usize {
        mem::size_of::<T>()
    }

    /// 获取类型对齐 / Get type alignment
    pub fn get_type_alignment<T>() -> usize {
        mem::align_of::<T>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i128_ffi_conversion() {
        let original = 123456789012345678901234567890i128;
        let ffi_value = FFIConverter::i128_to_ffi(original);
        let converted = FFIConverter::ffi_to_i128(ffi_value);

        assert_eq!(original, converted);
    }

    #[test]
    fn test_u128_ffi_conversion() {
        let original = 123456789012345678901234567890u128;
        let ffi_value = FFIConverter::u128_to_ffi(original);
        let converted = FFIConverter::ffi_to_u128(ffi_value);

        assert_eq!(original, converted);
    }

    #[test]
    fn test_string_conversion() {
        let rust_string = "Hello, World!";
        let c_string = FFIConverter::string_to_cstring(rust_string).unwrap();
        let converted = FFIConverter::cstring_to_string(c_string.as_ptr()).unwrap();

        assert_eq!(rust_string, converted);
    }

    #[test]
    fn test_ffi_binding_generator() {
        let mut generator = FFIBindingGenerator::new();

        let binding = FFIBinding {
            name: "test_function".to_string(),
            function_type: FFIFunctionType::Function,
            parameters: vec![FFIParameter {
                name: "param1".to_string(),
                param_type: FFIType::I32,
                is_optional: false,
                is_output: false,
            }],
            return_type: FFIType::I32,
            calling_convention: CallingConvention::C,
        };

        generator.add_binding(binding);
        let code = generator.generate_rust_bindings();

        assert!(code.contains("test_function"));
        assert!(code.contains("extern \"C\""));
    }

    #[test]
    fn test_ffi_safe_wrapper() {
        let mut wrapper = FFISafeWrapper::new(42);

        assert!(wrapper.is_valid());
        assert_eq!(*wrapper.get_data().unwrap(), 42);

        wrapper.invalidate();
        assert!(!wrapper.is_valid());
        assert!(wrapper.get_data().is_err());
    }

    #[test]
    fn test_ffi_utils() {
        let size = utils::get_type_size::<i32>();
        assert_eq!(size, 4);

        let align = utils::get_type_alignment::<i32>();
        assert_eq!(align, 4);
    }
}
