//! C 语言互操作 (FFI)
//!
//! Rust 可以无缝调用 C 代码，也可以被 C 代码调用。
//! 这在嵌入式中非常重要，因为大量驱动库和硬件抽象层是用 C 编写的。
//!
//! ## 核心概念
//!
//! - extern "C"：指定 C 调用约定
//! - #[repr(C)]：确保 Rust 结构体与 C 布局兼容
//! - unsafe：FFI 边界必须标记为 unsafe，因为编译器无法验证 C 代码的安全性

/// 与 C 兼容的结构体
///
/// #[repr(C)] 确保字段顺序与 C 编译器一致（而非 Rust 的默认重排）。
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SensorData {
    /// 温度值（摄氏度，浮点）
    pub temperature: f32,
    /// 湿度值（百分比）
    pub humidity: f32,
    /// 传感器状态码
    pub status: u32,
    /// 预留字段（C 中常见）
    pub reserved: u32,
}

/// 与 C 兼容的枚举
///
/// 注意：#[repr(C)] 枚举需要有显式整型表示。
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SensorStatus {
    /// 离线
    Offline = 0,
    /// 初始化中
    Initializing = 1,
    /// 运行中
    Running = 2,
    /// 错误
    Error = 3,
}

/// 从 Rust 导出给 C 的函数
///
/// no_mangle 防止 Rust 编译器对函数名进行混淆，确保 C 代码能通过符号名找到它。
///
/// ```c
/// // C 代码调用示例
/// extern void rust_initialize_sensor(uint32_t id);
/// ```
#[unsafe(no_mangle)]
pub extern "C" fn rust_initialize_sensor(id: u32) -> i32 {
    if id > 100 {
        -1 // 错误
    } else {
        0 // 成功
    }
}

/// 接受 C 风格字符串的函数
///
/// C 字符串是以 null 结尾的字节数组。Rust 中需要谨慎处理空指针和 UTF-8 验证。
///
/// # Safety
///
/// c_str 必须是有效的、以 null 结尾的 C 字符串指针。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_process_name(c_str: *const u8) -> i32 {
    if c_str.is_null() {
        return -1;
    }

    let mut len = 0usize;
    while unsafe { *c_str.add(len) } != 0 {
        len += 1;
    }

    let slice = unsafe { core::slice::from_raw_parts(c_str, len) };
    let _name = slice;
    0
}

/// C 回调函数类型
///
/// 在嵌入式中，经常需要注册 C 回调（如中断回调）。
pub type CCallback = extern "C" fn(data: *mut core::ffi::c_void);

/// 模拟 C 库提供的初始化函数声明
///
/// 在真实项目中，这些声明通常在 build.rs 中使用 bindgen 自动生成。
///
/// ```rust,ignore
/// extern "C" {
///     fn hal_init() -> i32;
///     fn hal_read_register(addr: u32) -> u32;
///     fn hal_write_register(addr: u32, value: u32);
/// }
/// ```
pub struct CBindingsConcept;

impl CBindingsConcept {
    /// 描述 bindgen 工作流程
    pub fn bindgen_workflow() -> &'static str {
        "1. 准备 C 头文件 -> 2. 运行 bindgen 生成 .rs -> 3. 在 build.rs 中链接 C 库 -> 4. 调用 FFI 函数"
    }
}

/// build.rs 示例概念
///
/// ```rust,ignore
/// use std::env;
/// use std::path::PathBuf;
///
/// fn main() {
///     println!("cargo:rerun-if-changed=wrapper.h");
///
///     let bindings = bindgen::Builder::default()
///         .header("wrapper.h")
///         .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
///         .generate()
///         .expect("无法生成绑定");
///
///     let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
///     bindings
///         .write_to_file(out_path.join("bindings.rs"))
///         .expect("无法写入绑定文件");
/// }
/// ```
pub struct BuildRsExample;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sensor_data_layout() {
        assert_eq!(core::mem::size_of::<SensorData>(), 16);
    }

    #[test]
    fn test_rust_initialize_sensor() {
        assert_eq!(rust_initialize_sensor(50), 0);
        assert_eq!(rust_initialize_sensor(101), -1);
    }

    #[test]
    fn test_sensor_status_values() {
        assert_eq!(SensorStatus::Offline as u32, 0);
        assert_eq!(SensorStatus::Running as u32, 2);
    }

    #[test]
    fn test_bindgen_workflow() {
        assert!(!CBindingsConcept::bindgen_workflow().is_empty());
    }
}
