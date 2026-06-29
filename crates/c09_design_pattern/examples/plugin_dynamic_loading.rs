//! 插件架构：动态加载（libloading）示例
//!
//! 本示例展示如何使用 `libloading` 在运行时加载动态库插件。
//! 运行前需要先构建一个 `cdylib` 插件库，并确保路径 `target/debug/libdemo_plugin.so`
//!（Linux）、`target/debug/libdemo_plugin.dylib`（macOS）或 `target/debug/demo_plugin.dll`
//!（Windows）存在。
//!
//! 本示例为演示 `libloading` API 的使用方式，默认在找不到插件库时打印提示信息并安全退出。

use std::ffi::{CStr, CString, c_char};
use std::path::Path;

use libloading::{Library, Symbol};

/// 插件 C ABI 描述表。
///
/// 所有跨动态库传递的结构体必须使用 `#[repr(C)]`，并仅包含 C 兼容类型
///（指针、函数指针、基本数值类型等），以避免 Rust ABI 不稳定导致的未定义行为。
#[repr(C)]
pub struct RawPlugin {
    pub name: extern "C" fn() -> *const c_char,
    pub execute: extern "C" fn(*const c_char) -> *mut c_char,
    pub free_string: extern "C" fn(*mut c_char),
}

/// 动态库入口符号名，包含末尾 NUL 字节以适配 `libloading::Library::get`。
pub const PLUGIN_ENTRY_NAME: &[u8] = b"plugin_entry\0";

fn platform_plugin_path() -> &'static str {
    #[cfg(target_os = "linux")]
    {
        "target/debug/libdemo_plugin.so"
    }
    #[cfg(target_os = "macos")]
    {
        "target/debug/libdemo_plugin.dylib"
    }
    #[cfg(target_os = "windows")]
    {
        "target/debug/demo_plugin.dll"
    }
}

fn load_and_run(plugin_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    if !Path::new(plugin_path).exists() {
        return Err(format!("plugin library not found at {}", plugin_path).into());
    }

    unsafe {
        // `Library::new` 打开动态库，返回的句柄必须保持存活，直到所有从库中获取的
        // 指针/符号都不再使用。
        let lib = Library::new(plugin_path)?;

        // 获取入口符号。注意：符号类型必须与实际动态库导出完全一致。
        let entry: Symbol<extern "C" fn() -> *const RawPlugin> = lib.get(PLUGIN_ENTRY_NAME)?;

        let raw = &*entry();

        // 读取插件名称。
        let name = CStr::from_ptr((raw.name)())
            .to_str()
            .map_err(|e| format!("plugin name is not valid UTF-8: {}", e))?;

        // 构造 C 字符串输入并调用插件。
        let input = CString::new("dynamic world")?;
        let out_ptr = (raw.execute)(input.as_ptr());
        if out_ptr.is_null() {
            return Err("plugin returned null pointer".into());
        }
        let out = CStr::from_ptr(out_ptr)
            .to_str()
            .map_err(|e| format!("plugin output is not valid UTF-8: {}", e))?
            .to_string();

        // 使用插件提供的释放函数归还内存，避免跨动态库边界使用错误分配器。
        (raw.free_string)(out_ptr);

        println!("plugin '{}' output: {}", name, out);
    }

    Ok(())
}

fn main() {
    let path = platform_plugin_path();
    match load_and_run(path) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("dynamic plugin demo skipped: {}", e);
            eprintln!(
                "hint: build a cdylib plugin named 'demo_plugin' and place it at {}",
                path
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_plugin_has_c_repr() {
        // 确保跨动态库结构体使用 C 表示法。
        assert_eq!(
            std::mem::align_of::<RawPlugin>(),
            std::mem::align_of::<*const c_char>()
        );
    }

    #[test]
    fn entry_name_is_nul_terminated() {
        assert!(PLUGIN_ENTRY_NAME.last() == Some(&0u8));
    }
}
