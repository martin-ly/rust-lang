//! build_script_practice
//!
//! 本 crate 演示 build.rs 的两个典型用法：
//! 1. 将外部构建信息（build-info.json）注入为编译期常量；
//! 2. 编译并链接原生 C 代码（native/math.c）。

// 引入 build.rs 生成的代码。路径由 OUT_DIR 环境变量决定。
include!(concat!(env!("OUT_DIR"), "/build_info.rs"));

// 声明 C 函数。该函数在 build.rs 中通过 cc crate 编译并链接。
// Rust 2024 Edition 要求 extern 块标记为 unsafe。
unsafe extern "C" {
    fn mylib_add(a: i32, b: i32) -> i32;
}

/// 调用原生 C 函数 `mylib_add`。
///
/// # Safety
///
/// `mylib_add` 是由 build.rs 编译的简单纯函数，无全局状态，此处包装为安全接口。
pub fn add_via_c(a: i32, b: i32) -> i32 {
    // SAFETY: mylib_add 是 C 端实现的纯函数，无内存副作用。
    unsafe { mylib_add(a, b) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_constants_are_present() {
        assert_eq!(PROJECT_NAME, "build_script_practice");
        assert_eq!(MAINTAINER, "rust-lang-kb");
        assert!(!LICENSE.is_empty());
    }

    #[test]
    fn c_addition_works() {
        assert_eq!(add_via_c(2, 3), 5);
        assert_eq!(add_via_c(-1, 1), 0);
    }
}
