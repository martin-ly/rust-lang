#!/usr/bin/env cargo
---
[package]
name = "module_system_patterns"
version = "0.1.0"
edition = "2024"
---
//! # 模块系统代码实践模式示例
//!
//! 对应文档: [docs/research_notes/formal_modules/70_module_patterns_and_refactoring.md](../docs/research_notes/formal_modules/70_module_patterns_and_refactoring.md)
//!
//! 运行方式:
//! ```bash
//! cargo +nightly -Zscript examples/module_system_patterns.rs
//! # 或安装 rust-script 后: rust-script examples/module_system_patterns.rs
//! ```

fn main() {
    println!("=== 模块系统代码实践模式 ===\n");

    facade_demo::run();
    sealed_trait_demo::run();
    unsafe_encapsulation_demo::run();
}

// ============================================================================
// 模式 1：门面 + 按职责分层
// ============================================================================
mod facade_demo {
    // 内部模块不公开，但同一 crate 内可用
    mod lexer {
        pub fn tokenize(input: &str) -> Vec<String> {
            input.split_whitespace().map(String::from).collect()
        }
    }

    mod parser {
        pub fn parse(tokens: &[String]) -> Vec<String> {
            tokens.to_vec()
        }
    }

    // 公开 API：用户只需调用 parse_expr
    pub fn parse_expr(input: &str) -> Vec<String> {
        let tokens = lexer::tokenize(input);
        parser::parse(&tokens)
    }

    pub fn run() {
        println!("[门面模式] 解析输入: {:?}", parse_expr("1 + 2 * 3"));
    }
}

// ============================================================================
// 模式 2：pub use 重导出 + sealed trait
// ============================================================================
mod sealed_trait_demo {
    // 私有模块，外部无法访问
    mod private {
        pub trait Sealed {}
    }

    /// 公开 trait，但下游 crate 不能实现它，因为缺少私有 supertrait。
    pub trait StableGreet: private::Sealed {
        fn greet(&self) -> &'static str;
    }

    /// 稳定门面类型
    pub struct Greeter;

    impl private::Sealed for Greeter {}
    impl StableGreet for Greeter {
        fn greet(&self) -> &'static str {
            "Hello from sealed trait!"
        }
    }

    pub fn run() {
        let g = Greeter;
        println!("[Sealed trait] {}", g.greet());
    }
}

// ============================================================================
// 模式 3：内部模块封装 unsafe
// ============================================================================
mod unsafe_encapsulation_demo {
    // 私有模块，存放裸指针操作
    mod raw {
        /// 内部 unsafe 辅助函数：反转字节缓冲区。
        /// 安全前提：ptr 指向 len 个有效可读写字节。
        pub(crate) unsafe fn reverse_bytes(ptr: *mut u8, len: usize) {
            let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
            slice.reverse();
        }
    }

    /// 安全公开 API。
    pub fn reverse_buffer(buf: &mut [u8]) {
        unsafe { raw::reverse_bytes(buf.as_mut_ptr(), buf.len()) };
    }

    pub fn run() {
        let mut data = *b"Rust";
        reverse_buffer(&mut data);
        println!("[unsafe 封装] 反转后: {}", String::from_utf8_lossy(&data));
    }
}
