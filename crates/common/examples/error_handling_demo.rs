//! Common crate 错误处理示例
//!
//! 运行: cargo run -p common --example error_handling_demo

use common::{CommonError, Result, RustLangError};

fn may_fail() -> Result<i32> {
    Ok(42)
}

fn may_fail_with_error() -> Result<i32, CommonError> {
    Err(CommonError::NotFound("answer".to_string()))
}

fn main() {
    match may_fail() {
        Ok(v) => println!("成功: {}", v),
        Err(e) => println!("错误: {} (code: {:?})", e, e.error_code()),
    }

    match may_fail_with_error() {
        Ok(v) => println!("成功: {}", v),
        Err(e) => println!("错误: {} (code: {:?})", e, e.error_code()),
    }
}
