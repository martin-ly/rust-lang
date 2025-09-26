//! Rust 1.90 真正的语言特性实现演示程序
//! 
//! 本程序演示了Rust 1.90版本中真正可用的语言特性实现，包括：
//! - 改进的const generics
//! - 更好的生命周期推断
//! - 优化的trait求解器
//! - 改进的错误处理
//! - 新的标准库特性

use c03_control_fn::rust_190_real_implementation::*;
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 1.90 真正的语言特性实现演示程序");
    println!("==========================================");
    
    // 运行综合演示
    demonstrate_rust_190_real_implementation().await?;
    
    println!("\n🎉 演示程序运行完成！");
    Ok(())
}
