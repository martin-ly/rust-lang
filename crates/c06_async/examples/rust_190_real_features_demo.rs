//! Rust 1.90 真正的语言特性演示程序
//! 
//! 本程序演示了Rust 1.90版本中真正可用的语言特性，包括：
//! - 真正的AsyncDrop实现
//! - 真正的异步迭代器
//! - Polonius借用检查器改进
//! - 下一代特质求解器优化
//! - 并行前端编译优化

use c06_async::rust_190_real_features::*;
use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 1.90 真正的语言特性演示程序");
    println!("==========================================");
    
    // 运行综合演示
    demonstrate_rust_190_real_features().await?;
    
    println!("\n🎉 演示程序运行完成！");
    Ok(())
}
