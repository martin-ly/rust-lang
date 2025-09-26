//! Rust 1.90 真正的泛型特性演示程序
//! 
//! 本程序演示了Rust 1.90版本中真正可用的泛型特性，包括：
//! - 改进的const generics
//! - 更好的trait bounds
//! - 优化的类型推断
//! - 新的泛型约束
//! - 改进的关联类型

use c04_generic::rust_190_real_generics::*;
use anyhow::Result;

fn main() -> Result<()> {
    println!("🚀 Rust 1.90 真正的泛型特性演示程序");
    println!("==========================================");
    
    // 运行综合演示
    demonstrate_rust_190_real_generics()?;
    
    println!("\n🎉 演示程序运行完成！");
    Ok(())
}
