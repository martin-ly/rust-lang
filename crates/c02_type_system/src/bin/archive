//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 类型系统演示程序
//!
//! 文件: rust_189_demo.rs  
//! 创建日期: 2025-01-27  
//! 版本: 1.0

use c02_type_system::performance::*;
use c02_type_system::rust_189_enhancements::rust_189_type_composition::*;

fn main() {
    println!("🚀 Rust 1.89 类型系统演示程序\n");

    // 1. 常量泛型演示
    println!("1. 常量泛型演示:");
    let arr = ConstGenericArray::new([1, 2, 3, 4, 5]);
    println!("   数组长度: {}", arr.len());
    println!("   是否为空: {}", arr.is_empty());
    println!("   第一个元素: {:?}", arr.data.first());

    // 2. 生命周期组合演示
    println!("\n2. 生命周期组合演示:");
    let data = String::from("Hello, Rust 1.89!");
    let metadata = "演示数据";
    let composed = LifetimeComposed::new(&data, metadata);
    println!("   数据: {}", composed.get_data());
    println!("   元数据: {}", composed.get_metadata());

    // 3. 智能指针组合演示
    println!("\n3. 智能指针组合演示:");
    let value = 42;
    let mut composition = SmartPointerComposition::new(value);
    println!("   初始值: {}", *composition.get());
    *composition.get_mut() = 100;
    println!("   修改后值: {}", *composition.get());

    // 4. 类型处理器演示
    println!("\n4. 类型处理器演示:");
    let processor = create_number_processor();
    println!("   处理器值: {}", processor);

    // 5. 性能测试演示
    println!("\n5. 性能测试演示:");
    let analysis = run_all_benchmarks();
    println!("   性能分析结果:");
    println!("   {}", analysis.summary);

    println!("\n✅ Rust 1.89 类型系统演示完成！");
}
