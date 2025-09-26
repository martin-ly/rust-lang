//! Rust 1.90 性能优化技巧演示
//! 
//! 本示例演示了 Rust 1.90 中的各种性能优化技巧，包括：
//! - 内存布局优化
//! - 零成本抽象
//! - 内联优化
//! - 分支预测优化
//! - SIMD 优化
//! - 编译时优化

use c02_type_system::performance_optimization::*;

fn main() {
    println!("🎯 Rust 1.90 性能优化技巧演示程序");
    println!("=====================================");
    
    // 运行主演示函数
    demonstrate_performance_optimization();
    
    println!("\n🔍 详细性能分析:");
    println!("==================");
    
    // 详细的内存布局分析
    println!("\n📊 内存布局分析:");
    memory_layout::demonstrate_memory_layout_optimization();
    
    // 零成本抽象详细演示
    println!("\n⚡ 零成本抽象详细演示:");
    zero_cost_abstractions::demonstrate_zero_cost_abstractions();
    
    // 内联优化详细演示
    println!("\n🔧 内联优化详细演示:");
    inlining_optimization::demonstrate_inlining_optimization();
    
    // 分支预测优化详细演示
    println!("\n🎯 分支预测优化详细演示:");
    branch_prediction::demonstrate_branch_prediction();
    
    // SIMD 优化详细演示
    println!("\n🚀 SIMD 优化详细演示:");
    simd_optimization::demonstrate_simd_optimization();
    
    // 编译时优化详细演示
    println!("\n⚙️ 编译时优化详细演示:");
    compile_time_optimization::demonstrate_compile_time_optimization();
    
    // 性能分析工具详细演示
    println!("\n📈 性能分析工具详细演示:");
    profiling_tools::demonstrate_profiling_tools();
    
    println!("\n🎉 所有性能优化技巧演示完成！");
    println!("这些技巧可以帮助你编写更高效的 Rust 代码。");
}
