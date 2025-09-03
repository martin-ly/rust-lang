// Rust 1.89 类型系统演示程序
// 文件: rust_189_demo.rs
// 创建日期: 2025-01-27
// 版本: 1.0

use c02_type_system::rust_189_enhancements::rust_189_type_composition::*;
use c02_type_system::performance::*;

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
