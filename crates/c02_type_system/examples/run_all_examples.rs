//! 运行所有类型系统示例

use c02_type_system::examples::{
    generics_examples,
    lifetimes_examples,
    traits_examples,
    type_definition_examples,
};

fn main() {
    println!("Rust 类型系统示例集合");
    println!("========================");
    
    // 运行泛型示例
    generics_examples::run_all_examples();
    
    println!("\n{}\n", "=".repeat(50));
    
    // 运行生命周期示例
    lifetimes_examples::run_all_examples();
    
    println!("\n{}\n", "=".repeat(50));
    
    // 运行特征示例
    traits_examples::run_all_examples();
    
    println!("\n{}\n", "=".repeat(50));
    
    // 运行类型定义示例
    type_definition_examples::run_all_examples();
    
    println!("\n所有示例运行完成！");
}
