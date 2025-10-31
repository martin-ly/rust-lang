//! Rust 1.91 泛型特性演示示例
//!
//! 本示例展示了 Rust 1.91 中泛型系统的新特性和改进：
//!
//! 1. const 上下文增强在泛型中的应用
//! 2. JIT 编译器优化对泛型函数的影响
//! 3. 优化的泛型容器操作
//! 4. 泛型类型推断优化
//! 5. 泛型关联类型 (GAT) 优化
//! 6. 高阶 trait 边界 (HRTB) 优化
//! 7. 单态化 (Monomorphization) 优化

use c04_generic::rust_191_features::{
    self,
    demonstrate_rust_191_generics,
    get_rust_191_generics_info,
};

fn main() {
    println!("=== Rust 1.91 泛型特性演示示例 ===\n");

    // 运行所有演示
    demonstrate_rust_191_generics();

    println!("\n=== 所有演示完成 ===");

    // 显示模块信息
    println!("\n{}", get_rust_191_generics_info());
}

/// 单独演示各个特性的函数
#[allow(dead_code)]
mod individual_demos {
    use super::*;

    pub fn demo_const_generics() {
        println!("=== 1. const 上下文增强在泛型中的应用 ===\n");
        rust_191_features::const_generics::demonstrate();
    }

    pub fn demo_jit_optimizations() {
        println!("=== 2. JIT 编译器优化对泛型函数的影响 ===\n");
        rust_191_features::generic_jit_optimizations::demonstrate();
    }

    pub fn demo_optimized_containers() {
        println!("=== 3. 优化的泛型容器操作 ===\n");
        rust_191_features::optimized_generic_containers::demonstrate();
    }

    pub fn demo_type_inference() {
        println!("=== 4. 泛型类型推断优化 ===\n");
        rust_191_features::generic_type_inference::demonstrate();
    }

    pub fn demo_gat() {
        println!("=== 5. 泛型关联类型 (GAT) 优化 ===\n");
        rust_191_features::generic_associated_types::demonstrate();
    }

    pub fn demo_hrb() {
        println!("=== 6. 高阶 trait 边界 (HRTB) 优化 ===\n");
        rust_191_features::higher_ranked_trait_bounds::demonstrate();
    }

    pub fn demo_monomorphization() {
        println!("=== 7. 单态化 (Monomorphization) 优化 ===\n");
        rust_191_features::monomorphization_optimization::demonstrate();
    }

    pub fn demo_trait_objects() {
        println!("=== 8. 泛型 Trait 对象优化 ===\n");
        rust_191_features::generic_trait_objects::demonstrate();
    }

    pub fn demo_constraints() {
        println!("=== 9. 泛型约束优化 ===\n");
        rust_191_features::generic_constraints::demonstrate();
    }
}

