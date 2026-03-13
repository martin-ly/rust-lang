//! # 算法库核心模块
//!
//! 本模块按照主题分类组织算法，每个主题包含同步、异步、多线程、分布式四个版本。
//! 充分利用 Rust 1.90 的新特性，提供高性能、类型安全的算法实现。
//!
//! ## 核心特性
//!
//! - **形式化验证**: 包含循环不变量、霍尔逻辑、正确性证明
//! - **复杂度分析**: 主定理、摊还分析、渐进分析
//! - **多种实现**: 同步、并行、异步、分布式
//! - **Rust 1.90**: GATs、Async Traits、常量泛型
pub mod backtracking;
pub mod combinatorics;
pub mod divide_and_conquer;
pub mod dynamic_programming;
pub mod geometry;
pub mod graph;
pub mod greedy;
pub mod machine_learning;
pub mod number_theory;
pub mod optimization;
pub mod searching;
pub mod sorting;
pub mod string_algorithms;

// 形式化验证与证明示例
pub mod formal_verification_examples;

// Rust 2025 新特性应用
pub mod rust_2025_features;
// Rust 2024 成熟特性示例
pub mod rust_2024_features;

// 算法执行模式
pub mod execution_modes;

// 算法验证和证明
pub mod verification {
    pub mod complexity_analysis;
    pub mod correctness;
    pub mod formal_proofs;
}

// 算法性能分析
pub mod performance {
    pub mod benchmarking;
    pub mod optimization;
    pub mod profiling;
}

// 算法知识体系
pub mod knowledge_base {
    pub mod applications;
    pub mod best_practices;
    pub mod theory;
}

// 重新导出常用类型和特征
pub use execution_modes::*;
pub use knowledge_base::*;
pub use performance::*;
pub use verification::*;
