//! # 算法库核心模块
//! 
//! 本模块按照主题分类组织算法，每个主题包含同步、异步、多线程、分布式四个版本。
//! 充分利用 Rust 1.90 的新特性，提供高性能、类型安全的算法实现。

pub mod sorting;
pub mod searching;
pub mod graph;
pub mod dynamic_programming;
pub mod divide_and_conquer;
pub mod greedy;
pub mod backtracking;
pub mod string_algorithms;
pub mod number_theory;
pub mod geometry;
pub mod machine_learning;
pub mod optimization;
pub mod combinatorics;

// Rust 2025 新特性应用
pub mod rust_2025_features;

// 算法执行模式
pub mod execution_modes;

// 算法验证和证明
pub mod verification {
    pub mod formal_proofs;
    pub mod correctness;
    pub mod complexity_analysis;
}

// 算法性能分析
pub mod performance {
    pub mod benchmarking;
    pub mod profiling;
    pub mod optimization;
}

// 算法知识体系
pub mod knowledge_base {
    pub mod theory;
    pub mod applications;
    pub mod best_practices;
}

// 重新导出常用类型和特征
pub use execution_modes::*;
pub use verification::*;
pub use performance::*;
pub use knowledge_base::*;
