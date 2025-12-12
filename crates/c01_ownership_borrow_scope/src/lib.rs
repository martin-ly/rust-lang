//! # Rust所有权和借用作用域模块 / Rust Ownership and Borrowing Scope Module
//!
//! 本模块提供了完整的Rust所有权系统和借用作用域的理论体系和实现框架。
//! This module provides a complete theoretical system and implementation framework for Rust ownership and borrowing scope.
//!
//! ## 理论基础 / Theoretical Foundation
//!
//! ### 线性类型理论 / Linear Type Theory
//!
//! Rust的所有权系统基于线性类型理论，确保每个值在任意时刻只有一个所有者。
//! Rust's ownership system is based on linear type theory, ensuring that each value has exactly one owner at any given time.
//!
//! ```rust
//! /// 线性类型特征 / Linear Type Trait
//! pub trait LinearType {
//!     /// 移动语义 / Move Semantics
//!     fn move_ownership(self) -> Self;
//!
//!     /// 复制语义 / Copy Semantics
//!     fn copy_value(&self) -> Self
//!     where
//!         Self: Copy;
//!
//!     /// 借用语义 / Borrow Semantics
//!     fn borrow_value(&self) -> &Self;
//!
//!     /// 可变借用 / Mutable Borrow
//!     fn borrow_mut(&mut self) -> &mut Self;
//! }
//! ```
//!
//! ### 生命周期理论 / Lifetime Theory
//!
//! 生命周期系统确保引用的有效性，防止悬垂引用和内存安全问题。
//! The lifetime system ensures reference validity, preventing dangling references and memory safety issues.
//!
//! ```rust
//! /// 生命周期特征 / Lifetime Trait
//! pub trait Lifetime<'a> {
//!     /// 生命周期参数 / Lifetime Parameter
//!     type LifetimeParam;
//!
//!     /// 生命周期约束 / Lifetime Constraint
//!     fn lifetime_constraint(&self, other: &'a Self) -> bool;
//!
//!     /// 生命周期推断 / Lifetime Inference
//!     fn infer_lifetime(&self) -> &'a Self;
//!
//!     /// 生命周期扩展 / Lifetime Extension
//!     fn extend_lifetime<'b>(&'a self) -> &'b Self
//!     where
//!         'a: 'b;
//! }
//! ```
//!
//! ### 借用检查器理论 / Borrow Checker Theory
//!
//! 借用检查器通过静态分析确保内存安全和线程安全。
//! The borrow checker ensures memory safety and thread safety through static analysis.
//!
//! 借用检查器通过静态分析确保内存安全和线程安全。
//! The borrow checker ensures memory safety and thread safety through static analysis.
//!
//! 主要功能包括：
//! Main functions include:
//! - 借用规则检查 / Borrow rule checking
//! - 生命周期验证 / Lifetime validation
//! - 数据竞争检测 / Data race detection
//! - 悬垂引用检测 / Dangling reference detection
//!
//! ## 工程实践 / Engineering Practice
//!
//! ### 所有权模式实现 / Ownership Pattern Implementation
//!
//! 所有权管理器负责跟踪和管理程序中的所有权关系。
//! The ownership manager is responsible for tracking and managing ownership relationships in the program.
//!
//! 主要功能包括：
//! Main functions include:
//! - 所有权转移 / Ownership transfer
//! - 借用管理 / Borrow management
//! - 生命周期跟踪 / Lifetime tracking
//! - 内存安全检查 / Memory safety checking
//!
//! ### 作用域管理机制 / Scope Management Mechanisms
//!
//! 作用域管理器负责管理程序中的变量作用域和生命周期。
//! The scope manager is responsible for managing variable scopes and lifetimes in the program.
//!
//! 主要功能包括：
//! Main functions include:
//! - 作用域栈管理 / Scope stack management
//! - 变量声明和查找 / Variable declaration and lookup
//! - 生命周期跟踪 / Lifetime tracking
//! - 作用域清理 / Scope cleanup
//!
//! ### 内存安全保证 / Memory Safety Guarantees
//!
//! 内存安全检查器负责确保程序的内存安全性。
//! The memory safety checker is responsible for ensuring memory safety in the program.
//!
//! 主要功能包括：
//! Main functions include:
//! - 内存分配跟踪 / Memory allocation tracking
//! - 引用有效性检查 / Reference validity checking
//! - 数据竞争检测 / Data race detection
//! - 所有权规则验证 / Ownership rule validation
//!
//! ## 批判性分析 / Critical Analysis
//!
//! ### 优势分析 / Advantage Analysis
//!
//! #### 技术优势 / Technical Advantages
//!
//! 1. **内存安全保证 / Memory Safety Guarantees**
//!    - 编译时检查防止内存泄漏和悬垂引用
//!    - Compile-time checks prevent memory leaks and dangling references
//!    - 零成本抽象，运行时无性能开销
//!    - Zero-cost abstractions with no runtime performance overhead
//!
//! 2. **线程安全保证 / Thread Safety Guarantees**
//!    - 借用检查器防止数据竞争
//!    - Borrow checker prevents data races
//!    - 所有权系统确保线程间安全的数据共享
//!    - Ownership system ensures safe data sharing between threads
//!
//! 3. **类型安全保证 / Type Safety Guarantees**
//!    - 强类型系统防止类型错误
//!    - Strong type system prevents type errors
//!    - 生命周期系统确保引用有效性
//!    - Lifetime system ensures reference validity
//!
//! #### 性能优势 / Performance Advantages
//!
//! 1. **零成本抽象 / Zero-cost Abstractions**
//!    - 所有权检查在编译时完成
//!    - Ownership checks are completed at compile time
//!    - 运行时无额外开销
//!    - No additional runtime overhead
//!
//! 2. **内存效率 / Memory Efficiency**
//!    - 确定性内存管理
//!    - Deterministic memory management
//!    - 无垃圾回收开销
//!    - No garbage collection overhead
//!
//! ### 局限性讨论 / Limitation Discussion
//!
//! #### 技术限制 / Technical Limitations
//!
//! 1. **学习曲线 / Learning Curve**
//!    - 所有权和借用概念对新手较难理解
//!    - Ownership and borrowing concepts are difficult for beginners to understand
//!    - 生命周期注解增加了复杂性
//!    - Lifetime annotations increase complexity
//!
//! 2. **编译时间 / Compilation Time**
//!    - 借用检查增加了编译时间
//!    - Borrow checking increases compilation time
//!    - 复杂的所有权关系可能导致编译错误
//!    - Complex ownership relationships may cause compilation errors
//!
//! #### 表达能力限制 / Expressiveness Limitations
//!
//! 1. **借用限制 / Borrowing Limitations**
//!    - 同时只能有一个可变借用或多个不可变借用
//!    - Can only have one mutable borrow or multiple immutable borrows at the same time
//!    - 某些模式需要重构代码
//!    - Some patterns require code restructuring
//!
//! 2. **生命周期复杂性 / Lifetime Complexity**
//!    - 复杂的生命周期关系难以理解
//!    - Complex lifetime relationships are difficult to understand
//!    - 某些场景需要显式生命周期注解
//!    - Some scenarios require explicit lifetime annotations
//!
//! ### 改进建议 / Improvement Suggestions
//!
//! #### 短期改进 / Short-term Improvements
//!
//! 1. **开发工具改进 / Development Tool Improvements**
//!    - 提供更好的借用检查错误信息
//!    - Provide better borrow checker error messages
//!    - 所有权可视化工具
//!    - Ownership visualization tools
//!
//! 2. **文档完善 / Documentation Enhancement**
//!    - 提供更多所有权模式示例
//!    - Provide more ownership pattern examples
//!    - 生命周期最佳实践指南
//!    - Lifetime best practices guide
//!
//! #### 中期规划 / Medium-term Planning
//!
//! 1. **编译器优化 / Compiler Optimizations**
//!    - 改进借用检查算法
//!    - Improve borrow checking algorithms
//!    - 减少编译时间
//!    - Reduce compilation time
//!
//! 2. **语言特性扩展 / Language Feature Extensions**
//!    - 更灵活的所有权模式
//!    - More flexible ownership patterns
//!    - 简化的生命周期语法
//!    - Simplified lifetime syntax
//!
//! #### 长期愿景 / Long-term Vision
//!
//! 1. **理论发展 / Theoretical Development**
//!    - 改进线性类型理论
//!    - Improve linear type theory
//!    - 探索新的内存安全模型
//!    - Explore new memory safety models
//!
//! 2. **生态系统扩展 / Ecosystem Expansion**
//!    - 开发更多所有权相关的工具
//!    - Develop more ownership-related tools
//!    - 建立最佳实践标准
//!    - Establish best practice standards
//!
//! ## 生态系统 / Ecosystem
//!
//! ### 工具链支持 / Toolchain Support
//!
//! ```rust
//! /// 所有权分析工具 / Ownership Analysis Tools
//! pub mod tools {
//!     /// 所有权可视化器 / Ownership Visualizer
//!     pub struct OwnershipVisualizer;
//!
//!     /// 借用检查器 / Borrow Checker
//!     pub struct BorrowChecker;
//!
//!     /// 生命周期分析器 / Lifetime Analyzer
//!     pub struct LifetimeAnalyzer;
//! }
//! ```
//!
//! ### 社区实践 / Community Practices
//!
//! 1. **设计模式 / Design Patterns**
//!    - RAII模式（资源获取即初始化）
//!    - RAII pattern (Resource Acquisition Is Initialization)
//!    - 智能指针模式
//!    - Smart pointer patterns
//!    - 借用模式
//!    - Borrowing patterns
//!
//! 2. **最佳实践 / Best Practices**
//!    - 最小化可变性
//!    - Minimize mutability
//!    - 优先使用不可变借用
//!    - Prefer immutable borrows
//!    - 合理使用生命周期
//!    - Use lifetimes appropriately
//!
//! ### 发展趋势 / Development Trends
//!
//! 1. **编译器改进 / Compiler Improvements**
//!    - 更智能的借用检查
//!    - Smarter borrow checking
//!    - 更好的错误信息
//!    - Better error messages
//!
//! 2. **语言特性 / Language Features**
//!    - 更灵活的所有权系统
//!    - More flexible ownership system
//!    - 简化的生命周期语法
//!    - Simplified lifetime syntax
//!
//! ## 使用示例 / Usage Examples
//!
//! ```rust
//! use c01_ownership_borrow_scope::rust_190_features::{ImprovedBorrowChecker, BorrowType};
//! use c01_ownership_borrow_scope::scope::{ScopeManager, ScopeType};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建改进的借用检查器 / Create improved borrow checker
//!     let mut borrow_checker = ImprovedBorrowChecker::new();
//!
//!     // 创建作用域管理器 / Create scope manager
//!     let mut scope_manager = ScopeManager::new();
//!
//!     // 进入作用域 / Enter scope
//!     scope_manager.enter_scope("main".to_string(), ScopeType::Block);
//!
//!     // 创建不可变借用 / Create immutable borrow
//!     let borrow_result = borrow_checker.create_borrow(
//!         "owner".to_string(),
//!         "borrower".to_string(),
//!         BorrowType::Immutable
//!     );
//!
//!     match borrow_result {
//!         Ok(borrow) => println!("借用创建成功 / Borrow created successfully: {:?}", borrow),
//!         Err(e) => println!("借用创建失败 / Borrow creation failed: {:?}", e),
//!     }
//!
//!     // 退出作用域 / Exit scope
//!     scope_manager.exit_scope()?;
//!
//!     println!("所有权和借用系统运行正常 / Ownership and borrowing system running normally");
//!
//!     Ok(())
//! }
//! ```

// 核心类型定义 / Core Type Definitions
pub mod basic_syntax;
pub mod copy_move;
pub mod expression;
pub mod function;
pub mod internal_mut;
pub mod scope;
pub mod variable;
pub mod ownership_utils;
pub mod rust_190_features;
pub mod rust_190_latest_features;
pub mod rust_191_features;
pub mod rust_192_features;

// 重新导出主要类型 / Re-export main types
// 使用具体的导出而不是通配符导出以避免名称冲突 / Use specific exports instead of wildcard exports to avoid name conflicts

// 从 basic_syntax 模块导出 / Export from basic_syntax module
pub use basic_syntax::{
    ownership_basics,
    borrowing_basics,
    lifetime_basics,
    scope_basics,
    smart_pointer_basics,
    error_handling_basics,
    concurrency_basics,
    performance_basics,
    testing_basics,
    module_basics,
    OwnershipError,
    run_all_basic_syntax_examples,
    // 重命名以避免与下面的函数冲突 / Rename to avoid conflict with function below
    get_basic_syntax_info as basic_syntax_info,
};

// 从 copy_move 模块导出 / Export from copy_move module
pub use copy_move::{
    factory,
    strategy,
    r#struct,
};

// 从 internal_mut 模块导出 / Export from internal_mut module
pub use internal_mut::{
    cell,
    refcell,
    threads,
    unsafecell,
};

// 从 scope 模块导出 / Export from scope module
pub use scope::{
    ScopeType,
    Scope,
    ScopeError,
    ScopeManager,
    VariableInfo,
    ScopeAnalyzer,
};

// 从 ownership_utils 模块导出 / Export from ownership_utils module
pub use ownership_utils::{
    OwnershipTracker,
    OwnershipRecord,
    OwnershipStatistics,
    BorrowTracker,
    BorrowRecord,
    BorrowType,
    BorrowStatistics,
    LifetimeTracker,
    LifetimeRecord,
    LifetimeStatistics,
    OwnershipSystemManager,
    SystemStatistics,
    PerformanceAnalyzer,
    PerformanceMetric,
    // 注意：这里重命名了冲突的错误类型 / Note: Renamed conflicting error types here
    OwnershipError as UtilsOwnershipError,
    BorrowError as UtilsBorrowError,
    LifetimeError as UtilsLifetimeError,
    // 实用函数 / Utility functions
    safe_ownership_transfer,
    safe_borrow_check,
    safe_mutable_borrow_check,
    safe_lifetime_check,
};

// 从 rust_190_features 模块导出 / Export from rust_190_features module
pub use rust_190_features::{
    // 改进的借用检查器 / Improved borrow checker
    ImprovedBorrowChecker,
    BorrowRecord as Rust190BorrowRecord,
    BorrowCheckResult,
    BorrowStatistics as Rust190BorrowStatistics,
    // 增强的生命周期推断 / Enhanced lifetime inference
    LifetimeParam,
    LifetimeInferencer,
    InferenceRule,
    // 新的智能指针特性 / New smart pointer features
    SmartPointerType,
    SmartPointerManager,
    // 优化的作用域管理 / Optimized scope management
    ScopeType as Rust190ScopeType,
    ScopeInfo,
    OptimizedScopeManager,
    ScopeOptimizer,
    OptimizationRule,
    ScopeStatistics,
    // 增强的并发安全 / Enhanced concurrency safety
    ConcurrencySafetyChecker,
    ThreadInfo,
    ThreadStatus,
    LockInfo,
    LockType,
    DataRaceDetector,
    AccessRecord,
    AccessType,
    DetectionRule,
    DataRaceReport,
    // 智能内存管理 / Smart memory management
    SmartMemoryManager,
    AllocationRecord,
    AllocationType,
    MemoryUsageStatistics,
    // 主要功能函数 / Main function functions
    run_all_rust_190_features_examples,
    get_rust_190_features_info,
};

// 从 rust_190_latest_features 模块导出 / Export from rust_190_latest_features module
pub use rust_190_latest_features::{
    // 主要功能函数 / Main function functions
    run_all_rust_190_latest_features_examples,
    get_rust_190_latest_features_info,
    run_async_examples,
    // 生成器特征和实现 / Generator traits and implementations
    SyncGenerator,
    AsyncGenerator,
    CustomSyncGenerator,
    CustomAsyncGenerator,
    // 生成器工具函数 / Generator utility functions
    create_number_generator,
    create_filtered_generator,
    create_transformed_generator,
    combine_generators,
    zip_generators,
    // 性能分析 / Performance analysis
    GeneratorMetrics,
    PerformanceAnalyzer as Rust190PerformanceAnalyzer,
    CachedGenerator,
};

// 从 rust_191_features 模块导出 / Export from rust_191_features module
pub use rust_191_features::{
    // 改进的类型检查器（借用检查器优化）/ Improved Type Checker (Borrow Checker Optimizations)
    Rust191BorrowChecker,
    BorrowRecord191,
    BorrowType191,
    BorrowCheckResult191,
    BorrowCheckerStatistics191,
    // 增强的 const 上下文（对生命周期的影响）/ Enhanced Const Context (Impact on Lifetimes)
    LifetimeParam191,
    ConstContextLifetimeInferencer191,
    // 优化的内存分配器（所有权和内存管理改进）/ Optimized Memory Allocator (Ownership and Memory Management Improvements)
    OptimizedMemoryManager191,
    AllocationRecord191,
    AllocationType191,
    MemoryManagerStatistics191,
    // 改进的生命周期推断（编译时优化）/ Improved Lifetime Inference (Compile-time Optimizations)
    OptimizedLifetimeInferencer191,
    LifetimeInferenceStatistics191,
    // 主要功能函数 / Main function functions
    run_all_rust_191_features_examples,
    get_rust_191_features_info,
};

// 从 rust_192_features 模块导出 / Export from rust_192_features module
pub use rust_192_features::{
    // MaybeUninit 安全使用 / Safe MaybeUninit Usage
    SafeMaybeUninit,
    // 联合体原始引用 / Union Raw References
    Rust192Union,
    // 自动特征和 Sized 边界 / Auto-Trait and Sized Bounds
    Rust192Trait,
    // 零大小数组 / Zero-Sized Arrays
    Rust192ZeroSizedArray,
    // 多边界关联项 / Multiple Bounds for Associated Items
    Rust192MultipleBounds,
    // 主要功能函数 / Main function functions
    run_all_rust_192_features_examples,
    get_rust_192_features_info,
    // 实用函数 / Utility functions
    rust_192_tracked_function,
    rust_192_never_type_example,
    rust_192_higher_ranked_lifetime,
    rust_192_must_use_result,
    rust_192_nonzero_div_ceil_example,
    rust_192_location_file_as_c_str_example,
    rust_192_rotate_right_example,
    rust_192_iterator_eq_example,
    rust_192_tuple_extend_example,
    rust_192_encode_wide_example,
    rust_192_repeat_example,
};

/// 所有权系统版本 / Ownership System Version
pub const VERSION: &str = "1.0.0";

/// 模块初始化 / Module Initialization
pub fn init() -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "Rust所有权和借用作用域模块已初始化 / Rust Ownership and Borrowing Scope Module Initialized"
    );
    Ok(())
}

/// 获取模块信息 / Get Module Information
pub fn get_module_info() -> &'static str {
    "Rust Ownership and Borrowing Scope Module v1.0.0"
}

/// 运行测试套件 / Run Test Suite
#[cfg(test)]
pub fn run_tests() -> Result<(), Box<dyn std::error::Error>> {
    println!("运行所有权和借用作用域测试套件 / Running Ownership and Borrowing Scope Test Suite");

    // 这里可以添加测试运行逻辑
    // Add test running logic here

    Ok(())
}

/// 运行基础语法示例 / Run Basic Syntax Examples
pub fn run_basic_syntax_examples() {
    basic_syntax::run_all_basic_syntax_examples();
}

/// 获取基础语法信息 / Get Basic Syntax Information
pub fn get_basic_syntax_info() -> &'static str {
    basic_syntax::get_basic_syntax_info()
}
