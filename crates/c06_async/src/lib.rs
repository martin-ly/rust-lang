//! 模块→示例→解释 索引（精选）
//!
//! - actix：`examples/actix_basic.rs` → 最小 Actor 消息交互；`src/actix/actor01.rs`
//! - utils：`examples/utils_strategy_smoke.rs` → `ExecStrategyBuilder` 组合策略最小用法；`src/utils/mod.rs`
//! - 混合模式：`examples/actor_csp_hybrid_minimal.rs`（最小） / `examples/actor_csp_hybrid_advanced.rs`（进阶，含监督/限速/指标）
//! - API 网关：`examples/async_api_gateway_2025.rs` → 统一观测与指标输出
//!
//! 提示：更多示例请查看 `examples/` 目录及各模块顶部文档注释。

pub mod actix;
pub mod async_runtime;
pub mod async_std;
pub mod r#await;
pub mod futures;
pub mod streams;
pub mod tokio;
pub mod utils;

// 高级异步工具库
pub mod advanced_tools;

// Rust 异步特性模块
pub mod rust_190_features;
pub mod rust_190_real_features;  // 真正的异步特性实现
pub mod rust_190_real_stable_features;  // 真实稳定特性
pub mod rust_190_advanced_features;  // 高级异步特性
pub mod improved_async_features;  // 改进的异步特性实现
pub mod async_control_flow_190;
pub mod performance_optimization_190;

// 异步生态系统全面分析模块
pub mod async_ecosystem_comprehensive;
pub mod async_runtime_examples;
pub mod async_integration_framework;
pub mod async_runtime_integration_framework_simple;
pub mod async_logging_debugging;

// 高级异步调试和生态系统集成模块
pub mod async_debugging_advanced;
pub mod async_ecosystem_integration;