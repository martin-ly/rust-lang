//! 训练模块
//! 
//! 提供完整的模型训练管道和任务管理功能

pub mod pipeline;
pub mod job;
pub mod scheduler;
pub mod metrics;
pub mod checkpoint;

pub use pipeline::*;
pub use job::*;
pub use scheduler::*;
pub use metrics::*;
pub use checkpoint::*;
