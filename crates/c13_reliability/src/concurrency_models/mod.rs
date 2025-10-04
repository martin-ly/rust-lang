// Concurrency Models Module
//
// Provides high-level concurrency abstractions:
// - Actor Model: Message-passing concurrency inspired by Erlang/Akka
// - CSP Model: Communicating Sequential Processes inspired by Go
// - STM: Software Transactional Memory ✅
// - Fork-Join: Parallel divide-and-conquer ✅

pub mod actor;
pub mod csp;
pub mod stm;
pub mod fork_join;

// Re-export commonly used types
pub use actor::{
    Actor, ActorContext, ActorId, ActorMessage, ActorRef, ActorSystem, ActorSystemConfig,
    SupervisorDirective,
};

pub use csp::{
    Barrier, Channel, Pipeline, Process, Select, SelectResult, UnboundedReceiver, UnboundedSender,
    fan_in, fan_out,
};

pub use stm::{
    TVar, Transaction, STMRuntime, STMStats, atomically, atomic,
};

pub use fork_join::{
    ForkJoinPool, ForkJoinTask, ForkJoinPoolConfig, PoolStats,
    RecursiveSumTask, ParallelMapTask,
};

/// Concurrency pattern trait
pub trait ConcurrencyPattern: Send + Sync {
    /// Name of the pattern
    fn name(&self) -> &str;

    /// Description of when to use this pattern
    fn use_case(&self) -> &str;
}

/// Concurrency model configuration
#[derive(Debug, Clone)]
pub struct ConcurrencyConfig {
    /// Maximum number of concurrent tasks
    pub max_concurrency: usize,
    /// Default timeout for operations
    pub default_timeout_ms: u64,
    /// Enable detailed logging
    pub enable_logging: bool,
}

impl Default for ConcurrencyConfig {
    fn default() -> Self {
        Self {
            max_concurrency: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4),
            default_timeout_ms: 5000,
            enable_logging: false,
        }
    }
}

/// Utility functions for concurrency
pub mod utils {
    use std::future::Future;
    use tokio::time::{timeout, Duration};

    /// Run a future with timeout
    pub async fn with_timeout<F, T>(
        fut: F,
        duration: Duration,
    ) -> Result<T, tokio::time::error::Elapsed>
    where
        F: Future<Output = T>,
    {
        timeout(duration, fut).await
    }

    /// Get number of available CPU cores
    pub fn num_cores() -> usize {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    }

    /// Get number of physical CPU cores (same as num_cores in std)
    pub fn num_physical_cores() -> usize {
        num_cores()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concurrency_config() {
        let config = ConcurrencyConfig::default();
        assert!(config.max_concurrency > 0);
        assert_eq!(config.default_timeout_ms, 5000);
    }

    #[test]
    fn test_utils() {
        assert!(utils::num_cores() > 0);
        assert!(utils::num_physical_cores() > 0);
    }
}

