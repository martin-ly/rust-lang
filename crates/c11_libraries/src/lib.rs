pub mod prelude {
    pub use crate::database::sql::{SqlDatabase, SqlRow};
    pub use crate::enhanced_config::{
        EnhancedRedisConfig, EnhancedPostgresConfig, EnhancedNatsConfig,
        ConfigFactory, ConfigComposer, ConfigValidator
    };
    pub use crate::rust190_optimizations::{
        OptimizedConnectionPool, OptimizedMiddleware, MiddlewareType, MiddlewareConfig,
        OptimizedErrorHandler, OptimizedBuffer, PerformanceMonitor
    };
    pub use crate::benchmarks::{
        BenchmarkResult, OptimizedBenchmarker, MemoryMonitor, MemoryStats,
        ConcurrencyBenchmarker, BenchmarkSuite
    };
    pub use crate::advanced_benchmarks::{
        AdvancedBenchmarker, AdvancedBenchmarkResult, AdvancedMemoryMonitor
    };
    pub use crate::glommio_runtime::{
        RuntimeFactory, RuntimeType, RuntimeBenchmarker, 
        RuntimeComparison, RuntimeBox
    };
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    pub use crate::glommio_runtime::GlommioRuntime;
    #[cfg(feature = "tokio")]
    pub use crate::glommio_runtime::TokioRuntime;
    pub use crate::kv::KeyValueStore;
    pub use crate::mq::mq::{MessageConsumer, MessageProducer};
}

pub mod config;
pub mod enhanced_config;
pub mod rust190_optimizations;
pub mod benchmarks;
pub mod advanced_benchmarks;
pub mod glommio_runtime;
pub mod kv;
pub mod util;

mod error;
pub use error::{Error, Result};

// 数据库模块
pub mod database {
    pub mod sql;

    #[cfg(feature = "sql-postgres")]
    pub mod postgres_client;

    #[cfg(feature = "sql-mysql")]
    pub mod mysql_client;

    #[cfg(feature = "sql-sqlite")]
    pub mod sqlite_client;
}

// 缓存模块
pub mod cache {
    #[cfg(feature = "kv-redis")]
    pub mod redis_client;
}

// 消息队列模块
pub mod mq {
    pub mod mq;

    #[cfg(feature = "mq-nats")]
    pub mod nats_client;

    #[cfg(feature = "mq-kafka")]
    pub mod kafka_client;

    #[cfg(feature = "mq-mqtt")]
    pub mod mqtt_client;
}

// HTTP 代理模块
pub mod http {
    #[cfg(feature = "proxy-nix")]
    pub mod pingora_proxy;
}
