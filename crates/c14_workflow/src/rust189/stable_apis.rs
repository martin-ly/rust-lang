//! # API 稳定化 / API Stabilization
//!
//! Rust 1.89 在 API 稳定化方面进行了重要改进，包括 `Result::flatten` 等
//! 实用 API 的稳定化。
//!
//! Rust 1.89 has made important improvements in API stabilization, including
//! stabilization of practical APIs like `Result::flatten`.

use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 稳定的结果类型 / Stable Result Type
///
/// 提供稳定的结果处理功能。
/// Provides stable result processing functionality.
pub struct StableResult<T, E> {
    inner: Result<T, E>,
}

impl<T, E> StableResult<T, E> {
    /// 创建新的稳定结果 / Create new stable result
    pub fn new(result: Result<T, E>) -> Self {
        Self { inner: result }
    }

    /// 展平嵌套结果 / Flatten nested result
    pub fn flatten(self) -> Result<T, E>
    where
        T: Into<Result<T, E>>,
    {
        match self.inner {
            Ok(inner_result) => inner_result.into(),
            Err(e) => Err(e),
        }
    }

    /// 映射成功值 / Map success value
    pub fn map<U, F>(self, f: F) -> StableResult<U, E>
    where
        F: FnOnce(T) -> U,
    {
        StableResult::new(self.inner.map(f))
    }

    /// 映射错误值 / Map error value
    pub fn map_err<F, O>(self, f: F) -> StableResult<T, O>
    where
        F: FnOnce(E) -> O,
    {
        StableResult::new(self.inner.map_err(f))
    }

    /// 获取内部结果 / Get inner result
    pub fn into_inner(self) -> Result<T, E> {
        self.inner
    }
}

/// 稳定的集合类型 / Stable Collection Types
pub mod collections {
    use super::*;

    /// 稳定的哈希映射 / Stable HashMap
    pub struct StableHashMap<K, V> {
        inner: HashMap<K, V>,
        version: u64,
    }

    impl<K, V> StableHashMap<K, V>
    where
        K: std::hash::Hash + Eq + Clone,
        V: Clone,
    {
        /// 创建新的稳定哈希映射 / Create new stable hash map
        pub fn new() -> Self {
            Self {
                inner: HashMap::new(),
                version: 0,
            }
        }

        /// 插入键值对 / Insert key-value pair
        pub fn insert(&mut self, key: K, value: V) -> Option<V> {
            let result = self.inner.insert(key, value);
            self.version += 1;
            result
        }

        /// 获取值 / Get value
        pub fn get(&self, key: &K) -> Option<&V> {
            self.inner.get(key)
        }

        /// 移除键值对 / Remove key-value pair
        pub fn remove(&mut self, key: &K) -> Option<V> {
            let result = self.inner.remove(key);
            if result.is_some() {
                self.version += 1;
            }
            result
        }

        /// 获取版本号 / Get version
        pub fn version(&self) -> u64 {
            self.version
        }

        /// 检查是否为空 / Check if empty
        pub fn is_empty(&self) -> bool {
            self.inner.is_empty()
        }

        /// 获取长度 / Get length
        pub fn len(&self) -> usize {
            self.inner.len()
        }

        /// 清空映射 / Clear map
        pub fn clear(&mut self) {
            self.inner.clear();
            self.version += 1;
        }
    }

    impl<K, V> Default for StableHashMap<K, V>
    where
        K: std::hash::Hash + Eq + Clone,
        V: Clone,
    {
        fn default() -> Self {
            Self::new()
        }
    }
}

/// 稳定的异步类型 / Stable Async Types
pub mod async_types {

    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    /// 稳定的异步结果 / Stable Async Result
    pub struct StableAsyncResult<T, E> {
        future: Pin<Box<dyn Future<Output = Result<T, E>> + Send + 'static>>,
    }

    impl<T, E> StableAsyncResult<T, E> {
        /// 创建新的稳定异步结果 / Create new stable async result
        pub fn new<F>(future: F) -> Self
        where
            F: Future<Output = Result<T, E>> + Send + 'static,
        {
            Self {
                future: Box::pin(future),
            }
        }

        /// 等待结果 / Await result
        pub async fn await_result(self) -> Result<T, E> {
            self.future.await
        }
    }

    impl<T, E> Future for StableAsyncResult<T, E> {
        type Output = Result<T, E>;

        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            self.future.as_mut().poll(cx)
        }
    }
}

/// 稳定的时间类型 / Stable Time Types
pub mod time {
    use super::*;

    /// 稳定的时间戳 / Stable Timestamp
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct StableTimestamp {
        seconds: u64,
        nanoseconds: u32,
    }

    impl StableTimestamp {
        /// 创建新的时间戳 / Create new timestamp
        pub fn new(seconds: u64, nanoseconds: u32) -> Self {
            Self {
                seconds,
                nanoseconds,
            }
        }

        /// 获取当前时间戳 / Get current timestamp
        pub fn now() -> Self {
            let now = Instant::now();
            Self {
                seconds: now.elapsed().as_secs(),
                nanoseconds: now.elapsed().subsec_nanos(),
            }
        }

        /// 获取秒数 / Get seconds
        pub fn seconds(&self) -> u64 {
            self.seconds
        }

        /// 获取纳秒数 / Get nanoseconds
        pub fn nanoseconds(&self) -> u32 {
            self.nanoseconds
        }

        /// 转换为持续时间 / Convert to duration
        pub fn to_duration(&self) -> Duration {
            Duration::new(self.seconds, self.nanoseconds)
        }

        /// 从持续时间创建 / Create from duration
        pub fn from_duration(duration: Duration) -> Self {
            Self {
                seconds: duration.as_secs(),
                nanoseconds: duration.subsec_nanos(),
            }
        }
    }

    /// 稳定的时间间隔 / Stable Time Interval
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct StableTimeInterval {
        start: StableTimestamp,
        end: StableTimestamp,
    }

    impl StableTimeInterval {
        /// 创建新的时间间隔 / Create new time interval
        pub fn new(start: StableTimestamp, end: StableTimestamp) -> Self {
            Self { start, end }
        }

        /// 获取开始时间 / Get start time
        pub fn start(&self) -> StableTimestamp {
            self.start
        }

        /// 获取结束时间 / Get end time
        pub fn end(&self) -> StableTimestamp {
            self.end
        }

        /// 获取持续时间 / Get duration
        pub fn duration(&self) -> Duration {
            let start_duration = self.start.to_duration();
            let end_duration = self.end.to_duration();

            if end_duration > start_duration {
                end_duration - start_duration
            } else {
                Duration::ZERO
            }
        }

        /// 检查是否包含时间点 / Check if contains timestamp
        pub fn contains(&self, timestamp: StableTimestamp) -> bool {
            timestamp >= self.start && timestamp <= self.end
        }
    }
}

/// 稳定的错误类型 / Stable Error Types
pub mod error_types {

    use thiserror::Error;

    /// 稳定的错误 / Stable Error
    #[derive(Debug, Error)]
    pub enum StableError {
        #[error("操作失败 / Operation failed: {0}")]
        OperationFailed(String),

        #[error("参数无效 / Invalid parameter: {0}")]
        InvalidParameter(String),

        #[error("资源不可用 / Resource unavailable: {0}")]
        ResourceUnavailable(String),

        #[error("超时 / Timeout: {0}")]
        Timeout(String),

        #[error("内部错误 / Internal error: {0}")]
        InternalError(String),
    }

    /// 稳定的结果类型 / Stable Result Type
    pub type StableResult<T> = Result<T, StableError>;

    /// 错误转换器 / Error Converter
    pub struct ErrorConverter;

    impl ErrorConverter {
        /// 转换为稳定错误 / Convert to stable error
        pub fn to_stable_error<E: std::error::Error>(error: E) -> StableError {
            StableError::InternalError(error.to_string())
        }

        /// 从字符串创建错误 / Create error from string
        pub fn from_string(message: String) -> StableError {
            StableError::OperationFailed(message)
        }
    }
}

/// 稳定的配置类型 / Stable Configuration Types
pub mod config {
    use super::*;
    use serde::{Deserialize, Serialize};

    /// 稳定的配置 / Stable Configuration
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct StableConfig {
        pub version: String,
        pub settings: HashMap<String, serde_json::Value>,
        pub metadata: HashMap<String, String>,
    }

    impl StableConfig {
        /// 创建新的配置 / Create new configuration
        pub fn new(version: String) -> Self {
            Self {
                version,
                settings: HashMap::new(),
                metadata: HashMap::new(),
            }
        }

        /// 设置配置值 / Set configuration value
        pub fn set<T: Serialize>(
            &mut self,
            key: String,
            value: T,
        ) -> Result<(), StableConfigError> {
            let json_value = serde_json::to_value(value)
                .map_err(|e| StableConfigError::SerializationError(e.to_string()))?;
            self.settings.insert(key, json_value);
            Ok(())
        }

        /// 获取配置值 / Get configuration value
        pub fn get<T: for<'de> Deserialize<'de>>(
            &self,
            key: &str,
        ) -> Result<Option<T>, StableConfigError> {
            if let Some(value) = self.settings.get(key) {
                let deserialized = serde_json::from_value(value.clone())
                    .map_err(|e| StableConfigError::DeserializationError(e.to_string()))?;
                Ok(Some(deserialized))
            } else {
                Ok(None)
            }
        }

        /// 设置元数据 / Set metadata
        pub fn set_metadata(&mut self, key: String, value: String) {
            self.metadata.insert(key, value);
        }

        /// 获取元数据 / Get metadata
        pub fn get_metadata(&self, key: &str) -> Option<&String> {
            self.metadata.get(key)
        }
    }

    /// 配置错误 / Configuration Error
    #[derive(Debug, thiserror::Error)]
    pub enum StableConfigError {
        #[error("序列化错误 / Serialization error: {0}")]
        SerializationError(String),

        #[error("反序列化错误 / Deserialization error: {0}")]
        DeserializationError(String),

        #[error("配置未找到 / Configuration not found: {0}")]
        ConfigurationNotFound(String),
    }
}

/// 稳定的工具函数 / Stable Utility Functions
pub mod utils {

    /// 稳定的哈希函数 / Stable hash function
    pub fn stable_hash<T: std::hash::Hash>(value: &T) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    /// 稳定的随机数生成器 / Stable random number generator
    pub struct StableRandom {
        seed: u64,
    }

    impl StableRandom {
        /// 创建新的随机数生成器 / Create new random number generator
        pub fn new(seed: u64) -> Self {
            Self { seed }
        }

        /// 生成随机数 / Generate random number
        pub fn next(&mut self) -> u64 {
            self.seed = self.seed.wrapping_mul(1103515245).wrapping_add(12345);
            self.seed
        }

        /// 生成范围内的随机数 / Generate random number in range
        pub fn next_range(&mut self, min: u64, max: u64) -> u64 {
            min + (self.next() % (max - min + 1))
        }
    }

    /// 稳定的字符串工具 / Stable string utilities
    pub struct StableStringUtils;

    impl StableStringUtils {
        /// 安全地截取字符串 / Safely truncate string
        pub fn safe_truncate(s: &str, max_len: usize) -> String {
            if s.len() <= max_len {
                s.to_string()
            } else {
                format!("{}...", &s[..max_len.saturating_sub(3)])
            }
        }

        /// 安全地连接字符串 / Safely concatenate strings
        pub fn safe_concat(s1: &str, s2: &str) -> String {
            format!("{}{}", s1, s2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stable_result() {
        let result: StableResult<i32, String> = StableResult::new(Ok(42));
        assert_eq!(result.into_inner(), Ok(42));

        let nested_result: Result<Result<i32, String>, String> = Ok(Ok(42));
        let flattened = nested_result.flatten();
        assert_eq!(flattened, Ok(42));
    }

    #[test]
    fn test_stable_hash_map() {
        let mut map = collections::StableHashMap::new();

        map.insert("key1".to_string(), 42);
        map.insert("key2".to_string(), 84);

        assert_eq!(map.get(&"key1".to_string()), Some(&42));
        assert_eq!(map.get(&"key2".to_string()), Some(&84));
        assert_eq!(map.len(), 2);
        assert_eq!(map.version(), 2);

        map.remove(&"key1".to_string());
        assert_eq!(map.len(), 1);
        assert_eq!(map.version(), 3);
    }

    #[test]
    fn test_stable_timestamp() {
        let timestamp = time::StableTimestamp::new(1234567890, 123456789);

        assert_eq!(timestamp.seconds(), 1234567890);
        assert_eq!(timestamp.nanoseconds(), 123456789);

        let duration = timestamp.to_duration();
        assert_eq!(duration.as_secs(), 1234567890);
        assert_eq!(duration.subsec_nanos(), 123456789);
    }

    #[test]
    fn test_stable_time_interval() {
        let start = time::StableTimestamp::new(1000, 0);
        let end = time::StableTimestamp::new(2000, 0);
        let interval = time::StableTimeInterval::new(start, end);

        assert_eq!(interval.duration().as_secs(), 1000);

        let middle = time::StableTimestamp::new(1500, 0);
        assert!(interval.contains(middle));

        let before = time::StableTimestamp::new(500, 0);
        assert!(!interval.contains(before));
    }

    #[test]
    fn test_stable_config() {
        let mut config = config::StableConfig::new("1.0.0".to_string());

        config.set("test_key".to_string(), 42).unwrap();
        let value: Option<i32> = config.get("test_key").unwrap();
        assert_eq!(value, Some(42));

        config.set_metadata("author".to_string(), "Rust Team".to_string());
        assert_eq!(
            config.get_metadata("author"),
            Some(&"Rust Team".to_string())
        );
    }

    #[test]
    fn test_stable_utils() {
        let hash = utils::stable_hash(&"test");
        assert!(hash > 0);

        let mut random = utils::StableRandom::new(12345);
        let num1 = random.next();
        let num2 = random.next();
        assert_ne!(num1, num2);

        let truncated = utils::StableStringUtils::safe_truncate("Hello, World!", 5);
        assert_eq!(truncated, "He...");
    }
}
