//! # OTLP工具模块
//! 
//! 提供OTLP相关的工具函数和实用程序，支持Rust 1.90的特性。

use std::time::{SystemTime, UNIX_EPOCH, Duration};
use crate::error::Result;

/// 压缩工具
pub struct CompressionUtils;

impl CompressionUtils {
    /// 创建新的压缩工具实例
    pub fn new() -> Self {
        Self
    }

    /// Gzip压缩
    pub async fn gzip_compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            use flate2::write::GzEncoder;
            use flate2::Compression;
            use std::io::Write;
            
            let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
            encoder.write_all(&data)
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Gzip compression failed: {}", e)))?;
            encoder.finish()
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Gzip compression finish failed: {}", e)))
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Gzip compression task failed: {}", e)))?
    }

    /// Gzip解压缩
    pub async fn gzip_decompress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            use flate2::read::GzDecoder;
            use std::io::Read;
            
            let mut decoder = GzDecoder::new(data.as_slice());
            let mut result = Vec::new();
            decoder.read_to_end(&mut result)
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Gzip decompression failed: {}", e)))?;
            Ok(result)
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Gzip decompression task failed: {}", e)))?
    }

    /// Brotli压缩
    pub async fn brotli_compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            use brotli::enc::BrotliEncoderParams;
            //use std::io::Write;
            
            let mut params = BrotliEncoderParams::default();
            params.quality = 6;
            
            let mut result = Vec::new();
            let mut data_mut = std::io::Cursor::new(data);
            brotli::BrotliCompress(&mut data_mut, &mut result, &params)
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Brotli compression failed: {}", e)))?;
            Ok(result)
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Brotli compression task failed: {}", e)))?
    }

    /// Brotli解压缩
    pub async fn brotli_decompress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            //use std::io::Read;
            
            let mut result = Vec::new();
            let mut data_mut = std::io::Cursor::new(data);
            brotli::BrotliDecompress(&mut data_mut, &mut result)
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Brotli decompression failed: {}", e)))?;
            Ok(result)
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Brotli decompression task failed: {}", e)))?
    }

    /// Zstd压缩
    pub async fn zstd_compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            use zstd::encode_all;
            
            encode_all(data.as_slice(), 3)
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Zstd compression failed: {}", e)))
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Zstd compression task failed: {}", e)))?
    }

    /// Zstd解压缩
    pub async fn zstd_decompress(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        tokio::task::spawn_blocking(move || {
            use zstd::decode_all;
            
            decode_all(data.as_slice())
                .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Zstd decompression failed: {}", e)))
        }).await
        .map_err(|e| crate::error::OtlpError::Internal(anyhow::anyhow!("Zstd decompression task failed: {}", e)))?
    }
}

/// 时间工具
pub struct TimeUtils;

impl TimeUtils {
    /// 获取当前时间戳（纳秒）
    pub fn current_timestamp_nanos() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64
    }

    /// 获取当前时间戳（微秒）
    pub fn current_timestamp_micros() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_micros() as u64
    }

    /// 获取当前时间戳（毫秒）
    pub fn current_timestamp_millis() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64
    }

    /// 获取当前时间戳（秒）
    pub fn current_timestamp_secs() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs()
    }

    /// 纳秒转毫秒
    pub fn nanos_to_millis(nanos: u64) -> u64 {
        nanos / 1_000_000
    }

    /// 毫秒转纳秒
    pub fn millis_to_nanos(millis: u64) -> u64 {
        millis * 1_000_000
    }

    /// 计算持续时间（纳秒）
    pub fn duration_nanos(start: u64, end: u64) -> u64 {
        if end >= start {
            end - start
        } else {
            0
        }
    }

    /// 格式化持续时间
    pub fn format_duration(duration: Duration) -> String {
        let total_nanos = duration.as_nanos();
        
        if total_nanos < 1_000 {
            format!("{}ns", total_nanos)
        } else if total_nanos < 1_000_000 {
            format!("{:.2}μs", total_nanos as f64 / 1_000.0)
        } else if total_nanos < 1_000_000_000 {
            format!("{:.2}ms", total_nanos as f64 / 1_000_000.0)
        } else {
            format!("{:.2}s", total_nanos as f64 / 1_000_000_000.0)
        }
    }
}

/// 字符串工具
pub struct StringUtils;

impl StringUtils {
    /// 截断字符串
    pub fn truncate(s: &str, max_len: usize) -> String {
        if s.len() <= max_len {
            s.to_string()
        } else {
            format!("{}...", &s[..max_len.saturating_sub(3)])
        }
    }

    /// 移除字符串中的控制字符
    pub fn remove_control_chars(s: &str) -> String {
        s.chars()
            .filter(|c| !c.is_control())
            .collect()
    }

    /// 验证字符串是否为有效的标识符
    pub fn is_valid_identifier(s: &str) -> bool {
        if s.is_empty() {
            return false;
        }

        let mut chars = s.chars();
        let first = chars.next().unwrap();
        
        // 第一个字符必须是字母或下划线
        if !first.is_alphabetic() && first != '_' {
            return false;
        }

        // 后续字符必须是字母、数字或下划线
        chars.all(|c| c.is_alphanumeric() || c == '_')
    }

    /// 生成随机字符串
    pub fn random_string(length: usize) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        use std::time::{
            SystemTime, 
            //UNIX_EPOCH,
        };
        
        let mut hasher = DefaultHasher::new();
        SystemTime::now().hash(&mut hasher);
        let hash = hasher.finish();
        
        let chars: Vec<char> = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".chars().collect();
        let mut result = String::with_capacity(length);
        
        for i in 0..length {
            let idx = (hash >> (i * 8)) as usize % chars.len();
            result.push(chars[idx]);
        }
        
        result
    }
}

/// 哈希工具
pub struct HashUtils;

impl HashUtils {
    /// 计算字符串的简单哈希值
    pub fn simple_hash(s: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        hasher.finish()
    }

    /// 计算字节数组的简单哈希值
    pub fn simple_hash_bytes(data: &[u8]) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        hasher.finish()
    }

    /// 生成追踪ID
    pub fn generate_trace_id() -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        use std::time::{
            SystemTime, 
            //UNIX_EPOCH,
        };
        
        let mut hasher = DefaultHasher::new();
        SystemTime::now().hash(&mut hasher);
        let hash = hasher.finish();
        
        format!("{:016x}", hash)
    }

    /// 生成跨度ID
    pub fn generate_span_id() -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        use std::time::{
            SystemTime, 
            //UNIX_EPOCH,
        };
        
        let mut hasher = DefaultHasher::new();
        SystemTime::now().hash(&mut hasher);
        let hash = hasher.finish();
        
        format!("{:08x}", hash)
    }
}

/// 批处理工具
pub struct BatchUtils;

impl BatchUtils {
    /// 将数据分批处理
    pub fn batch_data<T>(data: Vec<T>, batch_size: usize) -> Vec<Vec<T>> {
        if batch_size == 0 {
            return vec![data];
        }

        let mut batches = Vec::new();
        let mut current_batch = Vec::with_capacity(batch_size);

        for item in data {
            current_batch.push(item);
            
            if current_batch.len() >= batch_size {
                batches.push(current_batch);
                current_batch = Vec::with_capacity(batch_size);
            }
        }

        if !current_batch.is_empty() {
            batches.push(current_batch);
        }

        batches
    }

    /// 计算批处理大小
    pub fn calculate_batch_size(total_items: usize, max_batches: usize) -> usize {
        if max_batches == 0 {
            return total_items;
        }
        
        (total_items + max_batches - 1) / max_batches
    }

    /// 验证批处理大小
    pub fn validate_batch_size(batch_size: usize, max_size: usize) -> usize {
        batch_size.min(max_size).max(1)
    }
}

/// 重试工具
pub struct RetryUtils;

impl RetryUtils {
    /// 计算重试延迟（指数退避）
    pub fn calculate_retry_delay(
        attempt: usize,
        initial_delay: Duration,
        max_delay: Duration,
        multiplier: f64,
        randomize: bool,
    ) -> Duration {
        let mut delay = initial_delay.as_nanos() as f64;
        
        // 指数退避
        for _ in 0..attempt {
            delay *= multiplier;
        }
        
        // 限制最大延迟
        let max_delay_nanos = max_delay.as_nanos() as f64;
        if delay > max_delay_nanos {
            delay = max_delay_nanos;
        }
        
        // 随机化延迟
        if randomize {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            use std::time::{
                SystemTime, 
                //UNIX_EPOCH,
            };
            
            let mut hasher = DefaultHasher::new();
            SystemTime::now().hash(&mut hasher);
            let random_factor = (hasher.finish() % 1000) as f64 / 1000.0;
            
            delay *= 0.5 + random_factor * 0.5; // 0.5 到 1.0 之间的随机因子
        }
        
        Duration::from_nanos(delay as u64)
    }

    /// 判断是否应该重试
    pub fn should_retry(attempt: usize, max_retries: usize, error: &crate::error::OtlpError) -> bool {
        attempt < max_retries && error.is_retryable()
    }
}

/// 性能监控工具
pub struct PerformanceUtils;

impl PerformanceUtils {
    /// 测量执行时间
    pub async fn measure_time<F, R>(f: F) -> (R, Duration)
    where
        F: std::future::Future<Output = R>,
    {
        let start = std::time::Instant::now();
        let result = f.await;
        let duration = start.elapsed();
        (result, duration)
    }

    /// 测量同步执行时间
    pub fn measure_sync_time<F, R>(f: F) -> (R, Duration)
    where
        F: FnOnce() -> R,
    {
        let start = std::time::Instant::now();
        let result = f();
        let duration = start.elapsed();
        (result, duration)
    }

    /// 计算吞吐量
    pub fn calculate_throughput(items: usize, duration: Duration) -> f64 {
        if duration.is_zero() {
            return 0.0;
        }
        
        items as f64 / duration.as_secs_f64()
    }

    /// 计算平均延迟
    pub fn calculate_average_latency(total_duration: Duration, count: usize) -> Duration {
        if count == 0 {
            return Duration::ZERO;
        }
        
        Duration::from_nanos(total_duration.as_nanos() as u64 / count as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_time_utils() {
        let nanos = TimeUtils::current_timestamp_nanos();
        assert!(nanos > 0);
        
        let millis = TimeUtils::nanos_to_millis(1_000_000);
        assert_eq!(millis, 1);
        
        let nanos = TimeUtils::millis_to_nanos(1);
        assert_eq!(nanos, 1_000_000);
        
        let duration = TimeUtils::duration_nanos(1000, 2000);
        assert_eq!(duration, 1000);
    }

    #[test]
    fn test_string_utils() {
        let truncated = StringUtils::truncate("hello world", 5);
        assert_eq!(truncated, "he...");
        
        let cleaned = StringUtils::remove_control_chars("hello\tworld\n");
        assert_eq!(cleaned, "helloworld");
        
        assert!(StringUtils::is_valid_identifier("valid_identifier"));
        assert!(!StringUtils::is_valid_identifier("123invalid"));
        assert!(!StringUtils::is_valid_identifier(""));
        
        let random = StringUtils::random_string(10);
        assert_eq!(random.len(), 10);
    }

    #[test]
    fn test_hash_utils() {
        let hash1 = HashUtils::simple_hash("test");
        let hash2 = HashUtils::simple_hash("test");
        assert_eq!(hash1, hash2);
        
        let hash3 = HashUtils::simple_hash("different");
        assert_ne!(hash1, hash3);
        
        let trace_id = HashUtils::generate_trace_id();
        assert_eq!(trace_id.len(), 16);
        
        let span_id = HashUtils::generate_span_id();
        assert_eq!(span_id.len(), 8);
    }

    #[test]
    fn test_batch_utils() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let batches = BatchUtils::batch_data(data, 3);
        assert_eq!(batches.len(), 4);
        assert_eq!(batches[0], vec![1, 2, 3]);
        assert_eq!(batches[3], vec![10]);
        
        let batch_size = BatchUtils::calculate_batch_size(10, 3);
        assert_eq!(batch_size, 4);
        
        let validated = BatchUtils::validate_batch_size(100, 50);
        assert_eq!(validated, 50);
    }

    #[test]
    fn test_retry_utils() {
        let delay = RetryUtils::calculate_retry_delay(
            2,
            Duration::from_millis(100),
            Duration::from_secs(10),
            2.0,
            false,
        );
        assert!(delay >= Duration::from_millis(400));
        
        let should_retry = RetryUtils::should_retry(
            1,
            3,
            &crate::error::OtlpError::timeout("test", Duration::from_secs(1)),
        );
        assert!(should_retry);
    }

    #[test]
    fn test_performance_utils() {
        let (result, duration) = PerformanceUtils::measure_sync_time(|| {
            std::thread::sleep(Duration::from_millis(1));
            42
        });
        assert_eq!(result, 42);
        assert!(duration >= Duration::from_millis(1));
        
        let throughput = PerformanceUtils::calculate_throughput(100, Duration::from_secs(1));
        assert_eq!(throughput, 100.0);
        
        let avg_latency = PerformanceUtils::calculate_average_latency(
            Duration::from_millis(100),
            10,
        );
        assert_eq!(avg_latency, Duration::from_millis(10));
    }
}
