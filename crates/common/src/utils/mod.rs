//! 公共工具函数模块
//! 
//! 提供跨 crate 共享的实用工具函数。

use std::time::{Duration, Instant};

/// 计算执行时间的宏
#[macro_export]
macro_rules! timed {
    ($name:expr, $block:block) => {{
        let _start = std::time::Instant::now();
        let _result = $block;
        let _elapsed = _start.elapsed();
        tracing::debug!("{} took {:?}", $name, _elapsed);
        _result
    }};
}

/// 测量函数执行时间
pub fn measure_time<F, R>(f: F) -> (R, Duration)
where
    F: FnOnce() -> R,
{
    let start = Instant::now();
    let result = f();
    let elapsed = start.elapsed();
    (result, elapsed)
}

/// 带超时的重试函数
pub async fn retry_with_timeout<F, Fut, T, E>(
    mut f: F,
    max_retries: u32,
    timeout: Duration,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Debug,
{
    let mut last_error = None;
    
    for attempt in 0..max_retries {
        match tokio::time::timeout(timeout, f()).await {
            Ok(Ok(result)) => return Ok(result),
            Ok(Err(e)) => {
                tracing::warn!("Attempt {} failed: {:?}", attempt + 1, e);
                last_error = Some(e);
            }
            Err(_) => {
                tracing::warn!("Attempt {} timed out", attempt + 1);
            }
        }
        
        if attempt < max_retries - 1 {
            let delay = Duration::from_millis(100 * (attempt as u64 + 1));
            tokio::time::sleep(delay).await;
        }
    }
    
    Err(last_error.expect("At least one attempt was made"))
}

/// 批处理函数
pub fn batch_process<T, R, F>(items: Vec<T>, batch_size: usize, mut processor: F) -> Vec<R>
where
    F: FnMut(&[T]) -> Vec<R>,
{
    let mut results = Vec::new();
    
    for chunk in items.chunks(batch_size) {
        results.extend(processor(chunk));
    }
    
    results
}

/// 异步批处理函数
pub async fn batch_process_async<T, R, F, Fut>(
    items: Vec<T>,
    batch_size: usize,
    mut processor: F,
) -> Vec<R>
where
    F: FnMut(Vec<T>) -> Fut,
    Fut: std::future::Future<Output = Vec<R>>,
    T: Clone,
{
    let mut results = Vec::new();
    let chunks: Vec<Vec<T>> = items.chunks(batch_size).map(|c| c.to_vec()).collect();
    
    for chunk in chunks {
        results.extend(processor(chunk).await);
    }
    
    results
}

/// 字符串截断工具
pub fn truncate_with_ellipsis(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len.saturating_sub(3)])
    }
}

/// 安全的字符串切片
pub fn safe_slice(s: &str, start: usize, end: usize) -> &str {
    let len = s.len();
    let start = start.min(len);
    let end = end.min(len);
    &s[start..end]
}

/// 格式化字节大小
pub fn format_bytes(bytes: u64) -> String {
    const UNITS: &[&str] = &["B", "KB", "MB", "GB", "TB"];
    
    if bytes == 0 {
        return "0 B".to_string();
    }
    
    let exp = (bytes as f64).log(1024.0).min(UNITS.len() as f64 - 1.0) as usize;
    let value = bytes as f64 / 1024f64.powi(exp as i32);
    
    format!("{:.2} {}", value, UNITS[exp])
}

/// 格式化持续时间
pub fn format_duration(duration: Duration) -> String {
    let secs = duration.as_secs();
    let millis = duration.subsec_millis();
    
    if secs >= 3600 {
        format!("{}h {}m {}s", secs / 3600, (secs % 3600) / 60, secs % 60)
    } else if secs >= 60 {
        format!("{}m {}s", secs / 60, secs % 60)
    } else if secs > 0 {
        format!("{}.{:03}s", secs, millis)
    } else {
        format!("{}ms", millis)
    }
}

/// 生成唯一 ID
pub fn generate_id() -> String {
    use std::sync::atomic::{AtomicU64, Ordering};
    
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let count = COUNTER.fetch_add(1, Ordering::SeqCst);
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis();
    
    format!("{:x}{:x}", timestamp, count)
}

/// 限流器（简单实现）
pub struct RateLimiter {
    last_request: std::sync::Mutex<Instant>,
    min_interval: Duration,
}

impl RateLimiter {
    /// 创建限流器
    pub fn new(min_interval: Duration) -> Self {
        Self {
            last_request: std::sync::Mutex::new(Instant::now() - min_interval),
            min_interval,
        }
    }
    
    /// 检查是否允许请求
    pub fn allow(&self) -> bool {
        let mut last = self.last_request.lock().unwrap();
        let now = Instant::now();
        
        if now.duration_since(*last) >= self.min_interval {
            *last = now;
            true
        } else {
            false
        }
    }
    
    /// 等待直到允许请求
    pub async fn wait(&self) {
        loop {
            if self.allow() {
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
}

/// 一次性执行守卫
pub struct OnceGuard {
    executed: std::sync::atomic::AtomicBool,
}

impl OnceGuard {
    /// 创建新的一次性守卫
    pub const fn new() -> Self {
        Self {
            executed: std::sync::atomic::AtomicBool::new(false),
        }
    }
    
    /// 尝试执行一次
    pub fn try_execute<F>(&self, f: F) -> bool
    where
        F: FnOnce(),
    {
        if self
            .executed
            .compare_exchange(
                false,
                true,
                std::sync::atomic::Ordering::SeqCst,
                std::sync::atomic::Ordering::SeqCst,
            )
            .is_ok()
        {
            f();
            true
        } else {
            false
        }
    }
}

impl Default for OnceGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_truncate_with_ellipsis() {
        assert_eq!(truncate_with_ellipsis("hello", 10), "hello");
        assert_eq!(truncate_with_ellipsis("hello world", 8), "hello...");
    }
    
    #[test]
    fn test_format_bytes() {
        assert_eq!(format_bytes(0), "0 B");
        assert_eq!(format_bytes(1024), "1.00 KB");
        assert_eq!(format_bytes(1024 * 1024), "1.00 MB");
    }
    
    #[test]
    fn test_format_duration() {
        assert_eq!(format_duration(Duration::from_millis(500)), "500ms");
        assert_eq!(format_duration(Duration::from_secs(65)), "1m 5s");
    }
    
    #[test]
    fn test_batch_process() {
        let items = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let results = batch_process(items, 3, |chunk| {
            chunk.iter().map(|x| x * 2).collect()
        });
        assert_eq!(results.len(), 10);
        assert_eq!(results[0], 2);
    }
    
    #[test]
    fn test_once_guard() {
        let guard = OnceGuard::new();
        let mut count = 0;
        
        assert!(guard.try_execute(|| count += 1));
        assert!(!guard.try_execute(|| count += 1));
        assert_eq!(count, 1);
    }
}
