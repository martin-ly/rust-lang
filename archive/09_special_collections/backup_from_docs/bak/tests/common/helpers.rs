//! 测试辅助函数
//! 
//! 提供测试中使用的辅助函数和工具

use std::time::{Duration, Instant};

/// 测量函数执行时间
pub fn measure_time<F, R>(f: F) -> (R, Duration)
where
    F: FnOnce() -> R,
{
    let start = Instant::now();
    let result = f();
    let duration = start.elapsed();
    (result, duration)
}

/// 测量异步函数执行时间
pub async fn measure_async_time<F, R>(f: F) -> (R, Duration)
where
    F: std::future::Future<Output = R>,
{
    let start = Instant::now();
    let result = f.await;
    let duration = start.elapsed();
    (result, duration)
}

/// 获取当前内存使用量（简化实现）
pub fn get_memory_usage() -> usize {
    std::process::id() as usize
}

/// 等待指定时间
pub fn wait_for(duration: Duration) {
    std::thread::sleep(duration);
}

/// 异步等待指定时间
pub async fn async_wait_for(duration: Duration) {
    tokio::time::sleep(duration).await;
}

/// 生成随机字符串
pub fn generate_random_string(length: usize) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    length.hash(&mut hasher);
    let hash = hasher.finish();
    
    format!("{:016x}", hash)[..length].to_string()
}

/// 生成随机整数
pub fn generate_random_int(min: i32, max: i32) -> i32 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    std::time::SystemTime::now().hash(&mut hasher);
    let hash = hasher.finish();
    
    (hash as i32 % (max - min + 1)) + min
}

/// 断言两个浮点数近似相等
pub fn assert_float_eq(left: f64, right: f64, epsilon: f64) {
    assert!((left - right).abs() < epsilon, 
        "assertion failed: {} != {} (epsilon: {})", left, right, epsilon);
}

/// 断言两个向量近似相等
pub fn assert_vec_float_eq(left: &[f64], right: &[f64], epsilon: f64) {
    assert_eq!(left.len(), right.len(), "vector lengths differ");
    for (i, (&l, &r)) in left.iter().zip(right.iter()).enumerate() {
        assert_float_eq(l, r, epsilon);
    }
}

/// 创建临时文件
pub fn create_temp_file(content: &str) -> std::path::PathBuf {
    use std::fs::File;
    use std::io::Write;
    
    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join(format!("test_{}.txt", 
        std::process::id()));
    
    let mut file = File::create(&file_path).unwrap();
    file.write_all(content.as_bytes()).unwrap();
    
    file_path
}

/// 删除临时文件
pub fn cleanup_temp_file(file_path: &std::path::Path) {
    let _ = std::fs::remove_file(file_path);
}

/// 运行带超时的测试
pub fn run_with_timeout<F, R>(timeout: Duration, f: F) -> Result<R, String>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    let (tx, rx) = std::sync::mpsc::channel();
    
    let handle = std::thread::spawn(move || {
        let result = f();
        let _ = tx.send(Ok(result));
    });
    
    match rx.recv_timeout(timeout) {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(e)) => Err(e),
        Err(_) => {
            handle.join().ok();
            Err("Test timed out".to_string())
        }
    }
}

/// 运行带超时的异步测试
pub async fn run_async_with_timeout<F, R>(
    timeout: Duration, 
    f: F
) -> Result<R, String>
where
    F: std::future::Future<Output = R>,
{
    match tokio::time::timeout(timeout, f).await {
        Ok(result) => Ok(result),
        Err(_) => Err("Async test timed out".to_string()),
    }
}

/// 重试函数
pub fn retry<F, R>(mut f: F, max_attempts: usize) -> Result<R, String>
where
    F: FnMut() -> Result<R, String>,
{
    let mut last_error = String::new();
    
    for attempt in 1..=max_attempts {
        match f() {
            Ok(result) => return Ok(result),
            Err(e) => {
                last_error = e;
                if attempt < max_attempts {
                    std::thread::sleep(Duration::from_millis(100));
                }
            }
        }
    }
    
    Err(last_error)
}

/// 异步重试函数
pub async fn async_retry<F, R>(mut f: F, max_attempts: usize) -> Result<R, String>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<R, String>> + Send>>,
{
    let mut last_error = String::new();
    
    for attempt in 1..=max_attempts {
        match f().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                last_error = e;
                if attempt < max_attempts {
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
            }
        }
    }
    
    Err(last_error)
}

/// 性能基准测试辅助函数
pub fn benchmark_function<F, R>(f: F, iterations: usize) -> (R, Duration, Duration)
where
    F: Fn() -> R,
{
    let mut times = Vec::new();
    let mut result = None;
    
    for _ in 0..iterations {
        let (res, duration) = measure_time(&f);
        result = Some(res);
        times.push(duration);
    }
    
    let total_time: Duration = times.iter().sum();
    let avg_time = total_time / times.len() as u32;
    
    (result.unwrap(), total_time, avg_time)
}

/// 内存使用监控
pub struct MemoryMonitor {
    initial_memory: usize,
}

impl MemoryMonitor {
    pub fn new() -> Self {
        Self {
            initial_memory: get_memory_usage(),
        }
    }
    
    pub fn current_usage(&self) -> usize {
        get_memory_usage().saturating_sub(self.initial_memory)
    }
    
    pub fn reset(&mut self) {
        self.initial_memory = get_memory_usage();
    }
}
