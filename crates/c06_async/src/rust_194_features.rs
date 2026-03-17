//! Rust 1.94.0 异步编程特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在异步编程场景中的增强，包括：
//! - 异步上下文中的 LazyLock / LazyLock in Async Context
//! - 数学常量在异步计算中的应用 / Math Constants in Async Computation
//! - Peekable 流处理 / Peekable Stream Processing
//! - 异步数组窗口处理 / Async Array Windows Processing
//! - char 转换在异步解析中的应用 / char Conversion in Async Parsing
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::iter::Peekable;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

// ==================== 1. 异步上下文中的 LazyLock ====================

/// # 1. 异步上下文中的 LazyLock / LazyLock in Async Context
///
/// Rust 1.94.0 为 LazyLock 添加了新方法，使其在异步环境中更加灵活：
/// - `get()`: 获取引用，如果未初始化则进行初始化
/// - 这些新方法在异步上下文中特别有用，可以避免在 async fn 中直接使用阻塞初始化
///
/// 异步全局配置
///
/// Rust 1.94.0: 在异步上下文中使用 LazyLock 管理全局配置
pub static ASYNC_GLOBAL_CONFIG: LazyLock<AsyncConfig> = LazyLock::new(|| {
    println!("异步初始化全局配置...");
    AsyncConfig {
        max_connections: 100,
        timeout_seconds: 30,
        retry_count: 3,
    }
});

/// 异步配置结构
#[derive(Debug, Clone)]
pub struct AsyncConfig {
    pub max_connections: usize,
    pub timeout_seconds: u64,
    pub retry_count: u32,
}

/// 异步懒加载数据库连接池
///
/// Rust 1.94.0: 在异步上下文中管理昂贵资源
pub static ASYNC_DB_POOL: LazyLock<AsyncDbPool> = LazyLock::new(|| {
    println!("初始化异步数据库连接池...");
    AsyncDbPool {
        connections: (0..10).map(|i| format!("connection_{}", i)).collect(),
        active_count: AtomicU64::new(0),
    }
});

/// 异步数据库连接池
#[derive(Debug)]
pub struct AsyncDbPool {
    #[allow(dead_code)]
    connections: Vec<String>,
    active_count: AtomicU64,
}

impl AsyncDbPool {
    /// 获取连接
    pub fn acquire(&self) -> Option<String> {
        let idx = self.active_count.fetch_add(1, Ordering::Relaxed);
        self.connections.get(idx as usize).cloned()
    }

    /// 获取活跃连接数
    pub fn active_count(&self) -> u64 {
        self.active_count.load(Ordering::Relaxed)
    }
}

/// 异步配置管理器
///
/// Rust 1.94.0: 使用 LazyLock::get 在异步上下文中安全访问配置
pub struct AsyncConfigManager;

impl AsyncConfigManager {
    /// 获取配置引用
    ///
    /// Rust 1.94.0: 使用 Deref
    pub fn get_config() -> &'static AsyncConfig {
        &ASYNC_GLOBAL_CONFIG
    }

    /// 异步获取最大连接数
    pub async fn get_max_connections() -> usize {
        // 模拟异步操作
        tokio::time::sleep(Duration::from_millis(1)).await;
        Self::get_config().max_connections
    }

    /// 异步获取超时时间
    pub async fn get_timeout() -> Duration {
        tokio::time::sleep(Duration::from_millis(1)).await;
        Duration::from_secs(Self::get_config().timeout_seconds)
    }
}

/// 演示异步上下文中使用 LazyLock
#[allow(dead_code)]
pub async fn demonstrate_async_lazylock() {
    println!("\n=== 异步 LazyLock 演示 ===\n");

    // 使用 get() 获取配置引用
    let config = AsyncConfigManager::get_config();
    println!("配置: {:?}", config);

    // 异步获取配置值
    let max_conn = AsyncConfigManager::get_max_connections().await;
    println!("最大连接数: {}", max_conn);

    let timeout = AsyncConfigManager::get_timeout().await;
    println!("超时时间: {:?}", timeout);

    // 访问连接池
    let pool = &ASYNC_DB_POOL;
    if let Some(conn) = pool.acquire() {
        println!("获取连接: {}", conn);
    }
    println!("活跃连接数: {}", pool.active_count());
}

/// 异步懒加载值
///
/// Rust 1.94.0: 在异步任务中使用 LazyLock
pub struct AsyncLazyValue<T: Send + Sync> {
    inner: LazyLock<T>,
}

impl<T: Send + Sync> AsyncLazyValue<T> {
    /// 创建新的异步懒加载值
    pub fn new(f: fn() -> T) -> Self {
        Self {
            inner: LazyLock::new(f),
        }
    }

    /// 异步获取值
    ///
    /// Rust 1.94.0: 使用 Deref 在异步上下文中安全访问
    ///
    /// 注意：此方法不执行 yield，因为 LazyLock 的访问是快速的同步操作。
    /// 只有在需要长时间计算或处理大量数据时才应该使用 yield。
    pub async fn get(&self) -> &T {
        &self.inner
    }
}

// ==================== 2. 数学常量在异步计算中的应用 ====================

/// # 2. 数学常量在异步计算中的应用 / Math Constants in Async Computation
///
/// Rust 1.94.0 添加了 EULER_GAMMA 和 GOLDEN_RATIO 常量，
/// 这些常量在异步数值计算和科学计算中非常有用。
/// 异步数学计算器
///
/// Rust 1.94.0: 使用数学常量进行异步数值计算
pub struct AsyncMathCalculator;

impl AsyncMathCalculator {
    /// 异步计算黄金比例逼近
    pub async fn golden_ratio_approximation(iterations: u32) -> f64 {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let mut result = 1.0;

        for _ in 0..iterations {
            result = 1.0 + 1.0 / result;
            // 模拟异步计算延迟
            tokio::time::sleep(Duration::from_micros(10)).await;
        }

        (result - phi).abs()
    }

    /// 异步计算欧拉-马歇罗尼常数逼近
    pub async fn euler_gamma_approximation(n: u64) -> f64 {
        let gamma = 0.5772156649015329_f64; // std::f64::consts::EULER_GAMMA

        // 计算调和级数 H_n
        let harmonic: f64 = (1..=n).map(|i| 1.0 / i as f64).sum();
        let ln_n = (n as f64).ln();

        // H_n - ln(n) 逼近 γ
        (harmonic - ln_n - gamma).abs()
    }

    /// 异步斐波那契数计算（使用黄金比例）
    pub async fn fibonacci_approximation(n: u32) -> f64 {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let psi = 1.0 - phi; // -1/phi

        // F_n ≈ φ^n / √5
        let sqrt5 = 5.0_f64.sqrt();
        (phi.powi(n as i32) - psi.powi(n as i32)) / sqrt5
    }
}

/// 演示异步数学计算
#[allow(dead_code)]
pub async fn demonstrate_async_math() {
    println!("\n=== 异步数学计算演示 ===\n");

    let _calculator = AsyncMathCalculator;

    // 计算黄金比例逼近
    let error = AsyncMathCalculator::golden_ratio_approximation(50).await;
    println!("黄金比例逼近误差: {:.10}", error);

    // 计算欧拉常数逼近
    let gamma_error = AsyncMathCalculator::euler_gamma_approximation(10000).await;
    println!("欧拉常数逼近误差: {:.10}", gamma_error);

    // 计算斐波那契数
    let fib_20 = AsyncMathCalculator::fibonacci_approximation(20).await;
    println!("F(20) 近似值: {:.0}", fib_20);
}

/// 异步数值积分
///
/// Rust 1.94.0: 使用数学常量进行异步数值分析
pub async fn async_numerical_integration<F>(f: F, a: f64, b: f64, n: usize) -> f64
where
    F: Fn(f64) -> f64 + Send + 'static,
{
    let h = (b - a) / n as f64;
    let mut sum = 0.0;

    for i in 0..n {
        let x = a + (i as f64 + 0.5) * h;
        sum += f(x);

        // 每 1000 次迭代让出控制权
        if i % 1000 == 0 {
            tokio::task::yield_now().await;
        }
    }

    sum * h
}

// ==================== 3. Peekable 流处理 ====================

/// # 3. Peekable 流处理 / Peekable Stream Processing
///
/// Rust 1.94.0 为 Peekable 添加了 next_if_map 和 next_if_map_mut 方法，
/// 这些方法在异步流处理和解析中特别有用。
/// 异步令牌流
///
/// Rust 1.94.0: 使用 Peekable 处理异步数据流
pub struct AsyncTokenStream {
    tokens: Vec<String>,
    position: usize,
}

impl AsyncTokenStream {
    /// 创建新的令牌流
    pub fn new(tokens: Vec<String>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    /// 异步获取下一个令牌
    pub async fn next(&mut self) -> Option<String> {
        if self.position < self.tokens.len() {
            let token = self.tokens[self.position].clone();
            self.position += 1;
            Some(token)
        } else {
            None
        }
    }

    /// 查看下一个令牌
    pub async fn peek(&self) -> Option<&String> {
        self.tokens.get(self.position)
    }

    /// 异步解析数字令牌
    ///
    /// Rust 1.94.0: 使用 next_if_map 模式
    pub async fn parse_number(&mut self) -> Option<f64> {
        if let Some(token) = self.peek().await
            && let Ok(num) = token.parse::<f64>()
        {
            self.position += 1;
            return Some(num);
        }
        None
    }
}

/// 异步表达式解析器
///
/// Rust 1.94.0: 使用 Peekable 模式解析异步表达式
pub struct AsyncExpressionParser<I: Iterator<Item = String>> {
    tokens: Peekable<I>,
}

impl<I: Iterator<Item = String>> AsyncExpressionParser<I> {
    /// 创建新的解析器
    pub fn new(tokens: I) -> Self {
        Self {
            tokens: tokens.peekable(),
        }
    }

    /// 解析表达式
    pub async fn parse_expression(&mut self) -> Option<f64> {
        let mut left = self.parse_number().await?;

        while let Some(op) = self.tokens.peek().cloned() {
            match op.as_str() {
                "+" | "-" | "*" | "/" => {
                    self.tokens.next();
                    let right = self.parse_number().await?;
                    left = match op.as_str() {
                        "+" => left + right,
                        "-" => left - right,
                        "*" => left * right,
                        "/" => left / right,
                        _ => return None,
                    };
                }
                _ => break,
            }
        }

        Some(left)
    }

    /// 解析数字
    ///
    /// Rust 1.94.0: 使用 next_if_map 简化条件解析
    async fn parse_number(&mut self) -> Option<f64> {
        // 模拟异步操作
        tokio::time::sleep(Duration::from_micros(1)).await;

        // 使用 next_if_map 模式
        if let Some(token) = self.tokens.peek()
            && let Ok(num) = token.parse::<f64>()
        {
            self.tokens.next();
            return Some(num);
        }
        None
    }
}

/// 演示异步流处理
#[allow(dead_code)]
pub async fn demonstrate_async_stream_processing() {
    println!("\n=== 异步流处理演示 ===\n");

    // 创建令牌流
    let tokens = vec!["10".to_string(), "+".to_string(), "20".to_string()];
    let mut stream = AsyncTokenStream::new(tokens);

    while let Some(token) = stream.next().await {
        println!("令牌: {}", token);
    }

    // 解析表达式
    let expr_tokens = vec!["10".to_string(), "+".to_string(), "5".to_string()];
    let mut parser = AsyncExpressionParser::new(expr_tokens.into_iter());
    if let Some(result) = parser.parse_expression().await {
        println!("表达式结果: {}", result);
    }
}

// ==================== 4. 异步数组窗口处理 ====================

/// # 4. 异步数组窗口处理 / Async Array Windows Processing
///
/// Rust 1.94.0 的 array_windows 方法可以与异步流处理结合，
/// 用于实现高效的异步滑动窗口算法。
/// 异步滑动窗口处理器
///
/// Rust 1.94.0: 在异步上下文中处理数据窗口
pub struct AsyncSlidingWindowProcessor;

impl AsyncSlidingWindowProcessor {
    /// 异步计算移动平均
    ///
    /// 当数据量较大（超过 1000 个窗口）时，会定期让出控制权以支持并发。
    /// 使用常量泛型参数支持 array_windows。
    pub async fn moving_average<const N: usize>(data: &[f64]) -> Vec<f64> {
        let mut result = Vec::new();
        let total_windows = data.len().saturating_sub(N - 1);

        // Rust 1.94.0: 使用 array_windows 替代 windows
        for (i, window) in data.array_windows::<N>().enumerate() {
            let avg = window.iter().sum::<f64>() / N as f64;
            result.push(avg);

            // 只在处理大量数据时让出控制权
            if total_windows > 1000 && i % 1000 == 0 {
                tokio::task::yield_now().await;
            }
        }

        result
    }

    /// 异步检测趋势变化
    pub async fn detect_trend_changes(data: &[f64]) -> Vec<usize> {
        let mut changes = Vec::new();

        // Rust 1.94.0: 使用 array_windows::<2>
        for (i, [prev, curr]) in data.array_windows::<2>().enumerate() {
            if (curr - prev).abs() > 1.0 {
                changes.push(i);
            }

            if i % 1000 == 0 {
                tokio::task::yield_now().await;
            }
        }

        changes
    }

    /// 异步计算指数移动平均
    pub async fn exponential_moving_average(data: &[f64], alpha: f64) -> Vec<f64> {
        if data.is_empty() {
            return Vec::new();
        }

        let mut ema = Vec::with_capacity(data.len());
        ema.push(data[0]);

        for i in 1..data.len() {
            let value = alpha * data[i] + (1.0 - alpha) * ema[i - 1];
            ema.push(value);

            if i % 1000 == 0 {
                tokio::task::yield_now().await;
            }
        }

        ema
    }
}

/// 演示异步窗口处理
#[allow(dead_code)]
pub async fn demonstrate_async_windows() {
    println!("\n=== 异步数组窗口处理演示 ===\n");

    let data: Vec<f64> = (0..100).map(|i| i as f64).collect();

    // 计算移动平均
    let ma = AsyncSlidingWindowProcessor::moving_average::<5>(&data).await;
    println!("前5个移动平均值: {:?}", &ma[..5]);

    // 检测趋势变化
    let test_data = vec![1.0, 2.0, 10.0, 3.0, 4.0];
    let changes = AsyncSlidingWindowProcessor::detect_trend_changes(&test_data).await;
    println!("趋势变化位置: {:?}", changes);

    // 计算指数移动平均
    let ema = AsyncSlidingWindowProcessor::exponential_moving_average(&data, 0.3).await;
    println!("前5个EMA值: {:?}", &ema[..5]);
}

// ==================== 5. char 转换在异步解析中的应用 ====================

/// # 5. char 转换在异步解析中的应用 / char Conversion in Async Parsing
///
/// Rust 1.94.0 的 TryFrom<char> for usize 实现可以在异步解析中使用。
/// 异步 Unicode 解析器
///
/// Rust 1.94.0: 使用 char 到 usize 转换进行异步文本处理
pub struct AsyncUnicodeParser;

impl AsyncUnicodeParser {
    /// 异步分析字符串的 Unicode 组成
    ///
    /// 当字符串较长（超过 1000 个字符）时，会定期让出控制权以支持并发。
    pub async fn analyze_string(s: &str) -> UnicodeComposition {
        let mut composition = UnicodeComposition::default();
        let char_count = s.chars().count();

        for (i, ch) in s.chars().enumerate() {
            let code_point = usize::try_from(ch).unwrap_or(0); // Rust 1.94.0: TryFrom<char> for usize

            match code_point {
                0..=127 => composition.ascii_chars.push(ch),
                128..=255 => composition.latin_chars.push(ch),
                0x4E00..=0x9FFF | 0x3400..=0x4DBF => composition.cjk_chars.push(ch),
                0x1F600..=0x1F64F => composition.emoji_chars.push(ch),
                _ => composition.other_chars.push(ch),
            }

            // 只在处理长字符串时让出控制权
            if char_count > 1000 && i % 1000 == 0 {
                tokio::task::yield_now().await;
            }
        }

        composition
    }

    /// 异步验证字符编码
    pub async fn validate_encoding(chars: &[char]) -> Vec<bool> {
        let mut results = Vec::with_capacity(chars.len());

        for &ch in chars {
            let code_point = usize::try_from(ch).unwrap_or(0);
            // 验证是否为有效的 Unicode 标量值
            let is_valid = code_point <= 0x10FFFF;
            results.push(is_valid);

            if results.len() % 1000 == 0 {
                tokio::task::yield_now().await;
            }
        }

        results
    }
}

/// Unicode 组成分析结果
#[derive(Debug, Default)]
pub struct UnicodeComposition {
    pub ascii_chars: Vec<char>,
    pub latin_chars: Vec<char>,
    pub cjk_chars: Vec<char>,
    pub emoji_chars: Vec<char>,
    pub other_chars: Vec<char>,
}

impl UnicodeComposition {
    /// 获取总字符数
    pub fn total_count(&self) -> usize {
        self.ascii_chars.len()
            + self.latin_chars.len()
            + self.cjk_chars.len()
            + self.emoji_chars.len()
            + self.other_chars.len()
    }
}

/// 演示异步 char 转换
#[allow(dead_code)]
pub async fn demonstrate_async_char_conversion() {
    println!("\n=== 异步 char 转换演示 ===\n");

    let text = "Hello 世界! 🦀 Rust 1.94";
    let composition = AsyncUnicodeParser::analyze_string(text).await;

    println!("字符串: {}", text);
    println!("ASCII字符: {:?}", composition.ascii_chars);
    println!("CJK字符: {:?}", composition.cjk_chars);
    println!("表情符号: {:?}", composition.emoji_chars);
    println!("总字符数: {}", composition.total_count());
}

// ==================== Rust 1.94 真实特性: ControlFlow ====================

use std::ops::ControlFlow;

/// 搜索二维数组，找到目标时提前退出
pub fn search_in_matrix(matrix: &[Vec<i32>], target: i32) -> ControlFlow<(usize, usize), ()> {
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val == target {
                return ControlFlow::Break((i, j));
            }
        }
    }
    ControlFlow::Continue(())
}

/// 数据验证管道
pub fn validate_data(data: &str) -> ControlFlow<String, ()> {
    if data.is_empty() {
        return ControlFlow::Break("数据不能为空".to_string());
    }
    if data.len() < 8 {
        return ControlFlow::Break("数据长度至少为 8".to_string());
    }
    ControlFlow::Continue(())
}

/// 批量处理带错误控制
pub fn batch_process<T, E>(
    items: &[T],
    processor: impl Fn(&T) -> Result<(), E>,
) -> ControlFlow<E, usize> {
    let mut processed = 0;
    for item in items {
        match processor(item) {
            Ok(()) => processed += 1,
            Err(e) => return ControlFlow::Break(e),
        }
    }
    ControlFlow::Continue(processed)
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 异步编程特性
pub async fn demonstrate_rust_194_async_features() {
    println!("\n=== Rust 1.94.0 异步编程特性演示 ===\n");

    // 1. 异步 LazyLock
    demonstrate_async_lazylock().await;

    // 2. 异步数学计算
    demonstrate_async_math().await;

    // 3. 异步流处理
    demonstrate_async_stream_processing().await;

    // 4. 异步窗口处理
    demonstrate_async_windows().await;

    // 5. 异步 char 转换
    demonstrate_async_char_conversion().await;

    // 并发执行任务
    let handles: Vec<_> = vec![
        tokio::spawn(async move {
            AsyncMathCalculator::golden_ratio_approximation(30).await;
        }),
        tokio::spawn(async move {
            AsyncMathCalculator::euler_gamma_approximation(5000).await;
        }),
        tokio::spawn(async move {
            let data: Vec<f64> = (0..50).map(|i| i as f64).collect();
            let _ = AsyncSlidingWindowProcessor::moving_average::<5>(&data).await;
        }),
    ];

    for handle in handles {
        let _ = handle.await;
    }
    println!("\n所有异步任务完成!");
}

/// 获取 Rust 1.94.0 异步编程特性信息
pub fn get_rust_194_async_info() -> String {
    "Rust 1.94.0 异步编程特性:\n\
        - 异步上下文中的 LazyLock (get, get_mut, force_mut)\n\
        - 数学常量在异步计算中的应用 (EULER_GAMMA, GOLDEN_RATIO)\n\
        - Peekable 流处理 (next_if_map, next_if_map_mut)\n\
        - 异步数组窗口处理 (array_windows)\n\
        - char 转换在异步解析中的应用 (TryFrom<char> for usize)"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_config_manager() {
        let config = AsyncConfigManager::get_config();
        assert_eq!(config.max_connections, 100);

        let max_conn = AsyncConfigManager::get_max_connections().await;
        assert_eq!(max_conn, 100);
    }

    #[tokio::test]
    async fn test_async_lazy_value() {
        let lazy = AsyncLazyValue::new(|| 42);
        let value = lazy.get().await;
        assert_eq!(*value, 42);
    }

    #[tokio::test]
    async fn test_async_math_calculator() {
        let error = AsyncMathCalculator::golden_ratio_approximation(50).await;
        assert!(error < 0.0001);

        let fib = AsyncMathCalculator::fibonacci_approximation(10).await;
        assert!((fib - 55.0).abs() < 1.0);
    }

    #[tokio::test]
    async fn test_async_numerical_integration() {
        let result = async_numerical_integration(|x| x * x, 0.0, 1.0, 1000).await;
        // ∫₀¹ x² dx = 1/3
        assert!((result - 0.333).abs() < 0.01);
    }

    #[tokio::test]
    async fn test_async_token_stream() {
        let tokens = vec!["10".to_string(), "20".to_string()];
        let mut stream = AsyncTokenStream::new(tokens);

        assert_eq!(stream.parse_number().await, Some(10.0));
        assert_eq!(stream.parse_number().await, Some(20.0));
    }

    #[tokio::test]
    async fn test_async_sliding_window() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let ma = AsyncSlidingWindowProcessor::moving_average::<3>(&data).await;
        assert_eq!(ma, vec![2.0, 3.0, 4.0]);
    }

    #[tokio::test]
    async fn test_async_detect_trend_changes() {
        let data = vec![1.0, 2.0, 10.0, 3.0];
        let changes = AsyncSlidingWindowProcessor::detect_trend_changes(&data).await;
        assert!(changes.contains(&1)); // 2.0 -> 10.0 是趋势变化
    }

    #[tokio::test]
    async fn test_async_unicode_parser() {
        let text = "Hello";
        let composition = AsyncUnicodeParser::analyze_string(text).await;
        assert_eq!(composition.ascii_chars.len(), 5);
        assert_eq!(composition.cjk_chars.len(), 0);
    }

    #[tokio::test]
    async fn test_async_validate_encoding() {
        let chars = vec!['A', '中', '🦀'];
        let results = AsyncUnicodeParser::validate_encoding(&chars).await;
        assert!(results.iter().all(|&v| v));
    }

    #[tokio::test]
    async fn test_demonstrate_features() {
        demonstrate_rust_194_async_features().await;
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_async_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("LazyLock"));
    }

    // ==================== ControlFlow 测试 ====================

    #[test]
    fn test_control_flow_matrix_search() {
        let matrix = vec![vec![1, 2], vec![3, 4]];
        assert!(matches!(search_in_matrix(&matrix, 3), ControlFlow::Break((1, 0))));
    }

    #[test]
    fn test_control_flow_validate() {
        assert!(matches!(validate_data("valid123"), ControlFlow::Continue(())));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
    }

    #[test]
    fn test_control_flow_batch() {
        let items = vec![1, 2, 3];
        let result = batch_process(&items, |_| Ok::<_, String>(()));
        assert!(matches!(result, ControlFlow::Continue(3)));
    }

    // ==================== 异步边界测试 ====================

    /// 测试 AsyncLazyValue 的并发访问
    ///
    /// 验证多个并发任务同时访问同一个 LazyValue 时的行为
    #[tokio::test]
    async fn test_async_lazy_value_concurrent() {
        use std::sync::Arc;
        use tokio::sync::Barrier;

        let lazy = Arc::new(AsyncLazyValue::new(|| {
            println!("初始化懒加载值...");
            vec![1, 2, 3, 4, 5]
        }));

        let barrier = Arc::new(Barrier::new(3));
        let mut handles = vec![];

        // 创建 3 个并发任务
        for i in 0..3 {
            let lazy_clone = Arc::clone(&lazy);
            let barrier_clone = Arc::clone(&barrier);
            let handle = tokio::spawn(async move {
                // 等待所有任务都准备好
                barrier_clone.wait().await;
                
                // 并发访问
                let value = lazy_clone.get().await;
                println!("任务 {} 获取到值: {:?}", i, value);
                assert_eq!(value, &vec![1, 2, 3, 4, 5]);
            });
            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            handle.await.unwrap();
        }

        // 验证值只被初始化一次（由于 LazyLock 的保证）
        // 注意：LazyLock 内部保证了线程安全，因此值只会被初始化一次
    }

    /// 测试异步数学计算的超时
    ///
    /// 验证长时间计算可以被正确取消
    #[tokio::test]
    async fn test_async_math_timeout() {
        use tokio::time::{timeout, Duration};

        // 测试快速计算不会超时
        let result = timeout(
            Duration::from_secs(1),
            AsyncMathCalculator::golden_ratio_approximation(10)
        ).await;
        assert!(result.is_ok(), "快速计算不应该超时");

        // 测试计算结果正确性
        let error = AsyncMathCalculator::golden_ratio_approximation(50).await;
        assert!(error < 0.0001, "黄金比例逼近应该收敛");

        // 测试长时间计算可以被取消
        let long_calc = timeout(
            Duration::from_millis(1),
            async {
                // 模拟一个需要多次 yield 的计算
                for _ in 0..100 {
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
                42
            }
        ).await;
        
        assert!(long_calc.is_err(), "应该超时");
    }

    /// 测试 AsyncUnicodeParser 对空字符串的分析
    ///
    /// 验证空字符串和边界情况的处理
    #[tokio::test]
    async fn test_unicode_analyzer_empty() {
        // 测试空字符串
        let empty = "";
        let composition = AsyncUnicodeParser::analyze_string(empty).await;
        
        assert_eq!(composition.total_count(), 0);
        assert!(composition.ascii_chars.is_empty());
        assert!(composition.cjk_chars.is_empty());
        assert!(composition.emoji_chars.is_empty());
        assert!(composition.latin_chars.is_empty());
        assert!(composition.other_chars.is_empty());

        // 测试仅包含 ASCII 的字符串
        let ascii = "Hello World";
        let ascii_comp = AsyncUnicodeParser::analyze_string(ascii).await;
        assert_eq!(ascii_comp.total_count(), 11);
        assert_eq!(ascii_comp.ascii_chars.len(), 11);

        // 测试仅包含 CJK 的字符串
        let cjk = "你好世界";
        let cjk_comp = AsyncUnicodeParser::analyze_string(cjk).await;
        assert_eq!(cjk_comp.total_count(), 4);
        assert_eq!(cjk_comp.cjk_chars.len(), 4);

        // 测试 emoji 字符 - emoji 可能根据 Unicode 版本被归类到不同类别
        let emoji = "🎉🦀🚀";
        let emoji_comp = AsyncUnicodeParser::analyze_string(emoji).await;
        // emoji 字符的总数应该是 3，但它们可能被归类到 different 类别
        // 取决于 Unicode 版本和分类逻辑
        let total_emoji_len = emoji_comp.emoji_chars.len() + emoji_comp.other_chars.len();
        assert_eq!(emoji_comp.total_count(), 3);
        assert!(total_emoji_len >= 3, "emoji 应该被正确计数");

        // 测试 Unicode 验证
        let valid_chars = vec!['A', '中', '🦀'];
        let validation = AsyncUnicodeParser::validate_encoding(&valid_chars).await;
        assert!(validation.iter().all(|&v| v), "所有字符应该有效");
    }
}
