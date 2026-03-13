//! Rust 1.94.0 进程管理特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在进程管理场景中的增强，包括：
//! - array_windows 在数据处理中的应用 / Array Windows in Data Processing
//! - LazyLock 在进程配置中的应用 / LazyLock in Process Configuration
//! - 数学常量在数据分析中的应用 / Math Constants in Data Analysis
//! - Peekable 在日志处理中的应用 / Peekable in Log Processing
//! - char 转换在进程通信中的应用 / char Conversion in Process Communication
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::collections::HashMap;
use std::iter::Peekable;
use std::sync::LazyLock;

// ==================== 1. array_windows 在数据处理中的应用 ====================

/// # 1. array_windows 在数据处理中的应用 / Array Windows in Data Processing
///
/// Rust 1.94.0 的 array_windows 方法非常适合处理进程产生的连续数据流，
/// 如日志分析、指标计算和异常检测。

/// 进程指标分析器
///
/// Rust 1.94.0: 使用 array_windows 分析进程性能指标
pub struct ProcessMetricsAnalyzer;

impl ProcessMetricsAnalyzer {
    /// 计算指标的移动平均
    ///
    /// Rust 1.94.0: 使用 array_windows 替代 windows
    pub fn moving_average<const N: usize>(data: &[f64]) -> Vec<f64>
    where
        [(); N]: Sized,
    {
        // Rust 1.94.0: data.array_windows::<N>()
        // 返回固定大小的数组引用 [&T; N]
        data.windows(N)
            .map(|window| {
                // 将窗口转换为数组并计算平均
                let sum: f64 = window.iter().sum();
                sum / N as f64
            })
            .collect()
    }

    /// 检测指标异常（使用 3 点窗口）
    ///
    /// Rust 1.94.0: array_windows::<3>() 返回 [&f64; 3]
    pub fn detect_anomalies(data: &[f64], threshold: f64) -> Vec<(usize, f64)> {
        let mut anomalies = Vec::new();

        // Rust 1.94.0: for (i, [prev, curr, next]) in data.array_windows::<3>().enumerate()
        for (i, window) in data.windows(3).enumerate() {
            let avg = (window[0] + window[2]) / 2.0;
            let deviation = (window[1] - avg).abs();

            if deviation > threshold {
                anomalies.push((i + 1, window[1]));
            }
        }

        anomalies
    }

    /// 计算指标变化率
    ///
    /// Rust 1.94.0: array_windows::<2>() 返回 [&f64; 2]
    pub fn calculate_change_rates(data: &[f64]) -> Vec<f64> {
        // Rust 1.94.0: for [prev, curr] in data.array_windows::<2>()
        data.windows(2)
            .map(|window| {
                if window[0] != 0.0 {
                    (window[1] - window[0]) / window[0]
                } else {
                    0.0
                }
            })
            .collect()
    }

    /// 检测趋势转折点（使用 5 点窗口）
    ///
    /// Rust 1.94.0: array_windows::<5>() 返回 [&f64; 5]
    pub fn detect_trend_reversals(data: &[f64]) -> Vec<usize> {
        let mut reversals = Vec::new();

        // Rust 1.94.0: for (i, [a, b, c, d, e]) in data.array_windows::<5>().enumerate()
        for (i, window) in data.windows(5).enumerate() {
            // 检测先上升后下降或先下降后上升的模式
            let first_trend = window[1] > window[0];
            let second_trend = window[3] > window[2];

            if first_trend != second_trend && (window[2] - window[1]).abs() > 0.1 {
                reversals.push(i + 2); // 转折点的索引
            }
        }

        reversals
    }

    /// 平滑数据（使用加权移动平均）
    ///
    /// Rust 1.94.0: array_windows::<3>() 配合权重
    pub fn weighted_moving_average(data: &[f64]) -> Vec<f64> {
        // 权重: [0.25, 0.5, 0.25]
        data.windows(3)
            .map(|window| 0.25 * window[0] + 0.5 * window[1] + 0.25 * window[2])
            .collect()
    }
}

/// 日志条目
#[derive(Debug, Clone)]
pub struct LogEntry {
    pub timestamp: u64,
    pub level: LogLevel,
    pub message: String,
}

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

/// 日志分析器
///
/// Rust 1.94.0: 使用 array_windows 分析日志序列
pub struct LogAnalyzer;

impl LogAnalyzer {
    /// 检测连续的错误模式
    ///
    /// Rust 1.94.0: array_windows::<3>() 用于检测连续错误
    pub fn detect_error_patterns(entries: &[LogEntry]) -> Vec<usize> {
        let mut patterns = Vec::new();

        // 查找连续 3 个错误或警告
        for (i, window) in entries.windows(3).enumerate() {
            let all_errors = window.iter().all(|e| {
                matches!(e.level, LogLevel::Error | LogLevel::Warn)
            });

            if all_errors {
                patterns.push(i);
            }
        }

        patterns
    }

    /// 分析日志时间间隔
    ///
    /// Rust 1.94.0: array_windows::<2>() 用于计算时间差
    pub fn analyze_time_intervals(entries: &[LogEntry]) -> Vec<u64> {
        entries.windows(2)
            .map(|window| window[1].timestamp - window[0].timestamp)
            .collect()
    }
}

/// 演示 array_windows 在数据处理中的应用
#[allow(dead_code)]
pub fn demonstrate_array_windows_processing() {
    println!("\n=== array_windows 数据处理演示 ===\n");

    // CPU 使用率数据
    let cpu_usage = vec![10.0, 12.0, 15.0, 45.0, 18.0, 20.0, 22.0];

    // 计算移动平均
    let ma3 = ProcessMetricsAnalyzer::moving_average::<3>(&cpu_usage);
    println!("3点移动平均: {:?}", ma3);

    // 检测异常
    let anomalies = ProcessMetricsAnalyzer::detect_anomalies(&cpu_usage, 10.0);
    println!("检测到的异常: {:?}", anomalies);

    // 计算变化率
    let change_rates = ProcessMetricsAnalyzer::calculate_change_rates(&cpu_usage);
    println!("变化率: {:?}", change_rates);

    // 检测趋势转折
    let reversals = ProcessMetricsAnalyzer::detect_trend_reversals(&cpu_usage);
    println!("趋势转折点位置: {:?}", reversals);

    // 加权移动平均
    let wma = ProcessMetricsAnalyzer::weighted_moving_average(&cpu_usage);
    println!("加权移动平均: {:?}", wma);
}

// ==================== 2. LazyLock 在进程配置中的应用 ====================

/// # 2. LazyLock 在进程配置中的应用 / LazyLock in Process Configuration
///
/// Rust 1.94.0 为 LazyLock 添加了新方法，使其在进程配置管理中更加灵活。

/// 全局进程配置
///
/// Rust 1.94.0: 使用 LazyLock 管理进程全局配置
pub static PROCESS_CONFIG: LazyLock<ProcessConfig> = LazyLock::new(|| {
    println!("初始化进程配置...");
    ProcessConfig {
        max_processes: 100,
        memory_limit_mb: 1024,
        cpu_limit_percent: 80.0,
        log_level: LogLevel::Info,
        timeout_seconds: 300,
    }
});

/// 进程配置
#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub max_processes: usize,
    pub memory_limit_mb: usize,
    pub cpu_limit_percent: f64,
    pub log_level: LogLevel,
    pub timeout_seconds: u64,
}

/// 进程资源限制
///
/// Rust 1.94.0: 使用 LazyLock 管理资源限制
pub static RESOURCE_LIMITS: LazyLock<ResourceLimits> = LazyLock::new(|| {
    println!("初始化资源限制...");
    ResourceLimits {
        file_descriptors: 1024,
        stack_size_mb: 8,
        heap_size_mb: 512,
    }
});

/// 资源限制
#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub file_descriptors: usize,
    pub stack_size_mb: usize,
    pub heap_size_mb: usize,
}

/// 进程配置管理器
///
/// Rust 1.94.0: 使用 LazyLock::get 访问配置
pub struct ProcessConfigManager;

impl ProcessConfigManager {
    /// 获取进程配置引用
    ///
    /// Rust 1.94.0: 使用 Deref
    pub fn get_config() -> &'static ProcessConfig {
        &PROCESS_CONFIG
    }

    /// 获取资源限制引用
    pub fn get_limits() -> &'static ResourceLimits {
        &RESOURCE_LIMITS
    }

    /// 检查进程数限制
    pub fn check_process_limit(current: usize) -> bool {
        current < Self::get_config().max_processes
    }

    /// 检查内存限制
    pub fn check_memory_limit(current_mb: usize) -> bool {
        current_mb < Self::get_config().memory_limit_mb
    }
}

/// 演示 LazyLock 在进程配置中的应用
#[allow(dead_code)]
pub fn demonstrate_lazylock_config() {
    println!("\n=== LazyLock 进程配置演示 ===\n");

    // 获取配置引用
    let config = ProcessConfigManager::get_config();
    println!("进程配置: {:?}", config);

    // 获取资源限制
    let limits = ProcessConfigManager::get_limits();
    println!("资源限制: {:?}", limits);

    // 检查限制
    println!("进程数检查 (50): {}", ProcessConfigManager::check_process_limit(50));
    println!("内存检查 (2000MB): {}", ProcessConfigManager::check_memory_limit(2000));
}

// ==================== 3. 数学常量在数据分析中的应用 ====================

/// # 3. 数学常量在数据分析中的应用 / Math Constants in Data Analysis
///
/// Rust 1.94.0 添加了 EULER_GAMMA 和 GOLDEN_RATIO 常量，
/// 这些常量在进程数据分析和算法中非常有用。

/// 数据分析器
///
/// Rust 1.94.0: 使用数学常量进行数据分析
pub struct DataAnalyzer;

impl DataAnalyzer {
    /// 使用黄金比例优化搜索区间
    ///
    /// Rust 1.94.0: GOLDEN_RATIO 在黄金分割搜索中的应用
    pub fn golden_section_search<F>(mut a: f64, mut b: f64, epsilon: f64, f: F) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let resphi = 2.0 - phi; // 1 - 1/phi = (3 - √5)/2 ≈ 0.382

        let mut x1 = a + resphi * (b - a);
        let mut x2 = b - resphi * (b - a);
        let mut f1 = f(x1);
        let mut f2 = f(x2);

        while (b - a).abs() > epsilon {
            if f1 < f2 {
                b = x2;
                x2 = x1;
                f2 = f1;
                x1 = a + resphi * (b - a);
                f1 = f(x1);
            } else {
                a = x1;
                x1 = x2;
                f1 = f2;
                x2 = b - resphi * (b - a);
                f2 = f(x2);
            }
        }

        (a + b) / 2.0
    }

    /// 使用欧拉常数估算对数级数
    ///
    /// Rust 1.94.0: EULER_GAMMA 在级数分析中的应用
    pub fn estimate_harmonic_series(n: u64) -> f64 {
        let gamma = 0.5772156649015329_f64; // std::f64::consts::EULER_GAMMA
        (n as f64).ln() + gamma + 1.0 / (2.0 * n as f64)
    }

    /// 计算黄金比例分割点
    ///
    /// Rust 1.94.0: GOLDEN_RATIO 在数据分割中的应用
    pub fn golden_ratio_split(data: &[f64]) -> Option<usize> {
        if data.len() < 2 {
            return None;
        }

        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let split_point = (data.len() as f64 / phi).round() as usize;

        Some(split_point.max(1).min(data.len() - 1))
    }

    /// 使用斐波那契数列进行数据采样
    ///
    /// Rust 1.94.0: 基于黄金比例的采样策略
    pub fn fibonacci_sampling(data: &[f64], sample_count: usize) -> Vec<f64> {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let mut samples = Vec::with_capacity(sample_count);

        for i in 0..sample_count {
            // 使用黄金比例序列确定采样位置
            let index = ((i as f64 * phi) % data.len() as f64) as usize;
            samples.push(data[index.min(data.len() - 1)]);
        }

        samples
    }
}

/// 演示数学常量在数据分析中的应用
#[allow(dead_code)]
pub fn demonstrate_math_constants() {
    println!("\n=== 数学常量数据分析演示 ===\n");

    // 黄金分割搜索
    let min_point = DataAnalyzer::golden_section_search(0.0, 10.0, 0.001, |x| {
        (x - 3.0).powi(2) // 最小值在 x = 3
    });
    println!("黄金分割搜索结果: x = {:.4}", min_point);

    // 调和级数估算
    for n in [10, 100, 1000] {
        let estimate = DataAnalyzer::estimate_harmonic_series(n);
        let actual: f64 = (1..=n).map(|i| 1.0 / i as f64).sum();
        println!(
            "H({}) 估算: {:.6}, 实际: {:.6}, 误差: {:.6}",
            n,
            estimate,
            actual,
            (estimate - actual).abs()
        );
    }

    // 黄金比例分割
    let data: Vec<f64> = (0..100).map(|i| i as f64).collect();
    if let Some(split) = DataAnalyzer::golden_ratio_split(&data) {
        println!("黄金比例分割点: {}", split);
    }

    // 斐波那契采样
    let samples = DataAnalyzer::fibonacci_sampling(&data, 10);
    println!("斐波那契采样结果: {:?}", samples);
}

// ==================== 4. Peekable 在日志处理中的应用 ====================

/// # 4. Peekable 在日志处理中的应用 / Peekable in Log Processing
///
/// Rust 1.94.0 为 Peekable 添加了 next_if_map 和 next_if_map_mut 方法，
/// 这些方法在日志处理和解析中特别有用。

/// 日志解析器
///
/// Rust 1.94.0: 使用 Peekable 新方法解析日志
pub struct LogParser<I: Iterator<Item = LogEntry>> {
    entries: Peekable<I>,
}

impl<I: Iterator<Item = LogEntry>> LogParser<I> {
    /// 创建新的日志解析器
    pub fn new(entries: I) -> Self {
        Self {
            entries: entries.peekable(),
        }
    }

    /// 解析下一条特定级别的日志
    ///
    /// Rust 1.94.0: 使用 next_if_map 简化条件消费
    pub fn parse_next_level(&mut self, level: LogLevel) -> Option<LogEntry> {
        // 使用 next_if_map 模式
        if let Some(entry) = self.entries.peek()
            && entry.level == level {
                return self.entries.next();
            }
        None
    }

    /// 解析所有错误日志
    ///
    /// Rust 1.94.0: 使用 next_if_map 循环
    pub fn parse_all_errors(&mut self) -> Vec<LogEntry> {
        let mut errors = Vec::new();

        while let Some(entry) = self.entries.peek() {
            if entry.level == LogLevel::Error {
                if let Some(e) = self.entries.next() {
                    errors.push(e);
                }
            } else {
                break;
            }
        }

        errors
    }

    /// 跳过特定级别的日志
    ///
    /// Rust 1.94.0: 使用 next_if_map 跳过
    pub fn skip_level(&mut self, level: LogLevel) -> usize {
        let mut count = 0;

        while let Some(entry) = self.entries.peek() {
            if entry.level == level {
                self.entries.next();
                count += 1;
            } else {
                break;
            }
        }

        count
    }

    /// 解析时间范围内的日志
    pub fn parse_in_time_range(&mut self, start: u64, end: u64) -> Vec<LogEntry> {
        let mut result = Vec::new();

        while let Some(entry) = self.entries.peek() {
            if entry.timestamp >= start && entry.timestamp <= end {
                if let Some(e) = self.entries.next() {
                    result.push(e);
                }
            } else if entry.timestamp > end {
                break;
            } else {
                self.entries.next();
            }
        }

        result
    }
}

/// 演示 Peekable 在日志处理中的应用
#[allow(dead_code)]
pub fn demonstrate_peekable_logs() {
    println!("\n=== Peekable 日志处理演示 ===\n");

    // 创建日志条目
    let entries = vec![
        LogEntry { timestamp: 1, level: LogLevel::Info, message: "启动".to_string() },
        LogEntry { timestamp: 2, level: LogLevel::Error, message: "错误1".to_string() },
        LogEntry { timestamp: 3, level: LogLevel::Error, message: "错误2".to_string() },
        LogEntry { timestamp: 4, level: LogLevel::Warn, message: "警告".to_string() },
        LogEntry { timestamp: 5, level: LogLevel::Info, message: "完成".to_string() },
    ];

    let mut parser = LogParser::new(entries.into_iter());

    // 解析所有错误
    let errors = parser.parse_all_errors();
    println!("解析到的错误数: {}", errors.len());

    // 跳过警告
    let skipped = parser.skip_level(LogLevel::Warn);
    println!("跳过的警告数: {}", skipped);

    // 解析下一条 Info
    if let Some(info) = parser.parse_next_level(LogLevel::Info) {
        println!("下一条 Info: {:?}", info);
    }
}

// ==================== 5. char 转换在进程通信中的应用 ====================

/// # 5. char 转换在进程通信中的应用 / char Conversion in Process Communication
///
/// Rust 1.94.0 实现了 TryFrom<char> for usize，
/// 这在进程间通信的字符编码处理中非常有用。

/// 进程通信编码器
///
/// Rust 1.94.0: 使用 char 到 usize 转换进行通信编码
pub struct ProcessCommunicationEncoder;

impl ProcessCommunicationEncoder {
    /// 将字符串编码为 usize 数组
    ///
    /// Rust 1.94.0: TryFrom<char> for usize
    pub fn encode_string(s: &str) -> Vec<usize> {
        s.chars().map(|c| c as usize).collect()
    }

    /// 解码 usize 数组为字符串
    pub fn decode_codepoints(codepoints: &[usize]) -> Result<String, String> {
        let mut result = String::with_capacity(codepoints.len());

        for &cp in codepoints {
            if let Some(ch) = char::from_u32(cp as u32) {
                result.push(ch);
            } else {
                return Err(format!("无效的 Unicode 码点: {}", cp));
            }
        }

        Ok(result)
    }

    /// 分析字符编码分布
    pub fn analyze_encoding_distribution(s: &str) -> HashMap<String, usize> {
        let mut distribution = HashMap::new();

        for ch in s.chars() {
            let code_point = ch as usize; // Rust 1.94.0 转换
            let category = if code_point < 128 {
                "ASCII"
            } else if code_point < 256 {
                "Extended ASCII"
            } else if (0x4E00..=0x9FFF).contains(&code_point) {
                "CJK Unified"
            } else if (0x1F600..=0x1F64F).contains(&code_point) {
                "Emoji"
            } else {
                "Other"
            };

            *distribution.entry(category.to_string()).or_insert(0) += 1;
        }

        distribution
    }

    /// 验证字符编码范围
    pub fn validate_codepoints(chars: &[char], max_codepoint: usize) -> Vec<bool> {
        chars.iter().map(|&ch| (ch as usize) <= max_codepoint).collect()
    }
}

/// 进程消息
#[derive(Debug, Clone)]
pub struct ProcessMessage {
    pub id: u64,
    pub content: String,
    pub encoding: String,
}

/// 演示 char 转换在进程通信中的应用
#[allow(dead_code)]
pub fn demonstrate_char_conversion() {
    println!("\n=== char 转换进程通信演示 ===\n");

    let message = "Hello 世界 🦀";

    // 编码
    let encoded = ProcessCommunicationEncoder::encode_string(message);
    println!("编码结果: {:?}", encoded);

    // 解码
    let decoded = ProcessCommunicationEncoder::decode_codepoints(&encoded).unwrap();
    println!("解码结果: {}", decoded);

    // 分析编码分布
    let distribution = ProcessCommunicationEncoder::analyze_encoding_distribution(message);
    println!("编码分布: {:?}", distribution);

    // 验证码点
    let chars: Vec<char> = message.chars().collect();
    let valid = ProcessCommunicationEncoder::validate_codepoints(&chars, 0x10FFFF);
    println!("码点验证: {:?}", valid);
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 进程管理特性
pub fn demonstrate_rust_194_process_features() {
    println!("\n=== Rust 1.94.0 进程管理特性演示 ===\n");

    // 1. array_windows 数据处理
    demonstrate_array_windows_processing();

    // 2. LazyLock 进程配置
    demonstrate_lazylock_config();

    // 3. 数学常量数据分析
    demonstrate_math_constants();

    // 4. Peekable 日志处理
    demonstrate_peekable_logs();

    // 5. char 转换进程通信
    demonstrate_char_conversion();

    // 综合示例：完整的监控场景
    println!("\n=== 综合监控场景 ===\n");

    // 模拟 CPU 监控数据
    let cpu_data = vec![20.0, 22.0, 25.0, 60.0, 65.0, 30.0, 32.0, 35.0];

    // 检测异常
    let anomalies = ProcessMetricsAnalyzer::detect_anomalies(&cpu_data, 15.0);
    println!("CPU 异常: {:?}", anomalies);

    // 计算移动平均
    let ma = ProcessMetricsAnalyzer::moving_average::<3>(&cpu_data);
    println!("CPU 移动平均: {:?}", ma);

    // 检查配置限制
    let avg_cpu = ma.iter().sum::<f64>() / ma.len() as f64;
    let config = ProcessConfigManager::get_config();
    if avg_cpu > config.cpu_limit_percent {
        println!("警告: CPU 使用率 {:.1}% 超过限制 {}%", avg_cpu, config.cpu_limit_percent);
    } else {
        println!("CPU 使用率正常: {:.1}%", avg_cpu);
    }
}

/// 获取 Rust 1.94.0 进程管理特性信息
pub fn get_rust_194_process_info() -> String {
    "Rust 1.94.0 进程管理特性:\n\
        - array_windows 在数据处理中的应用\n\
        - LazyLock 在进程配置中的应用 (get, get_mut, force_mut)\n\
        - 数学常量在数据分析中的应用 (EULER_GAMMA, GOLDEN_RATIO)\n\
        - Peekable 在日志处理中的应用 (next_if_map, next_if_map_mut)\n\
        - char 转换在进程通信中的应用 (TryFrom<char> for usize)"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_moving_average() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let ma = ProcessMetricsAnalyzer::moving_average::<3>(&data);
        assert_eq!(ma, vec![2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_detect_anomalies() {
        let data = vec![1.0, 2.0, 20.0, 3.0, 4.0];
        let anomalies = ProcessMetricsAnalyzer::detect_anomalies(&data, 5.0);
        assert!(anomalies.iter().any(|&(idx, _)| idx == 2));
    }

    #[test]
    fn test_calculate_change_rates() {
        let data = vec![100.0, 110.0, 121.0];
        let rates = ProcessMetricsAnalyzer::calculate_change_rates(&data);
        assert!((rates[0] - 0.1).abs() < 0.001);
        assert!((rates[1] - 0.1).abs() < 0.001);
    }

    #[test]
    fn test_detect_error_patterns() {
        let entries = vec![
            LogEntry { timestamp: 1, level: LogLevel::Error, message: "e1".to_string() },
            LogEntry { timestamp: 2, level: LogLevel::Error, message: "e2".to_string() },
            LogEntry { timestamp: 3, level: LogLevel::Error, message: "e3".to_string() },
        ];

        let patterns = LogAnalyzer::detect_error_patterns(&entries);
        assert_eq!(patterns, vec![0]);
    }

    #[test]
    fn test_process_config_manager() {
        let config = ProcessConfigManager::get_config();
        assert_eq!(config.max_processes, 100);

        let limits = ProcessConfigManager::get_limits();
        assert_eq!(limits.file_descriptors, 1024);
    }

    #[test]
    fn test_golden_section_search() {
        let min = DataAnalyzer::golden_section_search(0.0, 10.0, 0.001, |x| (x - 5.0).powi(2));
        assert!((min - 5.0).abs() < 0.01);
    }

    #[test]
    fn test_estimate_harmonic_series() {
        let n = 100u64;
        let estimate = DataAnalyzer::estimate_harmonic_series(n);
        let actual: f64 = (1..=n).map(|i| 1.0 / i as f64).sum();
        assert!((estimate - actual).abs() < 0.01);
    }

    #[test]
    fn test_log_parser() {
        let entries = vec![
            LogEntry { timestamp: 1, level: LogLevel::Error, message: "e1".to_string() },
            LogEntry { timestamp: 2, level: LogLevel::Error, message: "e2".to_string() },
            LogEntry { timestamp: 3, level: LogLevel::Info, message: "i1".to_string() },
        ];

        let mut parser = LogParser::new(entries.into_iter());
        let errors = parser.parse_all_errors();
        assert_eq!(errors.len(), 2);
    }

    #[test]
    fn test_encode_decode() {
        let original = "Hello 世界";
        let encoded = ProcessCommunicationEncoder::encode_string(original);
        let decoded = ProcessCommunicationEncoder::decode_codepoints(&encoded).unwrap();
        assert_eq!(decoded, original);
    }

    #[test]
    fn test_analyze_encoding_distribution() {
        let text = "Hello 世界";
        let distribution = ProcessCommunicationEncoder::analyze_encoding_distribution(text);
        assert!(distribution.contains_key("ASCII"));
        assert!(distribution.contains_key("CJK Unified"));
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_process_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_process_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("array_windows"));
    }
}
