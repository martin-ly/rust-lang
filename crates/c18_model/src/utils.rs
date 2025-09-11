//! 通用工具函数
//! 
//! 本模块提供了各种通用工具函数，包括数学计算、数据处理、
//! 错误处理、日志记录等。使用Rust的类型安全特性确保工具的可靠性。

use std::collections::HashMap;
use std::f64;
use std::fmt;

/// 数学工具
pub struct MathUtils;

impl MathUtils {
    /// 计算阶乘
    pub fn factorial(n: usize) -> usize {
        match n {
            0 | 1 => 1,
            _ => (2..=n).fold(1, |acc, x| acc * x),
        }
    }

    /// 计算组合数 C(n, k)
    pub fn combination(n: usize, k: usize) -> usize {
        if k > n {
            return 0;
        }
        if k == 0 || k == n {
            return 1;
        }
        
        let k = k.min(n - k);
        let mut result = 1;
        for i in 0..k {
            result = result * (n - i) / (i + 1);
        }
        result
    }

    /// 计算排列数 P(n, k)
    pub fn permutation(n: usize, k: usize) -> usize {
        if k > n {
            return 0;
        }
        (n - k + 1..=n).fold(1, |acc, x| acc * x)
    }

    /// 计算最大公约数
    pub fn gcd(mut a: usize, mut b: usize) -> usize {
        while b != 0 {
            let temp = b;
            b = a % b;
            a = temp;
        }
        a
    }

    /// 计算最小公倍数
    pub fn lcm(a: usize, b: usize) -> usize {
        a * b / Self::gcd(a, b)
    }

    /// 判断是否为质数
    pub fn is_prime(n: usize) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        let sqrt_n = (n as f64).sqrt() as usize;
        for i in (3..=sqrt_n).step_by(2) {
            if n % i == 0 {
                return false;
            }
        }
        true
    }

    /// 生成质数列表
    pub fn generate_primes(limit: usize) -> Vec<usize> {
        let mut primes = Vec::new();
        for i in 2..=limit {
            if Self::is_prime(i) {
                primes.push(i);
            }
        }
        primes
    }

    /// 计算斐波那契数列
    pub fn fibonacci(n: usize) -> usize {
        if n <= 1 {
            return n;
        }
        
        let mut a = 0;
        let mut b = 1;
        for _ in 2..=n {
            let temp = a + b;
            a = b;
            b = temp;
        }
        b
    }

    /// 计算平方根（牛顿法）
    pub fn sqrt(x: f64) -> f64 {
        if x < 0.0 {
            return f64::NAN;
        }
        if x == 0.0 {
            return 0.0;
        }
        
        let mut guess = x / 2.0;
        for _ in 0..10 {
            guess = (guess + x / guess) / 2.0;
        }
        guess
    }

    /// 计算幂
    pub fn power(base: f64, exponent: f64) -> f64 {
        base.powf(exponent)
    }

    /// 计算对数
    pub fn logarithm(x: f64, base: f64) -> f64 {
        x.ln() / base.ln()
    }
}

/// 统计工具
pub struct StatisticsUtils;

impl StatisticsUtils {
    /// 计算均值
    pub fn mean(data: &[f64]) -> f64 {
        if data.is_empty() {
            return 0.0;
        }
        data.iter().sum::<f64>() / data.len() as f64
    }

    /// 计算中位数
    pub fn median(data: &mut [f64]) -> f64 {
        if data.is_empty() {
            return 0.0;
        }
        
        data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let n = data.len();
        
        if n % 2 == 0 {
            (data[n / 2 - 1] + data[n / 2]) / 2.0
        } else {
            data[n / 2]
        }
    }

    /// 计算众数
    pub fn mode(data: &[f64]) -> Option<f64> {
        if data.is_empty() {
            return None;
        }
        
        let mut counts = HashMap::new();
        for &value in data {
            let key = format!("{:.6}", value);
            *counts.entry(key).or_insert(0) += 1;
        }
        
        let max_count = counts.values().max()?;
        for (key, &count) in &counts {
            if count == *max_count {
                return key.parse().ok();
            }
        }
        None
    }

    /// 计算方差
    pub fn variance(data: &[f64]) -> f64 {
        if data.len() <= 1 {
            return 0.0;
        }
        
        let mean = Self::mean(data);
        let sum_squared_diff: f64 = data.iter()
            .map(|&x| (x - mean).powi(2))
            .sum();
        sum_squared_diff / (data.len() - 1) as f64
    }

    /// 计算标准差
    pub fn standard_deviation(data: &[f64]) -> f64 {
        Self::variance(data).sqrt()
    }

    /// 计算偏度
    pub fn skewness(data: &[f64]) -> f64 {
        if data.len() <= 2 {
            return 0.0;
        }
        
        let mean = Self::mean(data);
        let std_dev = Self::standard_deviation(data);
        
        if std_dev == 0.0 {
            return 0.0;
        }
        
        let n = data.len() as f64;
        let sum_cubed_diff: f64 = data.iter()
            .map(|&x| ((x - mean) / std_dev).powi(3))
            .sum();
        
        sum_cubed_diff / n
    }

    /// 计算峰度
    pub fn kurtosis(data: &[f64]) -> f64 {
        if data.len() <= 3 {
            return 0.0;
        }
        
        let mean = Self::mean(data);
        let std_dev = Self::standard_deviation(data);
        
        if std_dev == 0.0 {
            return 0.0;
        }
        
        let n = data.len() as f64;
        let sum_fourth_diff: f64 = data.iter()
            .map(|&x| ((x - mean) / std_dev).powi(4))
            .sum();
        
        sum_fourth_diff / n - 3.0
    }

    /// 计算相关系数
    pub fn correlation(x: &[f64], y: &[f64]) -> f64 {
        if x.len() != y.len() || x.is_empty() {
            return 0.0;
        }
        
        let mean_x = Self::mean(x);
        let mean_y = Self::mean(y);
        
        let numerator: f64 = x.iter().zip(y.iter())
            .map(|(&xi, &yi)| (xi - mean_x) * (yi - mean_y))
            .sum();
        
        let sum_sq_x: f64 = x.iter().map(|&xi| (xi - mean_x).powi(2)).sum();
        let sum_sq_y: f64 = y.iter().map(|&yi| (yi - mean_y).powi(2)).sum();
        
        let denominator = (sum_sq_x * sum_sq_y).sqrt();
        
        if denominator == 0.0 {
            0.0
        } else {
            numerator / denominator
        }
    }

    /// 计算百分位数
    pub fn percentile(data: &mut [f64], percentile: f64) -> f64 {
        if data.is_empty() {
            return 0.0;
        }
        
        data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let n = data.len();
        let index = (percentile / 100.0) * (n - 1) as f64;
        
        if index.fract() == 0.0 {
            data[index as usize]
        } else {
            let lower = data[index.floor() as usize];
            let upper = data[index.ceil() as usize];
            lower + (upper - lower) * index.fract()
        }
    }

    /// 计算四分位数
    pub fn quartiles(data: &mut [f64]) -> (f64, f64, f64) {
        let q1 = Self::percentile(data, 25.0);
        let q2 = Self::percentile(data, 50.0);
        let q3 = Self::percentile(data, 75.0);
        (q1, q2, q3)
    }

    /// 计算四分位距
    pub fn interquartile_range(data: &mut [f64]) -> f64 {
        let (q1, _, q3) = Self::quartiles(data);
        q3 - q1
    }
}

/// 数据处理工具
pub struct DataUtils;

impl DataUtils {
    /// 数据标准化（Z-score）
    pub fn standardize(data: &[f64]) -> Vec<f64> {
        if data.is_empty() {
            return Vec::new();
        }
        
        let mean = StatisticsUtils::mean(data);
        let std_dev = StatisticsUtils::standard_deviation(data);
        
        if std_dev == 0.0 {
            return vec![0.0; data.len()];
        }
        
        data.iter().map(|&x| (x - mean) / std_dev).collect()
    }

    /// 数据归一化（Min-Max）
    pub fn normalize(data: &[f64]) -> Vec<f64> {
        if data.is_empty() {
            return Vec::new();
        }
        
        let min_val = data.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_val = data.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        
        if max_val == min_val {
            return vec![0.5; data.len()];
        }
        
        data.iter().map(|&x| (x - min_val) / (max_val - min_val)).collect()
    }

    /// 数据平滑（移动平均）
    pub fn smooth(data: &[f64], window_size: usize) -> Vec<f64> {
        if data.is_empty() || window_size == 0 {
            return Vec::new();
        }
        
        let mut smoothed = Vec::new();
        for i in 0..data.len() {
            let start = if i >= window_size { i - window_size + 1 } else { 0 };
            let end = i + 1;
            let window = &data[start..end];
            smoothed.push(StatisticsUtils::mean(window));
        }
        smoothed
    }

    /// 数据差分
    pub fn difference(data: &[f64]) -> Vec<f64> {
        if data.len() <= 1 {
            return Vec::new();
        }
        
        data.windows(2).map(|w| w[1] - w[0]).collect()
    }

    /// 数据去重
    pub fn deduplicate(data: &[f64]) -> Vec<f64> {
        let mut unique = Vec::new();
        let mut seen = std::collections::HashSet::new();
        
        for &value in data {
            let key = format!("{:.6}", value);
            if seen.insert(key) {
                unique.push(value);
            }
        }
        
        unique
    }

    /// 数据分箱
    pub fn bin_data(data: &[f64], num_bins: usize) -> Vec<Vec<f64>> {
        if data.is_empty() || num_bins == 0 {
            return Vec::new();
        }
        
        let min_val = data.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_val = data.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        
        if max_val == min_val {
            return vec![data.to_vec()];
        }
        
        let bin_width = (max_val - min_val) / num_bins as f64;
        let mut bins = vec![Vec::new(); num_bins];
        
        for &value in data {
            let bin_index = ((value - min_val) / bin_width).floor() as usize;
            let bin_index = bin_index.min(num_bins - 1);
            bins[bin_index].push(value);
        }
        
        bins
    }
}

/// 错误处理工具
#[derive(Debug, Clone)]
pub enum ModelError {
    /// 数学错误
    MathError(String),
    /// 数据错误
    DataError(String),
    /// 配置错误
    ConfigError(String),
    /// 计算错误
    ComputationError(String),
    /// 验证错误
    ValidationError(String),
}

impl fmt::Display for ModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModelError::MathError(msg) => write!(f, "数学错误: {}", msg),
            ModelError::DataError(msg) => write!(f, "数据错误: {}", msg),
            ModelError::ConfigError(msg) => write!(f, "配置错误: {}", msg),
            ModelError::ComputationError(msg) => write!(f, "计算错误: {}", msg),
            ModelError::ValidationError(msg) => write!(f, "验证错误: {}", msg),
        }
    }
}

impl std::error::Error for ModelError {}

/// 验证工具
pub struct ValidationUtils;

impl ValidationUtils {
    /// 验证数值范围
    pub fn validate_range(value: f64, min: f64, max: f64) -> Result<(), ModelError> {
        if value < min || value > max {
            Err(ModelError::ValidationError(
                format!("值 {} 超出范围 [{}, {}]", value, min, max)
            ))
        } else {
            Ok(())
        }
    }

    /// 验证非负值
    pub fn validate_non_negative(value: f64) -> Result<(), ModelError> {
        if value < 0.0 {
            Err(ModelError::ValidationError(
                format!("值 {} 不能为负数", value)
            ))
        } else {
            Ok(())
        }
    }

    /// 验证正值
    pub fn validate_positive(value: f64) -> Result<(), ModelError> {
        if value <= 0.0 {
            Err(ModelError::ValidationError(
                format!("值 {} 必须为正数", value)
            ))
        } else {
            Ok(())
        }
    }

    /// 验证概率值
    pub fn validate_probability(value: f64) -> Result<(), ModelError> {
        if value < 0.0 || value > 1.0 {
            Err(ModelError::ValidationError(
                format!("概率值 {} 必须在 [0, 1] 范围内", value)
            ))
        } else {
            Ok(())
        }
    }

    /// 验证数据长度
    pub fn validate_data_length(data: &[f64], expected_length: usize) -> Result<(), ModelError> {
        if data.len() != expected_length {
            Err(ModelError::DataError(
                format!("数据长度 {} 与期望长度 {} 不匹配", data.len(), expected_length)
            ))
        } else {
            Ok(())
        }
    }

    /// 验证数据非空
    pub fn validate_non_empty(data: &[f64]) -> Result<(), ModelError> {
        if data.is_empty() {
            Err(ModelError::DataError("数据不能为空".to_string()))
        } else {
            Ok(())
        }
    }

    /// 验证矩阵维度
    pub fn validate_matrix_dimensions(matrix: &[Vec<f64>]) -> Result<(), ModelError> {
        if matrix.is_empty() {
            return Err(ModelError::DataError("矩阵不能为空".to_string()));
        }
        
        let expected_cols = matrix[0].len();
        for (i, row) in matrix.iter().enumerate() {
            if row.len() != expected_cols {
                return Err(ModelError::DataError(
                    format!("矩阵第 {} 行长度 {} 与期望长度 {} 不匹配", i, row.len(), expected_cols)
                ));
            }
        }
        
        Ok(())
    }
}

/// 日志工具
pub struct Logger {
    level: LogLevel,
    messages: Vec<LogMessage>,
}

/// 日志级别
#[derive(Debug, Clone, PartialEq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

/// 日志消息
#[derive(Debug, Clone)]
pub struct LogMessage {
    pub level: LogLevel,
    pub message: String,
    pub timestamp: std::time::SystemTime,
}

impl Logger {
    /// 创建新的日志器
    pub fn new(level: LogLevel) -> Self {
        Self {
            level,
            messages: Vec::new(),
        }
    }

    /// 记录调试消息
    pub fn debug(&mut self, message: &str) {
        self.log(LogLevel::Debug, message);
    }

    /// 记录信息消息
    pub fn info(&mut self, message: &str) {
        self.log(LogLevel::Info, message);
    }

    /// 记录警告消息
    pub fn warn(&mut self, message: &str) {
        self.log(LogLevel::Warn, message);
    }

    /// 记录错误消息
    pub fn error(&mut self, message: &str) {
        self.log(LogLevel::Error, message);
    }

    /// 记录日志
    fn log(&mut self, level: LogLevel, message: &str) {
        if self.should_log(&level) {
            let log_message = LogMessage {
                level: level.clone(),
                message: message.to_string(),
                timestamp: std::time::SystemTime::now(),
            };
            self.messages.push(log_message);
        }
    }

    /// 判断是否应该记录日志
    fn should_log(&self, level: &LogLevel) -> bool {
        match (&self.level, level) {
            (LogLevel::Debug, _) => true,
            (LogLevel::Info, LogLevel::Info | LogLevel::Warn | LogLevel::Error) => true,
            (LogLevel::Warn, LogLevel::Warn | LogLevel::Error) => true,
            (LogLevel::Error, LogLevel::Error) => true,
            _ => false,
        }
    }

    /// 获取所有日志消息
    pub fn get_messages(&self) -> &[LogMessage] {
        &self.messages
    }

    /// 清空日志
    pub fn clear(&mut self) {
        self.messages.clear();
    }
}

impl Default for Logger {
    fn default() -> Self {
        Self::new(LogLevel::Info)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_math_utils() {
        assert_eq!(MathUtils::factorial(5), 120);
        assert_eq!(MathUtils::combination(5, 2), 10);
        assert_eq!(MathUtils::permutation(5, 2), 20);
        assert_eq!(MathUtils::gcd(12, 8), 4);
        assert_eq!(MathUtils::lcm(12, 8), 24);
        assert!(MathUtils::is_prime(17));
        assert!(!MathUtils::is_prime(15));
        assert_eq!(MathUtils::fibonacci(10), 55);
    }

    #[test]
    fn test_statistics_utils() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert_eq!(StatisticsUtils::mean(&data), 3.0);
        assert_eq!(StatisticsUtils::variance(&data), 2.5);
        assert_eq!(StatisticsUtils::standard_deviation(&data), 2.5_f64.sqrt());
    }

    #[test]
    fn test_data_utils() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let standardized = DataUtils::standardize(&data);
        assert_eq!(standardized.len(), data.len());
        
        let normalized = DataUtils::normalize(&data);
        assert_eq!(normalized.len(), data.len());
        assert_eq!(normalized[0], 0.0);
        assert_eq!(normalized[4], 1.0);
    }

    #[test]
    fn test_validation_utils() {
        assert!(ValidationUtils::validate_range(5.0, 0.0, 10.0).is_ok());
        assert!(ValidationUtils::validate_range(15.0, 0.0, 10.0).is_err());
        assert!(ValidationUtils::validate_positive(5.0).is_ok());
        assert!(ValidationUtils::validate_positive(-5.0).is_err());
        assert!(ValidationUtils::validate_probability(0.5).is_ok());
        assert!(ValidationUtils::validate_probability(1.5).is_err());
    }

    #[test]
    fn test_logger() {
        let mut logger = Logger::new(LogLevel::Info);
        logger.info("测试消息");
        logger.debug("调试消息");
        logger.warn("警告消息");
        logger.error("错误消息");
        
        let messages = logger.get_messages();
        assert_eq!(messages.len(), 3); // debug消息被过滤
    }
}
