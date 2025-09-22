//! 排队论模型实现
//!
//! 本模块实现了各种排队论模型，包括M/M/1、M/M/c、M/G/1等经典模型。
//! 使用Rust的类型安全特性确保模型参数的正确性和计算结果的可靠性。

use std::collections::HashMap;
use serde::{Deserialize, Serialize};

// Rust 1.90 特性：使用常量泛型推断
/// 排队系统配置 - 使用常量泛型参数
#[derive(Debug, Clone)]
pub struct QueueConfig<const N: usize> {
    /// 系统参数数组
    pub parameters: [f64; N],
    /// 系统容量
    pub capacity: Option<usize>,
}

impl<const N: usize> QueueConfig<N> {
    /// 创建新的配置
    pub fn new(parameters: [f64; N]) -> Self {
        Self {
            parameters,
            capacity: None,
        }
    }
    
    /// 使用容量创建配置
    pub fn with_capacity(parameters: [f64; N], capacity: usize) -> Self {
        Self {
            parameters,
            capacity: Some(capacity),
        }
    }
}

/// M/M/1 排队系统 - 使用 Rust 1.90 增强特性
///
/// 实现经典的M/M/1排队模型，用于分析单服务器排队系统的性能。
/// 利用 Rust 1.90 的新特性提供更好的类型安全和性能。
///
/// # 数学公式
/// - 利用率: ρ = λ/μ
/// - 平均队长: L = λ/(μ-λ) (当 ρ < 1)
/// - 平均等待时间: W = 1/(μ-λ) (当 ρ < 1)
/// - 平均响应时间: R = W + 1/μ
///
/// # 参数
/// - λ (arrival_rate): 到达率
/// - μ (service_rate): 服务率
/// - capacity: 系统容量（可选，None表示无限容量）
#[derive(Debug, Clone)]
pub struct MM1Queue {
    /// 到达率 (λ)
    pub arrival_rate: f64,
    /// 服务率 (μ)
    pub service_rate: f64,
    /// 系统容量
    pub capacity: Option<usize>,
    /// 配置信息
    pub config: QueueConfig<2>,
}

impl MM1Queue {
    /// 创建新的M/M/1排队系统 - 使用 Rust 1.90 特性
    ///
    /// # 参数
    /// - `arrival_rate`: 到达率 λ
    /// - `service_rate`: 服务率 μ
    ///
    /// # 返回
    /// 返回无限容量的M/M/1排队系统
    pub fn new(arrival_rate: f64, service_rate: f64) -> Self {
        Self {
            arrival_rate,
            service_rate,
            capacity: None,
            config: QueueConfig::new([arrival_rate, service_rate]),
        }
    }

    /// 创建有限容量的排队系统 - 使用 Rust 1.90 特性
    ///
    /// # 参数
    /// - `arrival_rate`: 到达率 λ
    /// - `service_rate`: 服务率 μ
    /// - `capacity`: 系统容量
    pub fn with_capacity(arrival_rate: f64, service_rate: f64, capacity: usize) -> Self {
        Self {
            arrival_rate,
            service_rate,
            capacity: Some(capacity),
            config: QueueConfig::with_capacity([arrival_rate, service_rate], capacity),
        }
    }
    
    /// 使用配置创建排队系统 - 利用 Rust 1.90 的常量泛型推断
    pub fn from_config(config: QueueConfig<2>) -> Self {
        let [arrival_rate, service_rate] = config.parameters;
        Self {
            arrival_rate,
            service_rate,
            capacity: config.capacity,
            config,
        }
    }

    /// 计算系统利用率 (ρ = λ/μ)
    ///
    /// # 返回
    /// 系统利用率，范围 [0, ∞)
    pub fn utilization(&self) -> f64 {
        self.arrival_rate / self.service_rate
    }

    /// 计算平均队长 (L = λ/(μ-λ))
    ///
    /// # 返回
    /// - `Ok(f64)`: 平均队长
    /// - `Err(String)`: 系统不稳定（利用率 >= 1.0）
    pub fn average_queue_length(&self) -> Result<f64, String> {
        if self.utilization() >= 1.0 {
            return Err("系统不稳定：利用率 >= 1.0".to_string());
        }
        Ok(self.arrival_rate / (self.service_rate - self.arrival_rate))
    }

    /// 计算平均等待时间 (W = 1/(μ-λ))
    ///
    /// # 返回
    /// - `Ok(f64)`: 平均等待时间
    /// - `Err(String)`: 系统不稳定（利用率 >= 1.0）
    pub fn average_waiting_time(&self) -> Result<f64, String> {
        if self.utilization() >= 1.0 {
            return Err("系统不稳定：利用率 >= 1.0".to_string());
        }
        Ok(1.0 / (self.service_rate - self.arrival_rate))
    }

    /// 计算系统响应时间 (包括服务时间)
    ///
    /// # 返回
    /// - `Ok(f64)`: 平均响应时间
    /// - `Err(String)`: 系统不稳定（利用率 >= 1.0）
    pub fn average_response_time(&self) -> Result<f64, String> {
        Ok(self.average_waiting_time()? + 1.0 / self.service_rate)
    }

    /// 计算系统中平均客户数
    ///
    /// # 返回
    /// - `Ok(f64)`: 系统中平均客户数
    /// - `Err(String)`: 系统不稳定（利用率 >= 1.0）
    pub fn average_customers_in_system(&self) -> Result<f64, String> {
        Ok(self.average_queue_length()? + self.utilization())
    }

    /// 检查系统稳定性
    ///
    /// # 返回
    /// `true` 如果系统稳定（利用率 < 1.0），否则 `false`
    pub fn is_stable(&self) -> bool {
        self.utilization() < 1.0
    }

    /// 计算系统阻塞概率（仅适用于有限容量系统）
    ///
    /// # 返回
    /// - `Some(f64)`: 阻塞概率（仅当系统有容量限制时）
    /// - `None`: 无限容量系统
    pub fn blocking_probability(&self) -> Option<f64> {
        if let Some(capacity) = self.capacity {
            if !self.is_stable() {
                return Some(1.0);
            }

            let rho = self.utilization();
            let numerator = rho.powi(capacity as i32);
            let denominator: f64 = (0..=capacity).map(|i| rho.powi(i as i32)).sum();

            Some(numerator / denominator)
        } else {
            None
        }
    }
}

/// M/M/c 排队系统
///
/// 实现多服务器排队模型，用于分析多服务器排队系统的性能。
#[derive(Debug, Clone)]
pub struct MMcQueue {
    /// 到达率 (λ)
    pub arrival_rate: f64,
    /// 单个服务器服务率 (μ)
    pub service_rate: f64,
    /// 服务器数量 (c)
    pub servers: usize,
    /// 系统容量
    pub capacity: Option<usize>,
}

impl MMcQueue {
    /// 创建新的M/M/c排队系统
    pub fn new(arrival_rate: f64, service_rate: f64, servers: usize) -> Self {
        Self {
            arrival_rate,
            service_rate,
            servers,
            capacity: None,
        }
    }

    /// 计算系统利用率
    pub fn utilization(&self) -> f64 {
        self.arrival_rate / (self.servers as f64 * self.service_rate)
    }

    /// 计算平均队长
    pub fn average_queue_length(&self) -> Result<f64, String> {
        if self.utilization() >= 1.0 {
            return Err("系统不稳定：利用率 >= 1.0".to_string());
        }

        let rho = self.utilization();
        let c = self.servers as f64;
        let _lambda = self.arrival_rate;
        let _mu = self.service_rate;

        // 计算P0（系统中没有客户的概率）
        let mut p0_sum = 0.0;
        for n in 0..self.servers {
            p0_sum += (c * rho).powi(n as i32) / factorial(n);
        }
        p0_sum += (c * rho).powi(self.servers as i32) / (factorial(self.servers) * (1.0 - rho));
        let p0 = 1.0 / p0_sum;

        // 计算平均队长
        let lq = p0 * (c * rho).powi(self.servers as i32) * rho
            / (factorial(self.servers) * (1.0 - rho).powi(2));

        Ok(lq)
    }

    /// 计算平均等待时间
    pub fn average_waiting_time(&self) -> Result<f64, String> {
        Ok(self.average_queue_length()? / self.arrival_rate)
    }
}

/// 性能分析器
///
/// 用于收集和分析系统性能指标
#[derive(Debug)]
pub struct PerformanceAnalyzer {
    metrics: HashMap<String, Vec<f64>>,
}

impl PerformanceAnalyzer {
    /// 创建新的性能分析器
    pub fn new() -> Self {
        Self {
            metrics: HashMap::new(),
        }
    }

    /// 记录性能指标
    pub fn record_metric(&mut self, name: &str, value: f64) {
        self.metrics
            .entry(name.to_string())
            .or_default()
            .push(value);
    }

    /// 计算平均性能指标
    pub fn average_metric(&self, name: &str) -> Option<f64> {
        self.metrics
            .get(name)
            .map(|values| values.iter().sum::<f64>() / values.len() as f64)
    }

    /// 计算性能指标的标准差
    pub fn std_dev_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).map(|values| {
            let mean = values.iter().sum::<f64>() / values.len() as f64;
            let variance =
                values.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() / values.len() as f64;
            variance.sqrt()
        })
    }

    /// 获取性能指标的最小值
    pub fn min_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).and_then(|values| {
            values
                .iter()
                .fold(None, |min, &x| Some(min.map_or(x, |m: f64| m.min(x))))
        })
    }

    /// 获取性能指标的最大值
    pub fn max_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).and_then(|values| {
            values
                .iter()
                .fold(None, |max, &x| Some(max.map_or(x, |m: f64| m.max(x))))
        })
    }

    /// 生成性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::from("=== 性能分析报告 ===\n");

        for (name, values) in &self.metrics {
            let avg = self.average_metric(name).unwrap_or(0.0);
            let std_dev = self.std_dev_metric(name).unwrap_or(0.0);
            let min = self.min_metric(name).unwrap_or(0.0);
            let max = self.max_metric(name).unwrap_or(0.0);
            let count = values.len();

            report.push_str(&format!(
                "{}: 平均={:.2}, 标准差={:.2}, 最小值={:.2}, 最大值={:.2}, 样本数={}\n",
                name, avg, std_dev, min, max, count
            ));
        }

        report
    }
}

impl Default for PerformanceAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// 可靠性分析器
///
/// 用于分析系统可靠性指标
#[derive(Debug)]
pub struct ReliabilityAnalyzer {
    /// 平均故障间隔时间 (MTBF)
    pub mtbf: f64,
    /// 平均修复时间 (MTTR)
    pub mttr: f64,
}

impl ReliabilityAnalyzer {
    /// 创建新的可靠性分析器
    pub fn new(mtbf: f64, mttr: f64) -> Self {
        Self { mtbf, mttr }
    }

    /// 计算系统可用性
    pub fn availability(&self) -> f64 {
        self.mtbf / (self.mtbf + self.mttr)
    }

    /// 计算系统不可用性
    pub fn unavailability(&self) -> f64 {
        1.0 - self.availability()
    }

    /// 模拟系统运行
    pub fn simulate(&self, duration_hours: f64) -> SimulationResult {
        let mut total_downtime = 0.0;
        let mut failures = 0;
        let mut current_time = 0.0;

        while current_time < duration_hours {
            // 正常运行时间
            let uptime = fastrand::f64() * self.mtbf;
            current_time += uptime;

            if current_time < duration_hours {
                // 故障时间
                let downtime = fastrand::f64() * self.mttr;
                total_downtime += downtime;
                current_time += downtime;
                failures += 1;
            }
        }

        let simulated_availability = (duration_hours - total_downtime) / duration_hours;

        SimulationResult {
            duration_hours,
            failures,
            total_downtime,
            simulated_availability,
        }
    }
}

/// 仿真结果
#[derive(Debug)]
pub struct SimulationResult {
    pub duration_hours: f64,
    pub failures: usize,
    pub total_downtime: f64,
    pub simulated_availability: f64,
}

/// 可扩展性分析器
///
/// 用于分析系统扩展性能
#[derive(Debug)]
pub struct ScalabilityAnalyzer {
    /// 基础吞吐量
    pub base_throughput: f64,
    /// 基础延迟
    pub base_latency: f64,
    /// 扩展效率
    pub scaling_efficiency: f64,
}

impl ScalabilityAnalyzer {
    /// 创建新的可扩展性分析器
    pub fn new(base_throughput: f64, base_latency: f64, scaling_efficiency: f64) -> Self {
        Self {
            base_throughput,
            base_latency,
            scaling_efficiency,
        }
    }

    /// 分析扩展性能
    pub fn analyze_scaling(&self, scale_factor: f64) -> ScalingResult {
        let throughput = self.base_throughput * scale_factor * self.scaling_efficiency;
        let latency = self.base_latency / scale_factor;

        ScalingResult {
            scale_factor,
            throughput,
            latency,
            efficiency: self.scaling_efficiency,
        }
    }

    /// 分析多个扩展级别
    pub fn analyze_multiple_scales(&self, scales: &[f64]) -> Vec<ScalingResult> {
        scales
            .iter()
            .map(|&scale| self.analyze_scaling(scale))
            .collect()
    }
}

/// 扩展结果
#[derive(Debug)]
pub struct ScalingResult {
    pub scale_factor: f64,
    pub throughput: f64,
    pub latency: f64,
    pub efficiency: f64,
}

/// 高级排队论模型 - 利用 Rust 1.90 特性
/// 
/// 实现更复杂的排队系统模型，包括优先级队列、多级队列等

/// 优先级排队系统 - 使用 Rust 1.90 的生命周期改进
#[derive(Debug, Clone)]
pub struct PriorityQueue<const PRIORITIES: usize> {
    /// 各优先级的到达率
    pub arrival_rates: [f64; PRIORITIES],
    /// 各优先级的服务率
    pub service_rates: [f64; PRIORITIES],
    /// 系统配置
    pub config: QueueConfig<PRIORITIES>,
}

impl<const PRIORITIES: usize> PriorityQueue<PRIORITIES> {
    /// 创建新的优先级排队系统
    pub fn new(arrival_rates: [f64; PRIORITIES], service_rates: [f64; PRIORITIES]) -> Self {
        let mut parameters = [0.0; PRIORITIES];
        for i in 0..PRIORITIES {
            parameters[i] = arrival_rates[i] + service_rates[i];
        }
        
        Self {
            arrival_rates,
            service_rates,
            config: QueueConfig::new(parameters),
        }
    }
    
    /// 计算系统利用率
    pub fn utilization(&self) -> f64 {
        let total_arrival_rate: f64 = self.arrival_rates.iter().sum();
        let total_service_rate: f64 = self.service_rates.iter().sum();
        total_arrival_rate / total_service_rate
    }
    
    /// 计算各优先级的平均等待时间
    pub fn priority_waiting_times(&self) -> [f64; PRIORITIES] {
        let mut waiting_times = [0.0; PRIORITIES];
        let utilization = self.utilization();
        
        for i in 0..PRIORITIES {
            if utilization < 1.0 {
                let lambda_i = self.arrival_rates[i];
                let mu_i = self.service_rates[i];
                if mu_i > lambda_i {
                    waiting_times[i] = lambda_i / (mu_i * (mu_i - lambda_i));
                }
            }
        }
        
        waiting_times
    }
}

/// 多级反馈队列系统
#[derive(Debug, Clone)]
pub struct MultiLevelFeedbackQueue<const LEVELS: usize> {
    /// 各级队列的配置
    pub level_configs: [QueueConfig<3>; LEVELS], // [arrival_rate, service_rate, time_slice]
    /// 升级概率
    pub promotion_probabilities: [f64; LEVELS],
    /// 降级概率  
    pub demotion_probabilities: [f64; LEVELS],
}

impl<const LEVELS: usize> MultiLevelFeedbackQueue<LEVELS> {
    /// 创建新的多级反馈队列系统
    pub fn new(
        level_configs: [QueueConfig<3>; LEVELS],
        promotion_probabilities: [f64; LEVELS],
        demotion_probabilities: [f64; LEVELS],
    ) -> Self {
        Self {
            level_configs,
            promotion_probabilities,
            demotion_probabilities,
        }
    }
    
    /// 计算系统整体性能指标
    pub fn overall_metrics(&self) -> QueueMetrics {
        let mut total_throughput = 0.0;
        let mut total_response_time = 0.0;
        
        for config in &self.level_configs {
            let [arrival_rate, service_rate, _] = config.parameters;
            if service_rate > arrival_rate {
                total_throughput += arrival_rate;
                total_response_time += arrival_rate / (service_rate - arrival_rate);
            }
        }
        
        QueueMetrics {
            throughput: total_throughput,
            avg_response_time: total_response_time / LEVELS as f64,
            utilization: total_throughput / self.level_configs.iter()
                .map(|c| c.parameters[1])
                .sum::<f64>(),
            avg_queue_length: 0.0,
            avg_waiting_time: 0.0,
        }
    }
}

/// 排队系统性能指标 - 使用 Rust 1.90 的改进序列化
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueMetrics {
    /// 吞吐量
    pub throughput: f64,
    /// 平均响应时间
    pub avg_response_time: f64,
    /// 系统利用率
    pub utilization: f64,
    /// 平均队列长度
    pub avg_queue_length: f64,
    /// 平均等待时间
    pub avg_waiting_time: f64,
}

impl Default for QueueMetrics {
    fn default() -> Self {
        Self {
            throughput: 0.0,
            avg_response_time: 0.0,
            utilization: 0.0,
            avg_queue_length: 0.0,
            avg_waiting_time: 0.0,
        }
    }
}

/// 计算阶乘 - 使用 Rust 1.90 的优化
fn factorial(n: usize) -> f64 {
    match n {
        0 | 1 => 1.0,
        _ => (2..=n).fold(1.0, |acc, x| acc * x as f64),
    }
}

/// 高级数学函数 - 利用 Rust 1.90 的数学库优化
pub mod advanced_math {
    
    /// 计算阶乘
    pub fn factorial(n: usize) -> usize {
        match n {
            0 | 1 => 1,
            _ => (2..=n).product(),
        }
    }
    
    /// 计算 Erlang C 公式 - 用于 M/M/c 队列
    pub fn erlang_c(lambda: f64, mu: f64, c: usize) -> f64 {
        let rho = lambda / (c as f64 * mu);
        let numerator = (lambda / mu).powi(c as i32) / factorial(c) as f64;
        let mut denominator = 0.0;
        
        for i in 0..=c {
            denominator += (lambda / mu).powi(i as i32) / factorial(i) as f64;
        }
        denominator += (lambda / mu).powi(c as i32) / (factorial(c) as f64 * (1.0 - rho));
        
        numerator / denominator
    }
    
    /// 计算 Poisson 分布的概率质量函数
    pub fn poisson_pmf(k: usize, lambda: f64) -> f64 {
        if k == 0 {
            (-lambda).exp()
        } else {
            (lambda.powi(k as i32) * (-lambda).exp()) / factorial(k) as f64
        }
    }
    
    /// 计算 Gamma 函数
    pub fn gamma(z: f64) -> f64 {
        if z < 0.5 {
            std::f64::consts::PI / ((std::f64::consts::PI * z).sin() * gamma(1.0 - z))
        } else {
            let z = z - 1.0;
            let x = 0.99999999999980993 +
                z * (676.5203681218851 +
                z * (-1259.1392167224028 +
                z * (771.32342877765313 +
                z * (-176.61502916214059 +
                z * (12.507343278686905 +
                z * (-0.13857109526572012 +
                z * (9.9843695780195716e-6 +
                z * 1.5056327351493116e-7)))))));
            let t = z + 7.5;
            (2.0 * std::f64::consts::PI).sqrt() * t.powf(z + 0.5) * (-t).exp() * x
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mm1_queue_basic() {
        let queue = MM1Queue::new(1.0, 2.0);
        assert_eq!(queue.utilization(), 0.5);
        assert!(queue.is_stable());
    }

    #[test]
    fn test_mm1_queue_calculations() {
        let queue = MM1Queue::new(1.0, 2.0);
        assert_eq!(queue.utilization(), 0.5);
        assert_eq!(queue.average_queue_length().unwrap(), 1.0);
        assert_eq!(queue.average_waiting_time().unwrap(), 1.0);
        assert_eq!(queue.average_response_time().unwrap(), 1.5);
    }

    #[test]
    fn test_mm1_queue_unstable() {
        let queue = MM1Queue::new(2.0, 1.0);
        assert!(!queue.is_stable());
        assert!(queue.average_queue_length().is_err());
    }

    #[test]
    fn test_performance_analyzer() {
        let mut analyzer = PerformanceAnalyzer::new();
        analyzer.record_metric("throughput", 100.0);
        analyzer.record_metric("throughput", 200.0);

        assert_eq!(analyzer.average_metric("throughput"), Some(150.0));
        assert_eq!(analyzer.min_metric("throughput"), Some(100.0));
        assert_eq!(analyzer.max_metric("throughput"), Some(200.0));
    }

    #[test]
    fn test_reliability_analyzer() {
        let analyzer = ReliabilityAnalyzer::new(100.0, 1.0);
        let availability = analyzer.availability();
        assert!((availability - 0.990099).abs() < 1e-6);
    }

    #[test]
    fn test_scalability_analyzer() {
        let analyzer = ScalabilityAnalyzer::new(1000.0, 100.0, 0.8);
        let result = analyzer.analyze_scaling(2.0);

        assert_eq!(result.scale_factor, 2.0);
        assert_eq!(result.throughput, 1600.0);
        assert_eq!(result.latency, 50.0);
    }
}
