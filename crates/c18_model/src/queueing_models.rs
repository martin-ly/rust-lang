//! 排队论模型实现
//! 
//! 本模块实现了各种排队论模型，包括M/M/1、M/M/c、M/G/1等经典模型。
//! 使用Rust的类型安全特性确保模型参数的正确性和计算结果的可靠性。

use std::collections::HashMap;

/// M/M/1 排队系统
/// 
/// 实现经典的M/M/1排队模型，用于分析单服务器排队系统的性能。
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
}

impl MM1Queue {
    /// 创建新的M/M/1排队系统
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
        }
    }

    /// 创建有限容量的排队系统
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
        p0_sum += (c * rho).powi(self.servers as i32) / 
                  (factorial(self.servers) * (1.0 - rho));
        let p0 = 1.0 / p0_sum;

        // 计算平均队长
        let lq = p0 * (c * rho).powi(self.servers as i32) * rho / 
                 (factorial(self.servers) * (1.0 - rho).powi(2));

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
        self.metrics.entry(name.to_string()).or_insert_with(Vec::new).push(value);
    }

    /// 计算平均性能指标
    pub fn average_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).map(|values| {
            values.iter().sum::<f64>() / values.len() as f64
        })
    }

    /// 计算性能指标的标准差
    pub fn std_dev_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).map(|values| {
            let mean = values.iter().sum::<f64>() / values.len() as f64;
            let variance = values.iter()
                .map(|&x| (x - mean).powi(2))
                .sum::<f64>() / values.len() as f64;
            variance.sqrt()
        })
    }

    /// 获取性能指标的最小值
    pub fn min_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).and_then(|values| {
            values.iter().fold(None, |min, &x| {
                Some(min.map_or(x, |m: f64| m.min(x)))
            })
        })
    }

    /// 获取性能指标的最大值
    pub fn max_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).and_then(|values| {
            values.iter().fold(None, |max, &x| {
                Some(max.map_or(x, |m: f64| m.max(x)))
            })
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
        scales.iter()
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

/// 计算阶乘
fn factorial(n: usize) -> f64 {
    match n {
        0 | 1 => 1.0,
        _ => (2..=n).fold(1.0, |acc, x| acc * x as f64),
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
