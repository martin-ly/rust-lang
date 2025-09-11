//! 系统建模的Rust实现示例
//! 
//! 本文件展示了如何使用Rust实现各种系统建模技术，
//! 包括排队论、性能分析、可靠性建模等。

use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 排队论模型 - M/M/1 排队系统
/// 
/// 实现经典的M/M/1排队模型，用于分析系统性能
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
    pub fn new(arrival_rate: f64, service_rate: f64) -> Self {
        Self {
            arrival_rate,
            service_rate,
            capacity: None,
        }
    }

    /// 创建有限容量的排队系统
    pub fn with_capacity(arrival_rate: f64, service_rate: f64, capacity: usize) -> Self {
        Self {
            arrival_rate,
            service_rate,
            capacity: Some(capacity),
        }
    }

    /// 计算系统利用率 (ρ = λ/μ)
    pub fn utilization(&self) -> f64 {
        self.arrival_rate / self.service_rate
    }

    /// 计算平均队长 (L = λ/(μ-λ))
    pub fn average_queue_length(&self) -> Result<f64, String> {
        if self.utilization() >= 1.0 {
            return Err("系统不稳定：利用率 >= 1.0".to_string());
        }
        Ok(self.arrival_rate / (self.service_rate - self.arrival_rate))
    }

    /// 计算平均等待时间 (W = 1/(μ-λ))
    pub fn average_waiting_time(&self) -> Result<f64, String> {
        if self.utilization() >= 1.0 {
            return Err("系统不稳定：利用率 >= 1.0".to_string());
        }
        Ok(1.0 / (self.service_rate - self.arrival_rate))
    }

    /// 计算系统响应时间 (包括服务时间)
    pub fn average_response_time(&self) -> Result<f64, String> {
        Ok(self.average_waiting_time()? + 1.0 / self.service_rate)
    }

    /// 计算系统中平均客户数
    pub fn average_customers_in_system(&self) -> Result<f64, String> {
        Ok(self.average_queue_length()? + self.utilization())
    }
}

/// 性能分析器
/// 
/// 用于分析系统性能指标
#[derive(Debug)]
pub struct PerformanceAnalyzer {
    metrics: HashMap<String, Vec<f64>>,
}

impl PerformanceAnalyzer {
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
    pub fn metric_std_dev(&self, name: &str) -> Option<f64> {
        let values = self.metrics.get(name)?;
        if values.len() < 2 {
            return Some(0.0);
        }

        let mean = values.iter().sum::<f64>() / values.len() as f64;
        let variance = values.iter()
            .map(|v| (v - mean).powi(2))
            .sum::<f64>() / (values.len() - 1) as f64;
        
        Some(variance.sqrt())
    }

    /// 生成性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 性能分析报告 ===\n");
        
        for (metric_name, values) in &self.metrics {
            let avg = self.average_metric(metric_name).unwrap_or(0.0);
            let std_dev = self.metric_std_dev(metric_name).unwrap_or(0.0);
            let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
            let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
            
            report.push_str(&format!(
                "{}: 平均={:.2}, 标准差={:.2}, 最小值={:.2}, 最大值={:.2}, 样本数={}\n",
                metric_name, avg, std_dev, min, max, values.len()
            ));
        }
        
        report
    }
}

/// 可靠性分析器
/// 
/// 用于分析系统可靠性指标
#[derive(Debug, Clone)]
pub struct ReliabilityAnalyzer {
    /// 故障率 (λ)
    pub failure_rate: f64,
    /// 修复率 (μ)
    pub repair_rate: f64,
    /// 系统组件
    pub components: Vec<Component>,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub id: String,
    pub failure_rate: f64,
    pub repair_rate: f64,
    pub is_active: bool,
}

impl ReliabilityAnalyzer {
    pub fn new() -> Self {
        Self {
            failure_rate: 0.001, // 默认故障率
            repair_rate: 0.1,    // 默认修复率
            components: Vec::new(),
        }
    }

    /// 添加系统组件
    pub fn add_component(&mut self, id: String, failure_rate: f64, repair_rate: f64) {
        self.components.push(Component {
            id,
            failure_rate,
            repair_rate,
            is_active: true,
        });
    }

    /// 计算系统可用性 (A = μ/(λ+μ))
    pub fn system_availability(&self) -> f64 {
        self.repair_rate / (self.failure_rate + self.repair_rate)
    }

    /// 计算平均故障间隔时间 (MTBF = 1/λ)
    pub fn mean_time_between_failures(&self) -> f64 {
        1.0 / self.failure_rate
    }

    /// 计算平均修复时间 (MTTR = 1/μ)
    pub fn mean_time_to_repair(&self) -> f64 {
        1.0 / self.repair_rate
    }

    /// 模拟系统运行
    #[allow(unused)]
    pub fn simulate_system(&mut self, duration: Duration) -> SimulationResult {
        let start_time = Instant::now();
        let mut total_uptime = Duration::ZERO;
        let mut total_downtime = Duration::ZERO;
        let mut failure_count = 0;
        let mut current_time = Duration::ZERO;

        while current_time < duration {
            // 计算到下次故障的时间
            let time_to_failure = Duration::from_secs_f64(
                -1.0 / self.failure_rate * (1.0 - fastrand::f64()).ln()
            );
            
            if current_time + time_to_failure <= duration {
                total_uptime += time_to_failure;
                current_time += time_to_failure;
                failure_count += 1;
                
                // 计算修复时间
                let repair_time = Duration::from_secs_f64(
                    -1.0 / self.repair_rate * (1.0 - fastrand::f64()).ln()
                );
                
                if current_time + repair_time <= duration {
                    total_downtime += repair_time;
                    current_time += repair_time;
                } else {
                    total_downtime += duration - current_time;
                    break;
                }
            } else {
                total_uptime += duration - current_time;
                break;
            }
        }

        SimulationResult {
            duration,
            total_uptime,
            total_downtime,
            failure_count,
            availability: total_uptime.as_secs_f64() / duration.as_secs_f64(),
        }
    }
}

#[derive(Debug)]
pub struct SimulationResult {
    pub duration: Duration,
    pub total_uptime: Duration,
    pub total_downtime: Duration,
    pub failure_count: u32,
    pub availability: f64,
}

/// 可扩展性分析器
/// 
/// 用于分析系统可扩展性
#[derive(Debug)]
pub struct ScalabilityAnalyzer {
    pub base_throughput: f64,
    pub base_latency: f64,
    pub scaling_factor: f64,
}

impl ScalabilityAnalyzer {
    pub fn new(base_throughput: f64, base_latency: f64) -> Self {
        Self {
            base_throughput,
            base_latency,
            scaling_factor: 0.8, // 默认扩展效率
        }
    }

    /// 计算扩展后的吞吐量
    pub fn scaled_throughput(&self, scale: f64) -> f64 {
        self.base_throughput * scale * self.scaling_factor
    }

    /// 计算扩展后的延迟
    pub fn scaled_latency(&self, scale: f64) -> f64 {
        self.base_latency / (scale * self.scaling_factor)
    }

    /// 分析扩展效率
    pub fn scaling_efficiency(&self, scale: f64) -> f64 {
        let ideal_throughput = self.base_throughput * scale;
        let actual_throughput = self.scaled_throughput(scale);
        actual_throughput / ideal_throughput
    }
}

fn main() {
    println!("=== Rust系统建模示例 ===\n");

    // 1. 排队论示例
    println!("1. M/M/1 排队系统分析");
    let queue = MM1Queue::new(2.0, 3.0);
    
    match queue.average_queue_length() {
        Ok(length) => println!("   平均队长: {:.2}", length),
        Err(e) => println!("   错误: {}", e),
    }
    
    match queue.average_waiting_time() {
        Ok(time) => println!("   平均等待时间: {:.2} 秒", time),
        Err(e) => println!("   错误: {}", e),
    }
    
    println!("   系统利用率: {:.2}%", queue.utilization() * 100.0);
    println!();

    // 2. 性能分析示例
    println!("2. 性能分析");
    let mut analyzer = PerformanceAnalyzer::new();
    
    // 模拟一些性能数据
    for i in 0..100 {
        analyzer.record_metric("响应时间", 100.0 + (i as f64 * 0.1));
        analyzer.record_metric("吞吐量", 1000.0 - (i as f64 * 0.5));
    }
    
    println!("{}", analyzer.generate_report());

    // 3. 可靠性分析示例
    println!("3. 可靠性分析");
    let mut reliability = ReliabilityAnalyzer::new();
    reliability.add_component("CPU".to_string(), 0.0001, 0.01);
    reliability.add_component("内存".to_string(), 0.0002, 0.02);
    
    println!("   系统可用性: {:.2}%", reliability.system_availability() * 100.0);
    println!("   平均故障间隔时间: {:.2} 小时", reliability.mean_time_between_failures() / 3600.0);
    println!("   平均修复时间: {:.2} 小时", reliability.mean_time_to_repair() / 3600.0);
    
    // 运行可靠性模拟
    let simulation_result = reliability.simulate_system(Duration::from_secs(86400)); // 24小时
    println!("   模拟结果 (24小时):");
    println!("     可用性: {:.2}%", simulation_result.availability * 100.0);
    println!("     故障次数: {}", simulation_result.failure_count);
    println!();

    // 4. 可扩展性分析示例
    println!("4. 可扩展性分析");
    let scalability = ScalabilityAnalyzer::new(1000.0, 100.0);
    
    for scale in [1.0, 2.0, 4.0, 8.0] {
        let throughput = scalability.scaled_throughput(scale);
        let latency = scalability.scaled_latency(scale);
        let efficiency = scalability.scaling_efficiency(scale);
        
        println!("   扩展 {}x: 吞吐量={:.0}, 延迟={:.1}ms, 效率={:.1}%", 
                scale, throughput, latency, efficiency * 100.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mm1_queue_calculations() {
        let queue = MM1Queue::new(1.0, 2.0);
        assert_eq!(queue.utilization(), 0.5);
        assert_eq!(queue.average_queue_length().unwrap(), 1.0);
        assert_eq!(queue.average_waiting_time().unwrap(), 1.0);
    }

    #[test]
    fn test_unstable_queue() {
        let queue = MM1Queue::new(3.0, 2.0);
        assert!(queue.average_queue_length().is_err());
        assert!(queue.average_waiting_time().is_err());
    }

    #[test]
    fn test_performance_analyzer() {
        let mut analyzer = PerformanceAnalyzer::new();
        analyzer.record_metric("test", 1.0);
        analyzer.record_metric("test", 2.0);
        analyzer.record_metric("test", 3.0);
        
        assert_eq!(analyzer.average_metric("test"), Some(2.0));
    }

    #[test]
    fn test_reliability_analyzer() {
        let reliability = ReliabilityAnalyzer::new();
        assert!(reliability.system_availability() > 0.0);
        assert!(reliability.mean_time_between_failures() > 0.0);
    }

    #[test]
    fn test_scalability_analyzer() {
        let scalability = ScalabilityAnalyzer::new(100.0, 10.0);
        assert!(scalability.scaled_throughput(2.0) > 100.0);
        assert!(scalability.scaled_latency(2.0) < 10.0);
    }
}
