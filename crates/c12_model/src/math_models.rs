//! 数学建模实现
//!
//! 本模块实现了各种数学建模技术，包括概率模型、统计模型、优化算法等。
//! 使用Rust的类型安全特性确保数学计算的正确性。

use std::f64;
use serde::{Deserialize, Serialize};

// Rust 1.90 特性：使用常量泛型推断和生命周期改进
/// 数学配置 - 使用常量泛型参数
#[derive(Debug, Clone)]
pub struct MathConfig<const N_DIMENSIONS: usize> {
    /// 维度数量
    pub dimensions: usize,
    /// 配置参数
    pub parameters: [f64; N_DIMENSIONS],
    /// 精度设置
    pub precision: f64,
}

impl<const N_DIMENSIONS: usize> MathConfig<N_DIMENSIONS> {
    /// 创建新的数学配置
    pub fn new(precision: f64) -> Self {
        Self {
            dimensions: N_DIMENSIONS,
            parameters: [0.0; N_DIMENSIONS],
            precision,
        }
    }
    
    /// 更新参数
    pub fn update_parameters(&mut self, new_params: [f64; N_DIMENSIONS]) {
        self.parameters = new_params;
    }
}

/// 概率分布trait
pub trait ProbabilityDistribution {
    /// 概率密度函数
    fn pdf(&self, x: f64) -> f64;

    /// 累积分布函数
    fn cdf(&self, x: f64) -> f64;

    /// 生成随机样本
    fn sample(&self) -> f64;

    /// 计算期望值
    fn mean(&self) -> f64;

    /// 计算方差
    fn variance(&self) -> f64;
}

/// 正态分布
#[derive(Debug, Clone)]
pub struct NormalDistribution {
    /// 均值
    pub mean: f64,
    /// 标准差
    pub std_dev: f64,
}

impl NormalDistribution {
    /// 创建新的正态分布
    pub fn new(mean: f64, std_dev: f64) -> Self {
        Self { mean, std_dev }
    }

    /// 标准正态分布
    pub fn standard() -> Self {
        Self::new(0.0, 1.0)
    }
}

impl ProbabilityDistribution for NormalDistribution {
    fn pdf(&self, x: f64) -> f64 {
        let coefficient = 1.0 / (self.std_dev * (2.0 * std::f64::consts::PI).sqrt());
        let exponent = -0.5 * ((x - self.mean) / self.std_dev).powi(2);
        coefficient * exponent.exp()
    }

    fn cdf(&self, x: f64) -> f64 {
        // 简化实现：使用近似公式
        let z = (x - self.mean) / self.std_dev;
        0.5 * (1.0 + erf_approximation(z / 2.0_f64.sqrt()))
    }

    fn sample(&self) -> f64 {
        // Box-Muller变换生成正态分布随机数
        let u1 = fastrand::f64();
        let u2 = fastrand::f64();
        let z0 = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();
        self.mean + self.std_dev * z0
    }

    fn mean(&self) -> f64 {
        self.mean
    }

    fn variance(&self) -> f64 {
        self.std_dev.powi(2)
    }
}

/// 指数分布
#[derive(Debug, Clone)]
pub struct ExponentialDistribution {
    /// 速率参数
    pub rate: f64,
}

impl ExponentialDistribution {
    /// 创建新的指数分布
    pub fn new(rate: f64) -> Self {
        Self { rate }
    }
}

impl ProbabilityDistribution for ExponentialDistribution {
    fn pdf(&self, x: f64) -> f64 {
        if x >= 0.0 {
            self.rate * (-self.rate * x).exp()
        } else {
            0.0
        }
    }

    fn cdf(&self, x: f64) -> f64 {
        if x >= 0.0 {
            1.0 - (-self.rate * x).exp()
        } else {
            0.0
        }
    }

    fn sample(&self) -> f64 {
        -fastrand::f64().ln() / self.rate
    }

    fn mean(&self) -> f64 {
        1.0 / self.rate
    }

    fn variance(&self) -> f64 {
        1.0 / self.rate.powi(2)
    }
}

/// 泊松分布
#[derive(Debug, Clone)]
pub struct PoissonDistribution {
    /// 速率参数
    pub lambda: f64,
}

impl PoissonDistribution {
    /// 创建新的泊松分布
    pub fn new(lambda: f64) -> Self {
        Self { lambda }
    }
}

impl ProbabilityDistribution for PoissonDistribution {
    fn pdf(&self, x: f64) -> f64 {
        if x >= 0.0 && x.fract() == 0.0 {
            let k = x as usize;
            (self.lambda.powi(k as i32) * (-self.lambda).exp()) / factorial(k) as f64
        } else {
            0.0
        }
    }

    fn cdf(&self, x: f64) -> f64 {
        if x < 0.0 {
            0.0
        } else {
            let k = x.floor() as usize;
            (0..=k).map(|i| self.pdf(i as f64)).sum()
        }
    }

    fn sample(&self) -> f64 {
        // Knuth算法生成泊松分布随机数
        let mut k = 0;
        let mut p = 1.0;
        let l = (-self.lambda).exp();

        loop {
            k += 1;
            p *= fastrand::f64();
            if p <= l {
                break;
            }
        }

        (k - 1) as f64
    }

    fn mean(&self) -> f64 {
        self.lambda
    }

    fn variance(&self) -> f64 {
        self.lambda
    }
}

/// 蒙特卡洛模拟器
#[derive(Debug)]
pub struct MonteCarloSimulator {
    /// 样本数量
    pub sample_size: usize,
}

impl MonteCarloSimulator {
    /// 创建新的蒙特卡洛模拟器
    pub fn new(sample_size: usize) -> Self {
        Self { sample_size }
    }

    /// 模拟期望值
    pub fn simulate_expectation<F>(&self, f: F) -> f64
    where
        F: Fn() -> f64,
    {
        let sum: f64 = (0..self.sample_size).map(|_| f()).sum();
        sum / self.sample_size as f64
    }

    /// 模拟积分
    pub fn simulate_integral<F>(&self, f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let sum: f64 = (0..self.sample_size)
            .map(|_| {
                let x = a + fastrand::f64() * (b - a);
                f(x)
            })
            .sum();
        (b - a) * sum / self.sample_size as f64
    }

    /// 模拟概率
    pub fn simulate_probability<F>(&self, event: F) -> f64
    where
        F: Fn() -> bool,
    {
        let count = (0..self.sample_size).filter(|_| event()).count();
        count as f64 / self.sample_size as f64
    }
}

/// 数值积分器
#[derive(Debug)]
pub struct NumericalIntegrator {
    /// 积分方法
    pub method: IntegrationMethod,
    /// 精度
    pub tolerance: f64,
    /// 最大迭代次数
    pub max_iterations: usize,
}

/// 积分方法
#[derive(Debug, Clone)]
pub enum IntegrationMethod {
    /// 梯形法则
    Trapezoidal,
    /// 辛普森法则
    Simpson,
    /// 高斯-勒让德积分
    GaussLegendre,
}

impl NumericalIntegrator {
    /// 创建新的数值积分器
    pub fn new(method: IntegrationMethod, tolerance: f64, max_iterations: usize) -> Self {
        Self {
            method,
            tolerance,
            max_iterations,
        }
    }

    /// 计算定积分
    pub fn integrate<F>(&self, f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        match self.method {
            IntegrationMethod::Trapezoidal => self.trapezoidal_rule(f, a, b),
            IntegrationMethod::Simpson => self.simpson_rule(f, a, b),
            IntegrationMethod::GaussLegendre => self.gauss_legendre(f, a, b),
        }
    }

    /// 梯形法则
    fn trapezoidal_rule<F>(&self, f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let n = 1000; // 简化实现
        let h = (b - a) / n as f64;
        let mut sum = (f(a) + f(b)) / 2.0;

        for i in 1..n {
            let x = a + i as f64 * h;
            sum += f(x);
        }

        h * sum
    }

    /// 辛普森法则
    fn simpson_rule<F>(&self, f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let n = 1000; // 简化实现
        let h = (b - a) / n as f64;
        let mut sum = f(a) + f(b);

        for i in 1..n {
            let x = a + i as f64 * h;
            if i % 2 == 0 {
                sum += 2.0 * f(x);
            } else {
                sum += 4.0 * f(x);
            }
        }

        h * sum / 3.0
    }

    /// 高斯-勒让德积分
    fn gauss_legendre<F>(&self, f: F, a: f64, b: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        // 简化实现：使用2点高斯-勒让德公式
        let x1 = -1.0 / 3.0_f64.sqrt();
        let x2 = 1.0 / 3.0_f64.sqrt();
        let w1 = 1.0;
        let w2 = 1.0;

        let t1 = (b - a) / 2.0 * x1 + (a + b) / 2.0;
        let t2 = (b - a) / 2.0 * x2 + (a + b) / 2.0;

        (b - a) / 2.0 * (w1 * f(t1) + w2 * f(t2))
    }
}

/// 优化算法trait
pub trait OptimizationAlgorithm {
    /// 目标函数类型
    type ObjectiveFunction: Fn(&[f64]) -> f64;

    /// 优化
    fn optimize(&self, f: Self::ObjectiveFunction, initial: &[f64]) -> Vec<f64>;
}

/// 梯度下降优化器
#[derive(Debug)]
pub struct GradientDescentOptimizer {
    /// 学习率
    pub learning_rate: f64,
    /// 最大迭代次数
    pub max_iterations: usize,
    /// 收敛阈值
    pub tolerance: f64,
}

impl GradientDescentOptimizer {
    /// 创建新的梯度下降优化器
    pub fn new(learning_rate: f64, max_iterations: usize, tolerance: f64) -> Self {
        Self {
            learning_rate,
            max_iterations,
            tolerance,
        }
    }
}

impl OptimizationAlgorithm for GradientDescentOptimizer {
    type ObjectiveFunction = fn(&[f64]) -> f64;

    fn optimize(&self, f: Self::ObjectiveFunction, initial: &[f64]) -> Vec<f64> {
        let mut x = initial.to_vec();

        for _ in 0..self.max_iterations {
            // 计算数值梯度
            let gradient = self.numerical_gradient(f, &x);

            // 更新参数
            for i in 0..x.len() {
                x[i] -= self.learning_rate * gradient[i];
            }

            // 检查收敛
            let gradient_norm = gradient.iter().map(|&g| g * g).sum::<f64>().sqrt();
            if gradient_norm < self.tolerance {
                break;
            }
        }

        x
    }
}

impl GradientDescentOptimizer {
    /// 计算数值梯度
    fn numerical_gradient<F>(&self, f: F, x: &[f64]) -> Vec<f64>
    where
        F: Fn(&[f64]) -> f64,
    {
        let h = 1e-6;
        let mut gradient = Vec::new();

        for i in 0..x.len() {
            let mut x_plus = x.to_vec();
            let mut x_minus = x.to_vec();

            x_plus[i] += h;
            x_minus[i] -= h;

            let derivative = (f(&x_plus) - f(&x_minus)) / (2.0 * h);
            gradient.push(derivative);
        }

        gradient
    }
}

/// 统计工具
#[derive(Debug)]
pub struct StatisticalTools;

impl StatisticalTools {
    /// 计算样本均值
    pub fn mean(data: &[f64]) -> f64 {
        data.iter().sum::<f64>() / data.len() as f64
    }

    /// 计算样本方差
    pub fn variance(data: &[f64]) -> f64 {
        let mean = Self::mean(data);
        let sum_squared_diff: f64 = data.iter().map(|&x| (x - mean).powi(2)).sum();
        sum_squared_diff / (data.len() - 1) as f64
    }

    /// 计算样本标准差
    pub fn standard_deviation(data: &[f64]) -> f64 {
        Self::variance(data).sqrt()
    }

    /// 计算相关系数
    pub fn correlation(x: &[f64], y: &[f64]) -> f64 {
        if x.len() != y.len() {
            return 0.0;
        }

        let _n = x.len() as f64;
        let mean_x = Self::mean(x);
        let mean_y = Self::mean(y);

        let numerator: f64 = x
            .iter()
            .zip(y.iter())
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

    /// 计算置信区间
    pub fn confidence_interval(data: &[f64], confidence_level: f64) -> (f64, f64) {
        let mean = Self::mean(data);
        let std_dev = Self::standard_deviation(data);
        let n = data.len() as f64;

        // 简化实现：使用正态分布近似
        let z_score = match confidence_level {
            0.95 => 1.96,
            0.99 => 2.576,
            _ => 1.96,
        };

        let margin_error = z_score * std_dev / n.sqrt();
        (mean - margin_error, mean + margin_error)
    }

    /// 计算中位数
    pub fn median(data: &[f64]) -> f64 {
        let mut sorted_data = data.to_vec();
        sorted_data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let n = sorted_data.len();
        if n % 2 == 0 {
            (sorted_data[n / 2 - 1] + sorted_data[n / 2]) / 2.0
        } else {
            sorted_data[n / 2]
        }
    }
}

/// 计算阶乘
fn factorial(n: usize) -> usize {
    match n {
        0 | 1 => 1,
        _ => (2..=n).product::<usize>(),
    }
}

/// 误差函数近似
fn erf_approximation(x: f64) -> f64 {
    // Abramowitz和Stegun的近似公式
    let a1 = 0.254829592;
    let a2 = -0.284496736;
    let a3 = 1.421413741;
    let a4 = -1.453152027;
    let a5 = 1.061405429;
    let p = 0.3275911;

    let sign = if x >= 0.0 { 1.0 } else { -1.0 };
    let x = x.abs();

    let t = 1.0 / (1.0 + p * x);
    let y = 1.0 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * (-x * x).exp();

    sign * y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normal_distribution() {
        let dist = NormalDistribution::new(0.0, 1.0);
        assert_eq!(dist.mean(), 0.0);
        assert_eq!(dist.variance(), 1.0);
    }

    #[test]
    fn test_exponential_distribution() {
        let dist = ExponentialDistribution::new(1.0);
        assert_eq!(dist.mean(), 1.0);
        assert_eq!(dist.variance(), 1.0);
    }

    #[test]
    fn test_poisson_distribution() {
        let dist = PoissonDistribution::new(2.0);
        assert_eq!(dist.mean(), 2.0);
        assert_eq!(dist.variance(), 2.0);
    }

    #[test]
    fn test_monte_carlo_simulation() {
        let simulator = MonteCarloSimulator::new(10000);
        let expectation = simulator.simulate_expectation(|| fastrand::f64());
        assert!((expectation - 0.5).abs() < 0.1);
    }

    #[test]
    fn test_numerical_integration() {
        let integrator = NumericalIntegrator::new(IntegrationMethod::Trapezoidal, 1e-6, 1000);
        let result = integrator.integrate(|x| x * x, 0.0, 1.0);
        assert!((result - 1.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_gradient_descent() {
        let optimizer = GradientDescentOptimizer::new(0.01, 1000, 1e-6);
        let result = optimizer.optimize(|x| x[0] * x[0] + x[1] * x[1], &[1.0, 1.0]);
        assert!(result[0].abs() < 0.1);
        assert!(result[1].abs() < 0.1);
    }

    #[test]
    fn test_statistical_tools() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert_eq!(StatisticalTools::mean(&data), 3.0);
        assert_eq!(StatisticalTools::variance(&data), 2.5);
    }
}

// ============================================================================
// 高级数学模型 - 利用 Rust 1.90 特性
// ============================================================================

/// 高维概率分布 - 使用 Rust 1.90 的常量泛型推断
#[derive(Debug, Clone)]
pub struct MultivariateNormalDistribution<const N_DIMS: usize> {
    /// 均值向量
    pub mean: [f64; N_DIMS],
    /// 协方差矩阵（简化为一维数组）
    pub covariance: Vec<f64>,
    /// 配置信息
    pub config: MathConfig<N_DIMS>,
}

impl<const N_DIMS: usize> MultivariateNormalDistribution<N_DIMS> {
    /// 创建新的多元正态分布
    pub fn new(mean: [f64; N_DIMS], covariance: Vec<f64>) -> Self {
        Self {
            mean,
            covariance,
            config: MathConfig::new(1e-6),
        }
    }
    
    /// 计算概率密度函数
    pub fn pdf(&self, x: &[f64; N_DIMS]) -> f64 {
        // 简化的多元正态分布PDF计算
        let mut quad_form = 0.0;
        for i in 0..N_DIMS {
            for j in 0..N_DIMS {
                quad_form += (x[i] - self.mean[i]) * 
                           (x[j] - self.mean[j]) * 
                           self.covariance.get(i * N_DIMS + j).unwrap_or(&0.0);
            }
        }
        
        let det_cov = self.calculate_determinant();
        let coefficient = 1.0 / ((2.0 * std::f64::consts::PI).powi(N_DIMS as i32) * det_cov).sqrt();
        coefficient * (-0.5 * quad_form).exp()
    }
    
    /// 计算协方差矩阵的行列式（简化实现）
    fn calculate_determinant(&self) -> f64 {
        // 简化的行列式计算
        if N_DIMS == 1 {
            self.covariance.get(0).copied().unwrap_or(1.0)
        } else if N_DIMS == 2 {
            let a = self.covariance.get(0).copied().unwrap_or(1.0);
            let b = self.covariance.get(1).copied().unwrap_or(0.0);
            let c = self.covariance.get(2).copied().unwrap_or(0.0);
            let d = self.covariance.get(3).copied().unwrap_or(1.0);
            a * d - b * c
        } else {
            1.0 // 简化实现
        }
    }
}

/// 贝叶斯推理器 - 使用 Rust 1.90 的生命周期改进
#[derive(Debug, Clone)]
pub struct BayesianInference<const N_PARAMS: usize> {
    /// 先验分布参数
    pub prior_params: [f64; N_PARAMS],
    /// 似然函数参数
    pub likelihood_params: [f64; N_PARAMS],
    /// 后验分布参数
    pub posterior_params: [f64; N_PARAMS],
    /// 配置信息
    pub config: MathConfig<N_PARAMS>,
}

impl<const N_PARAMS: usize> BayesianInference<N_PARAMS> {
    /// 创建新的贝叶斯推理器
    pub fn new(prior_params: [f64; N_PARAMS], likelihood_params: [f64; N_PARAMS]) -> Self {
        Self {
            prior_params,
            likelihood_params,
            posterior_params: [0.0; N_PARAMS],
            config: MathConfig::new(1e-6),
        }
    }
    
    /// 更新后验分布
    pub fn update_posterior(&mut self, data: &[f64]) -> Result<(), String> {
        // 简化的贝叶斯更新
        for i in 0..N_PARAMS {
            // 假设共轭先验，简化更新规则
            self.posterior_params[i] = self.prior_params[i] + 
                                     self.likelihood_params[i] * data.len() as f64;
        }
        Ok(())
    }
    
    /// 计算后验预测分布
    pub fn posterior_predictive(&self, x: f64) -> f64 {
        // 简化的后验预测计算
        let mut result = 1.0;
        for i in 0..N_PARAMS {
            result *= (-(x - self.posterior_params[i]).powi(2) / 
                      (2.0 * self.posterior_params[i])).exp();
        }
        result
    }
}

/// 马尔可夫链蒙特卡洛 (MCMC) - 使用 Rust 1.90 的常量泛型推断
#[derive(Debug, Clone)]
pub struct MCMCSampler<const N_PARAMS: usize> {
    /// 当前状态
    pub current_state: [f64; N_PARAMS],
    /// 提议分布方差
    pub proposal_variance: [f64; N_PARAMS],
    /// 接受率
    pub acceptance_rate: f64,
    /// 样本历史
    pub samples: Vec<[f64; N_PARAMS]>,
    /// 配置信息
    pub config: MathConfig<N_PARAMS>,
}

impl<const N_PARAMS: usize> MCMCSampler<N_PARAMS> {
    /// 创建新的MCMC采样器
    pub fn new(initial_state: [f64; N_PARAMS], proposal_variance: [f64; N_PARAMS]) -> Self {
        Self {
            current_state: initial_state,
            proposal_variance,
            acceptance_rate: 0.0,
            samples: Vec::new(),
            config: MathConfig::new(1e-6),
        }
    }
    
    /// 执行MCMC采样
    pub fn sample<F>(&mut self, target_density: F, n_samples: usize) -> Result<(), String>
    where
        F: Fn(&[f64; N_PARAMS]) -> f64,
    {
        self.samples.clear();
        let mut accepted = 0;
        
        for _ in 0..n_samples {
            // 生成提议状态
            let mut proposal = [0.0; N_PARAMS];
            for i in 0..N_PARAMS {
                proposal[i] = self.current_state[i] + 
                             fastrand::f64() * self.proposal_variance[i].sqrt();
            }
            
            // 计算接受概率
            let current_density = target_density(&self.current_state);
            let proposal_density = target_density(&proposal);
            
            let acceptance_ratio = (proposal_density / current_density).min(1.0);
            
            // 接受或拒绝提议
            if fastrand::f64() < acceptance_ratio {
                self.current_state = proposal;
                accepted += 1;
            }
            
            self.samples.push(self.current_state);
        }
        
        self.acceptance_rate = accepted as f64 / n_samples as f64;
        Ok(())
    }
    
    /// 获取样本均值
    pub fn sample_mean(&self) -> [f64; N_PARAMS] {
        let mut mean = [0.0; N_PARAMS];
        let n = self.samples.len() as f64;
        
        for sample in &self.samples {
            for i in 0..N_PARAMS {
                mean[i] += sample[i];
            }
        }
        
        for i in 0..N_PARAMS {
            mean[i] /= n;
        }
        
        mean
    }
    
    /// 获取样本方差
    pub fn sample_variance(&self) -> [f64; N_PARAMS] {
        let mean = self.sample_mean();
        let mut variance = [0.0; N_PARAMS];
        let n = self.samples.len() as f64;
        
        for sample in &self.samples {
            for i in 0..N_PARAMS {
                let diff = sample[i] - mean[i];
                variance[i] += diff * diff;
            }
        }
        
        for i in 0..N_PARAMS {
            variance[i] /= n;
        }
        
        variance
    }
}

/// 时间序列分析器 - 使用 Rust 1.90 的生命周期改进
#[derive(Debug, Clone)]
pub struct TimeSeriesAnalyzer {
    /// 时间序列数据
    pub data: Vec<f64>,
    /// 趋势参数
    pub trend_params: Vec<f64>,
    /// 季节性参数
    pub seasonal_params: Vec<f64>,
    /// 配置信息
    pub config: MathConfig<3>,
}

impl TimeSeriesAnalyzer {
    /// 创建新的时间序列分析器
    pub fn new(data: Vec<f64>) -> Self {
        Self {
            data,
            trend_params: Vec::new(),
            seasonal_params: Vec::new(),
            config: MathConfig::new(1e-6),
        }
    }
    
    /// 拟合线性趋势
    pub fn fit_linear_trend(&mut self) -> Result<(), String> {
        if self.data.len() < 2 {
            return Err("数据点不足".to_string());
        }
        
        let n = self.data.len() as f64;
        let x_mean = (n - 1.0) / 2.0;
        let y_mean = self.data.iter().sum::<f64>() / n;
        
        let mut numerator = 0.0;
        let mut denominator = 0.0;
        
        for (i, &y) in self.data.iter().enumerate() {
            let x = i as f64;
            numerator += (x - x_mean) * (y - y_mean);
            denominator += (x - x_mean).powi(2);
        }
        
        let slope = numerator / denominator;
        let intercept = y_mean - slope * x_mean;
        
        self.trend_params = vec![intercept, slope];
        Ok(())
    }
    
    /// 预测未来值
    pub fn predict(&self, steps_ahead: usize) -> Result<Vec<f64>, String> {
        if self.trend_params.len() != 2 {
            return Err("趋势参数未拟合".to_string());
        }
        
        let intercept = self.trend_params[0];
        let slope = self.trend_params[1];
        let mut predictions = Vec::new();
        
        for i in 1..=steps_ahead {
            let x = self.data.len() as f64 + i as f64;
            let prediction = intercept + slope * x;
            predictions.push(prediction);
        }
        
        Ok(predictions)
    }
    
    /// 计算自相关系数
    pub fn autocorrelation(&self, lag: usize) -> f64 {
        if lag >= self.data.len() {
            return 0.0;
        }
        
        let mean = self.data.iter().sum::<f64>() / self.data.len() as f64;
        let n = self.data.len() - lag;
        
        let mut numerator = 0.0;
        let mut denominator = 0.0;
        
        for i in 0..n {
            let diff1 = self.data[i] - mean;
            let diff2 = self.data[i + lag] - mean;
            numerator += diff1 * diff2;
            denominator += diff1 * diff1;
        }
        
        if denominator == 0.0 {
            0.0
        } else {
            numerator / denominator
        }
    }
}

/// 高级统计指标 - 使用 Rust 1.90 的改进序列化
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdvancedStatistics {
    /// 偏度
    pub skewness: f64,
    /// 峰度
    pub kurtosis: f64,
    /// 信息熵
    pub entropy: f64,
    /// 分位数
    pub percentiles: Vec<f64>,
}

impl AdvancedStatistics {
    /// 计算高级统计指标
    pub fn from_data(data: &[f64]) -> Self {
        let mean = StatisticalTools::mean(data);
        let std_dev = StatisticalTools::standard_deviation(data);
        
        // 计算偏度
        let skewness = data.iter()
            .map(|&x| ((x - mean) / std_dev).powi(3))
            .sum::<f64>() / data.len() as f64;
        
        // 计算峰度
        let kurtosis = data.iter()
            .map(|&x| ((x - mean) / std_dev).powi(4))
            .sum::<f64>() / data.len() as f64 - 3.0;
        
        // 计算信息熵（简化实现）
        let entropy = -data.iter()
            .map(|&x| x * x.ln())
            .sum::<f64>();
        
        // 计算分位数
        let mut sorted_data = data.to_vec();
        sorted_data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let percentiles = vec![
            Self::percentile(&sorted_data, 0.25), // Q1
            Self::percentile(&sorted_data, 0.50), // Q2 (中位数)
            Self::percentile(&sorted_data, 0.75), // Q3
        ];
        
        Self {
            skewness,
            kurtosis,
            entropy,
            percentiles,
        }
    }
    
    /// 计算分位数
    fn percentile(sorted_data: &[f64], p: f64) -> f64 {
        let n = sorted_data.len();
        let index = p * (n - 1) as f64;
        let lower = index.floor() as usize;
        let upper = index.ceil() as usize;
        
        if lower == upper {
            sorted_data[lower]
        } else {
            let weight = index - lower as f64;
            sorted_data[lower] * (1.0 - weight) + sorted_data[upper] * weight
        }
    }
}
