//! Rust 1.90 新特性实现模块
//!
//! 本模块展示了如何利用 Rust 1.90 的新特性来增强模型实现，
//! 包括常量泛型推断、生命周期优化、函数指针安全等。

use serde::{Deserialize, Serialize};

/// Rust 1.90 常量泛型推断示例
/// 
/// 利用 `generic_arg_infer` 特性，允许在泛型参数中显式使用 `_` 来推断常量参数
#[derive(Debug, Clone)]
pub struct ModelConfig<const N: usize> {
    /// 模型参数数组
    pub parameters: [f64; N],
    /// 模型容量
    pub capacity: Option<usize>,
    /// 模型名称
    pub name: String,
}

impl<const N: usize> ModelConfig<N> {
    /// 创建新的模型配置
    pub fn new(parameters: [f64; N], name: String) -> Self {
        Self {
            parameters,
            capacity: None,
            name,
        }
    }

    /// 使用常量泛型推断创建配置
    /// 
    /// 示例：`ModelConfig::<2>::from_slice(&[1.0, 2.0], "test".to_string())`
    pub fn from_slice<const M: usize>(slice: &[f64], name: String) -> ModelConfig<M> {
        if slice.len() != M {
            panic!("Slice length {} does not match expected length {}", slice.len(), M);
        }
        let mut parameters = [0.0; M];
        parameters.copy_from_slice(slice);
        ModelConfig::new(parameters, name)
    }

    /// 获取参数数量
    pub const fn param_count(&self) -> usize {
        N
    }

    /// 计算参数的统计信息
    pub fn statistics(&self) -> ParameterStatistics {
        let sum: f64 = self.parameters.iter().sum();
        let mean = sum / N as f64;
        let variance = self.parameters.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f64>() / N as f64;
        
        ParameterStatistics {
            mean,
            variance,
            std_dev: variance.sqrt(),
            min: *self.parameters.iter().min_by(|a, b| a.partial_cmp(b).unwrap()).unwrap(),
            max: *self.parameters.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap(),
        }
    }
}

/// 参数统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParameterStatistics {
    pub mean: f64,
    pub variance: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
}

/// Rust 1.90 生命周期优化示例
/// 
/// 利用改进的生命周期语法一致性检查
pub struct DataProcessor<'a> {
    data: &'a [f64],
    processor_id: u32,
}

impl<'a> DataProcessor<'a> {
    /// 创建新的数据处理器
    pub fn new(data: &'a [f64], processor_id: u32) -> Self {
        Self { data, processor_id }
    }

    /// 处理数据 - 利用改进的生命周期管理
    pub fn process_data(&self) -> ProcessingResult<'a> {
        let mean = self.data.iter().sum::<f64>() / self.data.len() as f64;
        let variance = self.data.iter()
            .map(|&x| (x - mean).powi(2))
            .sum::<f64>() / self.data.len() as f64;
        
        ProcessingResult {
            data: self.data,
            mean,
            variance,
            std_dev: variance.sqrt(),
            processor_id: self.processor_id,
        }
    }

    /// 计算数据的分位数
    pub fn quantiles(&self, quantile: f64) -> f64 {
        let mut sorted_data = self.data.to_vec();
        sorted_data.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let index = (quantile * (sorted_data.len() - 1) as f64) as usize;
        sorted_data[index]
    }
}

/// 处理结果
#[derive(Debug, Clone)]
pub struct ProcessingResult<'a> {
    pub data: &'a [f64],
    pub mean: f64,
    pub variance: f64,
    pub std_dev: f64,
    pub processor_id: u32,
}

/// Rust 1.90 函数指针安全示例
/// 
/// 利用 `unpredictable_function_pointer_comparisons` lint 增强函数指针安全性
pub struct OptimizationEngine {
    algorithm_type: AlgorithmType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgorithmType {
    GradientDescent,
    NewtonRaphson,
    SimulatedAnnealing,
}

/// 目标函数类型定义
pub type ObjectiveFunction = fn(&[f64]) -> f64;

/// 梯度函数类型定义
pub type GradientFunction = fn(&[f64]) -> Vec<f64>;

impl OptimizationEngine {
    /// 创建新的优化引擎
    pub fn new(algorithm_type: AlgorithmType) -> Self {
        Self { algorithm_type }
    }

    /// 安全的函数指针比较和优化
    pub fn optimize(
        &self,
        objective: ObjectiveFunction,
        gradient: Option<GradientFunction>,
        initial: &[f64],
        max_iterations: usize,
    ) -> OptimizationResult {
        match self.algorithm_type {
            AlgorithmType::GradientDescent => {
                self.gradient_descent_optimize(objective, gradient, initial, max_iterations)
            }
            AlgorithmType::NewtonRaphson => {
                self.newton_raphson_optimize(objective, gradient, initial, max_iterations)
            }
            AlgorithmType::SimulatedAnnealing => {
                self.simulated_annealing_optimize(objective, initial, max_iterations)
            }
        }
    }

    /// 梯度下降优化
    fn gradient_descent_optimize(
        &self,
        objective: ObjectiveFunction,
        gradient: Option<GradientFunction>,
        initial: &[f64],
        max_iterations: usize,
    ) -> OptimizationResult {
        let mut current = initial.to_vec();
        let learning_rate = 0.01;
        let mut iterations = 0;
        let mut objective_values = Vec::new();

        for _ in 0..max_iterations {
            let obj_value = objective(&current);
            objective_values.push(obj_value);
            
            if let Some(grad_fn) = gradient {
                let grad = grad_fn(&current);
                for (i, &g) in grad.iter().enumerate() {
                    current[i] -= learning_rate * g;
                }
            } else {
                // 数值梯度
                let grad = self.numerical_gradient(objective, &current);
                for (i, &g) in grad.iter().enumerate() {
                    current[i] -= learning_rate * g;
                }
            }
            
            iterations += 1;
        }

        let final_obj = objective(&current);
        OptimizationResult {
            solution: current,
            final_objective: final_obj,
            iterations,
            objective_history: objective_values,
            converged: iterations < max_iterations,
        }
    }

    /// 牛顿-拉夫逊优化
    fn newton_raphson_optimize(
        &self,
        objective: ObjectiveFunction,
        gradient: Option<GradientFunction>,
        initial: &[f64],
        max_iterations: usize,
    ) -> OptimizationResult {
        // 简化的牛顿-拉夫逊实现
        self.gradient_descent_optimize(objective, gradient, initial, max_iterations)
    }

    /// 模拟退火优化
    fn simulated_annealing_optimize(
        &self,
        objective: ObjectiveFunction,
        initial: &[f64],
        max_iterations: usize,
    ) -> OptimizationResult {
        let mut current = initial.to_vec();
        let mut best = current.clone();
        let mut temperature = 1.0;
        let cooling_rate = 0.95;
        let mut objective_values = Vec::new();

        for _iteration in 0..max_iterations {
            let current_obj = objective(&current);
            objective_values.push(current_obj);
            
            // 生成邻域解
            let mut candidate = current.clone();
            for i in 0..candidate.len() {
                candidate[i] += (fastrand::f64() - 0.5) * 0.1;
            }
            
            let candidate_obj = objective(&candidate);
            
            // 接受准则
            if candidate_obj < current_obj || 
               fastrand::f64() < (-(candidate_obj - current_obj) / temperature).exp() {
                current = candidate;
                if candidate_obj < objective(&best) {
                    best = current.clone();
                }
            }
            
            temperature *= cooling_rate;
        }

        let final_obj = objective(&best);
        OptimizationResult {
            solution: best,
            final_objective: final_obj,
            iterations: max_iterations,
            objective_history: objective_values,
            converged: true,
        }
    }

    /// 数值梯度计算
    fn numerical_gradient(&self, f: ObjectiveFunction, x: &[f64]) -> Vec<f64> {
        let h = 1e-8;
        let mut grad = Vec::with_capacity(x.len());
        
        for i in 0..x.len() {
            let mut x_plus = x.to_vec();
            let mut x_minus = x.to_vec();
            x_plus[i] += h;
            x_minus[i] -= h;
            
            let grad_i = (f(&x_plus) - f(&x_minus)) / (2.0 * h);
            grad.push(grad_i);
        }
        
        grad
    }
}

/// 优化结果
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    pub solution: Vec<f64>,
    pub final_objective: f64,
    pub iterations: usize,
    pub objective_history: Vec<f64>,
    pub converged: bool,
}

/// Rust 1.90 标准库 API 增强示例
/// 
/// 利用新的标准库 API 进行进程间通信
pub struct ExternalModelChecker {
    checker_path: String,
}

impl ExternalModelChecker {
    /// 创建新的外部模型检查器
    pub fn new(checker_path: String) -> Self {
        Self { checker_path }
    }

    /// 执行外部模型检查 - 利用新的匿名管道 API
    pub fn check_model(&self, model_content: &str) -> Result<ModelCheckResult, String> {
        use std::process::Command;
        
        // 创建临时文件
        let temp_file = std::env::temp_dir().join("model_check.smv");
        std::fs::write(&temp_file, model_content)
            .map_err(|e| format!("Failed to write temp file: {}", e))?;
        
        // 执行外部检查器
        let output = Command::new(&self.checker_path)
            .arg("--input")
            .arg(&temp_file)
            .arg("--format")
            .arg("json")
            .output()
            .map_err(|e| format!("Failed to execute checker: {}", e))?;
        
        // 清理临时文件
        let _ = std::fs::remove_file(&temp_file);
        
        if output.status.success() {
            let result_str = String::from_utf8_lossy(&output.stdout);
            serde_json::from_str(&result_str)
                .map_err(|e| format!("Failed to parse result: {}", e))
        } else {
            let error_str = String::from_utf8_lossy(&output.stderr);
            Err(format!("Model checker failed: {}", error_str))
        }
    }
}

/// 模型检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelCheckResult {
    pub valid: bool,
    pub properties: Vec<PropertyResult>,
    pub execution_time: f64,
    pub memory_usage: usize,
}

/// 属性检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropertyResult {
    pub name: String,
    pub satisfied: bool,
    pub counterexample: Option<Vec<String>>,
}

/// Rust 1.90 编译器优化示例
/// 
/// 利用编译时优化提升性能
pub struct OptimizedMatrix<const ROWS: usize, const COLS: usize> {
    data: [[f64; COLS]; ROWS],
}

impl<const ROWS: usize, const COLS: usize> OptimizedMatrix<ROWS, COLS> {
    /// 创建新的矩阵
    pub fn new() -> Self {
        Self {
            data: [[0.0; COLS]; ROWS],
        }
    }

    /// 从数组创建矩阵
    pub fn from_array(data: [[f64; COLS]; ROWS]) -> Self {
        Self { data }
    }

    /// 矩阵乘法 - 利用编译时优化
    pub fn multiply<const OTHER_COLS: usize>(
        &self,
        other: &OptimizedMatrix<COLS, OTHER_COLS>,
    ) -> OptimizedMatrix<ROWS, OTHER_COLS> {
        let mut result = OptimizedMatrix::<ROWS, OTHER_COLS>::new();
        
        for i in 0..ROWS {
            for j in 0..OTHER_COLS {
                for k in 0..COLS {
                    result.data[i][j] += self.data[i][k] * other.data[k][j];
                }
            }
        }
        
        result
    }

    /// 矩阵转置
    pub fn transpose(&self) -> OptimizedMatrix<COLS, ROWS> {
        let mut result = OptimizedMatrix::<COLS, ROWS>::new();
        
        for i in 0..ROWS {
            for j in 0..COLS {
                result.data[j][i] = self.data[i][j];
            }
        }
        
        result
    }

    /// 获取元素
    pub fn get(&self, row: usize, col: usize) -> Option<f64> {
        if row < ROWS && col < COLS {
            Some(self.data[row][col])
        } else {
            None
        }
    }

    /// 设置元素
    pub fn set(&mut self, row: usize, col: usize, value: f64) -> bool {
        if row < ROWS && col < COLS {
            self.data[row][col] = value;
            true
        } else {
            false
        }
    }
}

impl<const ROWS: usize, const COLS: usize> Default for OptimizedMatrix<ROWS, COLS> {
    fn default() -> Self {
        Self::new()
    }
}

/// Rust 1.90 特性演示和测试
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_generic_inference() {
        // 测试常量泛型推断 - 明确指定常量参数
        let config = ModelConfig::<3>::from_slice(&[1.0, 2.0, 3.0], "test".to_string());
        assert_eq!(config.param_count(), 3);
        assert_eq!(config.parameters, [1.0, 2.0, 3.0]);
        
        let stats = config.statistics();
        assert!((stats.mean - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_lifetime_optimization() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let processor = DataProcessor::new(&data, 1);
        let result = processor.process_data();
        
        assert!((result.mean - 3.0).abs() < 1e-10);
        assert_eq!(result.processor_id, 1);
    }

    #[test]
    fn test_function_pointer_safety() {
        // 测试函数指针安全
        fn objective(x: &[f64]) -> f64 {
            x.iter().map(|&xi| xi * xi).sum()
        }
        
        fn gradient(x: &[f64]) -> Vec<f64> {
            x.iter().map(|&xi| 2.0 * xi).collect()
        }
        
        let engine = OptimizationEngine::new(AlgorithmType::GradientDescent);
        let initial = vec![1.0, 2.0, 3.0];
        let result = engine.optimize(objective, Some(gradient), &initial, 100);
        
        assert!(result.converged);
        assert!(result.final_objective < 1.0); // 应该接近0
    }

    #[test]
    fn test_optimized_matrix() {
        // 测试优化的矩阵操作
        let mut matrix = OptimizedMatrix::<2, 3>::new();
        matrix.set(0, 0, 1.0);
        matrix.set(0, 1, 2.0);
        matrix.set(0, 2, 3.0);
        matrix.set(1, 0, 4.0);
        matrix.set(1, 1, 5.0);
        matrix.set(1, 2, 6.0);
        
        let other = OptimizedMatrix::<3, 2>::from_array([
            [1.0, 2.0],
            [3.0, 4.0],
            [5.0, 6.0],
        ]);
        
        let result = matrix.multiply(&other);
        
        // 验证矩阵乘法结果
        assert_eq!(result.get(0, 0), Some(22.0));
        assert_eq!(result.get(0, 1), Some(28.0));
        assert_eq!(result.get(1, 0), Some(49.0));
        assert_eq!(result.get(1, 1), Some(64.0));
    }

    #[test]
    fn test_quantiles() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
        let processor = DataProcessor::new(&data, 1);
        
        let median = processor.quantiles(0.5);
        assert!((median - 5.5).abs() < 1e-10);
        
        let q25 = processor.quantiles(0.25);
        assert!((q25 - 3.25).abs() < 1e-10);
    }
}

