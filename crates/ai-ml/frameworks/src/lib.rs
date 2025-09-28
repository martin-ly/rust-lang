//! AI/ML框架集成与性能优化
//! 
//! 本模块提供了 Candle、Tch、ONNX Runtime 等AI/ML框架的
//! 集成、性能对比和优化策略。

pub mod candle_integration;
pub mod tch_bindings;
pub mod ort_optimization;
pub mod performance;
pub mod benchmarks;

use std::time::Duration;

/// AI/ML框架类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MLFramework {
    Candle,
    // Tch,  // 暂时注释，需要PyTorch库
    // ONNXRuntime,  // 暂时注释，版本问题
}

/// 模型类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModelType {
    Transformer,
    CNN,
    RNN,
    LSTM,
    GRU,
    Linear,
    Custom,
}

/// 硬件加速类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HardwareAcceleration {
    CPU,
    CUDA,
    Metal,
    OpenCL,
    WebGPU,
}

/// 模型性能指标
#[derive(Debug, Clone)]
pub struct ModelPerformance {
    pub framework: MLFramework,
    pub model_type: ModelType,
    pub hardware: HardwareAcceleration,
    pub inference_time: Duration,
    pub throughput: f64, // 样本/秒
    pub memory_usage: u64,
    pub gpu_memory_usage: Option<u64>,
    pub accuracy: Option<f64>,
    pub model_size: u64,
}

/// AI/ML框架分析器
pub struct MLFrameworkAnalyzer {
    performance_data: Vec<ModelPerformance>,
}

impl MLFrameworkAnalyzer {
    /// 创建新的分析器
    pub fn new() -> Self {
        Self {
            performance_data: Vec::new(),
        }
    }
    
    /// 添加性能数据
    pub fn add_performance(&mut self, performance: ModelPerformance) {
        self.performance_data.push(performance);
    }
    
    /// 生成性能对比报告
    pub fn generate_performance_report(&self) -> String {
        let mut report = String::new();
        report.push_str("# AI/ML框架性能对比报告\n\n");
        
        // 按模型类型分组
        let mut grouped: std::collections::HashMap<ModelType, Vec<&ModelPerformance>> = std::collections::HashMap::new();
        for perf in &self.performance_data {
            grouped.entry(perf.model_type).or_default().push(perf);
        }
        
        for (model_type, performances) in grouped {
            report.push_str(&format!("## {:?} 模型性能对比\n\n", model_type));
            
            // 找出最佳性能
            if let Some(best) = performances.iter().max_by(|a, b| a.throughput.partial_cmp(&b.throughput).unwrap()) {
                report.push_str(&format!("**最高吞吐量**: {:?} + {:?}\n", best.framework, best.hardware));
                report.push_str(&format!("- 推理时间: {:?}\n", best.inference_time));
                report.push_str(&format!("- 吞吐量: {:.2} 样本/秒\n", best.throughput));
                report.push_str(&format!("- 内存使用: {} MB\n", best.memory_usage / 1024 / 1024));
                if let Some(gpu_mem) = best.gpu_memory_usage {
                    report.push_str(&format!("- GPU内存: {} MB\n", gpu_mem / 1024 / 1024));
                }
                report.push_str(&format!("- 模型大小: {} MB\n\n", best.model_size / 1024 / 1024));
            }
            
            // 详细对比表格
            report.push_str("### 性能指标对比\n\n");
            report.push_str("| 框架 | 硬件 | 推理时间 | 吞吐量 | 内存(MB) | GPU内存(MB) | 模型大小(MB) |\n");
            report.push_str("|------|------|----------|--------|----------|-------------|-------------|\n");
            
            for perf in performances {
                let gpu_mem_str = perf.gpu_memory_usage
                    .map(|mem| format!("{}", mem / 1024 / 1024))
                    .unwrap_or_else(|| "N/A".to_string());
                
                report.push_str(&format!(
                    "| {:?} | {:?} | {:?} | {:.2} | {} | {} | {} |\n",
                    perf.framework,
                    perf.hardware,
                    perf.inference_time,
                    perf.throughput,
                    perf.memory_usage / 1024 / 1024,
                    gpu_mem_str,
                    perf.model_size / 1024 / 1024
                ));
            }
            report.push_str("\n");
        }
        
        // 框架特性对比
        report.push_str("## 框架特性对比\n\n");
        report.push_str("| 特性 | Candle | Tch | ONNX Runtime |\n");
        report.push_str("|------|--------|-----|-------------|\n");
        report.push_str("| 性能 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |\n");
        report.push_str("| 易用性 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |\n");
        report.push_str("| 模型支持 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |\n");
        report.push_str("| 硬件加速 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |\n");
        report.push_str("| 内存效率 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |\n");
        report.push_str("| 生态系统 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |\n");
        report.push_str("| 部署便利性 | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ |\n\n");
        
        // 使用建议
        report.push_str("## 使用建议\n\n");
        report.push_str("### 🕯️ Candle\n");
        report.push_str("- **适用场景**: 新项目、原型开发、边缘设备\n");
        report.push_str("- **优势**: 纯Rust实现、内存安全、部署简单\n");
        report.push_str("- **推荐指数**: ⭐⭐⭐⭐\n\n");
        
        report.push_str("### 🔥 Tch (PyTorch绑定)\n");
        report.push_str("- **适用场景**: 研究、复杂模型、GPU加速\n");
        report.push_str("- **优势**: 成熟生态、强大功能、GPU支持\n");
        report.push_str("- **推荐指数**: ⭐⭐⭐⭐⭐\n\n");
        
        report.push_str("### 🚀 ONNX Runtime\n");
        report.push_str("- **适用场景**: 生产环境、多框架支持、优化推理\n");
        report.push_str("- **优势**: 高性能、多硬件支持、模型互操作\n");
        report.push_str("- **推荐指数**: ⭐⭐⭐⭐⭐\n\n");
        
        // 硬件选择建议
        report.push_str("## 硬件选择建议\n\n");
        report.push_str("### 🖥️ CPU\n");
        report.push_str("- **适用**: 小模型、CPU推理、边缘设备\n");
        report.push_str("- **推荐框架**: Candle, ONNX Runtime\n\n");
        
        report.push_str("### 🎮 GPU (CUDA)\n");
        report.push_str("- **适用**: 大模型、训练、高性能推理\n");
        report.push_str("- **推荐框架**: Tch, ONNX Runtime\n\n");
        
        report.push_str("### 🍎 Metal (Apple Silicon)\n");
        report.push_str("- **适用**: Mac设备、移动设备\n");
        report.push_str("- **推荐框架**: Tch, ONNX Runtime\n\n");
        
        report
    }
    
    /// 获取最佳框架建议
    pub fn get_framework_recommendation(&self, requirements: &str) -> MLFramework {
        match requirements.to_lowercase().as_str() {
            // "research" | "training" | "gpu" => MLFramework::Tch,  // 暂时注释
            // "production" | "deployment" | "optimization" => MLFramework::ONNXRuntime,  // 暂时注释
            "new-project" | "rust-native" | "safety" | "research" | "training" | "production" | "deployment" | "optimization" => MLFramework::Candle,
            _ => MLFramework::Candle, // 默认推荐
        }
    }
    
    /// 获取最佳硬件建议
    pub fn get_hardware_recommendation(&self, model_size: u64, budget: &str) -> HardwareAcceleration {
        match (model_size, budget.to_lowercase().as_str()) {
            (size, _) if size > 1_000_000_000 => HardwareAcceleration::CUDA, // > 1GB模型
            (_, "high" | "unlimited") => HardwareAcceleration::CUDA,
            (_, "medium") => HardwareAcceleration::Metal,
            (_, "low" | "minimal") => HardwareAcceleration::CPU,
            _ => HardwareAcceleration::CPU, // 默认
        }
    }
}

impl Default for MLFrameworkAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_analyzer_creation() {
        let analyzer = MLFrameworkAnalyzer::new();
        assert!(analyzer.performance_data.is_empty());
    }
    
    #[test]
    fn test_add_performance() {
        let mut analyzer = MLFrameworkAnalyzer::new();
        let performance = ModelPerformance {
            framework: MLFramework::Candle,
            model_type: ModelType::Transformer,
            hardware: HardwareAcceleration::CPU,
            inference_time: Duration::from_millis(100),
            throughput: 100.0,
            memory_usage: 1024 * 1024,
            gpu_memory_usage: None,
            accuracy: Some(0.95),
            model_size: 100 * 1024 * 1024,
        };
        
        analyzer.add_performance(performance);
        assert_eq!(analyzer.performance_data.len(), 1);
    }
    
    #[test]
    fn test_framework_recommendation() {
        let analyzer = MLFrameworkAnalyzer::new();
        assert_eq!(analyzer.get_framework_recommendation("research"), MLFramework::Tch);
        assert_eq!(analyzer.get_framework_recommendation("production"), MLFramework::ONNXRuntime);
        assert_eq!(analyzer.get_framework_recommendation("new-project"), MLFramework::Candle);
    }
    
    #[test]
    fn test_hardware_recommendation() {
        let analyzer = MLFrameworkAnalyzer::new();
        assert_eq!(analyzer.get_hardware_recommendation(100_000_000, "high"), HardwareAcceleration::CUDA);
        assert_eq!(analyzer.get_hardware_recommendation(10_000_000, "medium"), HardwareAcceleration::Metal);
        assert_eq!(analyzer.get_hardware_recommendation(1_000_000, "low"), HardwareAcceleration::CPU);
    }
}
