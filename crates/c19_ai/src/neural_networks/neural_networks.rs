// 神经网络模块
// Neural Networks Module

use serde::{Deserialize, Serialize};

/// 神经网络层
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeuralLayer {
    pub weights: Vec<Vec<f64>>,
    pub biases: Vec<f64>,
    pub activation: ActivationFunction,
}

/// 激活函数类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ActivationFunction {
    ReLU,
    Sigmoid,
    Tanh,
    Linear,
}

impl ActivationFunction {
    pub fn apply(&self, x: f64) -> f64 {
        match self {
            ActivationFunction::ReLU => x.max(0.0),
            ActivationFunction::Sigmoid => 1.0 / (1.0 + (-x).exp()),
            ActivationFunction::Tanh => x.tanh(),
            ActivationFunction::Linear => x,
        }
    }
}

/// 神经网络结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeuralNetwork {
    pub layers: Vec<NeuralLayer>,
    pub input_size: usize,
    pub output_size: usize,
}

impl NeuralNetwork {
    /// 创建新的神经网络
    pub fn new(input_size: usize, hidden_sizes: Vec<usize>, output_size: usize) -> Self {
        let mut layers = Vec::new();
        let mut prev_size = input_size;
        
        // 创建隐藏层
        for &hidden_size in &hidden_sizes {
            layers.push(NeuralLayer {
                weights: vec![vec![0.0; prev_size]; hidden_size],
                biases: vec![0.0; hidden_size],
                activation: ActivationFunction::ReLU,
            });
            prev_size = hidden_size;
        }
        
        // 创建输出层
        layers.push(NeuralLayer {
            weights: vec![vec![0.0; prev_size]; output_size],
            biases: vec![0.0; output_size],
            activation: ActivationFunction::Linear,
        });
        
        Self {
            layers,
            input_size,
            output_size,
        }
    }
    
    /// 前向传播
    pub fn forward(&self, input: &[f64]) -> Vec<f64> {
        let mut current = input.to_vec();
        
        for layer in &self.layers {
            let mut next = Vec::new();
            
            for (i, bias) in layer.biases.iter().enumerate() {
                let mut sum = *bias;
                for (j, &weight) in layer.weights[i].iter().enumerate() {
                    if j < current.len() {
                        sum += weight * current[j];
                    }
                }
                next.push(layer.activation.apply(sum));
            }
            
            current = next;
        }
        
        current
    }
    
    /// 随机初始化权重
    pub fn random_init(&mut self) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        for layer in &mut self.layers {
            for i in 0..layer.weights.len() {
                for j in 0..layer.weights[i].len() {
                    let mut hasher = DefaultHasher::new();
                    (i, j).hash(&mut hasher);
                    let hash = hasher.finish();
                    layer.weights[i][j] = (hash as f64 / u64::MAX as f64) * 2.0 - 1.0;
                }
            }
            
            for i in 0..layer.biases.len() {
                let mut hasher = DefaultHasher::new();
                i.hash(&mut hasher);
                let hash = hasher.finish();
                layer.biases[i] = (hash as f64 / u64::MAX as f64) * 2.0 - 1.0;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_neural_network_creation() {
        let network = NeuralNetwork::new(2, vec![3, 4], 1);
        assert_eq!(network.input_size, 2);
        assert_eq!(network.output_size, 1);
        assert_eq!(network.layers.len(), 3);
    }
    
    #[test]
    fn test_forward_propagation() {
        let mut network = NeuralNetwork::new(2, vec![2], 1);
        network.random_init();
        
        let input = vec![1.0, 0.5];
        let output = network.forward(&input);
        
        assert_eq!(output.len(), 1);
    }
    
    #[test]
    fn test_activation_functions() {
        let relu = ActivationFunction::ReLU;
        assert_eq!(relu.apply(5.0), 5.0);
        assert_eq!(relu.apply(-3.0), 0.0);
        
        let sigmoid = ActivationFunction::Sigmoid;
        assert!(sigmoid.apply(0.0) > 0.4 && sigmoid.apply(0.0) < 0.6);
    }
}
