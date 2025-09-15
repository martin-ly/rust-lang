//! 神经网络实现
//! 
//! 本模块提供了基础的神经网络实现，包括：
//! - 多层感知机 (MLP)
//! - 前向传播
//! - 反向传播

use super::*;

/// 激活函数类型
#[derive(Debug, Clone)]
pub enum ActivationFunction {
    Sigmoid,
    ReLU,
    Tanh,
    Linear,
}

impl ActivationFunction {
    /// 计算激活函数值
    pub fn apply(&self, x: f64) -> f64 {
        match self {
            ActivationFunction::Sigmoid => 1.0 / (1.0 + (-x).exp()),
            ActivationFunction::ReLU => x.max(0.0),
            ActivationFunction::Tanh => x.tanh(),
            ActivationFunction::Linear => x,
        }
    }
    
    /// 计算激活函数的导数
    pub fn derivative(&self, x: f64) -> f64 {
        match self {
            ActivationFunction::Sigmoid => {
                let s = self.apply(x);
                s * (1.0 - s)
            },
            ActivationFunction::ReLU => if x > 0.0 { 1.0 } else { 0.0 },
            ActivationFunction::Tanh => 1.0 - x.tanh().powi(2),
            ActivationFunction::Linear => 1.0,
        }
    }
}

/// 神经网络层
#[derive(Debug, Clone)]
pub struct Layer {
    /// 权重矩阵 (输出维度 x 输入维度)
    weights: Vec<Vec<f64>>,
    /// 偏置向量
    biases: Vec<f64>,
    /// 激活函数
    activation: ActivationFunction,
}

impl Layer {
    /// 创建新的层
    pub fn new(input_size: usize, output_size: usize, activation: ActivationFunction) -> Self {
        use rand::{Rng, rngs::ThreadRng};
        let mut rng = ThreadRng::default();
        
        // Xavier 初始化
        let scale = (2.0 / (input_size + output_size) as f64).sqrt();
        
        let weights = (0..output_size)
            .map(|_| {
                (0..input_size)
                    .map(|_| rng.random_range(-scale..scale))
                    .collect()
            })
            .collect();
            
        let biases = vec![0.0; output_size];
        
        Self {
            weights,
            biases,
            activation,
        }
    }
    
    /// 前向传播
    pub fn forward(&self, input: &[f64]) -> Vec<f64> {
        self.weights
            .iter()
            .zip(self.biases.iter())
            .map(|(weight_row, &bias)| {
                let linear_output = weight_row
                    .iter()
                    .zip(input.iter())
                    .map(|(&w, &x)| w * x)
                    .sum::<f64>() + bias;
                self.activation.apply(linear_output)
            })
            .collect()
    }
    
    /// 获取权重的可变引用
    pub fn weights_mut(&mut self) -> &mut Vec<Vec<f64>> {
        &mut self.weights
    }
    
    /// 获取偏置的可变引用
    pub fn biases_mut(&mut self) -> &mut Vec<f64> {
        &mut self.biases
    }
    
    /// 获取激活函数
    pub fn activation(&self) -> &ActivationFunction {
        &self.activation
    }
}

/// 多层感知机
#[derive(Debug, Clone)]
pub struct MLP {
    /// 网络层
    layers: Vec<Layer>,
    /// 学习率
    learning_rate: f64,
    /// 是否已训练
    is_fitted: bool,
}

impl MLP {
    /// 创建新的 MLP
    pub fn new(layer_sizes: &[usize], activations: Vec<ActivationFunction>, learning_rate: f64) -> MLResult<Self> {
        if layer_sizes.len() < 2 {
            return Err(MLError::InvalidInput("至少需要2层（输入层和输出层）".to_string()));
        }
        
        if activations.len() != layer_sizes.len() - 1 {
            return Err(MLError::InvalidInput("激活函数数量必须等于层数减1".to_string()));
        }
        
        let layers = layer_sizes
            .windows(2)
            .zip(activations.into_iter())
            .map(|(sizes, activation)| Layer::new(sizes[0], sizes[1], activation))
            .collect();
            
        Ok(Self {
            layers,
            learning_rate,
            is_fitted: false,
        })
    }
    
    /// 前向传播
    pub fn forward(&self, input: &[f64]) -> Vec<f64> {
        self.layers.iter().fold(input.to_vec(), |acc, layer| layer.forward(&acc))
    }
    
    /// 计算损失（均方误差）
    pub fn loss(&self, predictions: &[f64], targets: &[f64]) -> f64 {
        predictions
            .iter()
            .zip(targets.iter())
            .map(|(pred, target)| (pred - target).powi(2))
            .sum::<f64>() / predictions.len() as f64
    }
    
    /// 反向传播训练
    pub fn train_step(&mut self, input: &[f64], target: &[f64]) -> MLResult<f64> {
        // 前向传播，保存中间结果
        let mut activations = vec![input.to_vec()];
        let mut linear_outputs = Vec::new();
        
        for layer in &self.layers {
            let current_input = activations.last().unwrap();
            let mut linear_output = Vec::new();
            let mut activation_output = Vec::new();
            
            for (weight_row, &bias) in layer.weights.iter().zip(layer.biases.iter()) {
                let linear = weight_row
                    .iter()
                    .zip(current_input.iter())
                    .map(|(&w, &x)| w * x)
                    .sum::<f64>() + bias;
                linear_output.push(linear);
                activation_output.push(layer.activation.apply(linear));
            }
            
            linear_outputs.push(linear_output);
            activations.push(activation_output);
        }
        
        let predictions = activations.last().unwrap();
        let loss = self.loss(predictions, target);
        
        // 反向传播
        let mut deltas = Vec::new();
        
        // 输出层误差
        let output_errors: Vec<f64> = predictions
            .iter()
            .zip(target.iter())
            .zip(linear_outputs.last().unwrap().iter())
            .map(|((&pred, &target), &linear)| {
                let error = pred - target;
                let activation_derivative = self.layers.last().unwrap().activation.derivative(linear);
                error * activation_derivative
            })
            .collect();
        deltas.push(output_errors);
        
        // 隐藏层误差
        for i in (0..self.layers.len() - 1).rev() {
            let current_errors = &deltas[deltas.len() - 1];
            let next_layer = &self.layers[i + 1];
            
            let errors: Vec<f64> = (0..self.layers[i].weights.len())
                .map(|j| {
                    let error_sum = current_errors
                        .iter()
                        .enumerate()
                        .map(|(k, &error)| error * next_layer.weights[k][j])
                        .sum::<f64>();
                    let activation_derivative = self.layers[i].activation.derivative(linear_outputs[i][j]);
                    error_sum * activation_derivative
                })
                .collect();
            deltas.push(errors);
        }
        
        deltas.reverse();
        
        // 更新权重和偏置
        for (i, layer) in self.layers.iter_mut().enumerate() {
            let layer_input = &activations[i];
            let layer_errors = &deltas[i];
            
            // 更新权重
            for (j, weight_row) in layer.weights_mut().iter_mut().enumerate() {
                for (k, weight) in weight_row.iter_mut().enumerate() {
                    *weight -= self.learning_rate * layer_errors[j] * layer_input[k];
                }
            }
            
            // 更新偏置
            for (j, bias) in layer.biases_mut().iter_mut().enumerate() {
                *bias -= self.learning_rate * layer_errors[j];
            }
        }
        
        Ok(loss)
    }
}

impl SupervisedLearning for MLP {
    fn train(&mut self, data: &Dataset, labels: &Labels) -> MLResult<()> {
        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }
        
        // 将标签转换为 one-hot 编码
        let unique_labels: std::collections::HashSet<_> = labels.iter().collect();
        let num_classes = unique_labels.len();
        
        if num_classes < 2 {
            return Err(MLError::InvalidInput("至少需要2个类别".to_string()));
        }
        
        let label_to_index: std::collections::HashMap<_, _> = unique_labels
            .iter()
            .enumerate()
            .map(|(i, &label)| (label, i))
            .collect();
        
        // 训练多个 epoch
        let epochs = 100;
        for epoch in 0..epochs {
            let mut total_loss = 0.0;
            
            for (sample, &label) in data.iter().zip(labels.iter()) {
                // 创建 one-hot 编码目标
                let mut target = vec![0.0; num_classes];
                if let Some(&class_index) = label_to_index.get(&label) {
                    target[class_index] = 1.0;
                }
                
                let loss = self.train_step(sample, &target)?;
                total_loss += loss;
            }
            
            let avg_loss = total_loss / data.len() as f64;
            if epoch % 10 == 0 {
                tracing::info!("Epoch {}: 平均损失 = {:.6}", epoch, avg_loss);
            }
            
            // 早停条件
            if avg_loss < 1e-6 {
                tracing::info!("在第 {} 个 epoch 收敛", epoch);
                break;
            }
        }
        
        self.is_fitted = true;
        Ok(())
    }
    
    fn predict(&self, sample: &DataPoint) -> MLResult<Label> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }
        
        let output = self.forward(sample);
        let predicted_class = output
            .iter()
            .enumerate()
            .max_by(|a, b| a.1.partial_cmp(b.1).unwrap())
            .map(|(i, _)| i as Label)
            .unwrap_or(0);
            
        Ok(predicted_class)
    }
}

impl Regression for MLP {
    fn train(&mut self, data: &Dataset, targets: &[f64]) -> MLResult<()> {
        if data.len() != targets.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: targets.len(),
            });
        }
        
        // 训练多个 epoch
        let epochs = 100;
        for epoch in 0..epochs {
            let mut total_loss = 0.0;
            
            for (sample, &target) in data.iter().zip(targets.iter()) {
                let loss = self.train_step(sample, &[target])?;
                total_loss += loss;
            }
            
            let avg_loss = total_loss / data.len() as f64;
            if epoch % 10 == 0 {
                tracing::info!("Epoch {}: 平均损失 = {:.6}", epoch, avg_loss);
            }
            
            // 早停条件
            if avg_loss < 1e-6 {
                tracing::info!("在第 {} 个 epoch 收敛", epoch);
                break;
            }
        }
        
        self.is_fitted = true;
        Ok(())
    }
    
    fn predict(&self, sample: &DataPoint) -> MLResult<f64> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }
        
        let output = self.forward(sample);
        Ok(output[0])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_activation_functions() {
        let sigmoid = ActivationFunction::Sigmoid;
        assert!(sigmoid.apply(0.0) - 0.5 < 1e-10);
        
        let relu = ActivationFunction::ReLU;
        assert_eq!(relu.apply(-1.0), 0.0);
        assert_eq!(relu.apply(1.0), 1.0);
        
        let tanh = ActivationFunction::Tanh;
        assert!(tanh.apply(0.0).abs() < 1e-10);
    }
    
    #[test]
    fn test_layer_creation() {
        let layer = Layer::new(3, 2, ActivationFunction::ReLU);
        assert_eq!(layer.weights.len(), 2);
        assert_eq!(layer.weights[0].len(), 3);
        assert_eq!(layer.biases.len(), 2);
    }
    
    #[test]
    fn test_layer_forward() {
        let layer = Layer::new(2, 1, ActivationFunction::Linear);
        let input = vec![1.0, 2.0];
        let output = layer.forward(&input);
        assert_eq!(output.len(), 1);
    }
    
    #[test]
    fn test_mlp_creation() {
        let layer_sizes = vec![2, 3, 1];
        let activations = vec![ActivationFunction::ReLU, ActivationFunction::Sigmoid];
        let mlp = MLP::new(&layer_sizes, activations, 0.01);
        assert!(mlp.is_ok());
        
        let mlp = mlp.unwrap();
        assert_eq!(mlp.layers.len(), 2);
    }
    
    #[test]
    fn test_mlp_forward() {
        let layer_sizes = vec![2, 3, 1];
        let activations = vec![ActivationFunction::ReLU, ActivationFunction::Sigmoid];
        let mlp = MLP::new(&layer_sizes, activations, 0.01).unwrap();
        
        let input = vec![1.0, 2.0];
        let output = mlp.forward(&input);
        assert_eq!(output.len(), 1);
        assert!(output[0] >= 0.0 && output[0] <= 1.0); // Sigmoid 输出范围
    }
    
    #[test]
    fn test_mlp_regression_training() {
        let layer_sizes = vec![1, 5, 1];
        let activations = vec![ActivationFunction::ReLU, ActivationFunction::Linear];
        let mut mlp = MLP::new(&layer_sizes, activations, 0.05).unwrap();
        
        // 简单的线性关系数据 y = 2x
        let data = vec![
            vec![1.0], vec![2.0], vec![3.0], vec![4.0]
        ];
        let targets = vec![2.0, 4.0, 6.0, 8.0];
        
        // 计算初始损失
        let preds_before: Vec<f64> = data.iter().map(|s| mlp.forward(s)[0]).collect();
        let loss_before = mlp.loss(&preds_before, &targets);
        
        // 进行若干步训练
        for (sample, &target) in data.iter().zip(targets.iter()) {
            let _ = mlp.train_step(sample, &[target]).unwrap();
        }
        
        // 训练后损失应降低
        let preds_after: Vec<f64> = data.iter().map(|s| mlp.forward(s)[0]).collect();
        let loss_after = mlp.loss(&preds_after, &targets);
        assert!(loss_after < loss_before);
    }
}
