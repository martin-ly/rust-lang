//! 回归算法实现
//!
//! 本模块提供了回归算法的实现，包括线性回归等

use super::*;

/// 线性回归模型
#[derive(Debug, Clone)]
pub struct LinearRegression {
    /// 权重系数
    coefficients: Option<Vec<f64>>,
    /// 截距
    intercept: Option<f64>,
    /// 是否已训练
    is_fitted: bool,
}

impl LinearRegression {
    /// 创建新的线性回归模型
    pub fn new() -> Self {
        Self {
            coefficients: None,
            intercept: None,
            is_fitted: false,
        }
    }

    /// 获取模型参数
    pub fn parameters(&self) -> Option<(Vec<f64>, f64)> {
        if let (Some(coef), Some(intercept)) = (&self.coefficients, &self.intercept) {
            Some((coef.clone(), *intercept))
        } else {
            None
        }
    }
}

impl Default for LinearRegression {
    fn default() -> Self {
        Self::new()
    }
}

impl Regression for LinearRegression {
    fn train(&mut self, data: &Dataset, targets: &[f64]) -> MLResult<()> {
        if data.len() != targets.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: targets.len(),
            });
        }

        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集不能为空".to_string()));
        }

        let n_samples = data.len();
        let n_features = data[0].len();

        // 使用最小二乘法求解
        // X^T * X * beta = X^T * y

        // 构建设计矩阵 (添加截距项)
        let mut x_matrix = vec![vec![0.0; n_features + 1]; n_samples];
        for (i, sample) in data.iter().enumerate() {
            x_matrix[i][0] = 1.0; // 截距项
            for (j, &value) in sample.iter().enumerate() {
                x_matrix[i][j + 1] = value;
            }
        }

        // 计算 X^T * X
        let mut xtx = vec![vec![0.0; n_features + 1]; n_features + 1];
        for i in 0..=n_features {
            for j in 0..=n_features {
                for k in 0..n_samples {
                    xtx[i][j] += x_matrix[k][i] * x_matrix[k][j];
                }
            }
        }

        // 计算 X^T * y
        let mut xty = vec![0.0; n_features + 1];
        for i in 0..=n_features {
            for k in 0..n_samples {
                xty[i] += x_matrix[k][i] * targets[k];
            }
        }

        // 解线性方程组 (简化版本：使用高斯消元法)
        let mut augmented = xtx;
        for i in 0..=n_features {
            augmented[i].push(xty[i]);
        }

        // 高斯消元
        for i in 0..=n_features {
            // 寻找主元
            let mut max_row = i;
            for k in i + 1..=n_features {
                if augmented[k][i].abs() > augmented[max_row][i].abs() {
                    max_row = k;
                }
            }
            augmented.swap(i, max_row);

            // 如果主元为0，矩阵奇异
            if augmented[i][i].abs() < 1e-10 {
                return Err(MLError::TrainingFailed("矩阵奇异，无法求解".to_string()));
            }

            // 消元
            for k in i + 1..=n_features {
                let factor = augmented[k][i] / augmented[i][i];
                for j in i..=n_features + 1 {
                    augmented[k][j] -= factor * augmented[i][j];
                }
            }
        }

        // 回代求解
        let mut solution = vec![0.0; n_features + 1];
        for i in (0..=n_features).rev() {
            solution[i] = augmented[i][n_features + 1];
            for j in i + 1..=n_features {
                solution[i] -= augmented[i][j] * solution[j];
            }
            solution[i] /= augmented[i][i];
        }

        self.intercept = Some(solution[0]);
        self.coefficients = Some(solution[1..].to_vec());
        self.is_fitted = true;

        Ok(())
    }

    fn predict(&self, sample: &DataPoint) -> MLResult<f64> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }

        if let (Some(coef), Some(intercept)) = (&self.coefficients, &self.intercept) {
            if sample.len() != coef.len() {
                return Err(MLError::DimensionMismatch {
                    expected: coef.len(),
                    actual: sample.len(),
                });
            }

            let prediction = intercept
                + sample
                    .iter()
                    .zip(coef.iter())
                    .map(|(x, w)| x * w)
                    .sum::<f64>();

            Ok(prediction)
        } else {
            Err(MLError::ModelNotTrained)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_regression() {
        let mut lr = LinearRegression::new();

        // 简单的线性关系: y = 2x + 1
        let data = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0]];
        let targets = vec![3.0, 5.0, 7.0, 9.0];

        let result = lr.train(&data, &targets);
        assert!(result.is_ok());

        // 测试预测
        let prediction = lr.predict(&vec![5.0]).unwrap();
        assert!((prediction - 11.0).abs() < 0.1); // 允许一定误差

        // 测试参数
        let (coef, intercept) = lr.parameters().unwrap();
        assert!((coef[0] - 2.0).abs() < 0.1);
        assert!((intercept - 1.0).abs() < 0.1);
    }

    #[test]
    fn test_mse_calculation() {
        let lr = LinearRegression::new();
        let data = vec![vec![1.0], vec![2.0]];
        let targets = vec![2.0, 4.0];

        let mse = lr.mse(&data, &targets);
        // 模型未训练，应该返回错误
        assert!(mse.is_err());
    }
}
