//! 数据预处理模块
//! 
//! 提供数据清洗、标准化、归一化等功能

use crate::data_processing::DataFrame;
use serde::{Deserialize, Serialize};

/// 数据预处理器
#[derive(Debug, Clone)]
pub struct DataPreprocessor {
    pub name: String,
    pub steps: Vec<PreprocessingStep>,
}

/// 预处理步骤
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PreprocessingStep {
    /// 缺失值处理
    HandleMissingValues(MissingValueStrategy),
    /// 数据标准化
    Standardize,
    /// 数据归一化
    Normalize,
    /// 特征缩放
    ScaleFeatures(ScalingMethod),
    /// 异常值处理
    HandleOutliers(OutlierStrategy),
    /// 特征选择
    SelectFeatures(Vec<String>),
}

/// 缺失值处理策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MissingValueStrategy {
    /// 删除包含缺失值的行
    DropRows,
    /// 删除包含缺失值的列
    DropColumns,
    /// 用均值填充
    FillWithMean,
    /// 用中位数填充
    FillWithMedian,
    /// 用众数填充
    FillWithMode,
    /// 用指定值填充
    FillWithValue(f64),
}

/// 特征缩放方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScalingMethod {
    /// 最小-最大缩放
    MinMax,
    /// Z-score 标准化
    ZScore,
    /// 鲁棒缩放
    Robust,
}

/// 异常值处理策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OutlierStrategy {
    /// 删除异常值
    Remove,
    /// 用分位数替换
    ReplaceWithQuantile(f64),
    /// 用均值替换
    ReplaceWithMean,
    /// 用中位数替换
    ReplaceWithMedian,
}

impl DataPreprocessor {
    /// 创建新的数据预处理器
    pub fn new(name: String) -> Self {
        Self {
            name,
            steps: Vec::new(),
        }
    }
    
    /// 添加预处理步骤
    pub fn add_step(&mut self, step: PreprocessingStep) {
        self.steps.push(step);
    }
    
    /// 执行预处理
    pub fn fit_transform(&self, mut df: DataFrame) -> Result<DataFrame, String> {
        for step in &self.steps {
            df = self.apply_step(df, step)?;
        }
        Ok(df)
    }
    
    /// 应用单个预处理步骤
    fn apply_step(&self, df: DataFrame, step: &PreprocessingStep) -> Result<DataFrame, String> {
        match step {
            PreprocessingStep::HandleMissingValues(strategy) => {
                self.handle_missing_values(df, strategy)
            }
            PreprocessingStep::Standardize => {
                self.standardize_data(df)
            }
            PreprocessingStep::Normalize => {
                self.normalize_data(df)
            }
            PreprocessingStep::ScaleFeatures(method) => {
                self.scale_features(df, method)
            }
            PreprocessingStep::HandleOutliers(strategy) => {
                self.handle_outliers(df, strategy)
            }
            PreprocessingStep::SelectFeatures(columns) => {
                df.select(columns)
            }
        }
    }
    
    /// 处理缺失值
    fn handle_missing_values(&self, mut df: DataFrame, strategy: &MissingValueStrategy) -> Result<DataFrame, String> {
        match strategy {
            MissingValueStrategy::DropRows => {
                df.data.retain(|row| !row.iter().any(|&x| x.is_nan()));
            }
            MissingValueStrategy::DropColumns => {
                // 简化实现：删除包含 NaN 的列
                let mut valid_columns = Vec::new();
                let mut valid_indices = Vec::new();
                
                for (i, column) in df.columns.iter().enumerate() {
                    let has_nan = df.data.iter().any(|row| row[i].is_nan());
                    if !has_nan {
                        valid_columns.push(column.clone());
                        valid_indices.push(i);
                    }
                }
                
                df.columns = valid_columns;
                df.data = df.data.into_iter()
                    .map(|row| valid_indices.iter().map(|&i| row[i]).collect())
                    .collect();
            }
            MissingValueStrategy::FillWithMean => {
                for i in 0..df.columns.len() {
                    let values: Vec<f64> = df.data.iter()
                        .map(|row| row[i])
                        .filter(|&x| !x.is_nan())
                        .collect();
                    
                    if !values.is_empty() {
                        let mean = values.iter().sum::<f64>() / values.len() as f64;
                        for row in &mut df.data {
                            if row[i].is_nan() {
                                row[i] = mean;
                            }
                        }
                    }
                }
            }
            MissingValueStrategy::FillWithMedian => {
                for i in 0..df.columns.len() {
                    let mut values: Vec<f64> = df.data.iter()
                        .map(|row| row[i])
                        .filter(|&x| !x.is_nan())
                        .collect();
                    
                    if !values.is_empty() {
                        values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                        let median = if values.len() % 2 == 0 {
                            (values[values.len() / 2 - 1] + values[values.len() / 2]) / 2.0
                        } else {
                            values[values.len() / 2]
                        };
                        
                        for row in &mut df.data {
                            if row[i].is_nan() {
                                row[i] = median;
                            }
                        }
                    }
                }
            }
            MissingValueStrategy::FillWithMode => {
                // 简化实现：用均值代替众数
                return self.handle_missing_values(df, &MissingValueStrategy::FillWithMean);
            }
            MissingValueStrategy::FillWithValue(value) => {
                for row in &mut df.data {
                    for val in row.iter_mut() {
                        if val.is_nan() {
                            *val = *value;
                        }
                    }
                }
            }
        }
        Ok(df)
    }
    
    /// 标准化数据
    fn standardize_data(&self, mut df: DataFrame) -> Result<DataFrame, String> {
        for i in 0..df.columns.len() {
            let values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
            let mean = values.iter().sum::<f64>() / values.len() as f64;
            let variance: f64 = values.iter()
                .map(|x| (x - mean).powi(2))
                .sum::<f64>() / values.len() as f64;
            let std = variance.sqrt();
            
            if std > 0.0 {
                for row in &mut df.data {
                    row[i] = (row[i] - mean) / std;
                }
            }
        }
        Ok(df)
    }
    
    /// 归一化数据
    fn normalize_data(&self, mut df: DataFrame) -> Result<DataFrame, String> {
        for i in 0..df.columns.len() {
            let values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
            let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
            let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
            
            if max > min {
                for row in &mut df.data {
                    row[i] = (row[i] - min) / (max - min);
                }
            }
        }
        Ok(df)
    }
    
    /// 特征缩放
    fn scale_features(&self, df: DataFrame, method: &ScalingMethod) -> Result<DataFrame, String> {
        match method {
            ScalingMethod::MinMax => self.normalize_data(df),
            ScalingMethod::ZScore => self.standardize_data(df),
            ScalingMethod::Robust => {
                // 鲁棒缩放：使用中位数和四分位距
                let mut scaled_df = df;
                for i in 0..scaled_df.columns.len() {
                    let mut values: Vec<f64> = scaled_df.data.iter().map(|row| row[i]).collect();
                    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    
                    let median = if values.len() % 2 == 0 {
                        (values[values.len() / 2 - 1] + values[values.len() / 2]) / 2.0
                    } else {
                        values[values.len() / 2]
                    };
                    
                    let q1_idx = values.len() / 4;
                    let q3_idx = 3 * values.len() / 4;
                    let iqr = values[q3_idx] - values[q1_idx];
                    
                    if iqr > 0.0 {
                        for row in &mut scaled_df.data {
                            row[i] = (row[i] - median) / iqr;
                        }
                    }
                }
                Ok(scaled_df)
            }
        }
    }
    
    /// 处理异常值
    fn handle_outliers(&self, mut df: DataFrame, strategy: &OutlierStrategy) -> Result<DataFrame, String> {
        match strategy {
            OutlierStrategy::Remove => {
                // 使用 IQR 方法检测异常值
                for i in 0..df.columns.len() {
                    let mut values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
                    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    
                    let q1_idx = values.len() / 4;
                    let q3_idx = 3 * values.len() / 4;
                    let q1 = values[q1_idx];
                    let q3 = values[q3_idx];
                    let iqr = q3 - q1;
                    
                    let lower_bound = q1 - 1.5 * iqr;
                    let upper_bound = q3 + 1.5 * iqr;
                    
                    df.data.retain(|row| row[i] >= lower_bound && row[i] <= upper_bound);
                }
            }
            OutlierStrategy::ReplaceWithQuantile(quantile) => {
                for i in 0..df.columns.len() {
                    let mut values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
                    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    
                    let idx = (values.len() as f64 * quantile) as usize;
                    let replacement_value = values[idx.min(values.len() - 1)];
                    
                    for row in &mut df.data {
                        if row[i] < values[values.len() / 4] || row[i] > values[3 * values.len() / 4] {
                            row[i] = replacement_value;
                        }
                    }
                }
            }
            OutlierStrategy::ReplaceWithMean => {
                for i in 0..df.columns.len() {
                    let values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
                    let mean = values.iter().sum::<f64>() / values.len() as f64;
                    
                    for row in &mut df.data {
                        if row[i] < values[values.len() / 4] || row[i] > values[3 * values.len() / 4] {
                            row[i] = mean;
                        }
                    }
                }
            }
            OutlierStrategy::ReplaceWithMedian => {
                for i in 0..df.columns.len() {
                    let mut values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
                    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    let median = values[values.len() / 2];
                    
                    for row in &mut df.data {
                        if row[i] < values[values.len() / 4] || row[i] > values[3 * values.len() / 4] {
                            row[i] = median;
                        }
                    }
                }
            }
        }
        Ok(df)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_preprocessor_creation() {
        let mut preprocessor = DataPreprocessor::new("test".to_string());
        preprocessor.add_step(PreprocessingStep::Standardize);
        preprocessor.add_step(PreprocessingStep::Normalize);
        
        assert_eq!(preprocessor.steps.len(), 2);
    }
    
    #[test]
    fn test_standardization() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![2.0]).unwrap();
        df.add_row(vec![3.0]).unwrap();
        
        let preprocessor = DataPreprocessor::new("test".to_string());
        let standardized = preprocessor.standardize_data(df).unwrap();
        
        // 标准化后的均值应该接近 0
        let values: Vec<f64> = standardized.data.iter().map(|row| row[0]).collect();
        let mean = values.iter().sum::<f64>() / values.len() as f64;
        assert!(mean.abs() < 1e-10);
    }
    
    #[test]
    fn test_normalization() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![2.0]).unwrap();
        df.add_row(vec![3.0]).unwrap();
        
        let preprocessor = DataPreprocessor::new("test".to_string());
        let normalized = preprocessor.normalize_data(df).unwrap();
        
        // 归一化后的值应该在 [0, 1] 范围内
        for row in &normalized.data {
            assert!(row[0] >= 0.0 && row[0] <= 1.0);
        }
    }
}
