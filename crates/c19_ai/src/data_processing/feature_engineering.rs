//! 特征工程模块
//!
//! 提供特征提取、选择、变换和创建功能

use crate::data_processing::DataFrame;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 特征工程器
#[derive(Debug, Clone)]
pub struct FeatureEngineer {
    pub name: String,
    pub transformations: Vec<FeatureTransformation>,
}

/// 特征变换类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FeatureTransformation {
    /// 多项式特征
    PolynomialFeatures { degree: u32, columns: Vec<String> },
    /// 特征组合
    FeatureCombination {
        columns: Vec<String>,
        operation: CombinationOperation,
    },
    /// 特征分箱
    FeatureBinning {
        column: String,
        bins: usize,
        strategy: BinningStrategy,
    },
    /// 特征编码
    FeatureEncoding {
        column: String,
        method: EncodingMethod,
    },
    /// 特征选择
    FeatureSelection { method: SelectionMethod, k: usize },
    /// 降维
    DimensionalityReduction {
        method: ReductionMethod,
        n_components: usize,
    },
}

/// 特征组合操作
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CombinationOperation {
    /// 加法
    Add,
    /// 乘法
    Multiply,
    /// 除法
    Divide,
    /// 减法
    Subtract,
    /// 幂运算
    Power(f64),
}

/// 分箱策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BinningStrategy {
    /// 等宽分箱
    EqualWidth,
    /// 等频分箱
    EqualFreq,
    /// 自定义分箱
    Custom(Vec<f64>),
}

/// 编码方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EncodingMethod {
    /// 独热编码
    OneHot,
    /// 标签编码
    Label,
    /// 目标编码
    Target,
}

/// 特征选择方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SelectionMethod {
    /// 方差阈值
    VarianceThreshold(f64),
    /// 相关性选择
    Correlation,
    /// 递归特征消除
    RecursiveFeatureElimination,
    /// 基于模型的选择
    ModelBased,
}

/// 降维方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReductionMethod {
    /// 主成分分析
    PCA,
    /// 线性判别分析
    LDA,
    /// 独立成分分析
    ICA,
}

impl FeatureEngineer {
    /// 创建新的特征工程器
    pub fn new(name: String) -> Self {
        Self {
            name,
            transformations: Vec::new(),
        }
    }

    /// 添加特征变换
    pub fn add_transformation(&mut self, transformation: FeatureTransformation) {
        self.transformations.push(transformation);
    }

    /// 执行特征工程
    pub fn fit_transform(&self, mut df: DataFrame) -> Result<DataFrame, String> {
        for transformation in &self.transformations {
            df = self.apply_transformation(df, transformation)?;
        }
        Ok(df)
    }

    /// 应用单个特征变换
    fn apply_transformation(
        &self,
        df: DataFrame,
        transformation: &FeatureTransformation,
    ) -> Result<DataFrame, String> {
        match transformation {
            FeatureTransformation::PolynomialFeatures { degree, columns } => {
                self.create_polynomial_features(df, *degree, columns)
            }
            FeatureTransformation::FeatureCombination { columns, operation } => {
                self.combine_features(df, columns, operation)
            }
            FeatureTransformation::FeatureBinning {
                column,
                bins,
                strategy,
            } => self.bin_feature(df, column, *bins, strategy),
            FeatureTransformation::FeatureEncoding { column, method } => {
                self.encode_feature(df, column, method)
            }
            FeatureTransformation::FeatureSelection { method, k } => {
                self.select_features(df, method, *k)
            }
            FeatureTransformation::DimensionalityReduction {
                method,
                n_components,
            } => self.reduce_dimensions(df, method, *n_components),
        }
    }

    /// 创建多项式特征
    fn create_polynomial_features(
        &self,
        mut df: DataFrame,
        degree: u32,
        columns: &[String],
    ) -> Result<DataFrame, String> {
        let mut new_columns = df.columns.clone();
        let mut new_data = df.data.clone();

        for col_name in columns {
            let col_idx = df
                .columns
                .iter()
                .position(|col| col == col_name)
                .ok_or_else(|| format!("列 '{}' 不存在", col_name))?;

            for d in 2..=degree {
                let new_col_name = format!("{}_pow_{}", col_name, d);
                new_columns.push(new_col_name);

                for (i, row) in new_data.iter_mut().enumerate() {
                    let value = df.data[i][col_idx];
                    row.push(value.powi(d as i32));
                }
            }
        }

        df.columns = new_columns;
        df.data = new_data;
        Ok(df)
    }

    /// 组合特征
    fn combine_features(
        &self,
        mut df: DataFrame,
        columns: &[String],
        operation: &CombinationOperation,
    ) -> Result<DataFrame, String> {
        if columns.len() < 2 {
            return Err("至少需要两个列进行组合".to_string());
        }

        let indices: Result<Vec<usize>, String> = columns
            .iter()
            .map(|col| {
                df.columns
                    .iter()
                    .position(|c| c == col)
                    .ok_or_else(|| format!("列 '{}' 不存在", col))
            })
            .collect();
        let indices = indices?;

        let new_col_name = format!("combined_{}", columns.join("_"));
        df.columns.push(new_col_name);

        for row in &mut df.data {
            let mut result = row[indices[0]];

            for &idx in &indices[1..] {
                result = match operation {
                    CombinationOperation::Add => result + row[idx],
                    CombinationOperation::Multiply => result * row[idx],
                    CombinationOperation::Divide => {
                        if row[idx] != 0.0 {
                            result / row[idx]
                        } else {
                            0.0
                        }
                    }
                    CombinationOperation::Subtract => result - row[idx],
                    CombinationOperation::Power(p) => result.powf(*p),
                };
            }

            row.push(result);
        }

        Ok(df)
    }

    /// 特征分箱
    fn bin_feature(
        &self,
        mut df: DataFrame,
        column: &str,
        bins: usize,
        strategy: &BinningStrategy,
    ) -> Result<DataFrame, String> {
        let col_idx = df
            .columns
            .iter()
            .position(|col| col == column)
            .ok_or_else(|| format!("列 '{}' 不存在", column))?;

        let values: Vec<f64> = df.data.iter().map(|row| row[col_idx]).collect();
        let bin_edges = match strategy {
            BinningStrategy::EqualWidth => {
                let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
                let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
                let width = (max - min) / bins as f64;
                (0..=bins).map(|i| min + i as f64 * width).collect()
            }
            BinningStrategy::EqualFreq => {
                let mut sorted_values = values.clone();
                sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let mut edges = vec![sorted_values[0]];
                for i in 1..bins {
                    let idx = (i * sorted_values.len()) / bins;
                    edges.push(sorted_values[idx]);
                }
                edges.push(sorted_values[sorted_values.len() - 1]);
                edges
            }
            BinningStrategy::Custom(edges) => edges.clone(),
        };

        let new_col_name = format!("{}_binned", column);
        df.columns.push(new_col_name);

        for row in &mut df.data {
            let value = row[col_idx];
            let bin_idx = bin_edges
                .iter()
                .position(|&edge| value <= edge)
                .unwrap_or(bins);
            row.push(bin_idx as f64);
        }

        Ok(df)
    }

    /// 特征编码
    fn encode_feature(
        &self,
        mut df: DataFrame,
        column: &str,
        method: &EncodingMethod,
    ) -> Result<DataFrame, String> {
        let col_idx = df
            .columns
            .iter()
            .position(|col| col == column)
            .ok_or_else(|| format!("列 '{}' 不存在", column))?;

        match method {
            EncodingMethod::OneHot => {
                // 简化实现：将连续值转换为分类
                let values: Vec<f64> = df.data.iter().map(|row| row[col_idx]).collect();
                let unique_values: Vec<f64> = {
                    let mut unique = values.clone();
                    unique.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    unique.dedup();
                    unique
                };

                for (i, unique_val) in unique_values.iter().enumerate() {
                    let new_col_name = format!("{}_cat_{}", column, i);
                    df.columns.push(new_col_name);

                    for row in &mut df.data {
                        let is_match = if (row[col_idx] - unique_val).abs() < 1e-10 {
                            1.0
                        } else {
                            0.0
                        };
                        row.push(is_match);
                    }
                }
            }
            EncodingMethod::Label => {
                // 标签编码：将值映射到整数
                let values: Vec<f64> = df.data.iter().map(|row| row[col_idx]).collect();
                let unique_values: Vec<f64> = {
                    let mut unique = values.clone();
                    unique.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    unique.dedup();
                    unique
                };

                let new_col_name = format!("{}_encoded", column);
                df.columns.push(new_col_name);

                for row in &mut df.data {
                    let encoded = unique_values
                        .iter()
                        .position(|&val| (row[col_idx] - val).abs() < 1e-10)
                        .unwrap_or(0) as f64;
                    row.push(encoded);
                }
            }
            EncodingMethod::Target => {
                // 目标编码：用目标变量的均值替换分类值
                // 简化实现：用当前列的均值
                let values: Vec<f64> = df.data.iter().map(|row| row[col_idx]).collect();
                let mean = values.iter().sum::<f64>() / values.len() as f64;

                let new_col_name = format!("{}_target_encoded", column);
                df.columns.push(new_col_name);

                for row in &mut df.data {
                    row.push(mean);
                }
            }
        }

        Ok(df)
    }

    /// 特征选择
    fn select_features(
        &self,
        df: DataFrame,
        method: &SelectionMethod,
        k: usize,
    ) -> Result<DataFrame, String> {
        match method {
            SelectionMethod::VarianceThreshold(threshold) => {
                let mut selected_columns = Vec::new();

                for (i, column) in df.columns.iter().enumerate() {
                    let values: Vec<f64> = df.data.iter().map(|row| row[i]).collect();
                    let mean = values.iter().sum::<f64>() / values.len() as f64;
                    let variance: f64 = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>()
                        / values.len() as f64;

                    if variance >= *threshold {
                        selected_columns.push(column.clone());
                    }
                }

                df.select(&selected_columns)
            }
            SelectionMethod::Correlation => {
                // 简化实现：选择前 k 个列
                let selected: Vec<String> = df.columns.iter().take(k).cloned().collect();
                df.select(&selected)
            }
            SelectionMethod::RecursiveFeatureElimination => {
                // 简化实现：选择前 k 个列
                let selected: Vec<String> = df.columns.iter().take(k).cloned().collect();
                df.select(&selected)
            }
            SelectionMethod::ModelBased => {
                // 简化实现：选择前 k 个列
                let selected: Vec<String> = df.columns.iter().take(k).cloned().collect();
                df.select(&selected)
            }
        }
    }

    /// 降维
    fn reduce_dimensions(
        &self,
        df: DataFrame,
        method: &ReductionMethod,
        n_components: usize,
    ) -> Result<DataFrame, String> {
        match method {
            ReductionMethod::PCA => {
                // 简化实现：选择前 n_components 个列
                let selected: Vec<String> = df.columns.iter().take(n_components).cloned().collect();
                df.select(&selected)
            }
            ReductionMethod::LDA => {
                // 简化实现：选择前 n_components 个列
                let selected: Vec<String> = df.columns.iter().take(n_components).cloned().collect();
                df.select(&selected)
            }
            ReductionMethod::ICA => {
                // 简化实现：选择前 n_components 个列
                let selected: Vec<String> = df.columns.iter().take(n_components).cloned().collect();
                df.select(&selected)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature_engineer_creation() {
        let mut engineer = FeatureEngineer::new("test".to_string());
        engineer.add_transformation(FeatureTransformation::PolynomialFeatures {
            degree: 2,
            columns: vec!["col1".to_string()],
        });

        assert_eq!(engineer.transformations.len(), 1);
    }

    #[test]
    fn test_polynomial_features() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![2.0]).unwrap();
        df.add_row(vec![3.0]).unwrap();

        let engineer = FeatureEngineer::new("test".to_string());
        let result = engineer
            .create_polynomial_features(df, 2, &["col1".to_string()])
            .unwrap();

        assert_eq!(result.columns.len(), 2); // 原列 + 平方列
        assert_eq!(result.data[0].len(), 2);
        assert_eq!(result.data[0][1], 4.0); // 2^2 = 4
    }

    #[test]
    fn test_feature_combination() {
        let mut df = DataFrame::new(
            "test".to_string(),
            vec!["col1".to_string(), "col2".to_string()],
        );
        df.add_row(vec![2.0, 3.0]).unwrap();
        df.add_row(vec![4.0, 5.0]).unwrap();

        let engineer = FeatureEngineer::new("test".to_string());
        let result = engineer
            .combine_features(
                df,
                &["col1".to_string(), "col2".to_string()],
                &CombinationOperation::Add,
            )
            .unwrap();

        assert_eq!(result.columns.len(), 3); // 原列 + 组合列
        assert_eq!(result.data[0][2], 5.0); // 2 + 3 = 5
    }
}
