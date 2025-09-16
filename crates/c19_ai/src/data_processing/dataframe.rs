//! DataFrame 数据处理
//!
//! 基于 Polars 的高性能 DataFrame 操作

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// DataFrame 包装器
#[derive(Debug, Clone)]
pub struct DataFrame {
    pub name: String,
    pub columns: Vec<String>,
    pub data: Vec<Vec<f64>>,
    pub metadata: HashMap<String, String>,
}

impl DataFrame {
    /// 创建新的 DataFrame
    pub fn new(name: String, columns: Vec<String>) -> Self {
        Self {
            name,
            columns,
            data: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// 添加行数据
    pub fn add_row(&mut self, row: Vec<f64>) -> Result<(), String> {
        if row.len() != self.columns.len() {
            return Err(format!(
                "行长度 {} 与列数 {} 不匹配",
                row.len(),
                self.columns.len()
            ));
        }
        self.data.push(row);
        Ok(())
    }

    /// 获取行数
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// 获取列数
    pub fn column_count(&self) -> usize {
        self.columns.len()
    }

    /// 获取列名
    pub fn get_columns(&self) -> &[String] {
        &self.columns
    }

    /// 获取指定列的数据
    pub fn get_column(&self, column_name: &str) -> Result<Vec<f64>, String> {
        let index = self
            .columns
            .iter()
            .position(|col| col == column_name)
            .ok_or_else(|| format!("列 '{}' 不存在", column_name))?;

        Ok(self.data.iter().map(|row| row[index]).collect())
    }

    /// 计算基本统计信息
    pub fn describe(&self) -> DataFrameStats {
        let mut stats = DataFrameStats::new();

        for (i, column) in self.columns.iter().enumerate() {
            let values: Vec<f64> = self.data.iter().map(|row| row[i]).collect();
            let column_stats = ColumnStats::from_values(&values);
            stats.add_column(column.clone(), column_stats);
        }

        stats
    }

    /// 过滤数据
    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&[f64]) -> bool,
    {
        let filtered_data: Vec<Vec<f64>> = self
            .data
            .iter()
            .filter(|row| predicate(row))
            .cloned()
            .collect();

        Self {
            name: format!("{}_filtered", self.name),
            columns: self.columns.clone(),
            data: filtered_data,
            metadata: self.metadata.clone(),
        }
    }

    /// 选择列
    pub fn select(&self, column_names: &[String]) -> Result<Self, String> {
        let mut selected_columns = Vec::new();
        let mut column_indices = Vec::new();

        for col_name in column_names {
            let index = self
                .columns
                .iter()
                .position(|col| col == col_name)
                .ok_or_else(|| format!("列 '{}' 不存在", col_name))?;
            selected_columns.push(col_name.clone());
            column_indices.push(index);
        }

        let selected_data: Vec<Vec<f64>> = self
            .data
            .iter()
            .map(|row| column_indices.iter().map(|&i| row[i]).collect())
            .collect();

        Ok(Self {
            name: format!("{}_selected", self.name),
            columns: selected_columns,
            data: selected_data,
            metadata: self.metadata.clone(),
        })
    }
}

/// DataFrame 统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataFrameStats {
    pub columns: HashMap<String, ColumnStats>,
}

impl DataFrameStats {
    pub fn new() -> Self {
        Self {
            columns: HashMap::new(),
        }
    }

    pub fn add_column(&mut self, name: String, stats: ColumnStats) {
        self.columns.insert(name, stats);
    }
}

/// 列统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ColumnStats {
    pub count: usize,
    pub mean: f64,
    pub std: f64,
    pub min: f64,
    pub max: f64,
    pub median: f64,
}

impl ColumnStats {
    pub fn from_values(values: &[f64]) -> Self {
        if values.is_empty() {
            return Self {
                count: 0,
                mean: 0.0,
                std: 0.0,
                min: 0.0,
                max: 0.0,
                median: 0.0,
            };
        }

        let count = values.len();
        let sum: f64 = values.iter().sum();
        let mean = sum / count as f64;

        let variance: f64 = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / count as f64;
        let std = variance.sqrt();

        let mut sorted_values = values.to_vec();
        sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let median = if count % 2 == 0 {
            (sorted_values[count / 2 - 1] + sorted_values[count / 2]) / 2.0
        } else {
            sorted_values[count / 2]
        };

        Self {
            count,
            mean,
            std,
            min: sorted_values[0],
            max: sorted_values[count - 1],
            median,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dataframe_creation() {
        let mut df = DataFrame::new(
            "test".to_string(),
            vec!["col1".to_string(), "col2".to_string()],
        );
        df.add_row(vec![1.0, 2.0]).unwrap();
        df.add_row(vec![3.0, 4.0]).unwrap();

        assert_eq!(df.len(), 2);
        assert_eq!(df.column_count(), 2);
    }

    #[test]
    fn test_dataframe_filter() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![2.0]).unwrap();
        df.add_row(vec![3.0]).unwrap();

        let filtered = df.filter(|row| row[0] > 1.5);
        assert_eq!(filtered.len(), 2);
    }

    #[test]
    fn test_column_stats() {
        let values = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = ColumnStats::from_values(&values);

        assert_eq!(stats.count, 5);
        assert_eq!(stats.mean, 3.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
        assert_eq!(stats.median, 3.0);
    }
}
