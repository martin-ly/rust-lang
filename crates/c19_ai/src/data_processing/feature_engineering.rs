//! 特征工程模块
//! 
//! 提供特征提取、选择和转换功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

use super::dataframe::DataFrame;

/// 特征工程师
#[derive(Debug, Clone)]
pub struct FeatureEngineer {
    pub id: Uuid,
    pub name: String,
    pub operations: Vec<FeatureOperation>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 特征操作
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FeatureOperation {
    /// 数学变换
    MathTransform(MathTransform),
    /// 统计特征
    StatisticalFeature(StatisticalFeature),
    /// 时间特征
    TimeFeature(TimeFeature),
    /// 文本特征
    TextFeature(TextFeature),
    /// 分类特征
    CategoricalFeature(CategoricalFeature),
    /// 特征选择
    FeatureSelection(FeatureSelection),
    /// 特征组合
    FeatureCombination(FeatureCombination),
    /// 自定义特征
    CustomFeature(CustomFeature),
}

/// 数学变换
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MathTransform {
    pub input_columns: Vec<String>,
    pub output_column: String,
    pub transform_type: MathTransformType,
    pub parameters: HashMap<String, f64>,
}

/// 数学变换类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MathTransformType {
    /// 对数变换
    Log,
    /// 平方根变换
    Sqrt,
    /// 平方变换
    Square,
    /// 倒数变换
    Reciprocal,
    /// 指数变换
    Exp,
    /// 幂变换
    Power(f64),
    /// 绝对值
    Abs,
    /// 符号函数
    Sign,
    /// 向上取整
    Ceil,
    /// 向下取整
    Floor,
    /// 四舍五入
    Round,
}

/// 统计特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StatisticalFeature {
    pub input_columns: Vec<String>,
    pub output_column: String,
    pub feature_type: StatisticalFeatureType,
    pub window_size: Option<usize>,
    pub group_by: Option<String>,
}

/// 统计特征类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StatisticalFeatureType {
    /// 均值
    Mean,
    /// 中位数
    Median,
    /// 标准差
    Std,
    /// 方差
    Variance,
    /// 最小值
    Min,
    /// 最大值
    Max,
    /// 范围
    Range,
    /// 分位数
    Quantile(f64),
    /// 偏度
    Skewness,
    /// 峰度
    Kurtosis,
    /// 计数
    Count,
    /// 唯一值计数
    UniqueCount,
    /// 缺失值计数
    MissingCount,
}

/// 时间特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeFeature {
    pub input_column: String,
    pub output_columns: Vec<String>,
    pub feature_types: Vec<TimeFeatureType>,
    pub timezone: Option<String>,
}

/// 时间特征类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TimeFeatureType {
    /// 年份
    Year,
    /// 月份
    Month,
    /// 日期
    Day,
    /// 小时
    Hour,
    /// 分钟
    Minute,
    /// 秒
    Second,
    /// 星期几
    Weekday,
    /// 一年中的第几天
    DayOfYear,
    /// 一年中的第几周
    WeekOfYear,
    /// 季度
    Quarter,
    /// 是否周末
    IsWeekend,
    /// 是否工作日
    IsWeekday,
    /// 是否月初
    IsMonthStart,
    /// 是否月末
    IsMonthEnd,
    /// 是否年初
    IsYearStart,
    /// 是否年末
    IsYearEnd,
}

/// 文本特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextFeature {
    pub input_column: String,
    pub output_columns: Vec<String>,
    pub feature_types: Vec<TextFeatureType>,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 文本特征类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TextFeatureType {
    /// 字符长度
    Length,
    /// 单词数量
    WordCount,
    /// 句子数量
    SentenceCount,
    /// 平均单词长度
    AverageWordLength,
    /// 大写字母数量
    UppercaseCount,
    /// 小写字母数量
    LowercaseCount,
    /// 数字数量
    DigitCount,
    /// 特殊字符数量
    SpecialCharCount,
    /// 是否包含特定词
    ContainsWord(String),
    /// 词频统计
    WordFrequency,
    /// 字符n-gram
    CharNGram(usize),
    /// 词n-gram
    WordNGram(usize),
    /// TF-IDF
    TfIdf,
    /// 词嵌入
    WordEmbedding,
}

/// 分类特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CategoricalFeature {
    pub input_column: String,
    pub output_columns: Vec<String>,
    pub feature_types: Vec<CategoricalFeatureType>,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 分类特征类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CategoricalFeatureType {
    /// 独热编码
    OneHot,
    /// 标签编码
    Label,
    /// 目标编码
    Target,
    /// 频率编码
    Frequency,
    /// 序数编码
    Ordinal,
    /// 二进制编码
    Binary,
    /// 哈希编码
    Hash(usize),
}

/// 特征选择
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureSelection {
    pub input_columns: Vec<String>,
    pub output_columns: Vec<String>,
    pub selection_type: FeatureSelectionType,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 特征选择类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FeatureSelectionType {
    /// 方差阈值
    VarianceThreshold(f64),
    /// 相关性阈值
    CorrelationThreshold(f64),
    /// 互信息
    MutualInformation(usize),
    /// 卡方检验
    ChiSquare(usize),
    /// 递归特征消除
    RecursiveFeatureElimination(usize),
    /// 基于模型的特征选择
    ModelBased(usize),
    /// 主成分分析
    PCA(usize),
    /// 线性判别分析
    LDA(usize),
}

/// 特征组合
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureCombination {
    pub input_columns: Vec<String>,
    pub output_column: String,
    pub combination_type: FeatureCombinationType,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 特征组合类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FeatureCombinationType {
    /// 加法
    Add,
    /// 减法
    Subtract,
    /// 乘法
    Multiply,
    /// 除法
    Divide,
    /// 多项式特征
    Polynomial(usize),
    /// 交互特征
    Interaction,
    /// 比率
    Ratio,
    /// 差值
    Difference,
    /// 乘积
    Product,
    /// 自定义组合
    Custom(String),
}

/// 自定义特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CustomFeature {
    pub name: String,
    pub input_columns: Vec<String>,
    pub output_column: String,
    pub function_name: String,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 特征工程结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureEngineeringResult {
    pub input_features: Vec<String>,
    pub output_features: Vec<String>,
    pub feature_importance: HashMap<String, f64>,
    pub processing_time: std::time::Duration,
    pub metadata: HashMap<String, serde_json::Value>,
}

impl FeatureEngineer {
    /// 创建新的特征工程师
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            operations: Vec::new(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 添加特征操作
    pub fn add_operation(&mut self, operation: FeatureOperation) {
        self.operations.push(operation);
        self.updated_at = Utc::now();
    }

    /// 移除特征操作
    pub fn remove_operation(&mut self, index: usize) -> Result<()> {
        if index < self.operations.len() {
            self.operations.remove(index);
            self.updated_at = Utc::now();
            Ok(())
        } else {
            Err(anyhow::anyhow!("Operation index out of bounds"))
        }
    }

    /// 执行特征工程
    pub fn fit_transform(&self, mut df: DataFrame) -> Result<(DataFrame, FeatureEngineeringResult)> {
        let start_time = std::time::Instant::now();
        let input_features = df.get_columns().to_vec();
        let mut output_features = Vec::new();
        let mut feature_importance = HashMap::new();
        let mut metadata = HashMap::new();

        for operation in &self.operations {
            match operation {
                FeatureOperation::MathTransform(transform) => {
                    df = self.apply_math_transform(df, transform)?;
                    output_features.push(transform.output_column.clone());
                }
                FeatureOperation::StatisticalFeature(feature) => {
                    df = self.apply_statistical_feature(df, feature)?;
                    output_features.push(feature.output_column.clone());
                }
                FeatureOperation::TimeFeature(feature) => {
                    df = self.apply_time_feature(df, feature)?;
                    output_features.extend(feature.output_columns.clone());
                }
                FeatureOperation::TextFeature(feature) => {
                    df = self.apply_text_feature(df, feature)?;
                    output_features.extend(feature.output_columns.clone());
                }
                FeatureOperation::CategoricalFeature(feature) => {
                    df = self.apply_categorical_feature(df, feature)?;
                    output_features.extend(feature.output_columns.clone());
                }
                FeatureOperation::FeatureSelection(selection) => {
                    df = self.apply_feature_selection(df, selection)?;
                    output_features.extend(selection.output_columns.clone());
                }
                FeatureOperation::FeatureCombination(combination) => {
                    df = self.apply_feature_combination(df, combination)?;
                    output_features.push(combination.output_column.clone());
                }
                FeatureOperation::CustomFeature(feature) => {
                    df = self.apply_custom_feature(df, feature)?;
                    output_features.push(feature.output_column.clone());
                }
            }
        }

        let processing_time = start_time.elapsed();

        let result = FeatureEngineeringResult {
            input_features,
            output_features,
            feature_importance,
            processing_time,
            metadata,
        };

        Ok((df, result))
    }

    /// 应用数学变换
    fn apply_math_transform(&self, mut df: DataFrame, transform: &MathTransform) -> Result<DataFrame> {
        let mut new_column_data = Vec::new();

        for row in &df.data {
            let mut values = Vec::new();
            for col_name in &transform.input_columns {
                let col_index = df.columns.iter().position(|c| c == col_name)
                    .ok_or_else(|| anyhow::anyhow!("Column {} not found", col_name))?;
                values.push(row[col_index]);
            }

            let transformed_value = match transform.transform_type {
                MathTransformType::Log => values[0].ln(),
                MathTransformType::Sqrt => values[0].sqrt(),
                MathTransformType::Square => values[0].powi(2),
                MathTransformType::Reciprocal => 1.0 / values[0],
                MathTransformType::Exp => values[0].exp(),
                MathTransformType::Power(power) => values[0].powf(power),
                MathTransformType::Abs => values[0].abs(),
                MathTransformType::Sign => values[0].signum(),
                MathTransformType::Ceil => values[0].ceil(),
                MathTransformType::Floor => values[0].floor(),
                MathTransformType::Round => values[0].round(),
            };

            new_column_data.push(transformed_value);
        }

        // 添加新列
        df.columns.push(transform.output_column.clone());
        for (i, row) in df.data.iter_mut().enumerate() {
            row.push(new_column_data[i]);
        }

        Ok(df)
    }

    /// 应用统计特征
    fn apply_statistical_feature(&self, mut df: DataFrame, feature: &StatisticalFeature) -> Result<DataFrame> {
        let mut new_column_data = Vec::new();

        for row in &df.data {
            let mut values = Vec::new();
            for col_name in &feature.input_columns {
                let col_index = df.columns.iter().position(|c| c == col_name)
                    .ok_or_else(|| anyhow::anyhow!("Column {} not found", col_name))?;
                values.push(row[col_index]);
            }

            let statistical_value = match feature.feature_type {
                StatisticalFeatureType::Mean => values.iter().sum::<f64>() / values.len() as f64,
                StatisticalFeatureType::Median => {
                    let mut sorted_values = values.clone();
                    sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    if sorted_values.len() % 2 == 0 {
                        (sorted_values[sorted_values.len() / 2 - 1] + sorted_values[sorted_values.len() / 2]) / 2.0
                    } else {
                        sorted_values[sorted_values.len() / 2]
                    }
                }
                StatisticalFeatureType::Std => {
                    let mean = values.iter().sum::<f64>() / values.len() as f64;
                    let variance = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / values.len() as f64;
                    variance.sqrt()
                }
                StatisticalFeatureType::Variance => {
                    let mean = values.iter().sum::<f64>() / values.len() as f64;
                    values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / values.len() as f64
                }
                StatisticalFeatureType::Min => values.iter().fold(f64::INFINITY, |a, &b| a.min(b)),
                StatisticalFeatureType::Max => values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b)),
                StatisticalFeatureType::Range => {
                    let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
                    let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
                    max - min
                }
                StatisticalFeatureType::Quantile(q) => {
                    let mut sorted_values = values.clone();
                    sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    let idx = (sorted_values.len() as f64 * q) as usize;
                    sorted_values[idx.min(sorted_values.len() - 1)]
                }
                StatisticalFeatureType::Count => values.len() as f64,
                StatisticalFeatureType::UniqueCount => {
                    let mut unique_values = std::collections::HashSet::new();
                    for value in &values {
                        unique_values.insert((value * 1000.0).round() as i64);
                    }
                    unique_values.len() as f64
                }
                StatisticalFeatureType::MissingCount => {
                    values.iter().filter(|&&x| x.is_nan()).count() as f64
                }
                _ => 0.0, // TODO: 实现其他统计特征
            };

            new_column_data.push(statistical_value);
        }

        // 添加新列
        df.columns.push(feature.output_column.clone());
        for (i, row) in df.data.iter_mut().enumerate() {
            row.push(new_column_data[i]);
        }

        Ok(df)
    }

    /// 应用时间特征
    fn apply_time_feature(&self, mut df: DataFrame, _feature: &TimeFeature) -> Result<DataFrame> {
        // TODO: 实现时间特征提取
        Ok(df)
    }

    /// 应用文本特征
    fn apply_text_feature(&self, mut df: DataFrame, _feature: &TextFeature) -> Result<DataFrame> {
        // TODO: 实现文本特征提取
        Ok(df)
    }

    /// 应用分类特征
    fn apply_categorical_feature(&self, mut df: DataFrame, _feature: &CategoricalFeature) -> Result<DataFrame> {
        // TODO: 实现分类特征提取
        Ok(df)
    }

    /// 应用特征选择
    fn apply_feature_selection(&self, df: DataFrame, selection: &FeatureSelection) -> Result<DataFrame> {
        df.select(&selection.output_columns)
            .map_err(|e| anyhow::anyhow!("Feature selection failed: {}", e))
    }

    /// 应用特征组合
    fn apply_feature_combination(&self, mut df: DataFrame, combination: &FeatureCombination) -> Result<DataFrame> {
        let mut new_column_data = Vec::new();

        for row in &df.data {
            let mut values = Vec::new();
            for col_name in &combination.input_columns {
                let col_index = df.columns.iter().position(|c| c == col_name)
                    .ok_or_else(|| anyhow::anyhow!("Column {} not found", col_name))?;
                values.push(row[col_index]);
            }

            let combined_value = match combination.combination_type {
                FeatureCombinationType::Add => values.iter().sum(),
                FeatureCombinationType::Subtract => values[0] - values[1],
                FeatureCombinationType::Multiply => values.iter().product(),
                FeatureCombinationType::Divide => values[0] / values[1],
                FeatureCombinationType::Ratio => values[0] / values[1],
                FeatureCombinationType::Difference => (values[0] - values[1]).abs(),
                FeatureCombinationType::Product => values.iter().product(),
                _ => 0.0, // TODO: 实现其他组合类型
            };

            new_column_data.push(combined_value);
        }

        // 添加新列
        df.columns.push(combination.output_column.clone());
        for (i, row) in df.data.iter_mut().enumerate() {
            row.push(new_column_data[i]);
        }

        Ok(df)
    }

    /// 应用自定义特征
    fn apply_custom_feature(&self, mut df: DataFrame, _feature: &CustomFeature) -> Result<DataFrame> {
        // TODO: 实现自定义特征提取
        Ok(df)
    }
}

/// 预定义特征工程模板
pub struct FeatureEngineeringTemplates;

impl FeatureEngineeringTemplates {
    /// 获取数值特征工程模板
    pub fn numerical_features() -> FeatureEngineer {
        let mut engineer = FeatureEngineer::new("numerical_features".to_string());
        
        // 添加数学变换
        engineer.add_operation(FeatureOperation::MathTransform(MathTransform {
            input_columns: vec!["value".to_string()],
            output_column: "log_value".to_string(),
            transform_type: MathTransformType::Log,
            parameters: HashMap::new(),
        }));

        engineer.add_operation(FeatureOperation::MathTransform(MathTransform {
            input_columns: vec!["value".to_string()],
            output_column: "sqrt_value".to_string(),
            transform_type: MathTransformType::Sqrt,
            parameters: HashMap::new(),
        }));

        // 添加统计特征
        engineer.add_operation(FeatureOperation::StatisticalFeature(StatisticalFeature {
            input_columns: vec!["value".to_string()],
            output_column: "value_mean".to_string(),
            feature_type: StatisticalFeatureType::Mean,
            window_size: None,
            group_by: None,
        }));

        engineer.add_operation(FeatureOperation::StatisticalFeature(StatisticalFeature {
            input_columns: vec!["value".to_string()],
            output_column: "value_std".to_string(),
            feature_type: StatisticalFeatureType::Std,
            window_size: None,
            group_by: None,
        }));

        engineer
    }

    /// 获取时间特征工程模板
    pub fn time_features() -> FeatureEngineer {
        let mut engineer = FeatureEngineer::new("time_features".to_string());
        
        engineer.add_operation(FeatureOperation::TimeFeature(TimeFeature {
            input_column: "timestamp".to_string(),
            output_columns: vec![
                "year".to_string(),
                "month".to_string(),
                "day".to_string(),
                "hour".to_string(),
                "weekday".to_string(),
            ],
            feature_types: vec![
                TimeFeatureType::Year,
                TimeFeatureType::Month,
                TimeFeatureType::Day,
                TimeFeatureType::Hour,
                TimeFeatureType::Weekday,
            ],
            timezone: None,
        }));

        engineer
    }

    /// 获取文本特征工程模板
    pub fn text_features() -> FeatureEngineer {
        let mut engineer = FeatureEngineer::new("text_features".to_string());
        
        engineer.add_operation(FeatureOperation::TextFeature(TextFeature {
            input_column: "text".to_string(),
            output_columns: vec![
                "text_length".to_string(),
                "word_count".to_string(),
                "avg_word_length".to_string(),
            ],
            feature_types: vec![
                TextFeatureType::Length,
                TextFeatureType::WordCount,
                TextFeatureType::AverageWordLength,
            ],
            parameters: HashMap::new(),
        }));

        engineer
    }
}
