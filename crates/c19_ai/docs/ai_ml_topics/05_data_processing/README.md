# 数据处理 (Data Processing)

## 概述

本文件夹包含Rust 1.90版本中最成熟和最新的数据处理库相关内容。

## 主要库

### 1. Polars

- **版本**: 0.50.0 (2025年最新)
- **特点**: 高性能DataFrame库
- **功能**:
  - 快速数据处理和分析
  - 懒加载和查询优化
  - 多线程并行处理
  - 多种数据格式支持
  - 时间序列处理
  - 字符串操作
- **优势**:
  - 比Pandas快10-100倍
  - 内存效率高
  - 类型安全
  - 丰富的API
- **文档**: [Polars官方文档](https://github.com/pola-rs/polars)
- **示例**: 见 `examples/` 文件夹

### 2. DataFusion

- **版本**: 49.0.2 (2025年最新)
- **特点**: 查询执行引擎
- **功能**:
  - SQL查询执行
  - 分布式查询处理
  - 查询优化器
  - 多种数据源支持
  - 流式处理
- **优势**:
  - 高性能查询引擎
  - 可扩展架构
  - SQL兼容性
  - 内存管理优化
- **文档**: [DataFusion官方文档](https://github.com/apache/arrow-datafusion)
- **示例**: 见 `examples/` 文件夹

### 3. Arrow

- **版本**: 56.1.0 (2025年最新)
- **特点**: 列式内存格式
- **功能**:
  - 高效的内存布局
  - 零拷贝数据共享
  - 多种数据类型支持
  - 跨语言互操作性
- **优势**:
  - 内存效率极高
  - 向量化计算
  - 标准化格式
  - 生态系统支持
- **文档**: [Arrow官方文档](https://github.com/apache/arrow-rs)
- **示例**: 见 `examples/` 文件夹

### 4. 其他数据处理库

#### Serde

- **版本**: 1.0.226 (2025年最新)
- **功能**: 序列化和反序列化
- **特点**: 支持多种数据格式 (JSON, YAML, TOML, Bincode)

#### CSV

- **版本**: 1.3.0 (2025年最新)
- **功能**: CSV文件处理
- **特点**: 高性能CSV读写

#### Parquet

- **版本**: 56.1.0 (2025年最新)
- **功能**: Parquet格式支持
- **特点**: 列式存储格式

## 主要任务

### 1. 数据清洗

- **缺失值处理**: 填充、删除、插值
- **异常值检测**: 统计方法、机器学习方法
- **数据标准化**: 归一化、标准化
- **重复数据**: 检测和删除重复记录

### 2. 数据转换

- **类型转换**: 数据类型转换
- **特征工程**: 特征创建和选择
- **数据聚合**: 分组和聚合操作
- **数据重塑**: 透视表、长宽格式转换

### 3. 数据分析

- **描述性统计**: 均值、中位数、标准差
- **相关性分析**: 变量间关系分析
- **时间序列分析**: 趋势、季节性分析
- **假设检验**: 统计显著性测试

### 4. 数据可视化

- **基础图表**: 柱状图、折线图、散点图
- **高级图表**: 热力图、箱线图、小提琴图
- **交互式图表**: 动态图表和仪表板
- **地理可视化**: 地图和地理数据展示

## 库对比

| 库 | 成熟度 | 性能 | 功能范围 | 学习曲线 | 推荐场景 |
|----|--------|------|----------|----------|----------|
| Polars | 高 | 极高 | 广泛 | 中等 | 大数据处理、分析 |
| DataFusion | 高 | 高 | SQL查询 | 中等 | 数据仓库、OLAP |
| Arrow | 高 | 极高 | 基础 | 高 | 底层数据处理 |
| Serde | 高 | 高 | 序列化 | 低 | 数据格式转换 |
| CSV | 高 | 高 | CSV处理 | 低 | CSV文件操作 |

## 使用建议

### 大数据处理

- **首选**: Polars + Arrow
- **原因**: 高性能、内存效率高

### 数据仓库

- **首选**: DataFusion + Arrow
- **原因**: SQL支持、查询优化

### 数据科学

- **首选**: Polars + Serde
- **原因**: 易用性、功能丰富

### 实时处理

- **首选**: DataFusion (流式)
- **原因**: 流式查询支持

## 文件结构

```text
05_data_processing/
├── README.md                    # 本文件
├── polars/                      # Polars相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── lazy/                   # 懒加载
│   ├── eager/                  # 即时执行
│   └── benchmarks/             # 性能测试
├── datafusion/                 # DataFusion相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── sql/                    # SQL查询
│   ├── streaming/              # 流式处理
│   └── optimization/           # 查询优化
├── arrow/                      # Arrow相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── memory/                 # 内存管理
│   ├── compute/                # 计算内核
│   └── io/                     # I/O操作
├── data_cleaning/              # 数据清洗
│   ├── missing_values/         # 缺失值处理
│   ├── outliers/               # 异常值检测
│   ├── normalization/          # 数据标准化
│   └── deduplication/          # 去重
├── data_transformation/        # 数据转换
│   ├── feature_engineering/    # 特征工程
│   ├── aggregation/            # 数据聚合
│   ├── reshaping/              # 数据重塑
│   └── type_conversion/        # 类型转换
├── data_analysis/              # 数据分析
│   ├── statistics/             # 统计分析
│   ├── correlation/            # 相关性分析
│   ├── time_series/            # 时间序列
│   └── hypothesis_testing/     # 假设检验
└── visualization/              # 数据可视化
    ├── basic_charts/           # 基础图表
    ├── advanced_charts/        # 高级图表
    ├── interactive/            # 交互式图表
    └── geographic/             # 地理可视化
```

## 快速开始

### Polars示例

```rust
use polars::prelude::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建DataFrame
    let df = df! [
        "name" => ["Alice", "Bob", "Charlie"],
        "age" => [25, 30, 35],
        "city" => ["New York", "London", "Tokyo"],
    ]?;
    
    // 基本操作
    println!("DataFrame形状: {:?}", df.shape());
    println!("列名: {:?}", df.get_column_names());
    
    // 过滤和选择
    let filtered = df
        .lazy()
        .filter(col("age").gt(25))
        .select([col("name"), col("age")])
        .collect()?;
    
    println!("过滤后的数据:");
    println!("{}", filtered);
    
    // 聚合操作
    let aggregated = df
        .lazy()
        .group_by([col("city")])
        .agg([col("age").mean().alias("avg_age")])
        .collect()?;
    
    println!("聚合结果:");
    println!("{}", aggregated);
    
    Ok(())
}
```

### DataFusion示例

```rust
use datafusion::prelude::*;
use datafusion::arrow::record_batch::RecordBatch;
use datafusion::arrow::array::{Int32Array, StringArray};
use datafusion::arrow::datatypes::{DataType, Field, Schema};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建DataFusion上下文
    let ctx = SessionContext::new();
    
    // 创建数据
    let schema = Schema::new(vec![
        Field::new("id", DataType::Int32, false),
        Field::new("name", DataType::Utf8, false),
        Field::new("value", DataType::Int32, false),
    ]);
    
    let batch = RecordBatch::try_new(
        Arc::new(schema),
        vec![
            Arc::new(Int32Array::from(vec![1, 2, 3])),
            Arc::new(StringArray::from(vec!["A", "B", "C"])),
            Arc::new(Int32Array::from(vec![10, 20, 30])),
        ],
    )?;
    
    // 注册数据
    ctx.register_batch("table", batch)?;
    
    // 执行SQL查询
    let df = ctx.sql("SELECT name, AVG(value) as avg_value FROM table GROUP BY name").await?;
    let results = df.collect().await?;
    
    // 打印结果
    for batch in results {
        println!("{}", batch);
    }
    
    Ok(())
}
```

### Arrow示例

```rust
use arrow::array::{Int32Array, StringArray};
use arrow::compute::kernels::arithmetic;
use arrow::record_batch::RecordBatch;
use arrow::datatypes::{DataType, Field, Schema};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建数组
    let a = Int32Array::from(vec![1, 2, 3, 4, 5]);
    let b = Int32Array::from(vec![10, 20, 30, 40, 50]);
    
    // 向量化计算
    let result = arithmetic::add(&a, &b)?;
    println!("加法结果: {:?}", result);
    
    // 创建RecordBatch
    let schema = Schema::new(vec![
        Field::new("a", DataType::Int32, false),
        Field::new("b", DataType::Int32, false),
        Field::new("result", DataType::Int32, false),
    ]);
    
    let batch = RecordBatch::try_new(
        Arc::new(schema),
        vec![Arc::new(a), Arc::new(b), Arc::new(result)],
    )?;
    
    println!("RecordBatch:");
    println!("{}", batch);
    
    Ok(())
}
```

## 性能优化

1. **懒加载**: 使用Polars的懒加载API
2. **并行处理**: 利用多核CPU并行计算
3. **内存优化**: 使用Arrow的列式存储
4. **查询优化**: 利用DataFusion的查询优化器
5. **批处理**: 批量处理数据减少I/O开销

## 最佳实践

1. **数据验证**: 验证数据质量和完整性
2. **错误处理**: 处理数据加载和处理错误
3. **内存管理**: 合理管理大数据集的内存使用
4. **缓存策略**: 缓存中间结果提高性能
5. **监控**: 监控数据处理性能和资源使用

## 相关资源

- [Rust数据处理生态](https://github.com/rust-ai/awesome-rust-data)
- [数据处理最佳实践](https://github.com/rust-ai/data-processing-best-practices)
- [性能优化指南](https://github.com/rust-ai/data-performance-guide)
