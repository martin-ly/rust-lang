# C18 模型库 API 参考总目录

## 概述

C18 模型库提供了全面的数学建模和计算方法，涵盖形式化方法、机器学习和排队论等核心领域。本文档集提供了完整的 API 参考，帮助开发者快速理解和使用各种模型。

## 文档结构

### 1. [形式化方法模型 API 参考](./formal-models.md)

**主题**: 形式化方法模型  
**编号**: 1  
**描述**: 提供各种形式化方法的实现，包括有限状态机、时序逻辑、进程代数等

#### 主要章节

- **1.1** 基础形式化模型
  - 1.1.1 State - 状态机状态
  - 1.1.2 Transition - 状态转换
  - 1.1.3 FiniteStateMachine - 有限状态机
  - 1.1.4 TemporalFormula - 时序逻辑公式
  - 1.1.5 TemporalModelChecker - 时序逻辑模型检查器
  - 1.1.6 ProcessTerm - 进程代数项
  - 1.1.7 ProcessAlgebraInterpreter - 进程代数解释器

- **1.2** 高级形式化方法
  - 1.2.1 形式化描述语言
  - 1.2.2 验证技术
  - 1.2.3 模型转换

- **1.3** 具体实现
- **1.4** 工具集
- **1.5** 使用示例
- **1.6** 错误处理
- **1.7** 性能考虑
- **1.8** 使用建议

### 2. [机器学习模型 API 参考](./ml-models.md)

**主题**: 机器学习模型  
**编号**: 2  
**描述**: 提供各种监督学习、无监督学习和强化学习算法的实现

#### 2.1 主要章节

- **2.1** 主要类型
  - 2.1.1 LinearRegression - 线性回归
  - 2.1.2 LogisticRegression - 逻辑回归
  - 2.1.3 KMeans - K均值聚类
  - 2.1.4 DecisionTree - 决策树
  - 2.1.5 DecisionTreeNode - 决策树节点

- **2.2** 算法细节
  - 2.2.1 线性回归
  - 2.2.2 逻辑回归
  - 2.2.3 KMeans聚类
  - 2.2.4 决策树

- **2.3** 性能指标
  - 2.3.1 回归指标
  - 2.3.2 分类指标
  - 2.3.3 聚类指标

- **2.4** 使用建议
  - 2.4.1 数据预处理
  - 2.4.2 模型选择
  - 2.4.3 超参数调优
  - 2.4.4 性能优化

- **2.5** 错误处理

### 3. [排队论模型 API 参考](./queueing-models.md)

**主题**: 排队论模型  
**编号**: 3  
**描述**: 提供各种排队系统的数学建模和分析功能

#### 3.1 主要章节

- **3.1** 主要类型
  - 3.1.1 MM1Queue - M/M/1 排队系统
  - 3.1.2 MMcQueue - M/M/c 多服务器排队系统
  - 3.1.3 PerformanceAnalyzer - 性能分析器
  - 3.1.4 ReliabilityAnalyzer - 可靠性分析器
  - 3.1.5 ScalabilityAnalyzer - 可扩展性分析器

- **3.2** 结果类型
  - 3.2.1 SimulationResult - 模拟结果
  - 3.2.2 ScalingResult - 扩展分析结果
  - 3.2.3 MetricStatistics - 指标统计信息

- **3.3** 错误处理
- **3.4** 数学公式
  - 3.4.1 M/M/1 模型公式
  - 3.4.2 M/M/c 模型公式
- **3.5** 性能考虑
- **3.6** 使用建议

## 快速导航

### 按功能分类

#### 形式化验证

- [有限状态机](./formal-models.md#finitestatemachine)
- [时序逻辑模型检查](./formal-models.md#temporalmodelchecker)
- [进程代数](./formal-models.md#processalgebrainterpreter)

#### 机器学习

- [线性回归](./ml-models.md#linearregression)
- [逻辑回归](./ml-models.md#logisticregression)
- [KMeans聚类](./ml-models.md#kmeans)
- [决策树](./ml-models.md#decisiontree)

#### 系统建模

- [M/M/1 排队系统](./queueing-models.md#mm1queue)
- [M/M/c 多服务器系统](./queueing-models.md#mmcqueue)
- [性能分析](./queueing-models.md#performanceanalyzer)
- [可靠性分析](./queueing-models.md#reliabilityanalyzer)

### 按使用场景分类

#### 软件开发

- 状态机设计
- 协议验证
- 系统建模

#### 数据分析

- 回归分析
- 分类预测
- 聚类分析

#### 系统优化

- 性能分析
- 容量规划
- 可靠性评估

## 使用指南

### 开始使用

1. **选择适合的模型**: 根据您的需求选择相应的模型类型
2. **阅读API文档**: 查看具体的API参考文档
3. **查看使用示例**: 每个模型都提供了详细的使用示例
4. **处理错误**: 了解可能的错误情况和处理方法

### 最佳实践

1. **参数验证**: 始终验证输入参数的有效性
2. **错误处理**: 使用适当的错误处理机制
3. **性能考虑**: 注意算法的复杂度和性能特征
4. **测试验证**: 使用提供的测试用例验证实现

### 扩展开发

1. **自定义实现**: 基于提供的trait实现自定义模型
2. **性能优化**: 根据具体需求优化算法实现
3. **集成测试**: 编写集成测试确保模型正确性

## 版本信息

- **当前版本**: 0.2.0
- **最后更新**: 2025年1月
- **兼容性**: Rust 1.70+

## 贡献指南

欢迎贡献代码和改进建议。请参考各模块的贡献指南：

- [形式化方法贡献指南](./formal-models.md#使用建议)
- [机器学习贡献指南](./ml-models.md#使用建议)
- [排队论贡献指南](./queueing-models.md#使用建议)

## 许可证

本项目采用 MIT 许可证。详情请参阅 [LICENSE](../../../LICENSE) 文件。
