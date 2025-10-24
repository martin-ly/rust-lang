# 排队论模型 API 参考

> 返回索引：`docs/README.md`

## 📊 目录

- [排队论模型 API 参考](#排队论模型-api-参考)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [概述](#概述)
  - [主要类型](#主要类型)
    - [MM1Queue {#mm1queue}](#mm1queue-mm1queue)
    - [MMcQueue {#mmcqueue}](#mmcqueue-mmcqueue)
  - [分析工具](#分析工具)
    - [PerformanceAnalyzer {#performanceanalyzer}](#performanceanalyzer-performanceanalyzer)
    - [ReliabilityAnalyzer {#reliabilityanalyzer}](#reliabilityanalyzer-reliabilityanalyzer)
    - [ScalabilityAnalyzer {#scalabilityanalyzer}](#scalabilityanalyzer-scalabilityanalyzer)
  - [结果类型](#结果类型)
    - [SimulationResult {#simulationresult}](#simulationresult-simulationresult)
    - [ScalingResult {#scalingresult}](#scalingresult-scalingresult)
    - [MetricStatistics {#metricstatistics}](#metricstatistics-metricstatistics)
  - [数学公式](#数学公式)
    - [M/M/1 关键公式](#mm1-关键公式)
    - [M/M/c 关键公式（Erlang-C）](#mmc-关键公式erlang-c)
  - [示例](#示例)
  - [错误处理与边界](#错误处理与边界)
  - [最佳实践](#最佳实践)
  - [版本](#版本)
  - [3. 排队论模型 API 参考](#3-排队论模型-api-参考)
  - [3.1 目录](#31-目录)
  - [3.2 概述](#32-概述)
  - [3.3 主要类型](#33-主要类型)
    - [3.3.1 MM1Queue](#331-mm1queue)
      - [3.3.1.1 构造函数](#3311-构造函数)
      - [3.3.1.2 主要方法](#3312-主要方法)
      - [3.3.1.3 使用示例](#3313-使用示例)
    - [3.3.2 MMcQueue](#332-mmcqueue)
      - [3.3.2.1 构造函数](#3321-构造函数)
      - [3.3.2.2 主要方法](#3322-主要方法)
    - [3.3.3 PerformanceAnalyzer](#333-performanceanalyzer)
      - [3.3.3.1 主要方法](#3331-主要方法)
    - [3.3.4 ReliabilityAnalyzer](#334-reliabilityanalyzer)
      - [3.3.4.1 主要方法](#3341-主要方法)
    - [3.3.5 ScalabilityAnalyzer](#335-scalabilityanalyzer)
      - [3.3.5.1 主要方法](#3351-主要方法)
  - [3.4 结果类型](#34-结果类型)
    - [3.4.1 SimulationResult](#341-simulationresult)
    - [3.4.2 ScalingResult](#342-scalingresult)
    - [3.4.3 MetricStatistics](#343-metricstatistics)
  - [3.5 错误处理](#35-错误处理)
  - [3.6 数学公式](#36-数学公式)
    - [3.6.1 M/M/1 模型公式](#361-mm1-模型公式)
    - [3.6.2 M/M/c 模型公式](#362-mmc-模型公式)
  - [3.7 性能考虑](#37-性能考虑)
  - [3.8 使用建议](#38-使用建议)

## 📋 目录

- [排队论模型 API 参考](#排队论模型-api-参考)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [概述](#概述)
  - [主要类型](#主要类型)
    - [MM1Queue {#mm1queue}](#mm1queue-mm1queue)
    - [MMcQueue {#mmcqueue}](#mmcqueue-mmcqueue)
  - [分析工具](#分析工具)
    - [PerformanceAnalyzer {#performanceanalyzer}](#performanceanalyzer-performanceanalyzer)
    - [ReliabilityAnalyzer {#reliabilityanalyzer}](#reliabilityanalyzer-reliabilityanalyzer)
    - [ScalabilityAnalyzer {#scalabilityanalyzer}](#scalabilityanalyzer-scalabilityanalyzer)
  - [结果类型](#结果类型)
    - [SimulationResult {#simulationresult}](#simulationresult-simulationresult)
    - [ScalingResult {#scalingresult}](#scalingresult-scalingresult)
    - [MetricStatistics {#metricstatistics}](#metricstatistics-metricstatistics)
  - [数学公式](#数学公式)
    - [M/M/1 关键公式](#mm1-关键公式)
    - [M/M/c 关键公式（Erlang-C）](#mmc-关键公式erlang-c)
  - [示例](#示例)
  - [错误处理与边界](#错误处理与边界)
  - [最佳实践](#最佳实践)
  - [版本](#版本)
  - [3. 排队论模型 API 参考](#3-排队论模型-api-参考)
  - [3.1 目录](#31-目录)
  - [3.2 概述](#32-概述)
  - [3.3 主要类型](#33-主要类型)
    - [3.3.1 MM1Queue](#331-mm1queue)
      - [3.3.1.1 构造函数](#3311-构造函数)
      - [3.3.1.2 主要方法](#3312-主要方法)
      - [3.3.1.3 使用示例](#3313-使用示例)
    - [3.3.2 MMcQueue](#332-mmcqueue)
      - [3.3.2.1 构造函数](#3321-构造函数)
      - [3.3.2.2 主要方法](#3322-主要方法)
    - [3.3.3 PerformanceAnalyzer](#333-performanceanalyzer)
      - [3.3.3.1 主要方法](#3331-主要方法)
    - [3.3.4 ReliabilityAnalyzer](#334-reliabilityanalyzer)
      - [3.3.4.1 主要方法](#3341-主要方法)
    - [3.3.5 ScalabilityAnalyzer](#335-scalabilityanalyzer)
      - [3.3.5.1 主要方法](#3351-主要方法)
  - [3.4 结果类型](#34-结果类型)
    - [3.4.1 SimulationResult](#341-simulationresult)
    - [3.4.2 ScalingResult](#342-scalingresult)
    - [3.4.3 MetricStatistics](#343-metricstatistics)
  - [3.5 错误处理](#35-错误处理)
  - [3.6 数学公式](#36-数学公式)
    - [3.6.1 M/M/1 模型公式](#361-mm1-模型公式)
    - [3.6.2 M/M/c 模型公式](#362-mmc-模型公式)
  - [3.7 性能考虑](#37-性能考虑)
  - [3.8 使用建议](#38-使用建议)

## 概述

提供 M/M/1、M/M/c 等经典排队系统的建模与分析 API，以及性能/可靠性/可扩展性分析工具。

## 主要类型

### MM1Queue {#mm1queue}

- **构造**: `new(lambda: f64, mu: f64) -> MM1Queue`
- **接口**:
  - `utilization(&self) -> f64`  // ρ = λ/μ
  - `avg_num_in_system(&self) -> f64` // L = ρ/(1-ρ)
  - `avg_wait_time(&self) -> f64` // W = 1/(μ-λ)

### MMcQueue {#mmcqueue}

- **构造**: `new(lambda: f64, mu: f64, c: usize) -> MMcQueue`
- **接口**:
  - `utilization(&self) -> f64`  // ρ = λ/(cμ)
  - `avg_num_in_queue(&self) -> f64`  // Lq (Erlang-C)
  - `avg_wait_time(&self) -> f64`     // Wq (Erlang-C)

## 分析工具

### PerformanceAnalyzer {#performanceanalyzer}

- 计算吞吐、延迟、并发、利用率等综合指标。

### ReliabilityAnalyzer {#reliabilityanalyzer}

- 评估失效率、MTBF、可用性等可靠性指标。

### ScalabilityAnalyzer {#scalabilityanalyzer}

- 进行扩展性分析与容量规划（横向/纵向扩展）。

## 结果类型

### SimulationResult {#simulationresult}

- 字段示例: `throughput`, `latency_p50/p95/p99`, `queue_lengths`。

### ScalingResult {#scalingresult}

- 字段示例: `speedup`, `efficiency`, `bottlenecks`。

### MetricStatistics {#metricstatistics}

- 字段示例: `mean`, `std_dev`, `min`, `max`。

## 数学公式

### M/M/1 关键公式

- 稳定条件: λ < μ
- ρ = λ/μ
- L = ρ/(1-ρ)
- W = 1/(μ-λ)

符号与单位：

- λ（到达率）：单位 1/s 或 req/s
- μ（服务率）：单位 1/s 或 req/s
- L（平均队长/系统内人数）：无量纲
- W（平均等待/响应时间）：单位 s

### M/M/c 关键公式（Erlang-C）

- 稳定条件: λ < cμ
- 记 a = λ/μ，ρ = a/c，P0 = [∑_{n=0}^{c-1} a^n/n! + a^c/(c!(1-ρ))]^{-1}
- 等待概率（队列非空）: C = a^c/(c!(1-ρ)) · P0
- 平均队长: Lq = C · ρ/(1-ρ)
- 平均等待: Wq = Lq/λ

## 示例

```rust
use c18_model::{MM1Queue, MMcQueue};

let q = MM1Queue::new(1.0, 2.0);
assert!(q.utilization() < 1.0);
println!("W = {}", q.avg_wait_time());

let qc = MMcQueue::new(10.0, 6.0, 2);
println!("ρ = {:.3}", qc.utilization());
println!("Wq = {:.3}", qc.avg_wait_time());
```

## 错误处理与边界

- 非法参数: 负率、零服务率、ρ ≥ 1 等需显式报错。
- 数值稳定性: 接近不稳定边界时建议提供警告或高精度路径。
- 服务器数 c=0、非整数等参数必须拒绝；极端 a^c/c! 计算需采取对数域或 Kahan 求和避免溢出。

参数校验清单：

- λ ≥ 0, μ > 0, c ∈ ℕ 且 c ≥ 1
- 稳定性：M/M/1 要求 λ < μ；M/M/c 要求 λ < cμ
- 容量（若有限）：capacity ≥ 1

## 最佳实践

1. 在构造时完成参数规范化与校验。
2. 提供闭式解与数值法双路径，按条件选择。
3. 对外暴露单位/维度文档，避免混用。

## 版本

- 适配版本: 0.2.0（Rust 1.70+）

## 3. 排队论模型 API 参考

## 3.1 目录

- [排队论模型 API 参考](#排队论模型-api-参考)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [概述](#概述)
  - [主要类型](#主要类型)
    - [MM1Queue {#mm1queue}](#mm1queue-mm1queue)
    - [MMcQueue {#mmcqueue}](#mmcqueue-mmcqueue)
  - [分析工具](#分析工具)
    - [PerformanceAnalyzer {#performanceanalyzer}](#performanceanalyzer-performanceanalyzer)
    - [ReliabilityAnalyzer {#reliabilityanalyzer}](#reliabilityanalyzer-reliabilityanalyzer)
    - [ScalabilityAnalyzer {#scalabilityanalyzer}](#scalabilityanalyzer-scalabilityanalyzer)
  - [结果类型](#结果类型)
    - [SimulationResult {#simulationresult}](#simulationresult-simulationresult)
    - [ScalingResult {#scalingresult}](#scalingresult-scalingresult)
    - [MetricStatistics {#metricstatistics}](#metricstatistics-metricstatistics)
  - [数学公式](#数学公式)
    - [M/M/1 关键公式](#mm1-关键公式)
    - [M/M/c 关键公式（Erlang-C）](#mmc-关键公式erlang-c)
  - [示例](#示例)
  - [错误处理与边界](#错误处理与边界)
  - [最佳实践](#最佳实践)
  - [版本](#版本)
  - [3. 排队论模型 API 参考](#3-排队论模型-api-参考)
  - [3.1 目录](#31-目录)
  - [3.2 概述](#32-概述)
  - [3.3 主要类型](#33-主要类型)
    - [3.3.1 MM1Queue](#331-mm1queue)
      - [3.3.1.1 构造函数](#3311-构造函数)
      - [3.3.1.2 主要方法](#3312-主要方法)
      - [3.3.1.3 使用示例](#3313-使用示例)
    - [3.3.2 MMcQueue](#332-mmcqueue)
      - [3.3.2.1 构造函数](#3321-构造函数)
      - [3.3.2.2 主要方法](#3322-主要方法)
    - [3.3.3 PerformanceAnalyzer](#333-performanceanalyzer)
      - [3.3.3.1 主要方法](#3331-主要方法)
    - [3.3.4 ReliabilityAnalyzer](#334-reliabilityanalyzer)
      - [3.3.4.1 主要方法](#3341-主要方法)
    - [3.3.5 ScalabilityAnalyzer](#335-scalabilityanalyzer)
      - [3.3.5.1 主要方法](#3351-主要方法)
  - [3.4 结果类型](#34-结果类型)
    - [3.4.1 SimulationResult](#341-simulationresult)
    - [3.4.2 ScalingResult](#342-scalingresult)
    - [3.4.3 MetricStatistics](#343-metricstatistics)
  - [3.5 错误处理](#35-错误处理)
  - [3.6 数学公式](#36-数学公式)
    - [3.6.1 M/M/1 模型公式](#361-mm1-模型公式)
    - [3.6.2 M/M/c 模型公式](#362-mmc-模型公式)
  - [3.7 性能考虑](#37-性能考虑)
  - [3.8 使用建议](#38-使用建议)

## 3.2 概述

排队论模型模块提供了各种排队系统的数学建模和分析功能，包括 M/M/1、M/M/c 等经典模型。

## 3.3 主要类型

### 3.3.1 MM1Queue

M/M/1 排队系统，单服务器指数分布排队模型。

```rust
pub struct MM1Queue {
    pub arrival_rate: f64,    // 到达率 (λ)
    pub service_rate: f64,    // 服务率 (μ)
    pub capacity: Option<usize>, // 系统容量
}
```

#### 3.3.1.1 构造函数

```rust
// 创建无限容量的 M/M/1 排队系统
pub fn new(arrival_rate: f64, service_rate: f64) -> Self

// 创建有限容量的排队系统
pub fn with_capacity(arrival_rate: f64, service_rate: f64, capacity: usize) -> Self
```

#### 3.3.1.2 主要方法

```rust
// 计算系统利用率 (ρ = λ/μ)
pub fn utilization(&self) -> f64

// 计算平均队长 (L = λ/(μ-λ))
pub fn average_queue_length(&self) -> Result<f64, String>

// 计算平均等待时间 (W = 1/(μ-λ))
pub fn average_waiting_time(&self) -> Result<f64, String>

// 计算平均响应时间 (包括服务时间)
pub fn average_response_time(&self) -> Result<f64, String>

// 计算系统空闲概率
pub fn idle_probability(&self) -> Result<f64, String>

// 计算系统中有 n 个客户的概率
pub fn probability_of_n_customers(&self, n: usize) -> Result<f64, String>
```

#### 3.3.1.3 使用示例

```rust
use c18_model::MM1Queue;

let queue = MM1Queue::new(1.0, 2.0);
println!("利用率: {:.2}%", queue.utilization() * 100.0);

match queue.average_queue_length() {
    Ok(length) => println!("平均队长: {:.2}", length),
    Err(e) => println!("计算错误: {}", e),
}
```

### 3.3.2 MMcQueue

M/M/c 多服务器排队系统。

```rust
pub struct MMcQueue {
    pub arrival_rate: f64,    // 到达率 (λ)
    pub service_rate: f64,    // 单服务器服务率 (μ)
    pub servers: usize,       // 服务器数量 (c)
}
```

#### 3.3.2.1 构造函数

```rust
pub fn new(arrival_rate: f64, service_rate: f64, servers: usize) -> Self
```

#### 3.3.2.2 主要方法

```rust
// 计算系统利用率
pub fn utilization(&self) -> f64

// 计算平均队长
pub fn average_queue_length(&self) -> Result<f64, String>

// 计算平均等待时间
pub fn average_waiting_time(&self) -> Result<f64, String>

// 计算所有服务器忙碌的概率
pub fn probability_all_busy(&self) -> Result<f64, String>
```

### 3.3.3 PerformanceAnalyzer

性能分析器，用于收集和分析系统性能指标。

```rust
pub struct PerformanceAnalyzer {
    metrics: HashMap<String, Vec<f64>>,
}
```

#### 3.3.3.1 主要方法

```rust
// 添加性能指标
pub fn add_metric(&mut self, name: &str, value: f64)

// 获取平均指标值
pub fn average_metric(&self, name: &str) -> Option<f64>

// 生成性能报告
pub fn generate_report(&self) -> String

// 获取指标统计信息
pub fn get_statistics(&self, name: &str) -> Option<MetricStatistics>
```

### 3.3.4 ReliabilityAnalyzer

可靠性分析器，用于分析系统可用性和可靠性。

```rust
pub struct ReliabilityAnalyzer {
    pub mttf: f64,  // 平均故障间隔时间
    pub mttr: f64,  // 平均修复时间
}
```

#### 3.3.4.1 主要方法

```rust
// 计算系统可用性
pub fn availability(&self) -> f64

// 模拟系统运行
pub fn simulate(&self, duration_hours: f64) -> SimulationResult

// 计算可靠性函数
pub fn reliability_function(&self, time: f64) -> f64
```

### 3.3.5 ScalabilityAnalyzer

可扩展性分析器，用于分析系统扩展性能。

```rust
pub struct ScalabilityAnalyzer {
    pub base_throughput: f64,
    pub base_latency: f64,
}
```

#### 3.3.5.1 主要方法

```rust
// 分析扩展性能
pub fn analyze_scaling(&self, scale_factor: f64) -> ScalingResult

// 计算扩展效率
pub fn scaling_efficiency(&self, scale_factor: f64) -> f64
```

## 3.4 结果类型

### 3.4.1 SimulationResult

模拟结果结构。

```rust
pub struct SimulationResult {
    pub availability: f64,
    pub failure_count: usize,
    pub total_uptime: f64,
    pub total_downtime: f64,
}
```

### 3.4.2 ScalingResult

扩展分析结果。

```rust
pub struct ScalingResult {
    pub throughput: f64,
    pub latency: f64,
    pub efficiency: f64,
}
```

### 3.4.3 MetricStatistics

指标统计信息。

```rust
pub struct MetricStatistics {
    pub mean: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
    pub count: usize,
}
```

## 3.5 错误处理

所有可能失败的操作都返回 `Result<T, String>` 类型，其中：

- `Ok(T)`：操作成功，包含结果值
- `Err(String)`：操作失败，包含错误描述

常见错误情况：

- 系统不稳定（利用率 >= 1.0）
- 参数超出有效范围
- 数值计算溢出

## 3.6 数学公式

### 3.6.1 M/M/1 模型公式

- **利用率**: ρ = λ/μ
- **平均队长**: L = λ/(μ-λ) (当 ρ < 1)
- **平均等待时间**: W = 1/(μ-λ) (当 ρ < 1)
- **平均响应时间**: R = W + 1/μ
- **空闲概率**: P₀ = 1 - ρ
- **n个客户概率**: Pₙ = ρⁿ(1-ρ)

### 3.6.2 M/M/c 模型公式

- **利用率**: ρ = λ/(cμ)
- **平均队长**: L = Lq + λ/μ
- **平均等待时间**: W = L/λ
- **所有服务器忙碌概率**: P(所有忙碌) = (λ/μ)ᶜP₀/(c!(1-ρ))

## 3.7 性能考虑

- 所有计算都是 O(1) 时间复杂度
- 内存使用量最小化
- 支持高精度浮点运算
- 数值稳定性优化

## 3.8 使用建议

1. **参数验证**：确保到达率和服务率都为正数
2. **稳定性检查**：使用前检查系统利用率是否小于1
3. **精度控制**：根据需求调整数值精度
4. **错误处理**：始终处理可能的错误情况
