# Rust异步工作流引擎：容错、优先级与可观测性设计

## 目录

- [Rust异步工作流引擎：容错、优先级与可观测性设计](#rust异步工作流引擎容错优先级与可观测性设计)
  - [目录](#目录)
  - [思维导图(文本形式)](#思维导图文本形式)
  - [1. 引言](#1-引言)
  - [2. 工作流系统核心概念](#2-工作流系统核心概念)
    - [2.1 状态模型与转换](#21-状态模型与转换)
    - [2.2 执行模型](#22-执行模型)
    - [2.3 形式化定义](#23-形式化定义)
  - [3. Rust异步生态系统分析](#3-rust异步生态系统分析)
    - [3.1 主流异步运行时比较](#31-主流异步运行时比较)
    - [3.2 异步特性与工作流要求对应关系](#32-异步特性与工作流要求对应关系)
    - [3.3 类型系统应用](#33-类型系统应用)
  - [4. 容错与恢复机制](#4-容错与恢复机制)
    - [4.1 故障模型分类](#41-故障模型分类)
    - [4.2 优雅故障处理策略](#42-优雅故障处理策略)
    - [4.3 恢复机制设计](#43-恢复机制设计)
    - [4.4 形式化证明](#44-形式化证明)
  - [5. 优先级调度系统](#5-优先级调度系统)
    - [5.1 多层优先级模型](#51-多层优先级模型)
    - [5.2 公平调度算法](#52-公平调度算法)
    - [5.3 资源限制与隔离](#53-资源限制与隔离)
    - [5.4 优先级继承与避免饥饿](#54-优先级继承与避免饥饿)
  - [6. 持久化与状态管理](#6-持久化与状态管理)
    - [6.1 事件溯源架构](#61-事件溯源架构)
    - [6.2 检查点优化](#62-检查点优化)
    - [6.3 状态重放与恢复](#63-状态重放与恢复)
    - [6.4 ACID保证](#64-acid保证)
  - [7. 可观测性框架](#7-可观测性框架)
    - [7.1 日志系统设计](#71-日志系统设计)
    - [7.2 指标收集与暴露](#72-指标收集与暴露)
    - [7.3 分布式追踪实现](#73-分布式追踪实现)
    - [7.4 告警与监控集成](#74-告警与监控集成)
    - [7.5 运行时指标监控](#75-运行时指标监控)
    - [7.6 工作流可视化与管理控制台](#76-工作流可视化与管理控制台)
    - [8. 集成示例](#8-集成示例)
    - [9. 总结与展望](#9-总结与展望)
      - [9.1 关键设计决策回顾](#91-关键设计决策回顾)
      - [9.2 与现有工作流系统的比较](#92-与现有工作流系统的比较)
      - [9.3 未来工作方向](#93-未来工作方向)
      - [9.4 结论](#94-结论)
    - [工作流引擎与Tokio调度的关系](#工作流引擎与tokio调度的关系)
    - [两者的关系](#两者的关系)
    - [是否需要完全自己实现？](#是否需要完全自己实现)
    - [定制化的需求](#定制化的需求)
    - [工作流执行中的精细调度方案](#工作流执行中的精细调度方案)
      - [1. 自定义执行器覆盖Tokio调度](#1-自定义执行器覆盖tokio调度)
      - [2. 使用自定义的工作流协程调度器](#2-使用自定义的工作流协程调度器)
      - [3. 基于有向无环图(DAG)的依赖执行引擎](#3-基于有向无环图dag的依赖执行引擎)
      - [4. 混合执行模型：状态机 + 回调控制](#4-混合执行模型状态机--回调控制)
      - [5. 基于配额和时间片的调度器](#5-基于配额和时间片的调度器)
    - [建议的最佳方案](#建议的最佳方案)
  - [工作流调度策略的领域特性分析](#工作流调度策略的领域特性分析)
    - [1. 线性序列型工作流的状态机调度](#1-线性序列型工作流的状态机调度)
      - [1.1 特性分析](#11-特性分析)
      - [1.2 调度策略设计](#12-调度策略设计)
      - [1.3 优化点](#13-优化点)
    - [2. 编排型工作流的事件驱动调度](#2-编排型工作流的事件驱动调度)
      - [2.1 特性分析](#21-特性分析)
      - [2.2 事件驱动调度策略](#22-事件驱动调度策略)
      - [2.3 优化点](#23-优化点)
    - [3. 事件流型工作流的公平调度策略](#3-事件流型工作流的公平调度策略)
      - [3.1 特性分析](#31-特性分析)
      - [3.2 公平调度策略设计](#32-公平调度策略设计)
      - [3.3 优化点](#33-优化点)
    - [4. 混合工作流的自适应调度策略](#4-混合工作流的自适应调度策略)
      - [4.1 特性分析](#41-特性分析)
      - [4.2 自适应混合调度策略](#42-自适应混合调度策略)
      - [4.3 策略等价性与动态转换](#43-策略等价性与动态转换)
      - [4.4 优化点](#44-优化点)
    - [5. 综合分析：统一调度框架的可能性](#5-综合分析统一调度框架的可能性)
      - [5.1 工作流本质的思考](#51-工作流本质的思考)
      - [5.2 统一调度框架设计](#52-统一调度框架设计)
    - [6. 工作流调度策略的等价性分析](#6-工作流调度策略的等价性分析)
      - [6.1 状态机模型与事件驱动模型的等价性](#61-状态机模型与事件驱动模型的等价性)
      - [6.2 公平调度与其他模型的关系](#62-公平调度与其他模型的关系)
      - [6.3 混合策略的优势](#63-混合策略的优势)
    - [7. 统一的设计方案](#7-统一的设计方案)
    - [8. 结论](#8-结论)
  - [工作流形式化模型与控制/执行流统一分析](#工作流形式化模型与控制执行流统一分析)
    - [形式化模型概述](#形式化模型概述)
      - [1. 进程演算(Process Calculi)](#1-进程演算process-calculi)
      - [2. Petri网模型扩展](#2-petri网模型扩展)
      - [3. 进程代数与类型系统的结合](#3-进程代数与类型系统的结合)
      - [4. 时态逻辑(Temporal Logic)](#4-时态逻辑temporal-logic)
      - [5. 类型化反应系统(Typed Reactive Systems)](#5-类型化反应系统typed-reactive-systems)
    - [统一分析与推理框架](#统一分析与推理框架)
      - [1. 工作流结构分析与推理](#1-工作流结构分析与推理)
      - [2. 静态/动态分析的统一](#2-静态动态分析的统一)
      - [3. 同构分析与转换(Isomorphic Analysis and Transformation)](#3-同构分析与转换isomorphic-analysis-and-transformation)
      - [4. 工作流类型系统(Workflow Type System)](#4-工作流类型系统workflow-type-system)
    - [具体实现方案](#具体实现方案)
      - [1. 核心表示层：图结构与π演算](#1-核心表示层图结构与π演算)
      - [2. 分析与推理层](#2-分析与推理层)
      - [3. 运行时监控与自适应层](#3-运行时监控与自适应层)
    - [理论基础](#理论基础)
    - [结论与实施建议](#结论与实施建议)

## 思维导图(文本形式)

```text
Rust异步工作流引擎
├── 核心概念
│   ├── 状态模型与转换
│   │   ├── 有限状态机表示
│   │   └── 状态转换规则
│   ├── 执行模型
│   │   ├── 同步执行
│   │   ├── 异步执行
│   │   └── 混合执行
│   └── 形式化定义
│       ├── 状态转换函数
│       ├── 不变性定理
│       └── 组合性质
├── Rust异步生态系统
│   ├── 主流运行时比较
│   │   ├── Tokio
│   │   ├── async-std
│   │   └── smol
│   ├── 异步特性与工作流映射
│   │   ├── Future操作
│   │   ├── Stream处理
│   │   └── 协程调度
│   └── 类型系统应用
│       ├── 类型状态模式
│       ├── trait界定
│       └── 错误类型设计
├── 容错与恢复
│   ├── 故障模型
│   │   ├── 节点故障
│   │   ├── 网络故障
│   │   └── 逻辑故障
│   ├── 故障处理策略
│   │   ├── 重试策略
│   │   ├── 超时控制
│   │   └── 熔断机制
│   ├── 恢复机制
│   │   ├── 检查点恢复
│   │   ├── 增量恢复
│   │   └── 热备份
│   └── 形式化证明
│       ├── 故障恢复一致性
│       ├── 恢复完整性定理
│       └── 最大进度保证
├── 优先级调度
│   ├── 多层优先级模型
│   │   ├── 静态优先级
│   │   ├── 动态优先级
│   │   └── 上下文感知优先级
│   ├── 公平调度算法
│   │   ├── 加权轮询
│   │   ├── 最小占用优先
│   │   └── 多级反馈队列
│   ├── 资源限制与隔离
│   │   ├── CPU配额
│   │   ├── 内存限制
│   │   └── I/O节流
│   └── 优先级继承与避免饥饿
│       ├── 优先级提升
│       ├── 优先级天花板
│       └── 公平性保证
├── 持久化与状态
│   ├── 事件溯源
│   │   ├── 事件设计
│   │   ├── 事件存储选择
│   │   └── 事件流优化
│   ├── 检查点优化
│   │   ├── 增量检查点
│   │   ├── 自适应检查点
│   │   └── 分层检查点
│   ├── 状态重放与恢复
│   │   ├── 并行重放
│   │   ├── 增量重放
│   │   └── 延迟重放
│   └── ACID保证
│       ├── 原子性实现
│       ├── 一致性验证
│       ├── 隔离级别
│       └── 持久性策略
└── 可观测性
    ├── 日志系统
    │   ├── 结构化日志
    │   ├── 上下文注入
    │   └── 日志级别控制
    ├── 指标收集
    │   ├── 核心指标定义
    │   ├── 聚合策略
    │   └── 输出格式
    ├── 分布式追踪
    │   ├── SpanContext设计
    │   ├── 传播机制
    │   └── 采样策略
    └── 告警与监控
        ├── 阈值设定
        ├── 告警聚合
        └── 通知渠道
```

## 1. 引言

工作流引擎是许多企业级应用的关键组件，负责协调复杂业务逻辑的执行、状态管理和错误处理。
传统的工作流引擎大多数依赖于Java、.NET等平台，
而使用Rust实现工作流引擎可以带来显著的性能提升和安全保证。

本文重点设计一个全面的Rust异步工作流引擎，特别关注以下几个方面：

- 容错与异步优先级调度
- 持久化与状态恢复机制
- 完整的可观测性框架（日志、指标、追踪）
- 与Rust现有异步生态系统的无缝集成

## 2. 工作流系统核心概念

### 2.1 状态模型与转换

工作流本质上是一个有限状态机，由状态和状态转换规则组成。

```rust
/// 工作流状态枚举
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WorkflowState {
    Created {
        workflow_id: WorkflowId,
        workflow_type: String,
        created_at: DateTime<Utc>,
    },
    Running {
        current_stage: String,
        progress: f32,
        started_at: DateTime<Utc>,
        last_updated: DateTime<Utc>,
    },
    Suspended {
        reason: String,
        suspended_at: DateTime<Utc>,
    },
    Completed {
        result: Option<serde_json::Value>,
        completed_at: DateTime<Utc>,
    },
    Failed {
        error: WorkflowError,
        failed_at: DateTime<Utc>,
        can_retry: bool,
    },
    Cancelled {
        reason: Option<String>,
        cancelled_at: DateTime<Utc>,
    },
}

/// 工作流转换事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WorkflowEvent {
    WorkflowCreated {
        workflow_id: WorkflowId,
        workflow_type: String,
        input: serde_json::Value,
        timestamp: DateTime<Utc>,
        trace_context: Option<TraceContext>,
        priority: WorkflowPriority,
    },
    WorkflowStarted {
        workflow_id: WorkflowId,
        timestamp: DateTime<Utc>,
        trace_context: Option<TraceContext>,
    },
    StageStarted {
        workflow_id: WorkflowId,
        stage_id: String,
        stage_name: String,
        timestamp: DateTime<Utc>,
    },
    StageCompleted {
        workflow_id: WorkflowId,
        stage_id: String,
        result: Option<serde_json::Value>,
        timestamp: DateTime<Utc>,
    },
    StageFailed {
        workflow_id: WorkflowId,
        stage_id: String,
        error: WorkflowError,
        retry_state: Option<RetryState>,
        timestamp: DateTime<Utc>,
    },
    WorkflowSuspended {
        workflow_id: WorkflowId,
        reason: String,
        timestamp: DateTime<Utc>,
    },
    WorkflowResumed {
        workflow_id: WorkflowId,
        timestamp: DateTime<Utc>,
    },
    WorkflowCompleted {
        workflow_id: WorkflowId,
        result: Option<serde_json::Value>,
        timestamp: DateTime<Utc>,
    },
    WorkflowFailed {
        workflow_id: WorkflowId,
        error: WorkflowError,
        timestamp: DateTime<Utc>,
    },
    WorkflowCancelled {
        workflow_id: WorkflowId,
        reason: Option<String>,
        timestamp: DateTime<Utc>,
    },
    // 用于优先级调度的事件
    WorkflowPriorityChanged {
        workflow_id: WorkflowId,
        old_priority: WorkflowPriority,
        new_priority: WorkflowPriority,
        reason: String,
        timestamp: DateTime<Utc>,
    },
    // 用于容错处理的事件
    WorkflowRecoveryStarted {
        workflow_id: WorkflowId,
        failure_reason: String,
        recovery_strategy: RecoveryStrategy,
        timestamp: DateTime<Utc>,
    },
    WorkflowRecoveryCompleted {
        workflow_id: WorkflowId,
        success: bool,
        timestamp: DateTime<Utc>,
    },
}
```

### 2.2 执行模型

工作流引擎支持三种执行模型：

1. **同步执行**：适用于简单、轻量的工作流
2. **异步执行**：适用于IO密集型或长时间运行的工作流
3. **混合执行**：根据任务特性动态选择执行模型

```rust
/// 定义工作流执行模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionMode {
    /// 同步执行 - 在当前线程上下文中执行
    Synchronous,
    /// 异步执行 - 在异步任务中执行
    Asynchronous,
    /// 混合执行 - 基于工作流活动复杂性自动选择
    Hybrid,
}

/// 工作流活动接口
#[async_trait]
pub trait Activity: Send + Sync {
    type Input: DeserializeOwned + Send + 'static;
    type Output: Serialize + Send + 'static;
    type Error: std::error::Error + Send + Sync + 'static;
    
    /// 是否适合异步执行
    fn is_async_preferred(&self) -> bool {
        true // 默认异步执行
    }
    
    /// 获取活动估计执行时间，用于调度决策
    fn estimated_duration(&self) -> Duration {
        Duration::from_secs(1) // 默认估计
    }
    
    /// 执行活动
    async fn execute(
        &self, 
        input: Self::Input, 
        context: &ActivityContext
    ) -> Result<Self::Output, Self::Error>;
}
```

### 2.3 形式化定义

工作流系统可以用形式化语言来定义。假设：

- $W$ 表示工作流
- $S$ 表示状态空间
- $E$ 表示事件集合
- $δ: S × E → S$ 表示状态转换函数

可以证明以下定理：

**定理1（确定性）**：对于任何工作流 $W$，给定初始状态 $s_0$ 和事件序列 $e_1, e_2, ..., e_n$，最终状态 $s_n$ 是确定的：
$s_n = δ(δ(...δ(δ(s_0, e_1), e_2)...), e_n)$

**证明**：通过归纳法证明。基本情况下，$s_1 = δ(s_0, e_1)$ 是确定的。归纳步骤，假设对于事件序列 $e_1, e_2, ..., e_k$，状态 $s_k$ 是确定的。那么 $s_{k+1} = δ(s_k, e_{k+1})$ 也是确定的。因此，定理得证。

**定理2（可恢复性）**：对于任何工作流 $W$，给定事件日志 $L = \{e_1, e_2, ..., e_n\}$，可以从初始状态 $s_0$ 恢复到最终状态 $s_n$。

**证明**：根据定理1，我们可以通过应用事件序列 $e_1, e_2, ..., e_n$ 到初始状态 $s_0$ 来恢复状态 $s_n$。具体来说，$s_n = δ(δ(...δ(δ(s_0, e_1), e_2)...), e_n)$。

## 3. Rust异步生态系统分析

### 3.1 主流异步运行时比较

| 特性 | Tokio | async-std | smol |
|-----|-------|-----------|------|
| 成熟度 | 高 | 中 | 中 |
| 生态系统 | 丰富 | 良好 | 较小 |
| 性能 | 优秀 | 良好 | 良好 |
| 内存占用 | 低 | 中 | 低 |
| 任务调度 | 工作窃取 | 工作窃取 | 工作窃取 |
| 优先级支持 | 有限 | 无 | 无 |
| IO多路复用 | 高效 | 良好 | 良好 |
| 文档 | 丰富 | 良好 | 有限 |

Tokio是最成熟的选择，提供了最完整的功能集和生态系统支持。

```rust
/// 配置异步运行时适配器
pub enum RuntimeAdapter {
    Tokio(TokioRuntime),
    AsyncStd(AsyncStdRuntime),
    Smol(SmolRuntime),
    Custom(Box<dyn RuntimeInterface>),
}

/// 通用运行时接口
#[async_trait]
pub trait RuntimeInterface: Send + Sync {
    /// 提交任务到运行时
    async fn spawn<F, T>(&self, future: F) -> Result<JoinHandle<T>, RuntimeError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static;
        
    /// 提交带优先级的任务
    async fn spawn_with_priority<F, T>(
        &self, 
        future: F, 
        priority: TaskPriority
    ) -> Result<JoinHandle<T>, RuntimeError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static;
        
    /// 创建定时器
    async fn create_timer(&self, duration: Duration) -> Result<TimerHandle, RuntimeError>;
    
    /// 获取运行时度量
    fn metrics(&self) -> RuntimeMetrics;
}

/// Tokio运行时适配器实现
pub struct TokioRuntime {
    runtime: Arc<tokio::runtime::Runtime>,
    // 额外添加优先级队列支持
    priority_executor: PriorityExecutor,
}

impl TokioRuntime {
    pub fn new() -> Result<Self, RuntimeError> {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(num_cpus::get())
            .enable_all()
            .build()
            .map_err(|e| RuntimeError::InitializationError(e.to_string()))?;
            
        let priority_executor = PriorityExecutor::new(4); // 4级优先级
        
        Ok(Self {
            runtime: Arc::new(runtime),
            priority_executor,
        })
    }
}

#[async_trait]
impl RuntimeInterface for TokioRuntime {
    async fn spawn<F, T>(&self, future: F) -> Result<JoinHandle<T>, RuntimeError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let handle = self.runtime.spawn(future);
        Ok(JoinHandle::Tokio(handle))
    }
    
    async fn spawn_with_priority<F, T>(
        &self, 
        future: F, 
        priority: TaskPriority
    ) -> Result<JoinHandle<T>, RuntimeError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let handle = self.priority_executor.spawn_with_priority(future, priority.into());
        Ok(JoinHandle::PriorityTask(handle))
    }
    
    // 其他方法实现...
}
```

### 3.2 异步特性与工作流要求对应关系

Rust的异步特性与工作流引擎需求的对应关系：

1. **Future trait**: 用于表示异步计算的基本单位，对应工作流中的活动
2. **Stream trait**: 用于表示异步数据流，对应工作流中的连续活动序列
3. **Select宏**: 用于同时等待多个Future，对应工作流中的并行分支
4. **异步上下文传播**: 用于传递上下文信息，对应工作流中的状态共享

```rust
/// 异步工作流定义
#[async_trait]
pub trait AsyncWorkflow: Send + Sync {
    type Input: DeserializeOwned + Send + 'static;
    type Output: Serialize + Send + 'static;
    type Error: Into<WorkflowError> + Send + Sync + 'static;
    
    /// 执行工作流
    async fn execute(
        &self,
        ctx: &dyn WorkflowContext,
        input: Self::Input
    ) -> Result<Self::Output, Self::Error>;
    
    /// 获取工作流的依赖活动
    fn activities(&self) -> Vec<ActivityRef>;
    
    /// 获取工作流的优先级
    fn priority(&self) -> WorkflowPriority {
        WorkflowPriority::Normal
    }
    
    /// 获取工作流的超时
    fn timeout(&self) -> Option<Duration> {
        None
    }
}

/// 工作流上下文
#[async_trait]
pub trait WorkflowContext: Send + Sync {
    /// 执行活动
    async fn execute_activity<A, I, O, E>(
        &self,
        activity_ref: &ActivityRef,
        input: I,
        options: ActivityOptions
    ) -> Result<O, WorkflowError>
    where
        A: Activity<Input = I, Output = O, Error = E> + 'static,
        I: Serialize + DeserializeOwned + Send + 'static,
        O: Serialize + DeserializeOwned + Send + 'static,
        E: Into<WorkflowError> + 'static;
        
    /// 并行执行多个活动
    async fn execute_activities_parallel<A, I, O, E>(
        &self,
        activities: Vec<(ActivityRef, I, ActivityOptions)>
    ) -> Result<Vec<Result<O, WorkflowError>>, WorkflowError>
    where
        A: Activity<Input = I, Output = O, Error = E> + 'static,
        I: Serialize + DeserializeOwned + Send + 'static,
        O: Serialize + DeserializeOwned + Send + 'static,
        E: Into<WorkflowError> + 'static;
        
    /// 等待信号
    async fn wait_for_signal<T: DeserializeOwned + Send + 'static>(
        &self,
        signal_name: &str,
        timeout: Option<Duration>
    ) -> Result<T, WorkflowError>;
    
    /// 发送信号到另一个工作流
    async fn signal_workflow(
        &self,
        workflow_id: &WorkflowId,
        signal_name: &str,
        payload: impl Serialize + Send
    ) -> Result<(), WorkflowError>;
    
    /// 获取/设置工作流状态
    async fn get_state<T: DeserializeOwned + Send + 'static>(
        &self,
        key: &str
    ) -> Result<Option<T>, WorkflowError>;
    
    async fn set_state<T: Serialize + Send>(
        &self,
        key: &str,
        value: T
    ) -> Result<(), WorkflowError>;
    
    /// 记录工作流轨迹
    async fn record_trace_event(
        &self,
        event: TraceEvent
    ) -> Result<(), WorkflowError>;
    
    /// 等待定时器
    async fn sleep(&self, duration: Duration) -> Result<(), WorkflowError>;
    
    /// 获取当前追踪上下文
    fn trace_context(&self) -> Option<&TraceContext>;
    
    /// 调整当前工作流优先级
    async fn set_priority(&self, priority: WorkflowPriority) -> Result<(), WorkflowError>;
}
```

### 3.3 类型系统应用

Rust的类型系统可以用于增强工作流引擎的类型安全性：

1. **类型状态模式**：利用Rust的类型系统确保工作流状态转换的正确性
2. **Trait约束**：用于限制工作流和活动的实现必须满足特定条件
3. **范型**：允许灵活定义工作流和活动的输入输出类型

```rust
/// 使用类型状态模式确保状态转换正确性
pub struct WorkflowBuilder<S = Initial> {
    workflow_id: Option<WorkflowId>,
    workflow_type: Option<String>,
    state: PhantomData<S>,
    activities: Vec<ActivityRef>,
    stages: Vec<WorkflowStage>,
}

// 类型状态标记
pub struct Initial;
pub struct WithType;
pub struct WithActivities;
pub struct Ready;

impl WorkflowBuilder<Initial> {
    pub fn new() -> Self {
        Self {
            workflow_id: None,
            workflow_type: None,
            state: PhantomData,
            activities: Vec::new(),
            stages: Vec::new(),
        }
    }
    
    pub fn with_type(self, workflow_type: impl Into<String>) -> WorkflowBuilder<WithType> {
        WorkflowBuilder {
            workflow_id: self.workflow_id,
            workflow_type: Some(workflow_type.into()),
            state: PhantomData,
            activities: self.activities,
            stages: self.stages,
        }
    }
}

impl WorkflowBuilder<WithType> {
    pub fn add_activity(mut self, activity: ActivityRef) -> Self {
        self.activities.push(activity);
        self
    }
    
    pub fn add_stage(mut self, stage: WorkflowStage) -> Self {
        self.stages.push(stage);
        self
    }
    
    pub fn with_activities(self) -> WorkflowBuilder<WithActivities> {
        WorkflowBuilder {
            workflow_id: self.workflow_id,
            workflow_type: self.workflow_type,
            state: PhantomData,
            activities: self.activities,
            stages: self.stages,
        }
    }
}

impl WorkflowBuilder<WithActivities> {
    pub fn build(self) -> Result<WorkflowDefinition, WorkflowError> {
        if self.stages.is_empty() {
            return Err(WorkflowError::ValidationError("Workflow must have at least one stage".into()));
        }
        
        Ok(WorkflowDefinition {
            workflow_id: self.workflow_id.unwrap_or_else(WorkflowId::new),
            workflow_type: self.workflow_type.expect("Workflow type must be set"),
            activities: self.activities,
            stages: self.stages,
        })
    }
}

// 使用示例：
let workflow = WorkflowBuilder::new()
    .with_type("order_processing")
    .add_activity(validate_activity)
    .add_activity(payment_activity)
    .add_stage(validation_stage)
    .add_stage(payment_stage)
    .with_activities()
    .build()?;
```

## 4. 容错与恢复机制

### 4.1 故障模型分类

为了建立健壮的容错系统，首先需要系统地分类可能的故障类型：

1. **节点故障**：运行工作流引擎的节点崩溃或重启
2. **网络故障**：节点间通信失败或超时
3. **存储故障**：持久化层写入/读取失败
4. **逻辑故障**：工作流活动执行出错
5. **资源耗尽**：内存、CPU或磁盘空间耗尽

```rust
/// 故障类型分类
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FailureType {
    /// 节点故障
    NodeFailure {
        node_id: String,
        restart_count: u32,
    },
    /// 网络故障
    NetworkFailure {
        target: String,
        error_code: Option<i32>,
        timeout: bool,
    },
    /// 存储故障
    StorageFailure {
        operation: StorageOperation,
        error_details: String,
    },
    /// 逻辑故障
    LogicFailure {
        activity_id: String,
        error_code: String,
        message: String,
    },
    /// 资源耗尽
    ResourceExhaustion {
        resource_type: ResourceType,
        limit: u64,
        requested: u64,
    },
    /// 超时故障
    Timeout {
        operation: String,
        duration_ms: u64,
        limit_ms: u64,
    },
    /// 未知故障
    Unknown {
        error_message: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StorageOperation {
    Read,
    Write,
    Delete,
    Update,
    Query,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResourceType {
    Memory,
    Cpu,
    Disk,
    Network,
    Connection,
    FileDescriptor,
    Thread,
    Other(String),
}

/// 故障上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailureContext {
    /// 故障ID
    pub failure_id: String,
    /// 故障类型
    pub failure_type: FailureType,
    /// 相关工作流ID
    pub workflow_id: Option<WorkflowId>,
    /// 相关活动ID
    pub activity_id: Option<String>,
    /// 故障发生时间
    pub timestamp: DateTime<Utc>,
    /// 故障发生位置（代码位置）
    pub location: String,
    /// 追踪上下文
    pub trace_context: Option<TraceContext>,
    /// 已尝试的恢复策略
    pub recovery_attempts: Vec<RecoveryAttempt>,
    /// 可能的解决方案
    pub possible_solutions: Vec<String>,
    /// 运行时信息快照
    pub runtime_snapshot: Option<serde_json::Value>,
}

/// 恢复尝试记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecoveryAttempt {
    /// 尝试ID
    pub attempt_id: String,
    /// 恢复策略
    pub strategy: RecoveryStrategy,
    /// 开始时间
    pub start_time: DateTime<Utc>,
    /// 结束时间
    pub end_time: Option<DateTime<Utc>>,
    /// 结果
    pub result: RecoveryResult,
    /// 详细信息
    pub details: String,
}

/// 恢复结果
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecoveryResult {
    Success,
    Failure,
    PartialSuccess,
    InProgress,
}
```

### 4.2 优雅故障处理策略

根据故障类型，我们设计不同的处理策略：

```rust
/// 恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryStrategy {
    /// 简单重试
    Retry {
        max_attempts: u32,
        backoff_policy: BackoffPolicy,
    },
    /// 使用降级服务
    Fallback {
        fallback_service: String,
        fallback_parameters: Option<serde_json::Value>,
    },
    /// 跳过故障点
    Skip {
        continue_from: String,
    },
    /// 补偿事务
    Compensate {
        compensation_activities: Vec<String>,
    },
    /// 人工干预
    ManualIntervention {
        required_role: String,
        instructions: String,
        timeout: Duration,
    },
    /// 系统重启
    Restart {
        clean_state: bool,
        notify_admin: bool,
    },
}

/// 退避策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BackoffPolicy {
    /// 固定间隔
    Fixed(Duration),
    /// 线性增长: initial + (attempt * increment)
    Linear {
        initial: Duration,
        increment: Duration,
    },
    /// 指数增长: initial * (multiplier ^ attempt)
    Exponential {
        initial: Duration,
        multiplier: f64,
        max: Duration,
    },
    /// 随机抖动: base * (1 + random(-jitter, jitter))
    Jitter {
        base: Duration,
        jitter: f64,
    },
}

impl BackoffPolicy {
    /// 计算第n次尝试的延迟时间
    pub fn calculate_delay(&self, attempt: u32) -> Duration {
        match self {
            Self::Fixed(duration) => *duration,
            Self::Linear { initial, increment } => {
                *initial + (*increment * attempt as u32)
            },
            Self::Exponential { initial, multiplier, max } => {
                let calculated = initial.as_millis() as f64 * multiplier.powf(attempt as f64);
                Duration::from_millis(calculated.min(max.as_millis() as f64) as u64)
            },
            Self::Jitter { base, jitter } => {
                let random_factor = 1.0 + thread_rng().gen_range(-*jitter..*jitter);
                let jittered_millis = (base.as_millis() as f64 * random_factor) as u64;
                Duration::from_millis(jittered_millis)
            },
        }
    }
}

/// 故障处理器
#[async_trait]
pub trait FailureHandler: Send + Sync {
    /// 处理故障
    async fn handle_failure(
        &self,
        context: &FailureContext,
        workflow_engine: &dyn WorkflowEngine,
    ) -> Result<RecoveryResult, WorkflowError>;
    
    /// 确定恢复策略
    fn determine_strategy(&self, context: &FailureContext) -> RecoveryStrategy;
    
    /// 应用恢复策略
    async fn apply_strategy(
        &self,
        strategy: &RecoveryStrategy,
        context: &FailureContext,
        workflow_engine: &dyn WorkflowEngine,
    ) -> Result<RecoveryResult, WorkflowError>;
}

/// 默认故障处理器实现
pub struct DefaultFailureHandler {
    config: FailureHandlerConfig,
    metrics: Arc<FailureMetrics>,
    alert_manager: Arc<dyn AlertManager>,
}

#[async_trait]
impl FailureHandler for DefaultFailureHandler {
    async fn handle_failure(
        &self,
        context: &FailureContext,
        workflow_engine: &dyn WorkflowEngine,
    ) -> Result<RecoveryResult, WorkflowError> {
        // 记录故障指标
        self.metrics.record_failure(&context.failure_type);
        
        // 确定恢复策略
        let strategy = self.determine_strategy(context);
        
        // 记录处理日志
        log::info!(
            "Handling failure {} with strategy {:?}",
            context.failure_id,
            strategy
        );
        
        // 构建新的失败上下文
        let mut updated_context = context.clone();
        let attempt = RecoveryAttempt {
            attempt_id: Uuid::new_v4().to_string(),
            strategy: strategy.clone(),
            start_time: Utc::now(),
            end_time: None,
            result: RecoveryResult::InProgress,
            details: format!("Attempting recovery with strategy: {:?}", strategy),
        };
        updated_context.recovery_attempts.push(attempt);
        
        // 根据故障级别决定是否发送告警
        let severity = self.calculate_severity(context);
        if severity >= AlertSeverity::Warning {
            self.alert_manager.send_alert(Alert {
                id: Uuid::new_v4().to_string(),
                title: format!("Workflow failure: {}", context.failure_type),
                message: format!("Failure in workflow {}. Recovery in progress.", 
                    context.workflow_id.as_ref().map(|id| id.to_string()).unwrap_or_default()),
                severity,
                timestamp: Utc::now(),
                context: serde_json::to_value(context).unwrap_or(serde_json::Value::Null),
                source: "workflow_engine".to_string(),
            }).await?;
        }
        
        // 应用恢复策略
        let result = self.apply_strategy(&strategy, &updated_context, workflow_engine).await?;
        
        // 更新恢复尝试结果
        if let Some(last_attempt) = updated_context.recovery_attempts.last_mut() {
            last_attempt.end_time = Some(Utc::now());
            last_attempt.result = result.clone();
            last_attempt.details = format!("Recovery attempt completed with result: {:?}", result);
        }
        
        // 记录恢复指标
        self.metrics.record_recovery(&context.failure_type, &result);
        
        Ok(result)
    }
    
    fn determine_strategy(&self, context: &FailureContext) -> RecoveryStrategy {
        match &context.failure_type {
            FailureType::NodeFailure { .. } => {
                // 节点故障通常需要重启或迁移
                if context.recovery_attempts.len() < 3 {
                    RecoveryStrategy::Retry {
                        max_attempts: 3,
                        backoff_policy: BackoffPolicy::Exponential {
                            initial: Duration::from_secs(1),
                            multiplier: 2.0,
                            max: Duration::from_secs(60),
                        },
                    }
                } else {
                    RecoveryStrategy::Restart {
                        clean_state: false,
                        notify_admin: true,
                    }
                }
            },
            FailureType::NetworkFailure { timeout, .. } => {
                // 网络超时通常采用重试策略
                if *timeout {
                    RecoveryStrategy::Retry {
                        max_attempts: 5,
                        backoff_policy: BackoffPolicy::Jitter {
                            base: Duration::from_secs(5),
                            jitter: 0.3,
                        },
                    }
                } else {
                    // 非超时网络错误可能需要更复杂的策略
                    RecoveryStrategy::Fallback {
                        fallback_service: "backup_network_service".to_string(),
                        fallback_parameters: None,
                    }
                }
            },
            FailureType::StorageFailure { operation, .. } => {
                match operation {
                    StorageOperation::Read => {
                        // 读取错误尝试使用备份存储
                        RecoveryStrategy::Fallback {
                            fallback_service: "backup_storage_service".to_string(),
                            fallback_parameters: None,
                        }
                    },
                    StorageOperation::Write | StorageOperation::Update => {
                        // 写入/更新错误可能需要重试
                        RecoveryStrategy::Retry {
                            max_attempts: 3,
                            backoff_policy: BackoffPolicy::Linear {
                                initial: Duration::from_secs(1),
                                increment: Duration::from_secs(2),
                            },
                        }
                    },
                    _ => {
                        // 其他存储操作使用通用策略
                        RecoveryStrategy::Retry {
                            max_attempts: 3,
                            backoff_policy: BackoffPolicy::Exponential {
                                initial: Duration::from_secs(1),
                                multiplier: 2.0,
                                max: Duration::from_secs(30),
                            },
                        }
                    }
                }
            },
            FailureType::LogicFailure { .. } => {
                // 逻辑错误通常需要补偿事务
                RecoveryStrategy::Compensate {
                    compensation_activities: vec!["rollback_activity".to_string()],
                }
            },
            FailureType::ResourceExhaustion { resource_type, .. } => {
                match resource_type {
                    ResourceType::Memory | ResourceType::Cpu => {
                        // 资源耗尽可能需要系统级干预
                        RecoveryStrategy::ManualIntervention {
                            required_role: "system_admin".to_string(),
                            instructions: format!("{:?} exhaustion detected, please allocate more resources", resource_type),
                            timeout: Duration::from_secs(3600),
                        }
                    },
                    _ => {
                        // 其他资源问题尝试重启
                        RecoveryStrategy::Restart {
                            clean_state: true,
                            notify_admin: true,
                        }
                    }
                }
            },
            FailureType::Timeout { .. } => {
                // 超时通常需要重试或跳过
                if context.recovery_attempts.len() < 2 {
                    RecoveryStrategy::Retry {
                        max_attempts: 2,
                        backoff_policy: BackoffPolicy::Fixed(Duration::from_secs(10)),
                    }
                } else {
                    // 多次超时后尝试跳过
                    RecoveryStrategy::Skip {
                        continue_from: "next_critical_point".to_string(),
                    }
                }
            },
            FailureType::Unknown { .. } => {
                // 未知错误需要人工干预
                RecoveryStrategy::ManualIntervention {
                    required_role: "workflow_admin".to_string(),
                    instructions: "Unknown error detected, please investigate".to_string(),
                    timeout: Duration::from_secs(7200),
                }
            },
        }
    }
    
    async fn apply_strategy(
        &self,
        strategy: &RecoveryStrategy,
        context: &FailureContext,
        workflow_engine: &dyn WorkflowEngine,
    ) -> Result<RecoveryResult, WorkflowError> {
        match strategy {
            RecoveryStrategy::Retry { max_attempts, backoff_policy } => {
                // 检查是否超过最大重试次数
                let retry_count = context.recovery_attempts.iter()
                    .filter(|a| matches!(a.strategy, RecoveryStrategy::Retry { .. }))
                    .count();
                    
                if retry_count >= *max_attempts as usize {
                    return Ok(RecoveryResult::Failure);
                }
                
                // 计算退避时间
                let delay = backoff_policy.calculate_delay(retry_count as u32);
                
                // 休眠指定时间
                tokio::time::sleep(delay).await;
                
                // 重试逻辑
                if let Some(workflow_id) = &context.workflow_id {
                    // 获取当前工作流状态
                    let state = workflow_engine.get_workflow_state(workflow_id).await?;
                    
                    // 基于状态执行重试
                    match state {
                        WorkflowState::Failed { .. } => {
                            // 重新启动失败的工作流
                            workflow_engine.retry_workflow(workflow_id).await?;
                            Ok(RecoveryResult::Success)
                        },
                        WorkflowState::Running { .. } => {
                            // 工作流已经在运行，可能是并发恢复导致
                            Ok(RecoveryResult::PartialSuccess)
                        },
                        _ => {
                            // 其他状态无法重试
                            Ok(RecoveryResult::Failure)
                        }
                    }
                } else {
                    // 没有工作流ID，无法执行具体重试
                    Ok(RecoveryResult::Failure)
                }
            },
            RecoveryStrategy::Fallback { fallback_service, fallback_parameters } => {
                // 调用降级服务
                log::info!(
                    "Calling fallback service {} with params {:?}",
                    fallback_service,
                    fallback_parameters
                );
                
                // 这里是示例实现，实际应调用具体的降级服务
                if let Some(workflow_id) = &context.workflow_id {
                    workflow_engine.execute_fallback(
                        workflow_id,
                        fallback_service,
                        fallback_parameters.clone().unwrap_or(serde_json::Value::Null)
                    ).await?;
                    
                    Ok(RecoveryResult::Success)
                } else {
                    Ok(RecoveryResult::Failure)
                }
            },
            RecoveryStrategy::Skip { continue_from } => {
                // 跳过当前失败的活动
                if let Some(workflow_id) = &context.workflow_id {
                    workflow_engine.skip_to_activity(workflow_id, continue_from).await?;
                    Ok(RecoveryResult::Success)
                } else {
                    Ok(RecoveryResult::Failure)
                }
            },
            RecoveryStrategy::Compensate { compensation_activities } => {
                // 执行补偿活动
                if let Some(workflow_id) = &context.workflow_id {
                    for activity in compensation_activities {
                        workflow_engine.execute_compensation(workflow_id, activity).await?;
                    }
                    Ok(RecoveryResult::Success)
                } else {
                    Ok(RecoveryResult::Failure)
                }
            },
            RecoveryStrategy::ManualIntervention { required_role, instructions, timeout } => {
                // 创建人工干预任务
                if let Some(workflow_id) = &context.workflow_id {
                    let intervention_id = workflow_engine.create_intervention_task(
                        workflow_id,
                        required_role,
                        instructions,
                        *timeout
                    ).await?;
                    
                    log::info!(
                        "Created manual intervention task {} for workflow {}",
                        intervention_id,
                        workflow_id
                    );
                    
                    // 这里我们不等待人工干预完成，返回进行中状态
                    Ok(RecoveryResult::InProgress)
                } else {
                    Ok(RecoveryResult::Failure)
                }
            },
            RecoveryStrategy::Restart { clean_state, notify_admin } => {
                // 重启处理逻辑
                log::warn!(
                    "Initiating system restart (clean_state={}, notify_admin={})",
                    clean_state,
                    notify_admin
                );
                
                if *notify_admin {
                    self.alert_manager.send_alert(Alert {
                        id: Uuid::new_v4().to_string(),
                        title: "System restart initiated".to_string(),
                        message: format!(
                            "Workflow engine restart initiated due to failure: {:?}",
                            context.failure_type
                        ),
                        severity: AlertSeverity::Critical,
                        timestamp: Utc::now(),
                        context: serde_json::to_value(context).unwrap_or(serde_json::Value::Null),
                        source: "workflow_engine".to_string(),
                    }).await?;
                }
                
                // 实际重启逻辑会通过工作流引擎对外接口触发
                // 这里只返回成功状态
                Ok(RecoveryResult::Success)
            },
        }
    }
    
    fn calculate_severity(&self, context: &FailureContext) -> AlertSeverity {
        match &context.failure_type {
            FailureType::NodeFailure { .. } => AlertSeverity::Critical,
            FailureType::NetworkFailure { timeout, .. } => {
                if *timeout {
                    AlertSeverity::Warning
                } else {
                    AlertSeverity::Error
                }
            },
            FailureType::StorageFailure { operation, .. } => {
                match operation {
                    StorageOperation::Read | StorageOperation::Write => AlertSeverity::Error,
                    _ => AlertSeverity::Warning,
                }
            },
            FailureType::LogicFailure { .. } => AlertSeverity::Warning,
            FailureType::ResourceExhaustion { .. } => AlertSeverity::Critical,
            FailureType::Timeout { .. } => AlertSeverity::Warning,
            FailureType::Unknown { .. } => AlertSeverity::Critical,
        }
    }
}
```

### 4.3 恢复机制设计

容错系统的关键是能够从故障中恢复。我们实现了三种主要恢复机制：

1. **检查点恢复**：基于定期保存的检查点恢复工作流状态
2. **增量恢复**：仅重播发生故障后的事件
3. **热备份恢复**：在备用节点上快速恢复工作流

```rust
/// 工作流恢复器
#[async_trait]
pub trait WorkflowRecovery: Send + Sync {
    /// 从故障中恢复工作流
    async fn recover_workflow(
        &self,
        workflow_id: &WorkflowId,
        failure_context: Option<&FailureContext>,
    ) -> Result<RecoveryResult, WorkflowError>;
    
    /// 确定最佳恢复点
    async fn determine_recovery_point(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<RecoveryPoint, WorkflowError>;
    
    /// 验证恢复后的工作流状态
    async fn validate_recovered_state(
        &self,
        workflow_id: &WorkflowId,
        recovered_state: &WorkflowState,
    ) -> Result<bool, WorkflowError>;
}

/// 恢复点定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecoveryPoint {
    /// 恢复点ID
    pub id: String,
    /// 关联的工作流ID
    pub workflow_id: WorkflowId,
    /// 恢复点类型
    pub point_type: RecoveryPointType,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 恢复点数据
    pub data: RecoveryPointData,
    /// 检查点序列号（对于事件日志）
    pub sequence_number: Option<u64>,
    /// 关联的检查点ID（如果有）
    pub checkpoint_id: Option<String>,
    /// 验证哈希
    pub verification_hash: String,
}

/// 恢复点类型
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecoveryPointType {
    /// 完整检查点
    FullCheckpoint,
    /// 增量检查点
    IncrementalCheckpoint,
    /// 事件日志位置
    EventLogPosition,
    /// 热备份快照
    HotBackupSnapshot,
}

/// 恢复点数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryPointData {
    /// 完整工作流状态
    FullState(WorkflowState),
    /// 增量状态变更
    IncrementalState {
        base_checkpoint_id: String,
        changes: Vec<StateChange>,
    },
    /// 事件日志位置
    EventPosition {
        last_event_id: String,
        event_sequence: u64,
    },
    /// 热备份快照引用
    SnapshotReference {
        snapshot_id: String,
        location: String,
    },
}

/// 状态变更
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateChange {
    /// 变更路径
    pub path: String,
    /// 变更操作
    pub operation: ChangeOperation,
    /// 变更值
    pub value: Option<serde_json::Value>,
}

/// 变更操作
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChangeOperation {
    Add,
    Remove,
    Replace,
    Copy,
    Move,
    Test,
}

/// 默认工作流恢复器
pub struct DefaultWorkflowRecovery {
    event_store: Arc<dyn EventStore>,
    checkpoint_store: Arc<dyn CheckpointStore>,
    snapshot_store: Arc<dyn SnapshotStore>,
    config: RecoveryConfig,
    metrics: Arc<RecoveryMetrics>,
}

#[async_trait]
impl WorkflowRecovery for DefaultWorkflowRecovery {
    async fn recover_workflow(
        &self,
        workflow_id: &WorkflowId,
        failure_context: Option<&FailureContext>,
    ) -> Result<RecoveryResult, WorkflowError> {
        // 记录恢复开始
        log::info!("Starting recovery for workflow {}", workflow_id);
        self.metrics.recovery_started(workflow_id);
        
        let start_time = Instant::now();
        
        // 确定恢复点
        let recovery_point = self.determine_recovery_point(workflow_id).await?;
        
        log::info!(
            "Using recovery point {:?} of type {:?}",
            recovery_point.id,
            recovery_point.point_type
        );
        
        // 根据恢复点类型执行不同的恢复策略
        let recovered_state = match recovery_point.point_type {
            RecoveryPointType::FullCheckpoint => {
                self.recover_from_full_checkpoint(&recovery_point).await?
            },
            RecoveryPointType::IncrementalCheckpoint => {
                self.recover_from_incremental_checkpoint(&recovery_point).await?
            },
            RecoveryPointType::EventLogPosition => {
                self.recover_from_event_log(&recovery_point).await?
            },
            RecoveryPointType::HotBackupSnapshot => {
                self.recover_from_snapshot(&recovery_point).await?
            },
        };
        
        // 验证恢复的状态
        let is_valid = self.validate_recovered_state(workflow_id, &recovered_state).await?;
        
        if !is_valid {
            log::error!(
                "Recovered state validation failed for workflow {}",
                workflow_id
            );
            self.metrics.recovery_failed(workflow_id, "validation_failed");
            return Ok(RecoveryResult::Failure);
        }
        
        // 应用恢复的状态到工作流引擎
        self.apply_recovered_state(workflow_id, &recovered_state).await?;
        
        // 处理特定故障的恢复逻辑
        if let Some(context) = failure_context {
            self.handle_specific_failure(workflow_id, context, &recovered_state).await?;
        }
        
        // 记录恢复完成
        let recovery_duration = start_time.elapsed();
        log::info!(
            "Recovery completed for workflow {} in {:?}",
            workflow_id,
            recovery_duration
        );
        
        self.metrics.recovery_completed(workflow_id, recovery_duration);
        
        Ok(RecoveryResult::Success)
    }
    
    async fn determine_recovery_point(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<RecoveryPoint, WorkflowError> {
        // 首先尝试获取最新热备份
        if let Ok(snapshot) = self.snapshot_store.get_latest_snapshot(workflow_id).await {
            return Ok(RecoveryPoint {
                id: format!("recovery-{}", Uuid::new_v4()),
                workflow_id: workflow_id.clone(),
                point_type: RecoveryPointType::HotBackupSnapshot,
                created_at: Utc::now(),
                data: RecoveryPointData::SnapshotReference {
                    snapshot_id: snapshot.id,
                    location: snapshot.location,
                },
                sequence_number: Some(snapshot.sequence_number),
                checkpoint_id: None,
                verification_hash: snapshot.verification_hash,
            });
        }
        
        // 尝试获取最新检查点
        if let Ok(Some((checkpoint, seq))) = self.checkpoint_store
            .get_latest_checkpoint(workflow_id).await
        {
            // 检查是否有增量检查点
            if let Ok(incremental) = self.checkpoint_store
                .get_incremental_checkpoints(workflow_id, &checkpoint.id).await
            {
                if !incremental.is_empty() {
                    // 使用最新的增量检查点
                    let latest = incremental.last().unwrap();
                    return Ok(RecoveryPoint {
                        id: format!("recovery-{}", Uuid::new_v4()),
                        workflow_id: workflow_id.clone(),
                        point_type: RecoveryPointType::IncrementalCheckpoint,
                        created_at: Utc::now(),
                        data: RecoveryPointData::IncrementalState {
                            base_checkpoint_id: checkpoint.id.clone(),
                            changes: latest.changes.clone(),
                        },
                        sequence_number: Some(latest.sequence_number),
                        checkpoint_id: Some(latest.id.clone()),
                        verification_hash: latest.verification_hash.clone(),
                    });
                }
            }
            
            // 使用完整检查点
            return Ok(RecoveryPoint {
                id: format!("recovery-{}", Uuid::new_v4()),
                workflow_id: workflow_id.clone(),
                point_type: RecoveryPointType::FullCheckpoint,
                created_at: Utc::now(),
                data: RecoveryPointData::FullState(checkpoint.clone()),
                sequence_number: Some(seq),
                checkpoint_id: Some(checkpoint.id.clone()),
                verification_hash: checkpoint.verification_hash.clone(),
            });
        }
        
        // 回退到事件日志恢复
        let events = self.event_store.get_events(workflow_id).await?;
        
        if events.is_empty() {
            return Err(WorkflowError::RecoveryError(
                format!("No recovery points available for workflow {}", workflow_id)
            ));
        }
        
        let last_event = events.last().unwrap();
        
        Ok(RecoveryPoint {
            id: format!("recovery-{}", Uuid::new_v4()),
            workflow_id: workflow_id.clone(),
            point_type: RecoveryPointType::EventLogPosition,
            created_at: Utc::now(),
            data: RecoveryPointData::EventPosition {
                last_event_id: last_event.0.clone(),
                event_sequence: last_event.1,
            },
            sequence_number: Some(last_event.1),
            checkpoint_id: None,
            verification_hash: calculate_events_hash(&events),
        })
    }
    
    async fn validate_recovered_state(
        &self,
        workflow_id: &WorkflowId,
        recovered_state: &WorkflowState,
    ) -> Result<bool, WorkflowError> {
        // 基本验证：确保状态中的工作流ID匹配
        if let Some(state_workflow_id) = get_workflow_id_from_state(recovered_state) {
            if state_workflow_id != *workflow_id {
                log::error!(
                    "Workflow ID mismatch: expected {}, found {}",
                    workflow_id,
                    state_workflow_id
                );
                return Ok(false);
            }
        } else {
            log::error!("Could not extract workflow ID from recovered state");
            return Ok(false);
        }
        
        // 验证状态一致性
        if !is_state_consistent(recovered_state) {
            log::error!("Recovered state is inconsistent");
            return Ok(false);
        }
        
        // 验证状态与事件日志匹配
        let events = self.event_store.get_events(workflow_id).await?;
        if !do_events_match_state(&events, recovered_state) {
            log::error!("Recovered state does not match event log");
            return Ok(false);
        }
        
        Ok(true)
    }
    
    // 辅助方法，从不同类型的恢复点恢复状态
    async fn recover_from_full_checkpoint(
        &self,
        recovery_point: &RecoveryPoint,
    ) -> Result<WorkflowState, WorkflowError> {
        if let RecoveryPointData::FullState(state) = &recovery_point.data {
            Ok(state.clone())
        } else {
            Err(WorkflowError::RecoveryError(
                "Invalid recovery point data type".to_string()
            ))
        }
    }
    
    async fn recover_from_incremental_checkpoint(
        &self,
        recovery_point: &RecoveryPoint,
    ) -> Result<WorkflowState, WorkflowError> {
        if let RecoveryPointData::IncrementalState { base_checkpoint_id, changes } = &recovery_point.data {
            // 获取基础检查点
            let base_checkpoint = self.checkpoint_store
                .get_checkpoint(&recovery_point.workflow_id, base_checkpoint_id)
                .await?
                .ok_or_else(|| WorkflowError::RecoveryError(
                    format!("Base checkpoint {} not found", base_checkpoint_id)
                ))?;
            
            // 应用增量变更
            let mut state = base_checkpoint.0;
            
            for change in changes {
                apply_state_change(&mut state, change)?;
            }
            
            Ok(state)
        } else {
            Err(WorkflowError::RecoveryError(
                "Invalid recovery point data type".to_string()
            ))
        }
    }
    
    async fn recover_from_event_log(
        &self,
        recovery_point: &RecoveryPoint,
    ) -> Result<WorkflowState, WorkflowError> {
        // 获取所有事件
        let events = self.event_store.get_events(&recovery_point.workflow_id).await?;
        
        // 从初始状态开始重放事件
        let mut state = WorkflowState::Created {
            workflow_id: recovery_point.workflow_id.clone(),
            workflow_type: "unknown".to_string(), // 将从事件中更新
            created_at: Utc::now(),
        };
        
        // 并行重放事件以加速恢复
        let chunks = chunk_events_for_parallel_replay(&events);
        let mut states = Vec::with_capacity(chunks.len());
        
        // 为每个分块创建初始状态
        for i in 0..chunks.len() {
            if i == 0 {
                states.push(state.clone());
            } else {
                // 占位符状态，将在处理前一块后更新
                states.push(state.clone());
            }
        }
        
        // 并行处理事件块
        let mut handles = Vec::new();
        for (i, chunk) in chunks.iter().enumerate() {
            let chunk = chunk.clone();
            let state = if i == 0 {
                states[0].clone()
            } else {
                // 等待前一块处理完成
                states[i].clone()
            };
            
            let handle = tokio::spawn(async move {
                replay_events(state, &chunk)
            });
            
            handles.push(handle);
        }
        
        // 收集结果
        for (i, handle) in handles.into_iter().enumerate() {
            let result = handle.await.map_err(|e| 
                WorkflowError::RecoveryError(format!("Event replay task failed: {}", e))
            )??;
            
            if i < states.len() - 1 {
                states[i + 1] = result.clone();
            }
            
            if i == handles.len() - 1 {
                // 最后一个处理完成的状态是最终结果
                return Ok(result);
            }
        }
        
        // 应该不会到达这里，除非没有事件
        Ok(state)
    }
    
    async fn recover_from_snapshot(
        &self,
        recovery_point: &RecoveryPoint,
    ) -> Result<WorkflowState, WorkflowError> {
        if let RecoveryPointData::SnapshotReference { snapshot_id, location } = &recovery_point.data {
            // 从快照存储获取状态
            let snapshot = self.snapshot_store.get_snapshot(
                &recovery_point.workflow_id,
                snapshot_id,
            ).await?;
            
            // 验证快照哈希
            if snapshot.verification_hash != recovery_point.verification_hash {
                return Err(WorkflowError::RecoveryError(
                    "Snapshot verification hash mismatch".to_string()
                ));
            }
            
            // 检查是否有更新的事件
            if let Some(seq) = recovery_point.sequence_number {
                let newer_events = self.event_store
                    .get_events_after(&recovery_point.workflow_id, seq)
                    .await?;
                
                if !newer_events.is_empty() {
                    // 应用更新的事件到快照状态
                    return Ok(replay_events(snapshot.state, &newer_events)?);
                }
            }
            
            Ok(snapshot.state)
        } else {
            Err(WorkflowError::RecoveryError(
                "Invalid recovery point data type".to_string()
            ))
        }
    }
    
    async fn apply_recovered_state(
        &self,
        workflow_id: &WorkflowId,
        state: &WorkflowState,
    ) -> Result<(), WorkflowError> {
        // 将恢复的状态应用到检查点存储
        self.checkpoint_store.save_checkpoint(
            workflow_id,
            state,
            format!("recovery-{}", Uuid::new_v4()),
            state.sequence_number().unwrap_or(0),
            calculate_state_hash(state),
        ).await?;
        
        Ok(())
    }
    
    async fn handle_specific_failure(
        &self,
        workflow_id: &WorkflowId,
        failure_context: &FailureContext,
        recovered_state: &WorkflowState,
    ) -> Result<(), WorkflowError> {
        match &failure_context.failure_type {
            FailureType::NodeFailure { .. } => {
                // 节点故障时可能需要迁移工作流到新节点
                log::info!("Preparing workflow migration after node failure");
                // 具体迁移逻辑...
            },
            FailureType::StorageFailure { .. } => {
                // 存储故障时可能需要验证数据一致性
                log::info!("Verifying data consistency after storage failure");
                // 一致性验证逻辑...
            },
            FailureType::LogicFailure { activity_id, .. } => {
                // 逻辑故障可能需要跳过或标记特定活动
                log::info!("Marking activity {} as failed", activity_id);
                // 活动标记逻辑...
            },
            _ => {
                // 通用故障处理
                log::info!("Applying generic failure handling");
            }
        }
        
        Ok(())
    }
}

// 辅助函数
fn calculate_events_hash(events: &[(String, u64, WorkflowEvent)]) -> String {
    use sha2::{Sha256, Digest};
    
    let mut hasher = Sha256::new();
    
    for (id, seq, event) in events {
        hasher.update(id.as_bytes());
        hasher.update(&seq.to_be_bytes());
        
        // 序列化事件并更新哈希
        if let Ok(json) = serde_json::to_string(event) {
            hasher.update(json.as_bytes());
        }
    }
    
    format!("{:x}", hasher.finalize())
}

fn get_workflow_id_from_state(state: &WorkflowState) -> Option<WorkflowId> {
    match state {
        WorkflowState::Created { workflow_id, .. } => Some(workflow_id.clone()),
        WorkflowState::Running { workflow_id, .. } => Some(workflow_id.clone()),
        WorkflowState::Suspended { workflow_id, .. } => Some(workflow_id.clone()),
        WorkflowState::Completed { workflow_id, .. } => Some(workflow_id.clone()),
        WorkflowState::Failed { workflow_id, .. } => Some(workflow_id.clone()),
        WorkflowState::Cancelled { workflow_id, .. } => Some(workflow_id.clone()),
    }
}

fn is_state_consistent(state: &WorkflowState) -> bool {
    // 验证状态内部一致性的逻辑
    // 例如，失败状态必须有错误信息等
    match state {
        WorkflowState::Failed { error, .. } => error.is_some(),
        WorkflowState::Completed { result, .. } => true,  // 结果可以为None
        WorkflowState::Running { current_stage, progress, .. } => {
            !current_stage.is_empty() && *progress >= 0.0 && *progress <= 1.0
        },
        _ => true,  // 其他状态的验证逻辑
    }
}

fn do_events_match_state(
    events: &[(String, u64, WorkflowEvent)],
    state: &WorkflowState,
) -> bool {
    if events.is_empty() {
        return false;
    }
    
    // 检查最后一个事件是否与当前状态匹配
    let (_, _, last_event) = events.last().unwrap();
    
    match (last_event, state) {
        (WorkflowEvent::WorkflowCompleted { .. }, WorkflowState::Completed { .. }) => true,
        (WorkflowEvent::WorkflowFailed { .. }, WorkflowState::Failed { .. }) => true,
        (WorkflowEvent::WorkflowCancelled { .. }, WorkflowState::Cancelled { .. }) => true,
        (WorkflowEvent::WorkflowSuspended { .. }, WorkflowState::Suspended { .. }) => true,
        (WorkflowEvent::StageStarted { .. }, WorkflowState::Running { .. }) => true,
        (WorkflowEvent::StageCompleted { .. }, WorkflowState::Running { .. }) => true,
        (WorkflowEvent::WorkflowStarted { .. }, WorkflowState::Running { .. }) => true,
        _ => false,
    }
}

fn apply_state_change(
    state: &mut WorkflowState,
    change: &StateChange,
) -> Result<(), WorkflowError> {
    // 使用JSON Patch风格应用状态变更
    match change.operation {
        ChangeOperation::Replace => {
            // 将状态序列化为JSON对象
            let mut state_json = serde_json::to_value(state)
                .map_err(|e| WorkflowError::SerializationError(e.to_string()))?;
            
            // 解析路径
            let path_segments: Vec<&str> = change.path.split('/').filter(|s| !s.is_empty()).collect();
            
            // 递归更新JSON对象
            update_json_at_path(&mut state_json, &path_segments, change.value.clone())?;
            
            // 反序列化回状态对象
            *state = serde_json::from_value(state_json)
                .map_err(|e| WorkflowError::DeserializationError(e.to_string()))?;
            
            Ok(())
        },
        // 其他操作类型的实现...
        _ => Err(WorkflowError::RecoveryError(
            format!("Change operation {:?} not implemented", change.operation)
        )),
    }
}

fn update_json_at_path(
    json: &mut serde_json::Value,
    path: &[&str],
    value: Option<serde_json::Value>,
) -> Result<(), WorkflowError> {
    if path.is_empty() {
        // 到达路径末尾，设置值
        if let Some(v) = value {
            *json = v;
        }
        return Ok(());
    }
    
    let segment = path[0];
    let remaining = &path[1..];
    
    if let Some(obj) = json.as_object_mut() {
        // 处理对象
        let next = obj.entry(segment).or_insert(serde_json::Value::Null);
        update_json_at_path(next, remaining, value)
    } else if let Some(arr) = json.as_array_mut() {
        // 处理数组
        if let Ok(index) = segment.parse::<usize>() {
            if index < arr.len() {
                update_json_at_path(&mut arr[index], remaining, value)
            } else {
                Err(WorkflowError::RecoveryError(
                    format!("Array index out of bounds: {}", index)
                ))
            }
        } else {
            Err(WorkflowError::RecoveryError(
                format!("Invalid array index: {}", segment)
            ))
        }
    } else {
        Err(WorkflowError::RecoveryError(
            format!("Cannot update path {} in non-object/non-array", path.join("/"))
        ))
    }
}

fn chunk_events_for_parallel_replay(
    events: &[(String, u64, WorkflowEvent)]
) -> Vec<Vec<(String, u64, WorkflowEvent)>> {
    let events_count = events.len();
    
    // 确定分块策略
    let num_cpus = num_cpus::get();
    let chunk_size = (events_count / num_cpus).max(1);
    
    // 分块事件
    let mut chunks = Vec::new();
    let mut current_chunk = Vec::new();
    
    for (i, event) in events.iter().enumerate() {
        current_chunk.push(event.clone());
        
        if current_chunk.len() >= chunk_size && i < events_count - 1 {
            chunks.push(std::mem::take(&mut current_chunk));
        }
    }
    
    if !current_chunk.is_empty() {
        chunks.push(current_chunk);
    }
    
    chunks
}

fn replay_events(
    mut state: WorkflowState,
    events: &[(String, u64, WorkflowEvent)]
) -> Result<WorkflowState, WorkflowError> {
    for (_, _, event) in events {
        state = apply_event_to_state(state, event)?;
    }
    
    Ok(state)
}

fn apply_event_to_state(
    state: WorkflowState,
    event: &WorkflowEvent
) -> Result<WorkflowState, WorkflowError> {
    match (state, event) {
        // 创建状态转换
        (WorkflowState::Created { workflow_id, .. }, WorkflowEvent::WorkflowStarted { timestamp, .. }) => {
            Ok(WorkflowState::Running {
                workflow_id,
                current_stage: "initial".to_string(),
                progress: 0.0,
                started_at: *timestamp,
                last_updated: *timestamp,
            })
        },
        
        // 运行状态转换
        (
            WorkflowState::Running { workflow_id, progress, started_at, .. },
            WorkflowEvent::StageStarted { stage_id, stage_name, timestamp, .. }
        ) => {
            Ok(WorkflowState::Running {
                workflow_id,
                current_stage: stage_name.clone(),
                progress,
                started_at,
                last_updated: *timestamp,
            })
        },
        
        (
            WorkflowState::Running { workflow_id, started_at, .. },
            WorkflowEvent::StageCompleted { stage_id, timestamp, .. }
        ) => {
            // 计算新进度（基于已完成阶段）
            let new_progress = 0.5; // 这里应该基于总阶段数计算
            
            Ok(WorkflowState::Running {
                workflow_id,
                current_stage: format!("after_{}", stage_id),
                progress: new_progress,
                started_at,
                last_updated: *timestamp,
            })
        },
        
        (
            WorkflowState::Running { workflow_id, .. },
            WorkflowEvent::WorkflowCompleted { result, timestamp, .. }
        ) => {
            Ok(WorkflowState::Completed {
                workflow_id,
                result: result.clone(),
                completed_at: *timestamp,
            })
        },
        
        (
            WorkflowState::Running { workflow_id, .. },
            WorkflowEvent::WorkflowFailed { error, timestamp, .. }
        ) => {
            Ok(WorkflowState::Failed {
                workflow_id,
                error: Some(error.clone()),
                failed_at: *timestamp,
                can_retry: true, // 默认可重试
            })
        },
        
        (
            WorkflowState::Running { workflow_id, .. },
            WorkflowEvent::WorkflowCancelled { reason, timestamp, .. }
        ) => {
            Ok(WorkflowState::Cancelled {
                workflow_id,
                reason: reason.clone(),
                cancelled_at: *timestamp,
            })
        },
        
        (
            WorkflowState::Running { workflow_id, progress, started_at, .. },
            WorkflowEvent::WorkflowSuspended { reason, timestamp, .. }
        ) => {
            Ok(WorkflowState::Suspended {
                workflow_id,
                reason: reason.clone(),
                suspended_at: *timestamp,
                progress,
                started_at,
                last_updated: *timestamp,
            })
        },
        
        // 恢复状态转换
        (
            WorkflowState::Suspended { workflow_id, progress, started_at, .. },
            WorkflowEvent::WorkflowResumed { timestamp, .. }
        ) => {
            Ok(WorkflowState::Running {
                workflow_id,
                current_stage: "resumed".to_string(),
                progress,
                started_at,
                last_updated: *timestamp,
            })
        },
        
        // 其他状态转换...
        
        // 默认情况：保持状态不变
        (state, _) => Ok(state),
    }
}

fn calculate_state_hash(state: &WorkflowState) -> String {
    use sha2::{Sha256, Digest};
    
    let mut hasher = Sha256::new();
    
    if let Ok(json) = serde_json::to_string(state) {
        hasher.update(json.as_bytes());
    }
    
    format!("{:x}", hasher.finalize())
}
```

### 4.4 形式化证明

为了证明容错与恢复机制的正确性，我们提出以下形式化定理：

**定理3（故障恢复一致性）**: 对于工作流 $W$ 和事件序列 $E = \{e_1, e_2, ..., e_n\}$，若在应用事件 $e_k$ 后发生故障，则从检查点 $C$ 恢复并应用事件序列 $\{e_{j+1}, e_{j+2}, ..., e_n\}$（其中 $j$ 是检查点 $C$ 对应的最后一个事件索引）后的状态等同于无故障情况下应用完整事件序列 $E$ 后的状态。

**证明**:
设 $S_0$ 为工作流初始状态，$\delta$ 为状态转换函数。

1. 无故障情况下，最终状态为：$S_n = \delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_n)$

2. 有故障且从检查点恢复的情况，检查点状态为：$C = \delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_j)$

3. 从检查点恢复后应用剩余事件得到状态：$S'_n = \delta(\delta(...\delta(\delta(C, e_{j+1}), e_{j+2})...), e_n)$

4. 根据状态转换函数的性质：$C = \delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_j)$

5. 将4代入3：$S'_n = \delta(\delta(...\delta(\delta(\delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_j), e_{j+1}), e_{j+2})...), e_n)$

6. 由状态转换函数的组合性质：$S'_n = \delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_n) = S_n$

因此，恢复后的状态与无故障情况下的最终状态相同，故障恢复一致性得证。

**定理4（最大进度保证）**: 在故障恢复时，系统能恢复到最后一个持久化的状态点，不会丢失已确认的操作。

**证明**:
设 $E = \{e_1, e_2, ..., e_n\}$ 为完整事件序列，$P = \{e_1, e_2, ..., e_p\}$ 为已持久化的事件序列（$p \leq n$）。

1. 根据持久化定义，事件 $e_1$ 到 $e_p$ 已被安全存储。

2. 故障恢复时，系统至少能访问到事件序列 $P$。

3. 应用 $P$ 中的事件到初始状态 $S_0$，可得到状态 $S_p = \delta(\delta(...\delta(\delta(S_0, e_1), e_2)...), e_p)$。

4. 由持久化的原子性保证，要么事件 $e_i$ 完全持久化，要么完全未持久化。

5. 因此，恢复点不会包含未完全持久化的事件，确保系统恢复到最后一个完全持久化的状态。

6. 由此可知，系统至少能恢复到状态 $S_p$，不会丢失已确认的操作。

最大进度保证得证。

## 5. 优先级调度系统

### 5.1 多层优先级模型

```rust
/// 工作流优先级级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum WorkflowPriority {
    Critical = 0,  // 最高优先级
    High = 1,
    Normal = 2,    // 默认优先级
    Low = 3,
    Background = 4, // 最低优先级
}

impl Default for WorkflowPriority {
    fn default() -> Self {
        Self::Normal
    }
}

impl From<WorkflowPriority> for u8 {
    fn from(priority: WorkflowPriority) -> Self {
        priority as u8
    }
}

impl TryFrom<u8> for WorkflowPriority {
    type Error = WorkflowError;
    
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(WorkflowPriority::Critical),
            1 => Ok(WorkflowPriority::High),
            2 => Ok(WorkflowPriority::Normal),
            3 => Ok(WorkflowPriority::Low),
            4 => Ok(WorkflowPriority::Background),
            _ => Err(WorkflowError::InvalidPriority(value.to_string())),
        }
    }
}

/// 动态优先级调整器
#[async_trait]
pub trait PriorityAdjuster: Send + Sync {
    /// 计算工作流的动态优先级
    async fn calculate_priority(
        &self,
        workflow_id: &WorkflowId,
        current_priority: WorkflowPriority,
        context: &PriorityContext,
    ) -> Result<WorkflowPriority, WorkflowError>;
}

/// 优先级上下文
#[derive(Debug, Clone)]
pub struct PriorityContext {
    /// 工作流类型
    pub workflow_type: String,
    /// 工作流开始时间
    pub started_at: DateTime<Utc>,
    /// 当前等待时间
    pub wait_time: Duration,
    /// 当前运行时间
    pub execution_time: Option<Duration>,
    /// 业务重要性指标
    pub business_importance: Option<i32>,
    /// 客户服务级别
    pub customer_sla: Option<String>,
    /// 资源消耗历史
    pub resource_usage: Option<ResourceUsageHistory>,
    /// 自定义属性
    pub custom_attributes: HashMap<String, serde_json::Value>,
}

/// 资源使用历史
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUsageHistory {
    /// CPU使用率记录
    pub cpu_usage: Vec<(DateTime<Utc>, f64)>,
    /// 内存使用记录 (单位: MB)
    pub memory_usage: Vec<(DateTime<Utc>, u64)>,
    /// I/O操作记录
    pub io_operations: Vec<(DateTime<Utc>, u64)>,
}

/// 优先级存储
#[async_trait]
pub trait PriorityStore: Send + Sync {
    /// 获取工作流当前优先级
    async fn get_priority(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<WorkflowPriority, WorkflowError>;
    
    /// 设置工作流优先级
    async fn set_priority(
        &self,
        workflow_id: &WorkflowId,
        priority: WorkflowPriority,
        reason: Option<&str>,
    ) -> Result<(), WorkflowError>;
    
    /// 获取特定优先级的工作流列表
    async fn get_workflows_by_priority(
        &self,
        priority: WorkflowPriority,
        limit: usize,
        offset: usize,
    ) -> Result<Vec<WorkflowId>, WorkflowError>;
    
    /// 获取优先级变更历史
    async fn get_priority_history(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Vec<PriorityChange>, WorkflowError>;
}

/// 优先级变更记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriorityChange {
    /// 变更ID
    pub change_id: String,
    /// 工作流ID
    pub workflow_id: WorkflowId,
    /// 旧优先级
    pub old_priority: WorkflowPriority,
    /// 新优先级
    pub new_priority: WorkflowPriority,
    /// 变更原因
    pub reason: Option<String>,
    /// 变更时间
    pub timestamp: DateTime<Utc>,
    /// 变更者
    pub changed_by: String,
}
```

### 5.2 公平调度算法

```rust
/// 工作流调度器
pub struct WorkflowScheduler {
    /// 调度策略
    strategy: SchedulingStrategy,
    /// 优先级队列
    priority_queues: Vec<WorkflowQueue>,
    /// 资源管理器
    resource_manager: Arc<dyn ResourceManager>,
    /// 优先级调整器
    priority_adjuster: Arc<dyn PriorityAdjuster>,
    /// 优先级存储
    priority_store: Arc<dyn PriorityStore>,
    /// 指标收集器
    metrics: Arc<SchedulerMetrics>,
    /// 调度配置
    config: SchedulerConfig,
}

/// 调度策略
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulingStrategy {
    /// 严格优先级 - 高优先级工作流总是先执行
    StrictPriority,
    /// 加权公平 - 按优先级权重分配资源
    WeightedFair,
    /// 多级反馈队列 - 动态调整优先级
    MultilevelFeedback,
    /// 保证最小资源 - 确保低优先级也有最小执行资源
    MinimumGuaranteed,
}

/// 工作流队列
struct WorkflowQueue {
    /// 优先级级别
    priority: WorkflowPriority,
    /// 权重
    weight: u32,
    /// 待执行工作流
    pending: VecDeque<ScheduledWorkflow>,
    /// 正在执行的工作流
    running: HashMap<WorkflowId, RunningWorkflowInfo>,
    /// 队列统计信息
    stats: QueueStats,
}

/// 已调度工作流
#[derive(Debug, Clone)]
struct ScheduledWorkflow {
    /// 工作流ID
    workflow_id: WorkflowId,
    /// 工作流类型
    workflow_type: String,
    /// 调度时间
    scheduled_at: DateTime<Utc>,
    /// 等待时间
    wait_time: Duration,
    /// 优先级
    priority: WorkflowPriority,
    /// 资源需求
    resource_requirements: ResourceRequirements,
    /// 超时
    timeout: Option<Duration>,
    /// 上下文数据
    context: HashMap<String, serde_json::Value>,
}

/// 正在运行的工作流信息
#[derive(Debug, Clone)]
struct RunningWorkflowInfo {
    /// 工作流ID
    workflow_id: WorkflowId,
    /// 开始时间
    started_at: DateTime<Utc>,
    /// 当前阶段
    current_stage: String,
    /// 分配的资源
    allocated_resources: AllocatedResources,
    /// 进度
    progress: f32,
    /// 最近心跳时间
    last_heartbeat: DateTime<Utc>,
}

/// 队列统计信息
#[derive(Debug, Clone, Default)]
struct QueueStats {
    /// 总排队工作流数
    total_queued: u64,
    /// 总完成工作流数
    total_completed: u64,
    /// 平均等待时间
    avg_wait_time: Duration,
    /// 平均执行时间
    avg_execution_time: Duration,
    /// 超时工作流数
    timeouts: u64,
    /// 抢占工作流数
    preemptions: u64,
}

impl WorkflowScheduler {
    pub fn new(
        strategy: SchedulingStrategy,
        resource_manager: Arc<dyn ResourceManager>,
        priority_adjuster: Arc<dyn PriorityAdjuster>,
        priority_store: Arc<dyn PriorityStore>,
        metrics: Arc<SchedulerMetrics>,
        config: SchedulerConfig,
    ) -> Self {
        let mut priority_queues = Vec::new();
        
        // 为每个优先级级别创建队列
        priority_queues.push(WorkflowQueue {
            priority: WorkflowPriority::Critical,
            weight: 100,
            pending: VecDeque::new(),
            running: HashMap::new(),
            stats: Default::default(),
        });
        
        priority_queues.push(WorkflowQueue {
            priority: WorkflowPriority::High,
            weight: 50,
            pending: VecDeque::new(),
            running: HashMap::new(),
            stats: Default::default(),
        });
        
        priority_queues.push(WorkflowQueue {
            priority: WorkflowPriority::Normal,
            weight: 20,
            pending: VecDeque::new(),
            running: HashMap::new(),
            stats: Default::default(),
        });
        
        priority_queues.push(WorkflowQueue {
            priority: WorkflowPriority::Low,
            weight: 10,
            pending: VecDeque::new(),
            running: HashMap::new(),
            stats: Default::default(),
        });
        
        priority_queues.push(WorkflowQueue {
            priority: WorkflowPriority::Background,
            weight: 5,
            pending: VecDeque::new(),
            running: HashMap::new(),
            stats: Default::default(),
        });
        
        Self {
            strategy,
            priority_queues,
            resource_manager,
            priority_adjuster,
            priority_store,
            metrics,
            config,
        }
    }
    
    /// 调度工作流
    pub async fn schedule(
        &mut self, 
        workflow_id: &WorkflowId,
        workflow_type: &str,
        priority: WorkflowPriority,
        resource_requirements: ResourceRequirements,
        timeout: Option<Duration>,
        context: HashMap<String, serde_json::Value>,
    ) -> Result<(), WorkflowError> {
        // 创建调度工作流对象
        let scheduled_workflow = ScheduledWorkflow {
            workflow_id: workflow_id.clone(),
            workflow_type: workflow_type.to_string(),
            scheduled_at: Utc::now(),
            wait_time: Duration::from_secs(0),
            priority,
            resource_requirements,
            timeout,
            context,
        };
        
        // 找到对应优先级队列
        let queue_index = self.find_queue_for_priority(priority);
        
        // 将工作流添加到队列
        self.priority_queues[queue_index].pending.push_back(scheduled_workflow);
        self.priority_queues[queue_index].stats.total_queued += 1;
        
        // 更新指标
        self.metrics.workflow_scheduled(workflow_id, priority);
        
        // 记录优先级信息
        self.priority_store.set_priority(
            workflow_id,
            priority,
            Some("Initial scheduling")
        ).await?;
        
        // 如果配置为立即调度，则尝试执行队列
        if self.config.schedule_immediately {
            self.execute_next_workflows().await?;
        }
        
        Ok(())
    }
    
    /// 执行队列中的下一批工作流
    pub async fn execute_next_workflows(&mut self) -> Result<usize, WorkflowError> {
        // 获取当前可用资源
        let available_resources = self.resource_manager.get_available_resources().await?;
        
        // 根据调度策略选择要执行的工作流
        let workflows_to_execute = match self.strategy {
            SchedulingStrategy::StrictPriority => {
                self.select_workflows_strict_priority(&available_resources)
            },
            SchedulingStrategy::WeightedFair => {
                self.select_workflows_weighted_fair(&available_resources)
            },
            SchedulingStrategy::MultilevelFeedback => {
                self.select_workflows_multilevel_feedback(&available_resources)
            },
            SchedulingStrategy::MinimumGuaranteed => {
                self.select_workflows_minimum_guaranteed(&available_resources)
            },
        };
        
        let mut executed_count = 0;
        
        // 执行选定的工作流
        for (queue_index, workflow_index) in workflows_to_execute {
            let queue = &mut self.priority_queues[queue_index];
            
            // 从队列取出工作流
            if let Some(workflow) = queue.pending.remove(workflow_index) {
                // 计算等待时间
                let wait_time = Utc::now() - workflow.scheduled_at;
                
                // 尝试分配资源
                match self.resource_manager.allocate_resources(
                    &workflow.workflow_id,
                    &workflow.resource_requirements
                ).await {
                    Ok(allocated) => {
                        let now = Utc::now();
                        
                        // 创建运行信息
                        let running_info = RunningWorkflowInfo {
                            workflow_id: workflow.workflow_id.clone(),
                            started_at: now,
                            current_stage: "starting".to_string(),
                            allocated_resources: allocated,
                            progress: 0.0,
                            last_heartbeat: now,
                        };
                        
                        // 添加到运行中工作流
                        queue.running.insert(workflow.workflow_id.clone(), running_info);
                        
                        // 更新指标
                        self.metrics.workflow_started(
                            &workflow.workflow_id,
                            workflow.priority,
                            wait_time
                        );
                        
                        // 更新队列统计
                        if let Some(avg) = update_avg_duration(
                            queue.stats.avg_wait_time,
                            wait_time,
                            queue.stats.total_completed
                        ) {
                            queue.stats.avg_wait_time = avg;
                        }
                        
                        executed_count += 1;
                    },
                    Err(e) => {
                        // 资源分配失败，放回队列
                        queue.pending.push_front(workflow);
                        
                        log::warn!(
                            "Failed to allocate resources for workflow {}: {}",
                            workflow.workflow_id,
                            e
                        );
                        
                        // 更新指标
                        self.metrics.resource_allocation_failed(&workflow.workflow_id);
                    }
                }
            }
        }
        
        Ok(executed_count)
    }
    
    /// 严格优先级策略：高优先级队列总是先执行
    fn select_workflows_strict_priority(&self, available_resources: &ResourceStats) -> Vec<(usize, usize)> {
        let mut result = Vec::new();
        
        // 跟踪已分配资源
        let mut remaining_resources = available_resources.clone();
        
        // 按优先级顺序处理队列
        for (queue_index, queue) in self.priority_queues.iter().enumerate() {
            // 尝试从队列中选择工作流
            for (workflow_index, workflow) in queue.pending.iter().enumerate() {
                // 检查是否有足够资源
                if can_allocate_resources(&remaining_resources, &workflow.resource_requirements) {
                    // 预留资源
                    reserve_resources(&mut remaining_resources, &workflow.resource_requirements);
                    
                    // 添加到结果
                    result.push((queue_index, workflow_index));
                    
                    // 如果资源不足，跳出
                    if !has_min_resources(&remaining_resources) {
                        return result;
                    }
                }
            }
        }
        
        result
    }
    
    /// 加权公平策略：按队列权重分配执行机会
    fn select_workflows_weighted_fair(&self, available_resources: &ResourceStats) -> Vec<(usize, usize)> {
        let mut result = Vec::new();
        
        // 计算总权重
        let total_weight: u32 = self.priority_queues.iter().map(|q| q.weight).sum();
        
        // 跟踪已分配资源
        let mut remaining_resources = available_resources.clone();
        
        // 为每个队列计算配额
        let mut quotas: Vec<u32> = self.priority_queues.iter()
            .map(|q| (q.weight as f64 / total_weight as f64 * 100.0).ceil() as u32)
            .collect();
        
        // 循环直到无法分配更多工作流或资源耗尽
        while has_min_resources(&remaining_resources) {
            let mut allocated_in_round = false;
            
            // 遍历所有队列，尝试分配工作流
            for queue_index in 0..self.priority_queues.len() {
                if quotas[queue_index] > 0 {
                    // 从队列选择一个工作流
                    if let Some(workflow_index) = self.find_allocatable_workflow(
                        queue_index,
                        &remaining_resources
                    ) {
                        // 获取工作流
                        let workflow = &self.priority_queues[queue_index].pending[workflow_index];
                        
                        // 预留资源
                        reserve_resources(&mut remaining_resources, &workflow.resource_requirements);
                        
                        // 添加到结果
                        result.push((queue_index, workflow_index));
                        
                        // 减少配额
                        quotas[queue_index] -= 1;
                        
                        allocated_in_round = true;
                        
                        // 如果资源不足，跳出
                        if !has_min_resources(&remaining_resources) {
                            return result;
                        }
                    }
                }
            }
            
            // 如果本轮没有分配任何工作流，退出循环
            if !allocated_in_round {
                break;
            }
        }
        
        result
    }
    
    /// 多级反馈队列策略：考虑执行时间的动态调度
    fn select_workflows_multilevel_feedback(&self, available_resources: &ResourceStats) -> Vec<(usize, usize)> {
        let mut result = Vec::new();
        
        // 跟踪已分配资源
        let mut remaining_resources = available_resources.clone();
        
        // 按优先级处理队列，但优先考虑短任务
        for queue_index in 0..self.priority_queues.len() {
            // 从队列中选择预计执行时间短的工作流
            let mut workflows: Vec<(usize, &ScheduledWorkflow)> = self.priority_queues[queue_index]
                .pending
                .iter()
                .enumerate()
                .collect();
            
            // 按预计执行时间排序
            workflows.sort_by(|a, b| {
                let a_time = estimate_execution_time(&a.1.workflow_type, &a.1.context);
                let b_time = estimate_execution_time(&b.1.workflow_type, &b.1.context);
                a_time.cmp(&b_time)
            });
            
            // 尝试分配短任务
            for (workflow_index, workflow) in workflows {
                // 检查是否有足够资源
                if can_allocate_resources(&remaining_resources, &workflow.resource_requirements) {
                    // 预留资源
                    reserve_resources(&mut remaining_resources, &workflow.resource_requirements);
                    
                    // 添加到结果
                    result.push((queue_index, workflow_index));
                    
                    // 如果资源不足，跳出
                    if !has_min_resources(&remaining_resources) {
                        return result;
                    }
                }
            }
        }
        
        result
    }
    
    /// 保证最小资源策略：确保低优先级队列也有最小执行机会
    fn select_workflows_minimum_guaranteed(&self, available_resources: &ResourceStats) -> Vec<(usize, usize)> {
        let mut result = Vec::new();
        
        // 跟踪已分配资源
        let mut remaining_resources = available_resources.clone();
        
        // 为每个队列设置最小保证资源比例
        let min_guarantees = [0.5, 0.3, 0.15, 0.04, 0.01];
        
        // 第一轮：为每个队列分配最小保证资源
        for (queue_index, min_guarantee) in min_guarantees.iter().enumerate() {
            // 计算该队列可用的最小资源数量
            let min_resources = ResourceStats {
                cpu_units: (available_resources.cpu_units as f64 * min_guarantee) as u32,
                memory_mb: (available_resources.memory_mb as f64 * min_guarantee) as u64,
                // 其他资源类似计算...
                ..Default::default()
            };
            
            // 从队列中选择工作流直到达到保证值
            let mut allocated_for_queue = ResourceStats::default();
            
            for workflow_index in 0..self.priority_queues[queue_index].pending.len() {
                let workflow = &self.priority_queues[queue_index].pending[workflow_index];
                
                // 检查是否超过该队列的最小保证
                if !exceeds_resource_limit(&allocated_for_queue, &min_resources) {
                    // 检查是否有足够的剩余资源
                    if can_allocate_resources(&remaining_resources, &workflow.resource_requirements) {
                        // 预留资源
                        reserve_resources(&mut remaining_resources, &workflow.resource_requirements);
                        add_resources(&mut allocated_for_queue, &workflow.resource_requirements);
                        
                        // 添加到结果
                        result.push((queue_index, workflow_index));
                        
                        // 如果总体资源不足，跳出
                        if !has_min_resources(&remaining_resources) {
                            return result;
                        }
                    }
                } else {
                    // 已达到该队列的最小保证，转到下一个队列
                    break;
                }
            }
        }
        
        // 第二轮：分配剩余资源，从高优先级开始
        if has_min_resources(&remaining_resources) {
            let strict_priority_selections = self.select_workflows_strict_priority(&remaining_resources);
            result.extend(strict_priority_selections);
        }
        
        result
    }
    
    /// 查找可分配资源的工作流
    fn find_allocatable_workflow(
        &self,
        queue_index: usize,
        available_resources: &ResourceStats
    ) -> Option<usize> {
        let queue = &self.priority_queues[queue_index];
        
        for (index, workflow) in queue.pending.iter().enumerate() {
            if can_allocate_resources(available_resources, &workflow.resource_requirements) {
                return Some(index);
            }
        }
        
        None
    }
    
    /// 查找对应优先级的队列索引
    fn find_queue_for_priority(&self, priority: WorkflowPriority) -> usize {
        self.priority_queues
            .iter()
            .position(|q| q.priority == priority)
            .unwrap_or(2) // 默认为Normal优先级
    }
    
    /// 完成工作流执行
    pub async fn complete_workflow(
        &mut self,
        workflow_id: &WorkflowId,
        result: Option<serde_json::Value>,
    ) -> Result<(), WorkflowError> {
        // 查找工作流所在队列
        for queue in &mut self.priority_queues {
            if let Some(running_info) = queue.running.remove(workflow_id) {
                // 计算执行时间
                let execution_time = Utc::now() - running_info.started_at;
                
                // 释放资源
                self.resource_manager.release_resources(
                    workflow_id,
                    &running_info.allocated_resources
                ).await?;
                
                // 更新队列统计
                queue.stats.total_completed += 1;
                
                if let Some(avg) = update_avg_duration(
                    queue.stats.avg_execution_time,
                    execution_time,
                    queue.stats.total_completed
                ) {
                    queue.stats.avg_execution_time = avg;
                }
                
                // 更新指标
                self.metrics.workflow_completed(workflow_id, execution_time);
                
                return Ok(());
            }
        }
        
        // 工作流未找到
        Err(WorkflowError::WorkflowNotFound(workflow_id.to_string()))
    }
    
    /// 调整工作流优先级
    pub async fn adjust_workflow_priority(
        &mut self,
        workflow_id: &WorkflowId,
        new_priority: WorkflowPriority,
        reason: &str,
    ) -> Result<(), WorkflowError> {
        let old_priority = self.priority_store.get_priority(workflow_id).await?;
        
        if old_priority == new_priority {
            return Ok(());
        }
        
        // 对于运行中的工作流，标记优先级变更但不中断
        let mut found_running = false;
        
        for queue in &mut self.priority_queues {
            if queue.running.contains_key(workflow_id) {
                // 只更新优先级记录，不中断运行
                found_running = true;
                break;
            }
        }
        
        if !found_running {
            // 查找待处理工作流
            let old_queue_index = self.find_queue_for_priority(old_priority);
            let queue = &mut self.priority_queues[old_queue_index];
            
            let workflow_index = queue.pending.iter().position(|w| w.workflow_id == *workflow_id);
            
            if let Some(index) = workflow_index {
                // 移除工作流
                let mut workflow = queue.pending.remove(index).unwrap();
                
                // 更新优先级
                workflow.priority = new_priority;
                
                // 添加到新队列
                let new_queue_index = self.find_queue_for_priority(new_priority);
                self.priority_queues[new_queue_index].pending.push_back(workflow);
            }
        }
        
        // 更新优先级存储
        self.priority_store.set_priority(workflow_id, new_priority, Some(reason)).await?;
        
        // 记录优先级变更事件
        let event = WorkflowEvent::WorkflowPriorityChanged {
            workflow_id: workflow_id.clone(),
            old_priority,
            new_priority,
            reason: reason.to_string(),
            timestamp: Utc::now(),
        };
        
        // 更新指标
        self.metrics.priority_changed(workflow_id, old_priority, new_priority);
        
        Ok(())
    }
    
    /// 动态调整所有工作流优先级
    pub async fn adjust_all_priorities(&mut self) -> Result<usize, WorkflowError> {
        let mut adjusted_count = 0;
        
        // 收集所有待处理工作流
        let mut all_pending = Vec::new();
        
        for (queue_index, queue) in self.priority_queues.iter().enumerate() {
            for workflow in &queue.pending {
                all_pending.push((queue_index, workflow.clone()));
            }
        }
        
        // 逐个评估并调整优先级
        for (queue_index, workflow) in all_pending {
            // 构建优先级上下文
            let context = PriorityContext {
                workflow_type: workflow.workflow_type.clone(),
                started_at: workflow.scheduled_at,
                wait_time: Utc::now() - workflow.scheduled_at,
                execution_time: None,
                business_importance: workflow.context.get("business_importance")
                    .and_then(|v| v.as_i64().map(|i| i as i32)),
                customer_sla: workflow.context.get("customer_sla")
                    .and_then(|v| v.as_str().map(|s| s.to_string())),
                resource_usage: None,
                custom_attributes: workflow.context.clone(),
            };
            
            // 计算新优先级
            let new_priority = self.priority_adjuster.calculate_priority(
                &workflow.workflow_id,
                workflow.priority,
                &context
            ).await?;
            
            // 如果优先级变化，进行调整
            if new_priority != workflow.priority {
                self.adjust_workflow_priority(
                    &workflow.workflow_id,
                    new_priority,
                    "Dynamic priority adjustment"
                ).await?;
                
                adjusted_count += 1;
            }
        }
        
        Ok(adjusted_count)
    }
}

// 辅助函数
fn can_allocate_resources(
    available: &ResourceStats,
    required: &ResourceRequirements
) -> bool {
    available.cpu_units >= required.min_cpu_units &&
    available.memory_mb >= required.min_memory_mb
    // 检查其他资源限制...
}

fn reserve_resources(
    available: &mut ResourceStats,
    required: &ResourceRequirements
) {
    available.cpu_units -= required.min_cpu_units;
    available.memory_mb -= required.min_memory_mb;
    // 预留其他资源...
}

fn has_min_resources(resources: &ResourceStats) -> bool {
    resources.cpu_units > 0 && resources.memory_mb > 0
    // 检查其他最小资源要求...
}

fn estimate_execution_time(
    workflow_type: &str,
    context: &HashMap<String, serde_json::Value>
) -> Duration {
    // 基于历史数据或启发式方法估计执行时间
    match workflow_type {
        "data_processing" => Duration::from_secs(60),
        "image_processing" => Duration::from_secs(120),
        "order_fulfillment" => Duration::from_secs(30),
        _ => Duration::from_secs(45), // 默认估计
    }
}

fn update_avg_duration(
    current_avg: Duration,
    new_value: Duration,
    total_count: u64
) -> Option<Duration> {
    if total_count == 0 {
        return Some(new_value);
    }
    
    let avg_millis = current_avg.as_millis() as u64;
    let new_millis = new_value.as_millis() as u64;
    
    let updated_avg = avg_millis + (new_millis - avg_millis) / (total_count + 1);
    
    Some(Duration::from_millis(updated_avg))
}

fn add_resources(
    target: &mut ResourceStats,
    requirements: &ResourceRequirements
) {
    target.cpu_units += requirements.min_cpu_units;
    target.memory_mb += requirements.min_memory_mb;
    // 添加其他资源...
}

fn exceeds_resource_limit(
    current: &ResourceStats,
    limit: &ResourceStats
) -> bool {
    current.cpu_units > limit.cpu_units || 
    current.memory_mb > limit.memory_mb
    // 检查其他资源限制...
}
```

### 5.3 资源限制与隔离

通过资源限制和隔离机制，我们可以防止单个工作流消耗过多系统资源：

```rust
/// 资源管理器
#[async_trait]
pub trait ResourceManager: Send + Sync {
    /// 获取可用资源统计
    async fn get_available_resources(&self) -> Result<ResourceStats, WorkflowError>;
    
    /// 为工作流分配资源
    async fn allocate_resources(
        &self,
        workflow_id: &WorkflowId,
        requirements: &ResourceRequirements,
    ) -> Result<AllocatedResources, WorkflowError>;
    
    /// 释放工作流资源
    async fn release_resources(
        &self,
        workflow_id: &WorkflowId,
        resources: &AllocatedResources,
    ) -> Result<(), WorkflowError>;
    
    /// 获取工作流当前资源使用情况
    async fn get_workflow_resource_usage(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<ResourceUsage>, WorkflowError>;
    
    /// 设置资源配额
    async fn set_resource_quota(
        &self,
        quota_key: &str,
        quota: ResourceQuota,
    ) -> Result<(), WorkflowError>;
    
    /// 获取资源配额
    async fn get_resource_quota(
        &self,
        quota_key: &str,
    ) -> Result<Option<ResourceQuota>, WorkflowError>;
}

/// 资源统计
#[derive(Debug, Clone, Default)]
pub struct ResourceStats {
    /// CPU单元(例如vCPU核心数×100)
    pub cpu_units: u32,
    /// 内存(MB)
    pub memory_mb: u64,
    /// 磁盘空间(MB)
    pub disk_mb: u64,
    /// 网络带宽(Mbps)
    pub network_mbps: u32,
    /// I/O操作数/秒
    pub iops: u32,
}

/// 资源需求
#[derive(Debug, Clone)]
pub struct ResourceRequirements {
    /// 最小CPU单元
    pub min_cpu_units: u32,
    /// 最小内存(MB)
    pub min_memory_mb: u64,
    /// 最小磁盘空间(MB)
    pub min_disk_mb: u64,
    /// 最小网络带宽(Mbps)
    pub min_network_mbps: u32,
    /// 最小I/O操作数/秒
    pub min_iops: u32,
    /// CPU突发限制
    pub cpu_burst_limit: Option<u32>,
    /// 内存突发限制
    pub memory_burst_limit: Option<u64>,
}

/// 已分配的资源
#[derive(Debug, Clone)]
pub struct AllocatedResources {
    /// 分配的CPU单元
    pub cpu_units: u32,
    /// 分配的内存(MB)
    pub memory_mb: u64,
    /// 分配的磁盘空间(MB)
    pub disk_mb: u64,
    /// 分配的网络带宽(Mbps)
    pub network_mbps: u32,
    /// 分配的I/O操作数/秒
    pub iops: u32,
    /// 资源分配ID
    pub allocation_id: String,
    /// 分配时间
    pub allocated_at: DateTime<Utc>,
    /// 资源限制器配置
    pub limiter_config: Option<ResourceLimiterConfig>,
}

/// 资源使用情况
#[derive(Debug, Clone)]
pub struct ResourceUsage {
    /// 工作流ID
    pub workflow_id: WorkflowId,
    /// CPU使用率(百分比)
    pub cpu_percentage: f64,
    /// 内存使用量(MB)
    pub memory_used_mb: u64,
    /// 磁盘使用量(MB)
    pub disk_used_mb: u64,
    /// 网络使用量(Mbps)
    pub network_used_mbps: f64,
    /// I/O操作数/秒
    pub iops_used: u32,
    /// 开始时间
    pub start_time: DateTime<Utc>,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
    /// 历史使用数据
    pub history: Vec<ResourceUsagePoint>,
}

/// 资源使用点
#[derive(Debug, Clone)]
pub struct ResourceUsagePoint {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// CPU使用率
    pub cpu_percentage: f64,
    /// 内存使用量
    pub memory_used_mb: u64,
    /// 其他资源使用量...
}

/// 资源配额
#[derive(Debug, Clone)]
pub struct ResourceQuota {
    /// 配额ID
    pub quota_id: String,
    /// 配额键(例如租户ID、工作流类型)
    pub quota_key: String,
    /// 最大CPU单元
    pub max_cpu_units: u32,
    /// 最大内存(MB)
    pub max_memory_mb: u64,
    /// 最大磁盘空间(MB)
    pub max_disk_mb: u64,
    /// 最大网络带宽(Mbps)
    pub max_network_mbps: u32,
    /// 最大I/O操作数/秒
    pub max_iops: u32,
    /// 最大并发工作流数
    pub max_concurrent_workflows: u32,
    /// 超额使用策略
    pub over_usage_policy: OverUsagePolicy,
}

/// 超额使用策略
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OverUsagePolicy {
    /// 拒绝新的资源请求
    Reject,
    /// 允许有限突发
    AllowBurst {
        /// 突发因子(相对于基准配额)
        burst_factor: f64,
        /// 最大突发时间
        max_burst_time: Duration,
    },
    /// 节流超额使用
    Throttle,
    /// 自动扩展配额
    AutoScale {
        /// 最大扩展因子
        max_scale_factor: f64,
        /// 冷却期
        cooldown_period: Duration,
    },
}

/// 资源限制器配置
#[derive(Debug, Clone)]
pub struct ResourceLimiterConfig {
    /// CPU限制策略
    pub cpu_limit: LimitStrategy,
    /// 内存限制策略
    pub memory_limit: LimitStrategy,
    /// 磁盘限制策略
    pub disk_limit: LimitStrategy,
    /// 网络限制策略
    pub network_limit: LimitStrategy,
    /// I/O限制策略
    pub io_limit: LimitStrategy,
}

/// 限制策略
#[derive(Debug, Clone, PartialEq)]
pub enum LimitStrategy {
    /// 无限制
    Unlimited,
    /// 固定限制
    Fixed {
        /// 限制值
        limit: u64,
        /// 单位
        unit: String,
    },
    /// 动态限制
    Dynamic {
        /// 基础限制
        base_limit: u64,
        /// 单位
        unit: String,
        /// 调整因子
        adjustment_factor: f64,
    },
    /// 阶梯限制
    Tiered {
        /// 阶梯
        tiers: Vec<ResourceTier>,
    },
}

/// 资源阶梯
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceTier {
    /// 用量阈值
    pub threshold: u64,
    /// 限制值
    pub limit: u64,
    /// 单位
    pub unit: String,
}

/// 资源管理器实现
pub struct DefaultResourceManager {
    /// 总资源容量
    total_capacity: ResourceStats,
    /// 已分配资源
    allocated_resources: RwLock<HashMap<WorkflowId, AllocatedResources>>,
    /// 资源使用追踪
    resource_usage: RwLock<HashMap<WorkflowId, ResourceUsage>>,
    /// 资源配额
    resource_quotas: RwLock<HashMap<String, ResourceQuota>>,
    /// 资源监控器
    resource_monitor: Arc<dyn ResourceMonitor>,
    /// 资源使用数据库
    usage_store: Arc<dyn ResourceUsageStore>,
    /// 锁管理器
    lock_manager: Arc<AsyncMutex<()>>,
    /// 配置
    config: ResourceManagerConfig,
}

#[async_trait]
impl ResourceManager for DefaultResourceManager {
    async fn get_available_resources(&self) -> Result<ResourceStats, WorkflowError> {
        // 获取所有已分配资源的锁
        let allocated = self.allocated_resources.read().await;
        
        // 计算已分配的总资源
        let mut used = ResourceStats::default();
        
        for (_, resources) in allocated.iter() {
            used.cpu_units += resources.cpu_units;
            used.memory_mb += resources.memory_mb;
            used.disk_mb += resources.disk_mb;
            used.network_mbps += resources.network_mbps;
            used.iops += resources.iops;
        }
        
        // 计算可用资源
        let available = ResourceStats {
            cpu_units: self.total_capacity.cpu_units.saturating_sub(used.cpu_units),
            memory_mb: self.total_capacity.memory_mb.saturating_sub(used.memory_mb),
            disk_mb: self.total_capacity.disk_mb.saturating_sub(used.disk_mb),
            network_mbps: self.total_capacity.network_mbps.saturating_sub(used.network_mbps),
            iops: self.total_capacity.iops.saturating_sub(used.iops),
        };
        
        Ok(available)
    }
    
    async fn allocate_resources(
        &self,
        workflow_id: &WorkflowId,
        requirements: &ResourceRequirements,
    ) -> Result<AllocatedResources, WorkflowError> {
        // 获取资源分配锁，确保原子性
        let _lock = self.lock_manager.lock().await;
        
        // 检查当前可用资源
        let available = self.get_available_resources().await?;
        
        // 验证资源请求
        if !can_allocate_resources(&available, requirements) {
            return Err(WorkflowError::ResourceExhausted(format!(
                "Insufficient resources for workflow {}. Required: {:?}, Available: {:?}",
                workflow_id, requirements, available
            )));
        }
        
        // 检查配额限制
        let quota_key = self.get_quota_key(workflow_id).await?;
        
        if let Some(quota_key) = quota_key {
            let quotas = self.resource_quotas.read().await;
            
            if let Some(quota) = quotas.get(&quota_key) {
                // 检查是否超过配额
                let current_usage = self.get_quota_usage(&quota_key).await?;
                
                if !can_allocate_within_quota(&current_usage, requirements, quota) {
                    match quota.over_usage_policy {
                        OverUsagePolicy::Reject => {
                            return Err(WorkflowError::QuotaExceeded(format!(
                                "Quota exceeded for key {}. Current usage: {:?}, Quota: {:?}",
                                quota_key, current_usage, quota
                            )));
                        },
                        OverUsagePolicy::AllowBurst { burst_factor, max_burst_time } => {
                            // 检查是否在突发限制内
                            if !can_burst_within_limits(&current_usage, requirements, quota, burst_factor) {
                                return Err(WorkflowError::QuotaExceeded(format!(
                                    "Burst quota exceeded for key {}",
                                    quota_key
                                )));
                            }
                            
                            // 记录突发使用
                            self.record_burst_usage(&quota_key, workflow_id).await?;
                        },
                        OverUsagePolicy::Throttle => {
                            // 应用节流策略
                            // 注意：实际实现可能需要复杂的节流逻辑
                            tokio::time::sleep(Duration::from_millis(500)).await;
                        },
                        OverUsagePolicy::AutoScale { max_scale_factor, cooldown_period } => {
                            // 自动调整配额
                            self.auto_scale_quota(&quota_key, max_scale_factor, cooldown_period).await?;
                        }
                    }
                }
            }
        }
        
        // 创建资源分配
        let allocation = AllocatedResources {
            cpu_units: requirements.min_cpu_units,
            memory_mb: requirements.min_memory_mb,
            disk_mb: requirements.min_disk_mb,
            network_mbps: requirements.min_network_mbps,
            iops: requirements.min_iops,
            allocation_id: Uuid::new_v4().to_string(),
            allocated_at: Utc::now(),
            limiter_config: Some(self.create_limiter_config(requirements)),
        };
        
        // 记录资源分配
        let mut allocated = self.allocated_resources.write().await;
        allocated.insert(workflow_id.clone(), allocation.clone());
        
        // 初始化资源使用追踪
        let mut usage = self.resource_usage.write().await;
        let now = Utc::now();
        
        usage.insert(workflow_id.clone(), ResourceUsage {
            workflow_id: workflow_id.clone(),
            cpu_percentage: 0.0,
            memory_used_mb: 0,
            disk_used_mb: 0,
            network_used_mbps: 0.0,
            iops_used: 0,
            start_time: now,
            last_updated: now,
            history: Vec::new(),
        });
        
        // 启动资源监控
        self.resource_monitor.start_monitoring(workflow_id, &allocation).await?;
        
        // 记录分配事件
        self.usage_store.record_allocation(workflow_id, &allocation).await?;
        
        Ok(allocation)
    }
    
    async fn release_resources(
        &self,
        workflow_id: &WorkflowId,
        resources: &AllocatedResources,
    ) -> Result<(), WorkflowError> {
        // 获取资源分配锁
        let _lock = self.lock_manager.lock().await;
        
        // 停止资源监控
        self.resource_monitor.stop_monitoring(workflow_id).await?;
        
        // 移除资源分配
        let mut allocated = self.allocated_resources.write().await;
        allocated.remove(workflow_id);
        
        // 最后一次记录使用情况
        if let Some(usage) = self.resource_usage.read().await.get(workflow_id) {
            self.usage_store.record_usage(workflow_id, usage).await?;
        }
        
        // 移除使用追踪
        let mut usage = self.resource_usage.write().await;
        usage.remove(workflow_id);
        
        // 记录释放事件
        self.usage_store.record_release(workflow_id, resources).await?;
        
        Ok(())
    }
    
    async fn get_workflow_resource_usage(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<ResourceUsage>, WorkflowError> {
        // 获取当前使用情况
        let usage = self.resource_usage.read().await;
        let current = usage.get(workflow_id).cloned();
        
        if current.is_some() {
            return Ok(current);
        }
        
        // 如果内存中没有，尝试从存储获取
        self.usage_store.get_last_usage(workflow_id).await
    }
    
    async fn set_resource_quota(
        &self,
        quota_key: &str,
        quota: ResourceQuota,
    ) -> Result<(), WorkflowError> {
        // 更新配额
        let mut quotas = self.resource_quotas.write().await;
        quotas.insert(quota_key.to_string(), quota.clone());
        
        // 记录配额更新
        self.usage_store.record_quota_update(quota_key, &quota).await?;
        
        Ok(())
    }
    
    async fn get_resource_quota(
        &self,
        quota_key: &str,
    ) -> Result<Option<ResourceQuota>, WorkflowError> {
        // 获取配额
        let quotas = self.resource_quotas.read().await;
        let quota = quotas.get(quota_key).cloned();
        
        Ok(quota)
    }
    
    // 辅助方法
    async fn get_quota_key(&self, workflow_id: &WorkflowId) -> Result<Option<String>, WorkflowError> {
        // 根据策略确定配额键
        // 例如，可以基于租户ID、工作流类型等
        // 此处简化，直接使用工作流类型
        
        // 获取工作流类型
        let metadata = self.usage_store.get_workflow_metadata(workflow_id).await?;
        
        if let Some(metadata) = metadata {
            if let Some(workflow_type) = metadata.get("workflow_type") {
                if let Some(type_str) = workflow_type.as_str() {
                    return Ok(Some(format!("type:{}", type_str)));
                }
            }
            
            if let Some(tenant_id) = metadata.get("tenant_id") {
                if let Some(tenant_str) = tenant_id.as_str() {
                    return Ok(Some(format!("tenant:{}", tenant_str)));
                }
            }
        }
        
        // 没有找到配额键
        Ok(None)
    }
    
    async fn get_quota_usage(&self, quota_key: &str) -> Result<ResourceStats, WorkflowError> {
        // 获取指定配额键下的所有工作流资源使用
        let allocated = self.allocated_resources.read().await;
        let workflows = self.usage_store.get_workflows_by_quota_key(quota_key).await?;
        
        // 计算总使用量
        let mut usage = ResourceStats::default();
        
        for workflow_id in workflows {
            if let Some(resources) = allocated.get(&workflow_id) {
                usage.cpu_units += resources.cpu_units;
                usage.memory_mb += resources.memory_mb;
                usage.disk_mb += resources.disk_mb;
                usage.network_mbps += resources.network_mbps;
                usage.iops += resources.iops;
            }
        }
        
        Ok(usage)
    }
    
    fn create_limiter_config(&self, requirements: &ResourceRequirements) -> ResourceLimiterConfig {
        ResourceLimiterConfig {
            cpu_limit: if let Some(burst) = requirements.cpu_burst_limit {
                LimitStrategy::Tiered {
                    tiers: vec![
                        ResourceTier {
                            threshold: 0,
                            limit: requirements.min_cpu_units as u64,
                            unit: "units".to_string(),
                        },
                        ResourceTier {
                            threshold: 80, // 80% 使用率
                            limit: burst as u64,
                            unit: "units".to_string(),
                        }
                    ],
                }
            } else {
                LimitStrategy::Fixed {
                    limit: requirements.min_cpu_units as u64,
                    unit: "units".to_string(),
                }
            },
            
            memory_limit: if let Some(burst) = requirements.memory_burst_limit {
                LimitStrategy::Tiered {
                    tiers: vec![
                        ResourceTier {
                            threshold: 0,
                            limit: requirements.min_memory_mb,
                            unit: "MB".to_string(),
                        },
                        ResourceTier {
                            threshold: 90, // 90% 使用率
                            limit: burst,
                            unit: "MB".to_string(),
                        }
                    ],
                }
            } else {
                LimitStrategy::Fixed {
                    limit: requirements.min_memory_mb,
                    unit: "MB".to_string(),
                }
            },
            
            // 其他资源限制配置...
            disk_limit: LimitStrategy::Fixed {
                limit: requirements.min_disk_mb,
                unit: "MB".to_string(),
            },
            
            network_limit: LimitStrategy::Dynamic {
                base_limit: requirements.min_network_mbps as u64,
                unit: "Mbps".to_string(),
                adjustment_factor: 1.2, // 允许20%的动态调整
            },
            
            io_limit: LimitStrategy::Fixed {
                limit: requirements.min_iops as u64,
                unit: "ops".to_string(),
            },
        }
    }
    
    async fn record_burst_usage(&self, quota_key: &str, workflow_id: &WorkflowId) -> Result<(), WorkflowError> {
        // 记录突发使用情况
        self.usage_store.record_burst_usage(quota_key, workflow_id, Utc::now()).await?;
        
        Ok(())
    }
    
    async fn auto_scale_quota(
        &self, 
        quota_key: &str,
        max_scale_factor: f64,
        cooldown_period: Duration
    ) -> Result<(), WorkflowError> {
        // 获取当前配额
        let quotas = self.resource_quotas.read().await;
        let current_quota = match quotas.get(quota_key) {
            Some(q) => q.clone(),
            None => return Err(WorkflowError::QuotaNotFound(quota_key.to_string())),
        };
        drop(quotas);
        
        // 检查最后一次扩展时间
        let last_scale = self.usage_store.get_last_quota_scale(quota_key).await?;
        
        if let Some(last_time) = last_scale {
            let elapsed = Utc::now() - last_time;
            
            if elapsed < cooldown_period {
                // 仍在冷却期内，不扩展
                return Ok(());
            }
        }
        
        // 计算新配额
        let new_quota = ResourceQuota {
            max_cpu_units: (current_quota.max_cpu_units as f64 * 1.2).min(
                current_quota.max_cpu_units as f64 * max_scale_factor
            ) as u32,
            max_memory_mb: (current_quota.max_memory_mb as f64 * 1.2).min(
                current_quota.max_memory_mb as f64 * max_scale_factor
            ) as u64,
            max_disk_mb: (current_quota.max_disk_mb as f64 * 1.2).min(
                current_quota.max_disk_mb as f64 * max_scale_factor
            ) as u64,
            max_network_mbps: (current_quota.max_network_mbps as f64 * 1.2).min(
                current_quota.max_network_mbps as f64 * max_scale_factor
            ) as u32,
            max_iops: (current_quota.max_iops as f64 * 1.2).min(
                current_quota.max_iops as f64 * max_scale_factor
            ) as u32,
            max_concurrent_workflows: (current_quota.max_concurrent_workflows as f64 * 1.1).min(
                current_quota.max_concurrent_workflows as f64 * max_scale_factor
            ) as u32,
            ..current_quota
        };
        
        // 更新配额
        self.set_resource_quota(quota_key, new_quota).await?;
        
        // 记录扩展事件
        self.usage_store.record_quota_scale(quota_key, Utc::now()).await?;
        
        Ok(())
    }
}

// 辅助函数
fn can_allocate_resources(
    available: &ResourceStats,
    required: &ResourceRequirements
) -> bool {
    available.cpu_units >= required.min_cpu_units &&
    available.memory_mb >= required.min_memory_mb &&
    available.disk_mb >= required.min_disk_mb &&
    available.network_mbps >= required.min_network_mbps &&
    available.iops >= required.min_iops
}

fn can_allocate_within_quota(
    current_usage: &ResourceStats,
    required: &ResourceRequirements,
    quota: &ResourceQuota
) -> bool {
    (current_usage.cpu_units + required.min_cpu_units) <= quota.max_cpu_units &&
    (current_usage.memory_mb + required.min_memory_mb) <= quota.max_memory_mb &&
    (current_usage.disk_mb + required.min_disk_mb) <= quota.max_disk_mb &&
    (current_usage.network_mbps + required.min_network_mbps) <= quota.max_network_mbps &&
    (current_usage.iops + required.min_iops) <= quota.max_iops
}

fn can_burst_within_limits(
    current_usage: &ResourceStats,
    required: &ResourceRequirements,
    quota: &ResourceQuota,
    burst_factor: f64
) -> bool {
    let burst_cpu = (quota.max_cpu_units as f64 * burst_factor) as u32;
    let burst_memory = (quota.max_memory_mb as f64 * burst_factor) as u64;
    let burst_disk = (quota.max_disk_mb as f64 * burst_factor) as u64;
    let burst_network = (quota.max_network_mbps as f64 * burst_factor) as u32;
    let burst_iops = (quota.max_iops as f64 * burst_factor) as u32;
    
    (current_usage.cpu_units + required.min_cpu_units) <= burst_cpu &&
    (current_usage.memory_mb + required.min_memory_mb) <= burst_memory &&
    (current_usage.disk_mb + required.min_disk_mb) <= burst_disk &&
    (current_usage.network_mbps + required.min_network_mbps) <= burst_network &&
    (current_usage.iops + required.min_iops) <= burst_iops
}
```

### 5.4 优先级继承与避免饥饿

为了防止低优先级工作流长时间等待（饥饿），我们实现了优先级继承与公平性保证机制：

```rust
/// 饥饿检测与预防
pub struct StarvationDetector {
    /// 配置
    config: StarvationConfig,
    /// 工作流等待时间
    workflow_wait_times: RwLock<HashMap<WorkflowId, StarvationStats>>,
    /// 优先级存储
    priority_store: Arc<dyn PriorityStore>,
    /// 调度器引用
    scheduler: Arc<RwLock<WorkflowScheduler>>,
}

/// 饥饿统计
#[derive(Debug, Clone)]
struct StarvationStats {
    /// 工作流ID
    workflow_id: WorkflowId,
    /// 原始优先级
    original_priority: WorkflowPriority,
    /// 当前优先级
    current_priority: WorkflowPriority,
    /// 入队时间
    enqueued_at: DateTime<Utc>,
    /// 等待时间
    wait_duration: Duration,
    /// 提升次数
    promotion_count: u32,
    /// 最后提升时间
    last_promotion: Option<DateTime<Utc>>,
}

/// 饥饿检测配置
#[derive(Debug, Clone)]
pub struct StarvationConfig {
    /// 饥饿阈值(秒)
    pub starvation_threshold_seconds: u64,
    /// 优先级提升间隔(秒)
    pub promotion_interval_seconds: u64,
    /// 最大提升次数
    pub max_promotions: u32,
    /// 优先级上升步长
    pub promotion_step: u32,
    /// 是否启用饥饿检测
    pub enabled: bool,
}

impl StarvationDetector {
    pub fn new(
        config: StarvationConfig,
        priority_store: Arc<dyn PriorityStore>,
        scheduler: Arc<RwLock<WorkflowScheduler>>,
    ) -> Self {
        Self {
            config,
            workflow_wait_times: RwLock::new(HashMap::new()),
            priority_store,
            scheduler,
        }
    }
    
    /// 注册工作流到饥饿检测器
    pub async fn register_workflow(
        &self,
        workflow_id: &WorkflowId,
        priority: WorkflowPriority,
    ) -> Result<(), WorkflowError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let mut wait_times = self.workflow_wait_times.write().await;
        
        wait_times.insert(workflow_id.clone(), StarvationStats {
            workflow_id: workflow_id.clone(),
            original_priority: priority,
            current_priority: priority,
            enqueued_at: Utc::now(),
            wait_duration: Duration::from_secs(0),
            promotion_count: 0,
            last_promotion: None,
        });
        
        Ok(())
    }
    
    /// 取消注册工作流
    pub async fn unregister_workflow(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<(), WorkflowError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let mut wait_times = self.workflow_wait_times.write().await;
        wait_times.remove(workflow_id);
        
        Ok(())
    }
    
    /// 检测和处理饥饿
    pub async fn detect_and_handle_starvation(&self) -> Result<usize, WorkflowError> {
        if !self.config.enabled {
            return Ok(0);
        }
        
        let now = Utc::now();
        let mut promotions = 0;
        let starvation_threshold = Duration::from_secs(self.config.starvation_threshold_seconds);
        let promotion_interval = Duration::from_secs(self.config.promotion_interval_seconds);
        
        // 获取等待时间
        let mut wait_times = self.workflow_wait_times.write().await;
        
        // 检查每个工作流
        for (workflow_id, stats) in wait_times.iter_mut() {
            // 更新等待时间
            stats.wait_duration = now - stats.enqueued_at;
            
            // 检查是否超过饥饿阈值
            if stats.wait_duration > starvation_threshold {
                // 检查是否可以再次提升
                let can_promote = match stats.last_promotion {
                    Some(last_time) => {
                        now - last_time > promotion_interval && 
                        stats.promotion_count < self.config.max_promotions
                    },
                    None => true,
                };
                
                if can_promote {
                    // 计算新优先级
                    let new_priority = self.calculate_promotion(stats.current_priority);
                    
                    if new_priority != stats.current_priority {
                        // 更新记录
                        stats.current_priority = new_priority;
                        stats.promotion_count += 1;
                        stats.last_promotion = Some(now);
                        
                        // 更新工作流优先级
                        let mut scheduler = self.scheduler.write().await;
                        
                        scheduler.adjust_workflow_priority(
                            workflow_id,
                            new_priority,
                            &format!("Starvation prevention (waited {:?})", stats.wait_duration)
                        ).await?;
                        
                        promotions += 1;
                    }
                }
            }
        }
        
        Ok(promotions)
    }
    
    /// 计算提升后的优先级
    fn calculate_promotion(&self, current: WorkflowPriority) -> WorkflowPriority {
        match current {
            WorkflowPriority::Background => WorkflowPriority::Low,
            WorkflowPriority::Low => WorkflowPriority::Normal,
            WorkflowPriority::Normal => WorkflowPriority::High,
            WorkflowPriority::High => WorkflowPriority::Critical,
            WorkflowPriority::Critical => WorkflowPriority::Critical, // 已是最高优先级
        }
    }
    
    /// 获取当前饥饿统计
    pub async fn get_starvation_stats(&self) -> Vec<StarvationStats> {
        let wait_times = self.workflow_wait_times.read().await;
        wait_times.values().cloned().collect()
    }
    
    /// 获取可能饥饿的工作流
    pub async fn get_potentially_starved_workflows(&self) -> Vec<(WorkflowId, Duration)> {
        let wait_times = self.workflow_wait_times.read().await;
        let starvation_threshold = Duration::from_secs(self.config.starvation_threshold_seconds);
        
        wait_times.iter()
            .filter(|(_, stats)| stats.wait_duration > starvation_threshold / 2) // 接近阈值
            .map(|(id, stats)| (id.clone(), stats.wait_duration))
            .collect()
    }
}

/// 优先级继承器
pub struct PriorityInheritanceManager {
    /// 依赖关系图
    dependency_graph: RwLock<DependencyGraph>,
    /// 优先级存储
    priority_store: Arc<dyn PriorityStore>,
    /// 调度器引用
    scheduler: Arc<RwLock<WorkflowScheduler>>,
    /// 配置
    config: InheritanceConfig,
}

/// 依赖关系图
#[derive(Debug, Default)]
struct DependencyGraph {
    /// 工作流依赖关系
    /// 键: 阻塞者工作流ID，值: 被阻塞的工作流ID列表
    blockers: HashMap<WorkflowId, HashSet<WorkflowId>>,
    /// 反向依赖关系
    /// 键: 被阻塞的工作流ID，值: 阻塞者工作流ID列表
    blocked_by: HashMap<WorkflowId, HashSet<WorkflowId>>,
    /// 工作流优先级
    priorities: HashMap<WorkflowId, WorkflowPriority>,
}

/// 优先级继承配置
#[derive(Debug, Clone)]
pub struct InheritanceConfig {
    /// 是否启用
    pub enabled: bool,
    /// 继承传播层数
    pub propagation_depth: u32,
    /// 最小提升间隔(秒)
    pub min_promotion_interval_seconds: u64,
}

impl PriorityInheritanceManager {
    pub fn new(
        priority_store: Arc<dyn PriorityStore>,
        scheduler: Arc<RwLock<WorkflowScheduler>>,
        config: InheritanceConfig,
    ) -> Self {
        Self {
            dependency_graph: RwLock::new(DependencyGraph::default()),
            priority_store,
            scheduler,
            config,
        }
    }
    
    /// 注册依赖关系
    pub async fn register_dependency(
        &self,
        blocker_id: &WorkflowId,
        blocked_id: &WorkflowId,
    ) -> Result<(), WorkflowError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let mut graph = self.dependency_graph.write().await;
        
        // 添加阻塞关系
        graph.blockers.entry(blocker_id.clone())
            .or_insert_with(HashSet::new)
            .insert(blocked_id.clone());
            
        // 添加反向关系
        graph.blocked_by.entry(blocked_id.clone())
            .or_insert_with(HashSet::new)
            .insert(blocker_id.clone());
            
        // 获取优先级
        if !graph.priorities.contains_key(blocker_id) {
            let priority = self.priority_store.get_priority(blocker_id).await?;
            graph.priorities.insert(blocker_id.clone(), priority);
        }
        
        if !graph.priorities.contains_key(blocked_id) {
            let priority = self.priority_store.get_priority(blocked_id).await?;
            graph.priorities.insert(blocked_id.clone(), priority);
        }
        
        // 重新计算优先级继承
        self.propagate_priorities(&mut graph, blocker_id, 0).await?;
        
        Ok(())
    }
    
    /// 注销依赖关系
    pub async fn unregister_dependency(
        &self,
        blocker_id: &WorkflowId,
        blocked_id: &WorkflowId,
    ) -> Result<(), WorkflowError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let mut graph = self.dependency_graph.write().await;
        
        // 移除阻塞关系
        if let Some(blocked) = graph.blockers.get_mut(blocker_id) {
            blocked.remove(blocked_id);
            if blocked.is_empty() {
                graph.blockers.remove(blocker_id);
            }
        }
        
        // 移除反向关系
        if let Some(blockers) = graph.blocked_by.get_mut(blocked_id) {
            blockers.remove(blocker_id);
            if blockers.is_empty() {
                graph.blocked_by.remove(blocked_id);
            }
        }
        
        // 重新计算可能受影响的优先级
        // 查找所有被阻塞的工作流
        let affected_workflows = self.find_affected_workflows(&graph, blocker_id);
        
        // 重置这些工作流的优先级并重新计算
        for workflow_id in affected_workflows {
            if let Some(blockers) = graph.blocked_by.get(&workflow_id) {
                if !blockers.is_empty() {
                    // 重置为原始优先级
                    let original_priority = self.priority_store.get_priority(&workflow_id).await?;
                    graph.priorities.insert(workflow_id.clone(), original_priority);
                    
                    // 重新计算继承
                    for blocker_id in blockers {
                        self.propagate_priorities(&mut graph, blocker_id, 0).await?;
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// 更新工作流优先级
    pub async fn update_workflow_priority(
        &self,
        workflow_id: &WorkflowId,
        new_priority: WorkflowPriority,
    ) -> Result<(), WorkflowError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let mut graph = self.dependency_graph.write().await;
        
        // 更新图中的优先级
        graph.priorities.insert(workflow_id.clone(), new_priority);
        
        // 传播优先级变更
        self.propagate_priorities(&mut graph, workflow_id, 0).await?;
        
        Ok(())
    }
    
    /// 传播优先级
    async fn propagate_priorities(
        &self,
        graph: &mut DependencyGraph,
        workflow_id: &WorkflowId,
        depth: u32,
    ) -> Result<(), WorkflowError> {
        // 检查是否超过传播深度
        if depth >= self.config.propagation_depth {
            return Ok(());
        }
        
        // 获取当前工作流优先级
        let current_priority = match graph.priorities.get(workflow_id) {
            Some(p) => *p,
            None => return Ok(()),
        };
        
        // 获取被此工作流阻塞的工作流
        if let Some(blocked_workflows) = graph.blockers.get(workflow_id) {
            for blocked_id in blocked_workflows {
                // 获取被阻塞工作流的当前优先级
                let blocked_priority = match graph.priorities.get(blocked_id) {
                    Some(p) => *p,
                    None => continue,
                };
                
                // 如果阻塞者优先级高于被阻塞者，继承优先级
                if current_priority < blocked_priority {
                    // 更新优先级
                    graph.priorities.insert(blocked_id.clone(), current_priority);
                    
                    // 实际调整调度器中的优先级
                    let mut scheduler = self.scheduler.write().await;
                    
                    scheduler.adjust_workflow_priority(
                        blocked_id,
                        current_priority,
                        &format!("Priority inheritance from blocking workflow {}", workflow_id)
                    ).await?;
                    
                    // 递归传播到下一级依赖
                    self.propagate_priorities(graph, blocked_id, depth + 1).await?;
                }
            }
        }
        
        Ok(())
    }
    
    /// 查找受优先级变更影响的工作流
    fn find_affected_workflows(
        &self,
        graph: &DependencyGraph,
        workflow_id: &WorkflowId,
    ) -> HashSet<WorkflowId> {
        let mut affected = HashSet::new();
        let mut queue = VecDeque::new();
        
        // 起始节点
        queue.push_back(workflow_id.clone());
        
        while let Some(current) = queue.pop_front() {
            // 如果当前节点是阻塞者
            if let Some(blocked) = graph.blockers.get(&current) {
                for blocked_id in blocked {
                    if !affected.contains(blocked_id) {
                        affected.insert(blocked_id.clone());
                        queue.push_back(blocked_id.clone());
                    }
                }
            }
        }
        
        affected
    }
    
    /// 获取工作流的关键路径
    pub async fn get_critical_path(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Vec<WorkflowId>, WorkflowError> {
        let graph = self.dependency_graph.read().await;
        
        // 使用广度优先搜索计算关键路径
        let mut path = Vec::new();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        
        // 起始节点
        queue.push_back((workflow_id.clone(), vec![workflow_id.clone()]));
        visited.insert(workflow_id.clone());
        
        while let Some((current, current_path)) = queue.pop_front() {
            // 更新最长路径
            if current_path.len() > path.len() {
                path = current_path.clone();
            }
            
            // 检查阻塞关系
            if let Some(blocked) = graph.blockers.get(&current) {
                for next in blocked {
                    if !visited.contains(next) {
                        visited.insert(next.clone());
                        
                        // 构建新路径
                        let mut new_path = current_path.clone();
                        new_path.push(next.clone());
                        
                        queue.push_back((next.clone(), new_path));
                    }
                }
            }
        }
        
        Ok(path)
    }
    
    /// 检测和解决优先级反转
    pub async fn detect_and_resolve_priority_inversion(&self) -> Result<usize, WorkflowError> {
        if !self.config.enabled {
            return Ok(0);
        }
        
        let graph = self.dependency_graph.read().await;
        let mut inversions_fixed = 0;
        
        // 检查每个依赖关系
        for (blocker_id, blocked_set) in &graph.blockers {
            let blocker_priority = match graph.priorities.get(blocker_id) {
                Some(p) => *p,
                None => continue,
            };
            
            for blocked_id in blocked_set {
                let blocked_priority = match graph.priorities.get(blocked_id) {
                    Some(p) => *p,
                    None => continue,
                };
                
                // 检测优先级反转：如果阻塞者优先级低于被阻塞者
                if blocker_priority > blocked_priority {
                    // 获取写锁进行修复
                    drop(graph);
                    
                    // 修复反转
                    let mut scheduler = self.scheduler.write().await;
                    
                    scheduler.adjust_workflow_priority(
                        blocker_id,
                        blocked_priority, // 继承被阻塞者的高优先级
                        &format!("Priority inversion resolution with {}", blocked_id)
                    ).await?;
                    
                    inversions_fixed += 1;
                    
                    // 重新获取读锁继续检查
                    let graph = self.dependency_graph.read().await;
                }
            }
        }
        
        Ok(inversions_fixed)
    }
}
```

## 6. 持久化与状态管理

### 6.1 事件溯源架构

事件溯源是持久化工作流状态的核心机制，它将所有状态变更记录为不可变的事件序列：

```rust
/// 事件存储接口
#[async_trait]
pub trait EventStore: Send + Sync + 'static {
    /// 添加工作流事件
    async fn append_workflow_event(
        &self,
        event: WorkflowEvent,
    ) -> Result<u64, StorageError>;
    
    /// 获取工作流的所有事件
    async fn get_workflow_events(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Vec<(u64, WorkflowEvent)>, StorageError>;
    
    /// 获取从特定序列号之后的事件
    async fn get_events_after(
        &self,
        workflow_id: &WorkflowId,
        sequence: u64,
    ) -> Result<Vec<(u64, WorkflowEvent)>, StorageError>;
    
    /// 获取特定工作流的最后一个事件
    async fn get_last_event(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<(u64, WorkflowEvent)>, StorageError>;
    
    /// 获取多个工作流的事件
    async fn get_workflows_events(
        &self,
        workflow_ids: &[WorkflowId],
    ) -> Result<HashMap<WorkflowId, Vec<(u64, WorkflowEvent)>>, StorageError>;
    
    /// 通过查询条件获取事件
    async fn query_events(
        &self,
        query: &EventQuery,
    ) -> Result<Vec<(WorkflowId, u64, WorkflowEvent)>, StorageError>;
}

/// 事件查询条件
#[derive(Debug, Clone)]
pub struct EventQuery {
    /// 工作流类型
    pub workflow_type: Option<String>,
    /// 事件类型
    pub event_types: Option<Vec<String>>,
    /// 开始时间
    pub start_time: Option<DateTime<Utc>>,
    /// 结束时间
    pub end_time: Option<DateTime<Utc>>,
    /// 最大结果数
    pub limit: Option<usize>,
    /// 偏移量
    pub offset: Option<usize>,
    /// 排序方式
    pub order: EventQueryOrder,
    /// 额外过滤条件
    pub filters: Option<HashMap<String, String>>,
}

/// 事件查询排序方式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventQueryOrder {
    /// 按序列号升序
    SequenceAsc,
    /// 按序列号降序
    SequenceDesc,
    /// 按时间戳升序
    TimestampAsc,
    /// 按时间戳降序
    TimestampDesc,
}

/// PostgreSQL事件存储实现
pub struct PostgresEventStore {
    /// 数据库连接池
    pool: PgPool,
    /// 事件批处理器
    batch_processor: Option<EventBatchProcessor>,
}

impl PostgresEventStore {
    pub async fn new(database_url: &str, use_batching: bool) -> Result<Self, StorageError> {
        let pool = PgPool::connect(database_url)
            .await
            .map_err(|e| StorageError::ConnectionError(e.to_string()))?;
            
        // 确保表存在
        Self::create_tables(&pool).await?;
        
        let batch_processor = if use_batching {
            Some(EventBatchProcessor::new(pool.clone()))
        } else {
            None
        };
        
        Ok(Self {
            pool,
            batch_processor,
        })
    }
    
    /// 创建必要的表
    async fn create_tables(pool: &PgPool) -> Result<(), StorageError> {
        // 事件表
        sqlx::query(r#"
            CREATE TABLE IF NOT EXISTS workflow_events (
                id BIGSERIAL PRIMARY KEY,
                workflow_id TEXT NOT NULL,
                sequence_num BIGINT NOT NULL,
                event_type TEXT NOT NULL,
                event_data JSONB NOT NULL,
                timestamp TIMESTAMPTZ NOT NULL,
                UNIQUE (workflow_id, sequence_num)
            );
            
            CREATE INDEX IF NOT EXISTS idx_workflow_events_workflow_id ON workflow_events (workflow_id);
            CREATE INDEX IF NOT EXISTS idx_workflow_events_event_type ON workflow_events (event_type);
            CREATE INDEX IF NOT EXISTS idx_workflow_events_timestamp ON workflow_events (timestamp);
            CREATE INDEX IF NOT EXISTS idx_workflow_events_sequence ON workflow_events (sequence_num);
        "#)
        .execute(pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
}

#[async_trait]
impl EventStore for PostgresEventStore {
    async fn append_workflow_event(
        &self,
        event: WorkflowEvent,
    ) -> Result<u64, StorageError> {
        // 使用批处理器或直接写入
        if let Some(ref processor) = self.batch_processor {
            processor.submit_event(event).await
        } else {
            self.append_single_event(event).await
        }
    }
    
    async fn get_workflow_events(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Vec<(u64, WorkflowEvent)>, StorageError> {
        let rows = sqlx::query(r#"
            SELECT sequence_num, event_data 
            FROM workflow_events 
            WHERE workflow_id = $1 
            ORDER BY sequence_num ASC
        "#)
        .bind(workflow_id.to_string())
        .fetch_all(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let mut events = Vec::with_capacity(rows.len());
        
        for row in rows {
            let sequence: i64 = row.get("sequence_num");
            let event_data: serde_json::Value = row.get("event_data");
            
            let event: WorkflowEvent = serde_json::from_value(event_data)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            events.push((sequence as u64, event));
        }
        
        Ok(events)
    }
    
    async fn get_events_after(
        &self,
        workflow_id: &WorkflowId,
        sequence: u64,
    ) -> Result<Vec<(u64, WorkflowEvent)>, StorageError> {
        let rows = sqlx::query(r#"
            SELECT sequence_num, event_data 
            FROM workflow_events 
            WHERE workflow_id = $1 AND sequence_num > $2
            ORDER BY sequence_num ASC
        "#)
        .bind(workflow_id.to_string())
        .bind(sequence as i64)
        .fetch_all(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let mut events = Vec::with_capacity(rows.len());
        
        for row in rows {
            let sequence: i64 = row.get("sequence_num");
            let event_data: serde_json::Value = row.get("event_data");
            
            let event: WorkflowEvent = serde_json::from_value(event_data)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            events.push((sequence as u64, event));
        }
        
        Ok(events)
    }
    
    async fn get_last_event(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<(u64, WorkflowEvent)>, StorageError> {
        let row = sqlx::query(r#"
            SELECT sequence_num, event_data 
            FROM workflow_events 
            WHERE workflow_id = $1 
            ORDER BY sequence_num DESC 
            LIMIT 1
        "#)
        .bind(workflow_id.to_string())
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        if let Some(row) = row {
            let sequence: i64 = row.get("sequence_num");
            let event_data: serde_json::Value = row.get("event_data");
            
            let event: WorkflowEvent = serde_json::from_value(event_data)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            Ok(Some((sequence as u64, event)))
        } else {
            Ok(None)
        }
    }
    
    async fn get_workflows_events(
        &self,
        workflow_ids: &[WorkflowId],
    ) -> Result<HashMap<WorkflowId, Vec<(u64, WorkflowEvent)>>, StorageError> {
        if workflow_ids.is_empty() {
            return Ok(HashMap::new());
        }
        
        let workflow_id_strings: Vec<String> = workflow_ids.iter()
            .map(|id| id.to_string())
            .collect();
            
        let rows = sqlx::query(r#"
            SELECT workflow_id, sequence_num, event_data 
            FROM workflow_events 
            WHERE workflow_id = ANY($1) 
            ORDER BY workflow_id, sequence_num ASC
        "#)
        .bind(&workflow_id_strings)
        .fetch_all(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let mut result = HashMap::new();
        
        for row in rows {
            let workflow_id_str: String = row.get("workflow_id");
            let workflow_id = WorkflowId::from_string(&workflow_id_str)
                .map_err(|_| StorageError::InvalidWorkflowId(workflow_id_str))?;
                
            let sequence: i64 = row.get("sequence_num");
            let event_data: serde_json::Value = row.get("event_data");
            
            let event: WorkflowEvent = serde_json::from_value(event_data)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            result.entry(workflow_id)
                .or_insert_with(Vec::new)
                .push((sequence as u64, event));
        }
        
        Ok(result)
    }
    
    async fn query_events(
        &self,
        query: &EventQuery,
    ) -> Result<Vec<(WorkflowId, u64, WorkflowEvent)>, StorageError> {
        // 构建查询
        let mut sql = "SELECT workflow_id, sequence_num, event_data FROM workflow_events WHERE 1=1".to_string();
        let mut params = Vec::new();
        let mut param_index = 1;
        
        // 添加过滤条件
        if let Some(ref workflow_type) = query.workflow_type {
            sql.push_str(&format!(" AND event_data->>'workflow_type' = ${}", param_index));
            params.push(workflow_type.clone());
            param_index += 1;
        }
        
        if let Some(ref event_types) = query.event_types {
            sql.push_str(&format!(" AND event_type = ANY(${})", param_index));
            params.push(event_types.clone());
            param_index += 1;
        }
        
        if let Some(start_time) = query.start_time {
            sql.push_str(&format!(" AND timestamp >= ${}", param_index));
            params.push(start_time.to_rfc3339());
            param_index += 1;
        }
        
        if let Some(end_time) = query.end_time {
            sql.push_str(&format!(" AND timestamp <= ${}", param_index));
            params.push(end_time.to_rfc3339());
            param_index += 1;
        }
        
        if let Some(ref filters) = query.filters {
            for (key, value) in filters {
                sql.push_str(&format!(" AND event_data->>'{0}' = ${1}", key, param_index));
                params.push(value.clone());
                param_index += 1;
            }
        }
        
        // 添加排序
        sql.push_str(" ORDER BY ");
        match query.order {
            EventQueryOrder::SequenceAsc => sql.push_str("sequence_num ASC"),
            EventQueryOrder::SequenceDesc => sql.push_str("sequence_num DESC"),
            EventQueryOrder::TimestampAsc => sql.push_str("timestamp ASC"),
            EventQueryOrder::TimestampDesc => sql.push_str("timestamp DESC"),
        }
        
        // 添加分页
        if let Some(limit) = query.limit {
            sql.push_str(&format!(" LIMIT {}", limit));
        }
        
        if let Some(offset) = query.offset {
            sql.push_str(&format!(" OFFSET {}", offset));
        }
        
        // 执行查询
        let mut query_builder = sqlx::query(&sql);
        
        for param in params {
            query_builder = query_builder.bind(param);
        }
        
        let rows = query_builder
            .fetch_all(&self.pool)
            .await
            .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
            
        let mut results = Vec::with_capacity(rows.len());
        
        for row in rows {
            let workflow_id_str: String = row.get("workflow_id");
            let workflow_id = WorkflowId::from_string(&workflow_id_str)
                .map_err(|_| StorageError::InvalidWorkflowId(workflow_id_str))?;
                
            let sequence: i64 = row.get("sequence_num");
            let event_data: serde_json::Value = row.get("event_data");
            
            let event: WorkflowEvent = serde_json::from_value(event_data)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            results.push((workflow_id, sequence as u64, event));
        }
        
        Ok(results)
    }
    
    // 辅助方法
    async fn append_single_event(&self, event: WorkflowEvent) -> Result<u64, StorageError> {
        // 提取工作流ID
        let workflow_id = match &event {
            WorkflowEvent::WorkflowCreated { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowStarted { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::StageStarted { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::StageCompleted { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::StageFailed { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowSuspended { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowResumed { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowCompleted { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowFailed { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowCancelled { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowPriorityChanged { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowRecoveryStarted { workflow_id, .. } => workflow_id.clone(),
            WorkflowEvent::WorkflowRecoveryCompleted { workflow_id, .. } => workflow_id.clone(),
        };
        
        // 获取事件类型
        let event_type = match &event {
            WorkflowEvent::WorkflowCreated { .. } => "workflow_created",
            WorkflowEvent::WorkflowStarted { .. } => "workflow_started",
            WorkflowEvent::StageStarted { .. } => "stage_started",
            WorkflowEvent::StageCompleted { .. } => "stage_completed",
            WorkflowEvent::StageFailed { .. } => "stage_failed",
            WorkflowEvent::WorkflowSuspended { .. } => "workflow_suspended",
            WorkflowEvent::WorkflowResumed { .. } => "workflow_resumed",
            WorkflowEvent::WorkflowCompleted { .. } => "workflow_completed",
            WorkflowEvent::WorkflowFailed { .. } => "workflow_failed",
            WorkflowEvent::WorkflowCancelled { .. } => "workflow_cancelled",
            WorkflowEvent::WorkflowPriorityChanged { .. } => "workflow_priority_changed",
            WorkflowEvent::WorkflowRecoveryStarted { .. } => "workflow_recovery_started",
            WorkflowEvent::WorkflowRecoveryCompleted { .. } => "workflow_recovery_completed",
        };
        
        // 时间戳
        let timestamp = match &event {
            WorkflowEvent::WorkflowCreated { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowStarted { timestamp, .. } => timestamp,
            WorkflowEvent::StageStarted { timestamp, .. } => timestamp,
            WorkflowEvent::StageCompleted { timestamp, .. } => timestamp,
            WorkflowEvent::StageFailed { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowSuspended { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowResumed { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowCompleted { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowFailed { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowCancelled { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowPriorityChanged { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowRecoveryStarted { timestamp, .. } => timestamp,
            WorkflowEvent::WorkflowRecoveryCompleted { timestamp, .. } => timestamp,
        };
        
        // 事件数据
        let event_data = serde_json::to_value(&event)
            .map_err(|e| StorageError::SerializationError(e.to_string()))?;
            
        // 事务中获取序列号并插入事件
        let mut transaction = self.pool.begin().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
            
        // 获取下一个序列号
        let sequence_num: i64 = sqlx::query(
            "SELECT COALESCE(MAX(sequence_num), 0) + 1 FROM workflow_events WHERE workflow_id = $1"
        )
        .bind(workflow_id.to_string())
        .fetch_one(&mut transaction)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?
        .get(0);
        
        // 插入事件
        sqlx::query(
            "INSERT INTO workflow_events(workflow_id, sequence_num, event_type, event_data, timestamp) VALUES($1, $2, $3, $4, $5)"
        )
        .bind(workflow_id.to_string())
        .bind(sequence_num)
        .bind(event_type)
        .bind(event_data)
        .bind(timestamp)
        .execute(&mut transaction)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        // 提交事务
        transaction.commit().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
            
        Ok(sequence_num as u64)
    }
}

/// 事件批处理器
pub struct EventBatchProcessor {
    /// 待处理事件队列
    event_queue: mpsc::Sender<(WorkflowEvent, oneshot::Sender<Result<u64, StorageError>>)>,
    /// 处理任务句柄
    _processor_task: JoinHandle<()>,
}

impl EventBatchProcessor {
    pub fn new(pool: PgPool) -> Self {
        const BATCH_SIZE: usize = 100;
        const FLUSH_INTERVAL_MS: u64 = 100;
        
        let (tx, mut rx) = mpsc::channel::<(WorkflowEvent, oneshot::Sender<Result<u64, StorageError>>)>(1000);
        
        // 启动处理任务
        let processor_task = tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_millis(FLUSH_INTERVAL_MS));
            let mut batch = Vec::with_capacity(BATCH_SIZE);
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        if !batch.is_empty() {
                            let to_process = std::mem::take(&mut batch);
                            if let Err(e) = Self::process_batch(&pool, to_process).await {
                                log::error!("Error processing event batch: {}", e);
                            }
                        }
                    }
                    Some((event, resp_tx)) = rx.recv() => {
                        batch.push((event, resp_tx));
                        
                        if batch.len() >= BATCH_SIZE {
                            let to_process = std::mem::take(&mut batch);
                            if let Err(e) = Self::process_batch(&pool, to_process).await {
                                log::error!("Error processing event batch: {}", e);
                            }
                        }
                    }
                    else => break,
                }
            }
            
            // 处理剩余事件
            if !batch.is_empty() {
                if let Err(e) = Self::process_batch(&pool, batch).await {
                    log::error!("Error processing final event batch: {}", e);
                }
            }
        });
        
        Self {
            event_queue: tx,
            _processor_task: processor_task,
        }
    }
    
    /// 提交事件到批处理队列
    pub async fn submit_event(&self, event: WorkflowEvent) -> Result<u64, StorageError> {
        let (resp_tx, resp_rx) = oneshot::channel();
        
        self.event_queue.send((event, resp_tx)).await
            .map_err(|_| StorageError::BatchProcessorError("Event queue full or closed".to_string()))?;
            
        resp_rx.await
            .map_err(|_| StorageError::BatchProcessorError("Response channel closed".to_string()))?
    }
    
    /// 处理事件批次
    async fn process_batch(
        pool: &PgPool,
        batch: Vec<(WorkflowEvent, oneshot::Sender<Result<u64, StorageError>>)>
    ) -> Result<(), StorageError> {
        if batch.is_empty() {
            return Ok(());
        }
        
        // 按工作流ID分组
        let mut grouped: HashMap<WorkflowId, Vec<(WorkflowEvent, oneshot::Sender<Result<u64, StorageError>>)>> = HashMap::new();
        
        for (event, resp_tx) in batch {
            let workflow_id = match &event {
                WorkflowEvent::WorkflowCreated { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowStarted { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::StageStarted { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::StageCompleted { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::StageFailed { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowSuspended { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowResumed { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowCompleted { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowFailed { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowCancelled { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowPriorityChanged { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowRecoveryStarted { workflow_id, .. } => workflow_id.clone(),
                WorkflowEvent::WorkflowRecoveryCompleted { workflow_id, .. } => workflow_id.clone(),
            };
            
            grouped.entry(workflow_id).or_default().push((event, resp_tx));
        }
        
        // 为每个工作流创建事务
        for (workflow_id, events) in grouped {
            let result = Self::process_workflow_batch(pool, &workflow_id, events).await;
            
            if let Err(e) = result {
                log::error!("Error processing batch for workflow {}: {}", workflow_id, e);
            }
        }
        
        Ok(())
    }
    
    /// 处理单个工作流的事件批次
    async fn process_workflow_batch(
        pool: &PgPool,
        workflow_id: &WorkflowId,
        events: Vec<(WorkflowEvent, oneshot::Sender<Result<u64, StorageError>>)>
    ) -> Result<(), StorageError> {
        // 开始事务
        let mut transaction = pool.begin().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
            
        // 获取基础序列号
        let base_sequence: i64 = sqlx::query(
            "SELECT COALESCE(MAX(sequence_num), 0) FROM workflow_events WHERE workflow_id = $1"
        )
        .bind(workflow_id.to_string())
        .fetch_one(&mut transaction)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?
        .get(0);
        
        // 准备批量插入
        let mut insert_query = "INSERT INTO workflow_events(workflow_id, sequence_num, event_type, event_data, timestamp) VALUES ".to_string();
        let mut params = Vec::new();
        let mut param_index = 1;
        let mut sequence_results = Vec::with_capacity(events.len());
        
        for (i, (event, _)) in events.iter().enumerate() {
            let sequence = base_sequence + (i as i64) + 1;
            sequence_results.push(sequence as u64);
            
            // 事件类型
            let event_type = match event {
                WorkflowEvent::WorkflowCreated { .. } => "workflow_created",
                WorkflowEvent::WorkflowStarted { .. } => "workflow_started",
                WorkflowEvent::StageStarted { .. } => "stage_started",
                WorkflowEvent::StageCompleted { .. } => "stage_completed",
                WorkflowEvent::StageFailed { .. } => "stage_failed",
                WorkflowEvent::WorkflowSuspended { .. } => "workflow_suspended",
                WorkflowEvent::WorkflowResumed { .. } => "workflow_resumed",
                WorkflowEvent::WorkflowCompleted { .. } => "workflow_completed",
                WorkflowEvent::WorkflowFailed { .. } => "workflow_failed",
                WorkflowEvent::WorkflowCancelled { .. } => "workflow_cancelled",
                WorkflowEvent::WorkflowPriorityChanged { .. } => "workflow_priority_changed",
                WorkflowEvent::WorkflowRecoveryStarted { .. } => "workflow_recovery_started",
                WorkflowEvent::WorkflowRecoveryCompleted { .. } => "workflow_recovery_completed",
            };
            
            // 时间戳
            let timestamp = match event {
                WorkflowEvent::WorkflowCreated { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowStarted { timestamp, .. } => timestamp,
                WorkflowEvent::StageStarted { timestamp, .. } => timestamp,
                WorkflowEvent::StageCompleted { timestamp, .. } => timestamp,
                WorkflowEvent::StageFailed { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowSuspended { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowResumed { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowCompleted { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowFailed { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowCancelled { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowPriorityChanged { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowRecoveryStarted { timestamp, .. } => timestamp,
                WorkflowEvent::WorkflowRecoveryCompleted { timestamp, .. } => timestamp,
            };
            
            // 事件数据
            let event_data = serde_json::to_value(event)
                .map_err(|e| StorageError::SerializationError(e.to_string()))?;
            
            if i > 0 {
                insert_query.push_str(", ");
            }
            
            insert_query.push_str(&format!(
                "(${}::TEXT, ${}::BIGINT, ${}::TEXT, ${}::JSONB, ${}::TIMESTAMPTZ)",
                param_index, param_index + 1, param_index + 2, param_index + 3, param_index + 4
            ));
            
            params.push(workflow_id.to_string());
            params.push(sequence.to_string());
            params.push(event_type.to_string());
            params.push(event_data.to_string());
            params.push(timestamp.to_rfc3339());
            
            param_index += 5;
        }
        
        // 执行批量插入
        let mut query = sqlx::query(&insert_query);
        
        for param in params {
            query = query.bind(param);
        }
        
        query.execute(&mut transaction).await
            .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
            
        // 提交事务
        transaction.commit().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
            
        // 发送结果
        for ((_, resp_tx), sequence) in events.into_iter().zip(sequence_results) {
            let _ = resp_tx.send(Ok(sequence));
        }
        
        Ok(())
    }
}
```

### 6.2 检查点优化

检查点机制优化工作流状态恢复性能：

```rust
/// 检查点存储接口
#[async_trait]
pub trait CheckpointStore: Send + Sync + 'static {
    /// 保存工作流状态检查点
    async fn save_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        state: &WorkflowState,
        checkpoint_id: String,
        sequence: u64,
        hash: String,
    ) -> Result<(), StorageError>;
    
    /// 获取工作流最新检查点
    async fn get_latest_checkpoint(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<(WorkflowState, u64)>, StorageError>;
    
    /// 获取特定检查点
    async fn get_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        checkpoint_id: &str,
    ) -> Result<Option<(WorkflowState, u64)>, StorageError>;
    
    /// 获取增量检查点
    async fn get_incremental_checkpoints(
        &self,
        workflow_id: &WorkflowId,
        base_checkpoint_id: &str,
    ) -> Result<Vec<IncrementalCheckpoint>, StorageError>;
    
    /// 保存增量检查点
    async fn save_incremental_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        checkpoint: &IncrementalCheckpoint,
    ) -> Result<(), StorageError>;
    
    /// 获取检查点计数
    async fn get_checkpoint_count(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<u64, StorageError>;
    
    /// 清理旧检查点
    async fn prune_checkpoints(
        &self,
        workflow_id: &WorkflowId,
        keep_latest: u32,
    ) -> Result<u32, StorageError>;
}

/// 增量检查点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncrementalCheckpoint {
    /// 检查点ID
    pub id: String,
    /// 工作流ID
    pub workflow_id: WorkflowId,
    /// 基础检查点ID
    pub base_checkpoint_id: String,
    /// 序列号
    pub sequence_number: u64,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 状态变更
    pub changes: Vec<StateChange>,
    /// 验证哈希
    pub verification_hash: String,
}

/// 检查点策略
#[derive(Debug, Clone)]
pub enum CheckpointStrategy {
    /// 每N个事件
    EveryNEvents(usize),
    /// 基于时间间隔
    TimeBased(Duration),
    /// 混合策略（事件数或时间，先到先得）
    Hybrid {
        event_count: usize,
        time_interval: Duration,
    },
    /// 状态转换后
    AfterStateTransitions(Vec<String>),
    /// 自适应策略
    Adaptive {
        min_events: usize,
        max_events: usize,
        min_interval: Duration,
        max_interval: Duration,
    },
}

/// PostgreSQL检查点存储实现
pub struct PostgresCheckpointStore {
    /// 数据库连接池
    pool: PgPool,
}

impl PostgresCheckpointStore {
    pub async fn new(database_url: &str) -> Result<Self, StorageError> {
        let pool = PgPool::connect(database_url)
            .await
            .map_err(|e| StorageError::ConnectionError(e.to_string()))?;
            
        // 确保表存在
        Self::create_tables(&pool).await?;
        
        Ok(Self {
            pool,
        })
    }
    
    /// 创建必要的表
    async fn create_tables(pool: &PgPool) -> Result<(), StorageError> {
        // 检查点表
        sqlx::query(r#"
            CREATE TABLE IF NOT EXISTS workflow_checkpoints (
                checkpoint_id TEXT PRIMARY KEY,
                workflow_id TEXT NOT NULL,
                state JSONB NOT NULL,
                sequence_num BIGINT NOT NULL,
                created_at TIMESTAMPTZ NOT NULL,
                verification_hash TEXT NOT NULL
            );
            
            CREATE INDEX IF NOT EXISTS idx_workflow_checkpoints_workflow_id 
            ON workflow_checkpoints (workflow_id);
            
            CREATE TABLE IF NOT EXISTS workflow_incremental_checkpoints (
                checkpoint_id TEXT PRIMARY KEY,
                workflow_id TEXT NOT NULL,
                base_checkpoint_id TEXT NOT NULL,
                changes JSONB NOT NULL,
                sequence_num BIGINT NOT NULL,
                created_at TIMESTAMPTZ NOT NULL,
                verification_hash TEXT NOT NULL,
                FOREIGN KEY (base_checkpoint_id) REFERENCES workflow_checkpoints(checkpoint_id)
            );
            
            CREATE INDEX IF NOT EXISTS idx_workflow_incremental_checkpoints_workflow_id 
            ON workflow_incremental_checkpoints (workflow_id);
            
            CREATE INDEX IF NOT EXISTS idx_workflow_incremental_checkpoints_base 
            ON workflow_incremental_checkpoints (base_checkpoint_id);
        "#)
        .execute(pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
}

#[async_trait]
impl CheckpointStore for PostgresCheckpointStore {
    async fn save_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        state: &WorkflowState,
        checkpoint_id: String,
        sequence: u64,
        hash: String,
    ) -> Result<(), StorageError> {
        // 序列化状态
        let state_json = serde_json::to_value(state)
            .map_err(|e| StorageError::SerializationError(e.to_string()))?;
            
        // 插入检查点
        sqlx::query(r#"
            INSERT INTO workflow_checkpoints(checkpoint_id, workflow_id, state, sequence_num, created_at, verification_hash)
            VALUES($1, $2, $3, $4, $5, $6)
            ON CONFLICT(checkpoint_id) DO UPDATE
            SET state = $3, sequence_num = $4, created_at = $5, verification_hash = $6
        "#)
        .bind(&checkpoint_id)
        .bind(workflow_id.to_string())
        .bind(state_json)
        .bind(sequence as i64)
        .bind(Utc::now())
        .bind(hash)
        .execute(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
    
    async fn get_latest_checkpoint(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Option<(WorkflowState, u64)>, StorageError> {
        // 查询最新检查点
        let row = sqlx::query(r#"
            SELECT state, sequence_num
            FROM workflow_checkpoints
            WHERE workflow_id = $1
            ORDER BY sequence_num DESC
            LIMIT 1
        "#)
        .bind(workflow_id.to_string())
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        if let Some(row) = row {
            let state_json: serde_json::Value = row.get("state");
            let sequence: i64 = row.get("sequence_num");
            
            let state: WorkflowState = serde_json::from_value(state_json)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            Ok(Some((state, sequence as u64)))
        } else {
            Ok(None)
        }
    }
    
    async fn get_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        checkpoint_id: &str,
    ) -> Result<Option<(WorkflowState, u64)>, StorageError> {
        // 查询特定检查点
        let row = sqlx::query(r#"
            SELECT state, sequence_num
            FROM workflow_checkpoints
            WHERE workflow_id = $1 AND checkpoint_id = $2
        "#)
        .bind(workflow_id.to_string())
        .bind(checkpoint_id)
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        if let Some(row) = row {
            let state_json: serde_json::Value = row.get("state");
            let sequence: i64 = row.get("sequence_num");
            
            let state: WorkflowState = serde_json::from_value(state_json)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            Ok(Some((state, sequence as u64)))
        } else {
            Ok(None)
        }
    }
    
    async fn get_incremental_checkpoints(
        &self,
        workflow_id: &WorkflowId,
        base_checkpoint_id: &str,
    ) -> Result<Vec<IncrementalCheckpoint>, StorageError> {
        // 查询增量检查点
        let rows = sqlx::query(r#"
            SELECT checkpoint_id, base_checkpoint_id, changes, sequence_num, created_at, verification_hash
            FROM workflow_incremental_checkpoints
            WHERE workflow_id = $1 AND base_checkpoint_id = $2
            ORDER BY sequence_num ASC
        "#)
        .bind(workflow_id.to_string())
        .bind(base_checkpoint_id)
        .fetch_all(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let mut checkpoints = Vec::with_capacity(rows.len());
        
        for row in rows {
            let checkpoint_id: String = row.get("checkpoint_id");
            let base_id: String = row.get("base_checkpoint_id");
            let changes_json: serde_json::Value = row.get("changes");
            let sequence: i64 = row.get("sequence_num");
            let created_at: DateTime<Utc> = row.get("created_at");
            let hash: String = row.get("verification_hash");
            
            let changes: Vec<StateChange> = serde_json::from_value(changes_json)
                .map_err(|e| StorageError::DeserializationError(e.to_string()))?;
                
            checkpoints.push(IncrementalCheckpoint {
                id: checkpoint_id,
                workflow_id: workflow_id.clone(),
                base_checkpoint_id: base_id,
                sequence_number: sequence as u64,
                created_at,
                changes,
                verification_hash: hash,
            });
        }
        
        Ok(checkpoints)
    }
    
    async fn save_incremental_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        checkpoint: &IncrementalCheckpoint,
    ) -> Result<(), StorageError> {
        // 序列化变更
        let changes_json = serde_json::to_value(&checkpoint.changes)
            .map_err(|e| StorageError::SerializationError(e.to_string()))?;
            
        // 插入增量检查点
        sqlx::query(r#"
            INSERT INTO workflow_incremental_checkpoints(
                checkpoint_id, workflow_id, base_checkpoint_id, changes, 
                sequence_num, created_at, verification_hash
            )
            VALUES($1, $2, $3, $4, $5, $6, $7)
            ON CONFLICT(checkpoint_id) DO UPDATE
            SET changes = $4, sequence_num = $5, created_at = $6, verification_hash = $7
        "#)
        .bind(&checkpoint.id)
        .bind(workflow_id.to_string())
        .bind(&checkpoint.base_checkpoint_id)
        .bind(changes_json)
        .bind(checkpoint.sequence_number as i64)
        .bind(checkpoint.created_at)
        .bind(&checkpoint.verification_hash)
        .execute(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
    
    async fn get_checkpoint_count(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<u64, StorageError> {
        // 查询检查点数量
        let row = sqlx::query(r#"
            SELECT COUNT(*) as count
            FROM workflow_checkpoints
            WHERE workflow_id = $1
        "#)
        .bind(workflow_id.to_string())
        .fetch_one(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let count: i64 = row.get("count");
        Ok(count as u64)
    }
    
    async fn prune_checkpoints(
        &self,
        workflow_id: &WorkflowId,
        keep_latest: u32,
    ) -> Result<u32, StorageError> {
        // 首先找出要保留的检查点ID
        let keep_ids: Vec<String> = sqlx::query(r#"
            SELECT checkpoint_id
            FROM workflow_checkpoints
            WHERE workflow_id = $1
            ORDER BY sequence_num DESC
            LIMIT $2
        "#)
        .bind(workflow_id.to_string())
        .bind(keep_latest as i64)
        .fetch_all(&self.pool)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?
        .into_iter()
        .map(|row| row.get("checkpoint_id"))
        .collect();
        
        // 开始事务
        let mut tx = self.pool.begin().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
        
        // 删除未被引用的增量检查点
        let delete_incremental = sqlx::query(r#"
            DELETE FROM workflow_incremental_checkpoints
            WHERE workflow_id = $1 AND base_checkpoint_id NOT IN (SELECT unnest($2::text[]))
            RETURNING checkpoint_id
        "#)
        .bind(workflow_id.to_string())
        .bind(&keep_ids)
        .fetch_all(&mut tx)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let deleted_incremental = delete_incremental.len();
        
        // 删除多余的完整检查点
        let delete_full = sqlx::query(r#"
            DELETE FROM workflow_checkpoints
            WHERE workflow_id = $1 AND checkpoint_id NOT IN (SELECT unnest($2::text[]))
            RETURNING checkpoint_id
        "#)
        .bind(workflow_id.to_string())
        .bind(&keep_ids)
        .fetch_all(&mut tx)
        .await
        .map_err(|e| StorageError::DatabaseError(e.to_string()))?;
        
        let deleted_full = delete_full.len();
        
        // 提交事务
        tx.commit().await
            .map_err(|e| StorageError::TransactionError(e.to_string()))?;
            
        Ok((deleted_incremental + deleted_full) as u32)
    }
}

/// 检查点管理器
pub struct CheckpointManager {
    /// 事件存储
    event_store: Arc<dyn EventStore>,
    /// 检查点存储
    checkpoint_store: Arc<dyn CheckpointStore>,
    /// 检查点策略
    strategy: CheckpointStrategy,
    /// 状态构建器
    state_builder: Arc<dyn StateBuilder>,
    /// 上次检查点时间
    last_checkpoint: RwLock<HashMap<WorkflowId, (DateTime<Utc>, u64)>>,
    /// 自上次检查点后的事件计数
    event_count: RwLock<HashMap<WorkflowId, usize>>,
    /// 配置
    config: CheckpointConfig,
}

/// 检查点配置
#[derive(Debug, Clone)]
pub struct CheckpointConfig {
    /// 启用增量检查点
    pub use_incremental: bool,
    /// 增量检查点间隔
    pub incremental_interval: usize,
    /// 最大检查点数量
    pub max_checkpoints: u32,
    /// 检查点压缩阈值
    pub compression_threshold_bytes: usize,
    /// 是否启用自动清理
    pub auto_prune: bool,
    /// 保留的检查点数量
    pub keep_latest: u32,
}

impl CheckpointManager {
    pub fn new(
        event_store: Arc<dyn EventStore>,
        checkpoint_store: Arc<dyn CheckpointStore>,
        strategy: CheckpointStrategy,
        state_builder: Arc<dyn StateBuilder>,
        config: CheckpointConfig,
    ) -> Self {
        Self {
            event_store,
            checkpoint_store,
            strategy,
            state_builder,
            last_checkpoint: RwLock::new(HashMap::new()),
            event_count: RwLock::new(HashMap::new()),
            config,
        }
    }
    
    /// 事件处理后调用，判断是否需要创建检查点
    pub async fn handle_event(
        &self,
        workflow_id: &WorkflowId,
        event: &WorkflowEvent,
        sequence: u64,
    ) -> Result<bool, WorkflowError> {
        // 更新事件计数
        {
            let mut counts = self.event_count.write().await;
            let count = counts.entry(workflow_id.clone()).or_insert(0);
            *count += 1;
        }
        
        // 检查是否应该创建检查点
        if self.should_checkpoint(workflow_id, event).await? {
            // 创建检查点
            self.create_checkpoint(workflow_id, sequence).await?;
            return Ok(true);
        }
        
        // 检查是否应该创建增量检查点
        if self.config.use_incremental && self.should_create_incremental(workflow_id).await? {
            self.create_incremental_checkpoint(workflow_id, sequence).await?;
            return Ok(true);
        }
        
        Ok(false)
    }
    
    /// 创建新的完整检查点
    pub async fn create_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        sequence: u64,
    ) -> Result<String, WorkflowError> {
        // 获取所有事件
        let events = self.event_store.get_workflow_events(workflow_id).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        if events.is_empty() {
            return Err(WorkflowError::WorkflowNotFound(workflow_id.to_string()));
        }
        
        // 构建当前状态
        let state = self.state_builder.build_state(events)
            .map_err(|e| WorkflowError::StateBuilderError(e.to_string()))?;
            
        // 生成检查点ID
        let checkpoint_id = format!("cp_{}_{}", workflow_id, Uuid::new_v4());
        
        // 计算验证哈希
        let hash = self.calculate_state_hash(&state);
        
        // 保存检查点
        self.checkpoint_store.save_checkpoint(
            workflow_id,
            &state,
            checkpoint_id.clone(),
            sequence,
            hash,
        ).await
        .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
        
        // 更新上次检查点时间和序列号
        {
            let mut last = self.last_checkpoint.write().await;
            last.insert(workflow_id.clone(), (Utc::now(), sequence));
        }
        
        // 重置事件计数
        {
            let mut counts = self.event_count.write().await;
            counts.insert(workflow_id.clone(), 0);
        }
        
        // 自动清理旧检查点
        if self.config.auto_prune {
            self.maybe_prune_checkpoints(workflow_id).await?;
        }
        
        Ok(checkpoint_id)
    }
    
    /// 创建增量检查点
    pub async fn create_incremental_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        sequence: u64,
    ) -> Result<String, WorkflowError> {
        // 获取最新基础检查点
        let latest_checkpoint = self.checkpoint_store.get_latest_checkpoint(workflow_id).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        let (base_state, base_sequence) = match latest_checkpoint {
            Some(cp) => cp,
            None => return Err(WorkflowError::NoCheckpointAvailable),
        };
        
        // 获取基础检查点ID
        let base_id = self.get_checkpoint_id_by_sequence(workflow_id, base_sequence).await?;
        
        // 获取新事件
        let new_events = self.event_store.get_events_after(workflow_id, base_sequence).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        if new_events.is_empty() {
            return Err(WorkflowError::NoEventsForIncremental);
        }
        
        // 构建当前状态
        let current_state = self.state_builder.build_state_from_base(base_state.clone(), new_events)
            .map_err(|e| WorkflowError::StateBuilderError(e.to_string()))?;
            
        // 计算状态差异
        let changes = self.calculate_state_diff(&base_state, &current_state)
            .map_err(|e| WorkflowError::StateBuilderError(e.to_string()))?;
            
        // 生成增量检查点ID
        let checkpoint_id = format!("icp_{}_{}", workflow_id, Uuid::new_v4());
        
        // 计算验证哈希
        let hash = self.calculate_changes_hash(&changes);
        
        // 创建增量检查点
        let incremental = IncrementalCheckpoint {
            id: checkpoint_id.clone(),
            workflow_id: workflow_id.clone(),
            base_checkpoint_id: base_id,
            sequence_number: sequence,
            created_at: Utc::now(),
            changes,
            verification_hash: hash,
        };
        
        // 保存增量检查点
        self.checkpoint_store.save_incremental_checkpoint(workflow_id, &incremental).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        // 更新事件计数
        {
            let mut counts = self.event_count.write().await;
            let count = counts.entry(workflow_id.clone()).or_insert(0);
            *count = 0;
        }
        
        Ok(checkpoint_id)
    }
    
    /// 确定检查点创建条件
    async fn should_checkpoint(
        &self,
        workflow_id: &WorkflowId,
        event: &WorkflowEvent,
    ) -> Result<bool, WorkflowError> {
        match &self.strategy {
            CheckpointStrategy::EveryNEvents(n) => {
                let count = {
                    let counts = self.event_count.read().await;
                    counts.get(workflow_id).copied().unwrap_or(0)
                };
                
                Ok(count >= *n)
            },
            CheckpointStrategy::TimeBased(interval) => {
                let last = {
                    let last_map = self.last_checkpoint.read().await;
                    last_map.get(workflow_id).map(|(time, _)| *time)
                };
                
                match last {
                    Some(last_time) => {
                        let elapsed = Utc::now() - last_time;
                        Ok(elapsed >= *interval)
                    },
                    None => Ok(true), // 首次创建检查点
                }
            },
            CheckpointStrategy::Hybrid { event_count, time_interval } => {
                let count = {
                    let counts = self.event_count.read().await;
                    counts.get(workflow_id).copied().unwrap_or(0)
                };
                
                let last = {
                    let last_map = self.last_checkpoint.read().await;
                    last_map.get(workflow_id).map(|(time, _)| *time)
                };
                
                match last {
                    Some(last_time) => {
                        let elapsed = Utc::now() - last_time;
                        Ok(count >= *event_count || elapsed >= *time_interval)
                    },
                    None => Ok(true), // 首次创建检查点
                }
            },
            CheckpointStrategy::AfterStateTransitions(transitions) => {
                // 检查事件是否触发状态转换
                match event {
                    WorkflowEvent::WorkflowStarted { .. } if transitions.contains(&"workflow_started".to_string()) => Ok(true),
                    WorkflowEvent::WorkflowCompleted { .. } if transitions.contains(&"workflow_completed".to_string()) => Ok(true),
                    WorkflowEvent::WorkflowFailed { .. } if transitions.contains(&"workflow_failed".to_string()) => Ok(true),
                    WorkflowEvent::StageCompleted { .. } if transitions.contains(&"stage_completed".to_string()) => Ok(true),
                    _ => Ok(false),
                }
            },
            CheckpointStrategy::Adaptive { min_events, max_events, min_interval, max_interval } => {
                // 动态计算检查点间隔
                let count = {
                    let counts = self.event_count.read().await;
                    counts.get(workflow_id).copied().unwrap_or(0)
                };
                
                let last = {
                    let last_map = self.last_checkpoint.read().await;
                    last_map.get(workflow_id).cloned()
                };
                
                match last {
                    Some((last_time, last_seq)) => {
                        let elapsed = Utc::now() - last_time;
                        
                        // 获取最近事件复杂度
                        let complexity = self.estimate_event_complexity(workflow_id, last_seq).await?;
                        
                        // 根据复杂度调整阈值
                        let adjusted_event_threshold = match complexity {
                            EventComplexity::Low => *max_events,
                            EventComplexity::Medium => (*min_events + *max_events) / 2,
                            EventComplexity::High => *min_events,
                        };
                        
                        let adjusted_time_threshold = match complexity {
                            EventComplexity::Low => *max_interval,
                            EventComplexity::Medium => Duration::from_secs(
                                (min_interval.as_secs() + max_interval.as_secs()) / 2
                            ),
                            EventComplexity::High => *min_interval,
                        };
                        
                        Ok(count >= adjusted_event_threshold || elapsed >= adjusted_time_threshold)
                    },
                    None => Ok(true), // 首次创建检查点
                }
            },
        }
    }
    
    /// 确定是否创建增量检查点
    async fn should_create_incremental(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<bool, WorkflowError> {
        if !self.config.use_incremental {
            return Ok(false);
        }
        
        // 检查是否有基础检查点
        let has_base = self.checkpoint_store.get_latest_checkpoint(workflow_id).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?
            .is_some();
            
        if !has_base {
            return Ok(false);
        }
        
        // 检查事件数量
        let count = {
            let counts = self.event_count.read().await;
            counts.get(workflow_id).copied().unwrap_or(0)
        };
        
        Ok(count >= self.config.incremental_interval)
    }
    
    /// 计算状态哈希
    fn calculate_state_hash(&self, state: &WorkflowState) -> String {
        use sha2::{Sha256, Digest};
        
        let mut hasher = Sha256::new();
        
        if let Ok(state_json) = serde_json::to_vec(state) {
            hasher.update(&state_json);
        }
        
        format!("{:x}", hasher.finalize())
    }
    
    /// 计算变更哈希
    fn calculate_changes_hash(&self, changes: &[StateChange]) -> String {
        use sha2::{Sha256, Digest};
        
        let mut hasher = Sha256::new();
        
        if let Ok(changes_json) = serde_json::to_vec(changes) {
            hasher.update(&changes_json);
        }
        
        format!("{:x}", hasher.finalize())
    }
    
    /// 计算状态差异
    fn calculate_state_diff(
        &self,
        base: &WorkflowState,
        current: &WorkflowState,
    ) -> Result<Vec<StateChange>, String> {
        // 序列化为JSON
        let base_json = serde_json::to_value(base)
            .map_err(|e| format!("Failed to serialize base state: {}", e))?;
            
        let current_json = serde_json::to_value(current)
            .map_err(|e| format!("Failed to serialize current state: {}", e))?;
            
        // 计算差异
        let patch = json_patch::diff(&base_json, &current_json);
        
        // 转换为状态变更
        let mut changes = Vec::with_capacity(patch.0.len());
        
        for op in patch.0 {
            match op {
                json_patch::PatchOperation::Add(add) => {
                    changes.push(StateChange {
                        path: add.path,
                        operation: ChangeOperation::Add,
                        value: Some(add.value),
                    });
                },
                json_patch::PatchOperation::Remove(remove) => {
                    changes.push(StateChange {
                        path: remove.path,
                        operation: ChangeOperation::Remove,
                        value: None,
                    });
                },
                json_patch::PatchOperation::Replace(replace) => {
                    changes.push(StateChange {
                        path: replace.path,
                        operation: ChangeOperation::Replace,
                        value: Some(replace.value),
                    });
                },
                json_patch::PatchOperation::Copy(copy) => {
                    changes.push(StateChange {
                        path: copy.path,
                        operation: ChangeOperation::Copy,
                        value: Some(serde_json::Value::String(copy.from)),
                    });
                },
                json_patch::PatchOperation::Move(mv) => {
                    changes.push(StateChange {
                        path: mv.path,
                        operation: ChangeOperation::Move,
                        value: Some(serde_json::Value::String(mv.from)),
                    });
                },
                json_patch::PatchOperation::Test(test) => {
                    changes.push(StateChange {
                        path: test.path,
                        operation: ChangeOperation::Test,
                        value: Some(test.value),
                    });
                },
            }
        }
        
        Ok(changes)
    }
    
    /// 获取检查点ID
    async fn get_checkpoint_id_by_sequence(
        &self,
        workflow_id: &WorkflowId,
        sequence: u64,
    ) -> Result<String, WorkflowError> {
        // 查询检查点ID
        // 注：这个方法在实际实现中需要添加到CheckpointStore接口中
        // 简化起见，这里使用假实现
        Ok(format!("cp_{}_{}", workflow_id, sequence))
    }
    
    /// 评估事件复杂度
    async fn estimate_event_complexity(
        &self,
        workflow_id: &WorkflowId,
        last_seq: u64,
    ) -> Result<EventComplexity, WorkflowError> {
        // 获取最新事件
        let events = self.event_store.get_events_after(workflow_id, last_seq).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        if events.is_empty() {
            return Ok(EventComplexity::Low);
        }
        
        // 评估复杂度
        let mut state_changes = 0;
        let mut data_size = 0;
        
        for (_, event) in &events {
            // 检查事件类型
            match event {
                WorkflowEvent::StageCompleted { .. } |
                WorkflowEvent::WorkflowCompleted { .. } |
                WorkflowEvent::WorkflowFailed { .. } => {
                    state_changes += 1;
                },
                _ => {},
            }
            
            // 估计数据大小
            if let Ok(json) = serde_json::to_string(event) {
                data_size += json.len();
            }
        }
        
        // 基于指标确定复杂度
        if state_changes > 5 || data_size > 50_000 {
            Ok(EventComplexity::High)
        } else if state_changes > 2 || data_size > 10_000 {
            Ok(EventComplexity::Medium)
        } else {
            Ok(EventComplexity::Low)
        }
    }
    
    /// 清理旧检查点
    async fn maybe_prune_checkpoints(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<(), WorkflowError> {
        // 检查检查点数量
        let count = self.checkpoint_store.get_checkpoint_count(workflow_id).await
            .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
            
        if count > self.config.max_checkpoints as u64 {
            // 清理
            self.checkpoint_store.prune_checkpoints(workflow_id, self.config.keep_latest).await
                .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
        }
        
        Ok(())
    }
}

/// 事件复杂度
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EventComplexity {
    Low,
    Medium,
    High,
}
```

### 6.3 状态重放与恢复

高效的状态重放和恢复机制：

```rust
/// 工作流状态构建器
#[async_trait]
pub trait StateBuilder: Send + Sync + 'static {
    /// 从事件列表构建工作流状态
    fn build_state(
        &self,
        events: Vec<(u64, WorkflowEvent)>,
    ) -> Result<WorkflowState, String>;
    
    /// 基于基础状态和增量事件构建状态
    fn build_state_from_base(
        &self,
        base_state: WorkflowState,
        events: Vec<(u64, WorkflowEvent)>,
    ) -> Result<WorkflowState, String>;
    
    /// 应用增量检查点变更
    fn apply_incremental_changes(
        &self,
        base_state: WorkflowState,
        changes: &[StateChange],
    ) -> Result<WorkflowState, String>;
    
    /// 从特定索引开始构建状态
    async fn build_state_from_index(
        &self,
        workflow_id: &WorkflowId,
        snapshot_index: Option<u64>,
    ) -> Result<(WorkflowState, u64), WorkflowError>;
}

/// 默认状态构建器
pub struct DefaultStateBuilder {
    event_store: Arc<dyn EventStore>,
    checkpoint_store: Arc<dyn CheckpointStore>,
    metrics: Arc<StateMetrics>,
}

impl DefaultStateBuilder {
    pub fn new(
        event_store: Arc<dyn EventStore>,
        checkpoint_store: Arc<dyn CheckpointStore>,
        metrics: Arc<StateMetrics>,
    ) -> Self {
        Self {
            event_store,
            checkpoint_store,
            metrics,
        }
    }
}

#[async_trait]
impl StateBuilder for DefaultStateBuilder {
    fn build_state(
        &self,
        events: Vec<(u64, WorkflowEvent)>,
    ) -> Result<WorkflowState, String> {
        if events.is_empty() {
            return Err("No events provided".to_string());
        }
        
        let start_time = Instant::now();
        
        // 初始化状态
        let (_, first_event) = &events[0];
        let mut state = match first_event {
            WorkflowEvent::WorkflowCreated { workflow_id, workflow_type, timestamp, .. } => {
                WorkflowState::Created {
                    workflow_id: workflow_id.clone(),
                    workflow_type: workflow_type.clone(),
                    created_at: *timestamp,
                }
            },
            _ => return Err("First event must be WorkflowCreated".to_string()),
        };
        
        // 应用所有事件
        for (_, event) in events.iter().skip(1) {
            state = self.apply_event(state, event)?;
        }
        
        let elapsed = start_time.elapsed();
        self.metrics.state_build_time.observe(elapsed.as_secs_f64());
        self.metrics.events_processed.add(events.len() as i64);
        
        Ok(state)
    }
    
    fn build_state_from_base(
        &self,
        mut base_state: WorkflowState,
        events: Vec<(u64, WorkflowEvent)>,
    ) -> Result<WorkflowState, String> {
        let start_time = Instant::now();
        
        // 应用所有事件
        for (_, event) in events {
            base_state = self.apply_event(base_state, &event)?;
        }
        
        let elapsed = start_time.elapsed();
        self.metrics.state_build_time.observe(elapsed.as_secs_f64());
        self.metrics.events_processed.add(events.len() as i64);
        
        Ok(base_state)
    }
    
    fn apply_incremental_changes(
        &self,
        mut base_state: WorkflowState,
        changes: &[StateChange],
    ) -> Result<WorkflowState, String> {
        let start_time = Instant::now();
        
        // 序列化基础状态到JSON
        let mut state_json = serde_json::to_value(&base_state)
            .map_err(|e| format!("Failed to serialize state: {}", e))?;
        
        // 应用每个变更
        for change in changes {
            match change.operation {
                ChangeOperation::Add => {
                    if let Some(value) = &change.value {
                        json_patch::patch(
                            &mut state_json,
                            &json_patch::Patch(vec![
                                json_patch::PatchOperation::Add(json_patch::AddOperation {
                                    path: change.path.clone(),
                                    value: value.clone(),
                                })
                            ])
                        ).map_err(|e| format!("Failed to apply add operation: {}", e))?;
                    }
                },
                ChangeOperation::Remove => {
                    json_patch::patch(
                        &mut state_json,
                        &json_patch::Patch(vec![
                            json_patch::PatchOperation::Remove(json_patch::RemoveOperation {
                                path: change.path.clone(),
                            })
                        ])
                    ).map_err(|e| format!("Failed to apply remove operation: {}", e))?;
                },
                ChangeOperation::Replace => {
                    if let Some(value) = &change.value {
                        json_patch::patch(
                            &mut state_json,
                            &json_patch::Patch(vec![
                                json_patch::PatchOperation::Replace(json_patch::ReplaceOperation {
                                    path: change.path.clone(),
                                    value: value.clone(),
                                })
                            ])
                        ).map_err(|e| format!("Failed to apply replace operation: {}", e))?;
                    }
                },
                ChangeOperation::Copy => {
                    if let Some(value) = &change.value {
                        if let Some(from) = value.as_str() {
                            json_patch::patch(
                                &mut state_json,
                                &json_patch::Patch(vec![
                                    json_patch::PatchOperation::Copy(json_patch::CopyOperation {
                                        path: change.path.clone(),
                                        from: from.to_string(),
                                    })
                                ])
                            ).map_err(|e| format!("Failed to apply copy operation: {}", e))?;
                        }
                    }
                },
                ChangeOperation::Move => {
                    if let Some(value) = &change.value {
                        if let Some(from) = value.as_str() {
                            json_patch::patch(
                                &mut state_json,
                                &json_patch::Patch(vec![
                                    json_patch::PatchOperation::Move(json_patch::MoveOperation {
                                        path: change.path.clone(),
                                        from: from.to_string(),
                                    })
                                ])
                            ).map_err(|e| format!("Failed to apply move operation: {}", e))?;
                        }
                    }
                },
                ChangeOperation::Test => {
                    if let Some(value) = &change.value {
                        json_patch::patch(
                            &mut state_json,
                            &json_patch::Patch(vec![
                                json_patch::PatchOperation::Test(json_patch::TestOperation {
                                    path: change.path.clone(),
                                    value: value.clone(),
                                })
                            ])
                        ).map_err(|e| format!("Failed to apply test operation: {}", e))?;
                    }
                },
            }
        }
        
        // 反序列化回状态对象
        base_state = serde_json::from_value(state_json)
            .map_err(|e| format!("Failed to deserialize state: {}", e))?;
            
        let elapsed = start_time.elapsed();
        self.metrics.incremental_apply_time.observe(elapsed.as_secs_f64());
        self.metrics.changes_applied.add(changes.len() as i64);
        
        Ok(base_state)
    }
    
    async fn build_state_from_index(
        &self,
        workflow_id: &WorkflowId,
        snapshot_index: Option<u64>,
    ) -> Result<(WorkflowState, u64), WorkflowError> {
        let start_time = Instant::now();
        
        // 策略：先尝试从最近检查点恢复，再重放后续事件
        
        // 获取检查点
        let checkpoint = match snapshot_index {
            Some(index) => {
                // 获取特定索引的检查点（这里需要实现从索引查询检查点的方法）
                // 简化实现：直接获取最近检查点
                self.checkpoint_store.get_latest_checkpoint(workflow_id).await
                    .map_err(|e| WorkflowError::StorageError(e.to_string()))?
            },
            None => {
                // 获取最近检查点
                self.checkpoint_store.get_latest_checkpoint(workflow_id).await
                    .map_err(|e| WorkflowError::StorageError(e.to_string()))?
            }
        };
        
        // 根据检查点情况处理
        match checkpoint {
            Some((checkpoint_state, checkpoint_seq)) => {
                // 获取检查点之后的事件
                let events = self.event_store.get_events_after(workflow_id, checkpoint_seq).await
                    .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
                    
                // 重放事件
                let final_state = if events.is_empty() {
                    checkpoint_state
                } else {
                    self.build_state_from_base(checkpoint_state, events.clone())
                        .map_err(|e| WorkflowError::StateBuilderError(e))?
                };
                
                // 计算新序列号
                let final_seq = if let Some((seq, _)) = events.last() {
                    *seq
                } else {
                    checkpoint_seq
                };
                
                let elapsed = start_time.elapsed();
                self.metrics.state_restore_time.observe(elapsed.as_secs_f64());
                
                Ok((final_state, final_seq))
            },
            None => {
                // 没有检查点，从头构建
                let events = self.event_store.get_workflow_events(workflow_id).await
                    .map_err(|e| WorkflowError::StorageError(e.to_string()))?;
                    
                if events.is_empty() {
                    return Err(WorkflowError::WorkflowNotFound(workflow_id.to_string()));
                }
                
                let state = self.build_state(events.clone())
                    .map_err(|e| WorkflowError::StateBuilderError(e))?;
                    
                let final_seq = events.last().map(|(seq, _)| *seq).unwrap_or(0);
                
                let elapsed = start_time.elapsed();
                self.metrics.state_restore_time.observe(elapsed.as_secs_f64());
                self.metrics.events_processed.add(events.len() as i64);
                
                Ok((state, final_seq))
            }
        }
    }
    
    // 辅助方法
    fn apply_event(&self, state: WorkflowState, event: &WorkflowEvent) -> Result<WorkflowState, String> {
        match (state, event) {
            // Created -> Started
            (
                WorkflowState::Created { workflow_id, workflow_type, .. },
                WorkflowEvent::WorkflowStarted { timestamp, .. }
            ) => {
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage: "initial".to_string(),
                    progress: 0.0,
                    started_at: *timestamp,
                    last_updated: *timestamp,
                })
            },
            
            // Running -> Stage transitions
            (
                WorkflowState::Running { workflow_id, workflow_type, started_at, .. },
                WorkflowEvent::StageStarted { stage_id, stage_name, timestamp, .. }
            ) => {
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage: stage_name.clone(),
                    progress: calculate_progress(stage_id),
                    started_at,
                    last_updated: *timestamp,
                })
            },
            
            (
                WorkflowState::Running { workflow_id, workflow_type, started_at, .. },
                WorkflowEvent::StageCompleted { stage_id, timestamp, .. }
            ) => {
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage: format!("after_{}", stage_id),
                    progress: calculate_progress(stage_id) + 0.1, // Increment progress
                    started_at,
                    last_updated: *timestamp,
                })
            },
            
            (
                WorkflowState::Running { workflow_id, workflow_type, started_at, .. },
                WorkflowEvent::StageFailed { stage_id, error, timestamp, .. }
            ) => {
                // Stage failed but workflow continues
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage: format!("failed_{}", stage_id),
                    progress: calculate_progress(stage_id),
                    started_at,
                    last_updated: *timestamp,
                })
            },
            
            // Running -> Terminal states
            (
                WorkflowState::Running { workflow_id, workflow_type, .. },
                WorkflowEvent::WorkflowCompleted { result, timestamp, .. }
            ) => {
                Ok(WorkflowState::Completed {
                    workflow_id,
                    workflow_type,
                    result: result.clone(),
                    completed_at: *timestamp,
                })
            },
            
            (
                WorkflowState::Running { workflow_id, workflow_type, .. },
                WorkflowEvent::WorkflowFailed { error, timestamp, .. }
            ) => {
                Ok(WorkflowState::Failed {
                    workflow_id,
                    workflow_type,
                    error: error.clone(),
                    failed_at: *timestamp,
                    can_retry: true, // Default to retryable
                })
            },
            
            (
                WorkflowState::Running { workflow_id, workflow_type, .. },
                WorkflowEvent::WorkflowCancelled { reason, timestamp, .. }
            ) => {
                Ok(WorkflowState::Cancelled {
                    workflow_id,
                    workflow_type,
                    reason: reason.clone(),
                    cancelled_at: *timestamp,
                })
            },
            
            // Running -> Suspended
            (
                WorkflowState::Running { workflow_id, workflow_type, current_stage, progress, started_at, .. },
                WorkflowEvent::WorkflowSuspended { reason, timestamp, .. }
            ) => {
                Ok(WorkflowState::Suspended {
                    workflow_id,
                    workflow_type,
                    reason: reason.clone(),
                    suspended_at: *timestamp,
                    current_stage,
                    progress,
                    started_at,
                })
            },
            
            // Suspended -> Running
            (
                WorkflowState::Suspended { workflow_id, workflow_type, current_stage, progress, started_at, .. },
                WorkflowEvent::WorkflowResumed { timestamp, .. }
            ) => {
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage,
                    progress,
                    started_at,
                    last_updated: *timestamp,
                })
            },
            
            // Failed -> Recovery
            (
                WorkflowState::Failed { workflow_id, workflow_type, .. },
                WorkflowEvent::WorkflowRecoveryStarted { recovery_strategy, timestamp, .. }
            ) => {
                Ok(WorkflowState::Running {
                    workflow_id,
                    workflow_type,
                    current_stage: format!("recovery_{}", recovery_strategy),
                    progress: 0.0, // Reset progress for recovery
                    started_at: *timestamp,
                    last_updated: *timestamp,
                })
            },
            
            // Handle priority changes - no state change
            (state, WorkflowEvent::WorkflowPriorityChanged { .. }) => {
                Ok(state)
            },
            
            // Default: state unchanged
            (state, _) => {
                Ok(state)
            }
        }
    }
}

// 辅助函数
fn calculate_progress(stage_id: &str) -> f32 {
    // 简化的进度计算，实际应根据工作流定义计算
    match stage_id {
        "validation" => 0.2,
        "processing" => 0.5,
        "finalization" => 0.8,
        _ => 0.0,
    }
}
```

### 6.4 ACID保证

我们的持久化设计提供了ACID（原子性、一致性、隔离性、持久性）保证：

```rust
/// 事务管理器
pub struct TransactionManager {
    /// 事件存储
    event_store: Arc<dyn EventStore>,
    /// 检查点存储
    checkpoint_store: Arc<dyn CheckpointStore>,
    /// 数据库连接池
    pool: PgPool,
    /// 锁管理器
    lock_manager: Arc<LockManager>,
    /// 指标
    metrics: Arc<TransactionMetrics>,
}

/// 事务隔离级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsolationLevel {
    /// 读未提交
    ReadUncommitted,
    /// 读已提交
    ReadCommitted,
    /// 可重复读
    RepeatableRead,
    /// 串行化
    Serializable,
}

/// 事务定义
pub struct Transaction<'a> {
    /// 事务ID
    id: String,
    /// 工作流ID
    workflow_id: WorkflowId,
    /// 隔离级别
    isolation_level: IsolationLevel,
    /// 数据库事务
    db_tx: Option<sqlx::Transaction<'a, sqlx::Postgres>>,
    /// 事件缓冲
    events: Vec<WorkflowEvent>,
    /// 事务状态
    state: TransactionState,
    /// 事务管理器
    manager: &'a TransactionManager,
    /// 开始时间
    start_time: Instant,
}

/// 事务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TransactionState {
    /// 活跃
    Active,
    /// 已提交
    Committed,
    /// 已回滚
    RolledBack,
}

/// 锁类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockType {
    /// 共享锁（读锁）
    Shared,
    /// 排他锁（写锁）
    Exclusive,
}

impl TransactionManager {
    pub async fn new(
        event_store: Arc<dyn EventStore>,
        checkpoint_store: Arc<dyn CheckpointStore>,
        database_url: &str,
        metrics: Arc<TransactionMetrics>,
    ) -> Result<Self, WorkflowError> {
        // 创建数据库连接池
        let pool = PgPool::connect(database_url)
            .await
            .map_err(|e| WorkflowError::DatabaseError(e.to_string()))?;
            
        // 创建锁管理器
        let lock_manager = Arc::new(LockManager::new());
        
        Ok(Self {
            event_store,
            checkpoint_store,
            pool,
            lock_manager,
            metrics,
        })
    }
    
    /// 开始新事务
    pub async fn begin_transaction<'a>(
        &'a self,
        workflow_id: &WorkflowId,
        isolation_level: IsolationLevel,
    ) -> Result<Transaction<'a>, WorkflowError> {
        // 创建数据库事务
        let db_tx = self.pool.begin().await
            .map_err(|e| WorkflowError::DatabaseError(e.to_string()))?;
            
        // 设置数据库隔离级别
        let isolation_sql = match isolation_level {
            IsolationLevel::ReadUncommitted => "SET TRANSACTION ISOLATION LEVEL READ UNCOMMITTED",
            IsolationLevel::ReadCommitted => "SET TRANSACTION ISOLATION LEVEL READ COMMITTED",
            IsolationLevel::RepeatableRead => "SET TRANSACTION ISOLATION LEVEL REPEATABLE READ",
            IsolationLevel::Serializable => "SET TRANSACTION ISOLATION LEVEL SERIALIZABLE",
        };
        
        sqlx::query(isolation_sql)
            .execute(&self.pool)
            .await
            .map_err(|e| WorkflowError::DatabaseError(e.to_string()))?;
            
        let transaction_id = format!("tx_{}", Uuid::new_v4());
        
        // 记录指标
        self.metrics.transaction_started(workflow_id);
        
        Ok(Transaction {
            id: transaction_id,
            workflow_id: workflow_id.clone(),
            isolation_level,
            db_tx: Some(db_tx),
            events: Vec::new(),
            state: TransactionState::Active,
            manager: self,
            start_time: Instant::now(),
        })
    }
}

impl<'a> Transaction<'a> {
    /// 添加事件到事务
    pub fn add_event(&mut self, event: WorkflowEvent) -> Result<(), WorkflowError> {
        if self.state != TransactionState::Active {
            return Err(WorkflowError::TransactionError(
                format!("Transaction {} is not active", self.id)
            ));
        }
        
        self.events.push(event);
        Ok(())
    }
    
    /// 获取工作流锁
    pub async fn acquire_lock(&self, lock_type: LockType) -> Result<(), WorkflowError> {
        match lock_type {
            LockType::Shared => {
                self.manager.lock_manager.acquire_shared_lock(&self.workflow_id).await?;
            },
            LockType::Exclusive => {
                self.manager.lock_manager.acquire_exclusive_lock(&self.workflow_id).await?;
            }
        }
        
        Ok(())
    }
    
    /// 释放工作流锁
    pub async fn release_lock(&self, lock_type: LockType) -> Result<(), WorkflowError> {
        match lock_type {
            LockType::Shared => {
                self.manager.lock_manager.release_shared_lock(&self.workflow_id).await?;
            },
            LockType::Exclusive => {
                self.manager.lock_manager.release_exclusive_lock(&self.workflow_id).await?;
            }
        }
        
        Ok(())
    }
    
    /// 提交事务
    pub async fn commit(mut self) -> Result<Vec<u64>, WorkflowError> {
        if self.state != TransactionState::Active {
            return Err(WorkflowError::TransactionError(
                format!("Transaction {} is not active", self.id)
            ));
        }
        
        if self.events.is_empty() {
            // 空事务，直接提交
            if let Some(db_tx) = self.db_tx.take() {
                db_tx.commit().await
                    .map_err(|e| WorkflowError::DatabaseError(e.to_string()))?;
            }
            
            self.state = TransactionState::Committed;
            
            // 记录指标
            self.manager.metrics.transaction_completed(&self.workflow_id, self.start_time.elapsed());
            
            return Ok(Vec::new());
        }
        
        // 获取数据库事务
        let db_tx = self.db_tx.take().ok_or_else(|| WorkflowError::TransactionError(
            format!("Transaction {} has no database transaction", self.id)
        ))?;
        
        // 批量添加事件
        let mut sequence_numbers = Vec::with_capacity(self.events.len());
        
        // 开始批量处理
        let batch_result = self.manager.event_store.batch_append_events(
            &self.workflow_id,
            self.events.clone(),
            Some(db_tx),
        ).await;
        
        match batch_result {
            Ok((sequences, committed_tx)) => {
                // 更新状态
                self.state = TransactionState::Committed;
                sequence_numbers = sequences;
                
                // 记录指标
                self.manager.metrics.transaction_completed(
                    &self.workflow_id,
                    self.start_time.elapsed()
                );
                self.manager.metrics.events_committed.add(self.events.len() as i64);
                
                // 检查是否需要创建检查点
                let checkpoint_manager = self.manager.checkpoint_manager();
                
                for (seq, event) in sequence_numbers.iter().zip(self.events.iter()) {
                    checkpoint_manager.handle_event(&self.workflow_id, event, *seq).await?;
                }
            },
            Err(e) => {
                // 事务已经被回滚
                self.state = TransactionState::RolledBack;
                
                // 记录指标
                self.manager.metrics.transaction_failed(
                    &self.workflow_id,
                    self.start_time.elapsed(),
                    "append_events_failed"
                );
                
                return Err(WorkflowError::from(e));
            }
        }
        
        Ok(sequence_numbers)
    }
    
    /// 回滚事务
    pub async fn rollback(mut self) -> Result<(), WorkflowError> {
        if self.state != TransactionState::Active {
            return Err(WorkflowError::TransactionError(
                format!("Transaction {} is not active", self.id)
            ));
        }
        
        // 回滚数据库事务
        if let Some(db_tx) = self.db_tx.take() {
            db_tx.rollback().await
                .map_err(|e| WorkflowError::DatabaseError(e.to_string()))?;
        }
        
        // 更新状态
        self.state = TransactionState::RolledBack;
        
        // 记录指标
        self.manager.metrics.transaction_rolled_back(
            &self.workflow_id,
            self.start_time.elapsed()
        );
        
        Ok(())
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if self.state == TransactionState::Active {
            // 事务未显式提交或回滚
            self.manager.metrics.transaction_leaked(&self.workflow_id);
            log::warn!("Transaction {} was dropped without commit or rollback", self.id);
            
            // 注意：这里我们不能异步回滚事务，只能记录警告
        }
    }
}

/// 锁管理器
pub struct LockManager {
    /// 工作流共享锁
    shared_locks: RwLock<HashMap<WorkflowId, u32>>,
    /// 工作流排他锁
    exclusive_locks: RwLock<HashSet<WorkflowId>>,
    /// 锁等待队列
    wait_queues: RwLock<HashMap<WorkflowId, Mutex<()>>>,
}

impl LockManager {
    pub fn new() -> Self {
        Self {
            shared_locks: RwLock::new(HashMap::new()),
            exclusive_locks: RwLock::new(HashSet::new()),
            wait_queues: RwLock::new(HashMap::new()),
        }
    }
    
    /// 获取共享锁
    pub async fn acquire_shared_lock(&self, workflow_id: &WorkflowId) -> Result<(), WorkflowError> {
        // 检查是否有排他锁
        {
            let exclusive = self.exclusive_locks.read().await;
            if exclusive.contains(workflow_id) {
                // 等待排他锁释放
                let queue = self.get_wait_queue(workflow_id).await;
                let _lock = queue.lock().await;
            }
        }
        
        // 增加共享锁计数
        let mut shared = self.shared_locks.write().await;
        let count = shared.entry(workflow_id.clone()).or_insert(0);
        *count += 1;
        
        Ok(())
    }
    
    /// 释放共享锁
    pub async fn release_shared_lock(&self, workflow_id: &WorkflowId) -> Result<(), WorkflowError> {
        let mut shared = self.shared_locks.write().await;
        
        if let Some(count) = shared.get_mut(workflow_id) {
            *count -= 1;
            if *count == 0 {
                shared.remove(workflow_id);
                
                // 唤醒等待队列
                self.notify_waiters(workflow_id).await;
            }
            Ok(())
        } else {
            Err(WorkflowError::LockError(format!(
                "No shared lock to release for workflow {}",
                workflow_id
            )))
        }
    }
    
    /// 获取排他锁
    pub async fn acquire_exclusive_lock(&self, workflow_id: &WorkflowId) -> Result<(), WorkflowError> {
        // 检查是否有其他锁
        {
            let shared = self.shared_locks.read().await;
            let exclusive = self.exclusive_locks.read().await;
            
            if shared.contains_key(workflow_id) || exclusive.contains(workflow_id) {
                // 等待锁释放
                let queue = self.get_wait_queue(workflow_id).await;
                let _lock = queue.lock().await;
            }
        }
        
        // 获取排他锁
        let mut exclusive = self.exclusive_locks.write().await;
        exclusive.insert(workflow_id.clone());
        
        Ok(())
    }
    
    /// 释放排他锁
    pub async fn release_exclusive_lock(&self, workflow_id: &WorkflowId) -> Result<(), WorkflowError> {
        let mut exclusive = self.exclusive_locks.write().await;
        
        if exclusive.remove(workflow_id) {
            // 唤醒等待队列
            self.notify_waiters(workflow_id).await;
            Ok(())
        } else {
            Err(WorkflowError::LockError(format!(
                "No exclusive lock to release for workflow {}",
                workflow_id
            )))
        }
    }
    
    /// 获取等待队列
    async fn get_wait_queue(&self, workflow_id: &WorkflowId) -> Arc<Mutex<()>> {
        let mut queues = self.wait_queues.write().await;
        queues.entry(workflow_id.clone())
            .or_insert_with(|| Arc::new(Mutex::new(())))
            .clone()
    }
    
    /// 通知等待者
    async fn notify_waiters(&self, workflow_id: &WorkflowId) {
        // 移除等待队列，强制释放互斥锁，唤醒等待者
        let mut queues = self.wait_queues.write().await;
        queues.remove(workflow_id);
    }
}
```

## 7. 可观测性框架

### 7.1 日志系统设计

```rust
/// 日志上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogContext {
    /// 工作流ID
    pub workflow_id: Option<WorkflowId>,
    /// 请求ID
    pub request_id: Option<String>,
    /// 用户ID
    pub user_id: Option<String>,
    /// 租户ID
    pub tenant_id: Option<String>,
    /// 追踪ID
    pub trace_id: Option<String>,
    /// Span ID
    pub span_id: Option<String>,
    /// 组件名称
    pub component: String,
    /// 额外上下文
    pub extra: HashMap<String, String>,
}

/// 可上下文日志记录器
pub struct ContextualLogger {
    /// 默认上下文
    default_context: RwLock<LogContext>,
    /// 日志层级
    level: log::Level,
    /// 输出格式
    format: LogFormat,
    /// 额外记录器
    recorders: Vec<Box<dyn LogRecorder>>,
}

/// 日志格式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogFormat {
    /// JSON格式
    Json,
    /// 文本格式
    Text,
}

/// 日志记录器接口
#[async_trait]
pub trait LogRecorder: Send + Sync {
    /// 记录日志
    async fn record(&self, record: &LogRecord) -> Result<(), LogError>;
    
    /// 刷新缓冲区
    async fn flush(&self) -> Result<(), LogError>;
}

/// 日志记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogRecord {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 日志级别
    pub level: String,
    /// 消息
    pub message: String,
    /// 上下文
    pub context: LogContext,
    /// 源文件
    pub file: Option<String>,
    /// 行号
    pub line: Option<u32>,
    /// 目标模块
    pub target: String,
}

impl ContextualLogger {
    pub fn new(
        component: &str,
        level: log::Level,
        format: LogFormat,
    ) -> Self {
        let default_context = LogContext {
            workflow_id: None,
            request_id: None,
            user_id: None,
            tenant_id: None,
            trace_id: None,
            span_id: None,
            component: component.to_string(),
            extra: HashMap::new(),
        };
        
        Self {
            default_context: RwLock::new(default_context),
            level,
            format,
            recorders: Vec::new(),
        }
    }
    
    /// 添加记录器
    pub fn add_recorder(&mut self, recorder: Box<dyn LogRecorder>) {
        self.recorders.push(recorder);
    }
    
    /// 设置默认上下文
    pub async fn set_default_context(&self, context: LogContext) {
        let mut default = self.default_context.write().await;
        *default = context;
    }
    
    /// 更新默认上下文
    pub async fn update_default_context<F>(&self, f: F)
    where
        F: FnOnce(&mut LogContext) + Send,
    {
        let mut default = self.default_context.write().await;
        f(&mut default);
    }
    
    /// 创建派生日志记录器
    pub async fn with_context<F>(&self, f: F) -> ContextualLogger
    where
        F: FnOnce(&mut LogContext) + Send,
    {
        let mut context = self.default_context.read().await.clone();
        f(&mut context);
        
        let mut logger = ContextualLogger {
            default_context: RwLock::new(context),
            level: self.level,
            format: self.format,
            recorders: Vec::new(),
        };
        
        // 复制记录器
        for recorder in &self.recorders {
            logger.recorders.push(recorder.clone_box());
        }
        
        logger
    }
    
    /// 带工作流ID的日志记录器
    pub async fn with_workflow(&self, workflow_id: &WorkflowId) -> ContextualLogger {
        self.with_context(|ctx| {
            ctx.workflow_id = Some(workflow_id.clone());
        }).await
    }
    
    /// 带追踪信息的日志记录器
    pub async fn with_trace(
        &self,
        trace_id: &str,
        span_id: &str,
    ) -> ContextualLogger {
        self.with_context(|ctx| {
            ctx.trace_id = Some(trace_id.to_string());
            ctx.span_id = Some(span_id.to_string());
        }).await
    }
    
    /// 记录日志
    pub async fn log(
        &self,
        level: log::Level,
        target: &str,
        message: &str,
        file: Option<&str>,
        line: Option<u32>,
    ) {
        // 检查日志级别
        if level > self.level {
            return;
        }
        
        // 创建日志记录
        let context = self.default_context.read().await.clone();
        
        let record = LogRecord {
            timestamp: Utc::now(),
            level: level.to_string(),
            message: message.to_string(),
            context,
            file: file.map(String::from),
            line,
            target: target.to_string(),
        };
        
        // 发送到所有记录器
        for recorder in &self.recorders {
            if let Err(e) = recorder.record(&record).await {
                eprintln!("Error recording log: {}", e);
            }
        }
    }
    
    /// 记录调试日志
    pub async fn debug(&self, message: &str, file: Option<&str>, line: Option<u32>) {
        self.log(log::Level::Debug, "workflow_engine", message, file, line).await;
    }
    
    /// 记录信息日志
    pub async fn info(&self, message: &str, file: Option<&str>, line: Option<u32>) {
        self.log(log::Level::Info, "workflow_engine", message, file, line).await;
    }
    
    /// 记录警告日志
    pub async fn warn(&self, message: &str, file: Option<&str>, line: Option<u32>) {
        self.log(log::Level::Warn, "workflow_engine", message, file, line).await;
    }
    
    /// 记录错误日志
    pub async fn error(&self, message: &str, file: Option<&str>, line: Option<u32>) {
        self.log(log::Level::Error, "workflow_engine", message, file, line).await;
    }
    
    /// 刷新所有记录器
    pub async fn flush(&self) {
        for recorder in &self.recorders {
            if let Err(e) = recorder.flush().await {
                eprintln!("Error flushing logs: {}", e);
            }
        }
    }
}

/// 日志错误
#[derive(Debug, thiserror::Error)]
pub enum LogError {
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Configuration error: {0}")]
    ConfigurationError(String),
}

/// 文件日志记录器
pub struct FileLogRecorder {
    /// 文件路径
    path: PathBuf,
    /// 日志格式
    format: LogFormat,
    /// 文件句柄
    file: RwLock<Option<File>>,
    /// 缓冲大小
    buffer_size: usize,
    /// 日志缓冲区
    buffer: RwLock<Vec<LogRecord>>,
    /// 上次刷新时间
    last_flush: RwLock<Instant>,
    /// 自动刷新间隔
    flush_interval: Duration,
}

impl FileLogRecorder {
    pub fn new(
        path: PathBuf,
        format: LogFormat,
        buffer_size: usize,
        flush_interval: Duration,
    ) -> Result<Self, LogError> {
        // 确保目录存在
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(LogError::IoError)?;
        }
        
        // 打开文件
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(LogError::IoError)?;
            
        Ok(Self {
            path,
            format,
            file: RwLock::new(Some(file)),
            buffer_size,
            buffer: RwLock::new(Vec::with_capacity(buffer_size)),
            last_flush: RwLock::new(Instant::now()),
            flush_interval,
        })
    }
    
    /// 格式化日志记录
    fn format_record(&self, record: &LogRecord) -> Result<String, LogError> {
        match self.format {
            LogFormat::Json => {
                serde_json::to_string(record)
                    .map_err(|e| LogError::SerializationError(e.to_string()))
                    .map(|s| s + "\n")
            },
            LogFormat::Text => {
                let workflow_id = record.context.workflow_id
                    .as_ref()
                    .map(|id| id.to_string())
                    .unwrap_or_else(|| "-".to_string());
                    
                let trace_id = record.context.trace_id
                    .as_ref()
                    .map(|id| id.to_string())
                    .unwrap_or_else(|| "-".to_string());
                    
                let location = match (record.file.as_ref(), record.line) {
                    (Some(file), Some(line)) => format!("{}:{}", file, line),
                    _ => "-".to_string(),
                };
                
                Ok(format!(
                    "[{}] [{}] [{}] [{}] [{}] {} - {}\n",
                    record.timestamp.to_rfc3339(),
                    record.level,
                    workflow_id,
                    trace_id,
                    record.context.component,
                    location,
                    record.message
                ))
            }
        }
    }
    
    /// 检查是否应该刷新
    async fn should_flush(&self) -> bool {
        let buffer = self.buffer.read().await;
        let last_flush = self.last_flush.read().await;
        
        buffer.len() >= self.buffer_size || last_flush.elapsed() >= self.flush_interval
    }
}

#[async_trait]
impl LogRecorder for FileLogRecorder {
    async fn record(&self, record: &LogRecord) -> Result<(), LogError> {
        // 添加到缓冲区
        {
            let mut buffer = self.buffer.write().await;
            buffer.push(record.clone());
        }
        
        // 检查是否需要刷新
        if self.should_flush().await {
            self.flush().await?;
        }
        
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), LogError> {
        // 获取并清空缓冲区
        let records = {
            let mut buffer = self.buffer.write().await;
            std::mem::take(&mut *buffer)
        };
        
        if records.is_empty() {
            return Ok(());
        }
        
        // 格式化所有记录
        let formatted: Result<Vec<String>, LogError> = records.iter()
            .map(|record| self.format_record(record))
            .collect();
            
        let content = formatted?.join("");
        
        // 写入文件
        {
            let mut file_handle = self.file.write().await;
            
            if let Some(file) = file_handle.as_mut() {
                file.write_all(content.as_bytes())
                    .map_err(LogError::IoError)?;
                    
                file.flush()
                    .map_err(LogError::IoError)?;
            } else {
                // 文件已关闭，重新打开
                let file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&self.path)
                    .map_err(LogError::IoError)?;
                    
                *file_handle = Some(file);
                
                if let Some(file) = file_handle.as_mut() {
                    file.write_all(content.as_bytes())
                        .map_err(LogError::IoError)?;
                        
                    file.flush()
                        .map_err(LogError::IoError)?;
                }
            }
        }
        
        // 更新上次刷新时间
        let mut last_flush = self.last_flush.write().await;
        *last_flush = Instant::now();
        
        Ok(())
    }
}

/// 控制台日志记录器
pub struct ConsoleLogRecorder {
    /// 日志格式
    format: LogFormat,
    /// 彩色输出
    colored: bool,
}

impl ConsoleLogRecorder {
    pub fn new(format: LogFormat, colored: bool) -> Self {
        Self {
            format,
            colored,
        }
    }
    
    /// 格式化日志记录
    fn format_record(&self, record: &LogRecord) -> Result<String, LogError> {
        match self.format {
            LogFormat::Json => {
                serde_json::to_string(record)
                    .map_err(|e| LogError::SerializationError(e.to_string()))
            },
            LogFormat::Text => {
                let workflow_id = record.context.workflow_id
                    .as_ref()
                    .map(|id| id.to_string())
                    .unwrap_or_else(|| "-".to_string());
                    
                let level_str = record.level.to_string();
                
                let level_colored = if self.colored {
                    match level_str.as_str() {
                        "ERROR" => format!("\x1b[31m{}\x1b[0m", level_str),
                        "WARN" => format!("\x1b[33m{}\x1b[0m", level_str),
                        "INFO" => format!("\x1b[32m{}\x1b[0m", level_str),
                        "DEBUG" => format!("\x1b[36m{}\x1b[0m", level_str),
                        "TRACE" => format!("\x1b[35m{}\x1b[0m", level_str),
                        _ => level_str,
                    }
                } else {
                    level_str
                };
                
                Ok(format!(
                    "[{}] [{}] [{}] [{}] {}",
                    record.timestamp.format("%Y-%m-%d %H:%M:%S%.3f"),
                    level_colored,
                    workflow_id,
                    record.context.component,
                    record.message
                ))
            }
        }
    }
}

#[async_trait]
impl LogRecorder for ConsoleLogRecorder {
    async fn record(&self, record: &LogRecord) -> Result<(), LogError> {
        let formatted = self.format_record(record)?;
        
        match record.level.as_str() {
            "ERROR" => eprintln!("{}", formatted),
            _ => println!("{}", formatted),
        }
        
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), LogError> {
        // 控制台输出不需要刷新
        Ok(())
    }
}

/// 日志宏
#[macro_export]
macro_rules! log_debug {
    ($logger:expr, $($arg:tt)*) => {
        $logger.debug(&format!($($arg)*), Some(file!()), Some(line!())).await
    };
}

#[macro_export]
macro_rules! log_info {
    ($logger:expr, $($arg:tt)*) => {
        $logger.info(&format!($($arg)*), Some(file!()), Some(line!())).await
    };
}

#[macro_export]
macro_rules! log_warn {
    ($logger:expr, $($arg:tt)*) => {
        $logger.warn(&format!($($arg)*), Some(file!()), Some(line!())).await
    };
}

#[macro_export]
macro_rules! log_error {
    ($logger:expr, $($arg:tt)*) => {
        $logger.error(&format!($($arg)*), Some(file!()), Some(line!())).await
    };
}
```

### 7.2 指标收集与暴露

```rust
/// 指标类型
#[derive(Debug, Clone)]
pub enum MetricType {
    /// 计数器 - 单调递增
    Counter,
    /// 仪表盘 - 可增可减
    Gauge,
    /// 直方图 - 统计分布
    Histogram,
    /// 摘要 - 百分位数
    Summary,
}

/// 指标标签
pub type Labels = HashMap<String, String>;

/// 指标值
#[derive(Debug, Clone)]
pub enum MetricValue {
    /// 计数器/仪表盘值
    Single(f64),
    /// 直方图/摘要观测值
    Observations(Vec<f64>),
    /// 摘要分位数
    Quantiles(HashMap<f64, f64>),
}

/// 指标
#[derive(Debug, Clone)]
pub struct Metric {
    /// 名称
    pub name: String,
    /// 帮助文本
    pub help: String,
    /// 类型
    pub metric_type: MetricType,
    /// 值
    pub value: MetricValue,
    /// 标签
    pub labels: Labels,
    /// 时间戳
    pub timestamp: Option<DateTime<Utc>>,
}

/// 指标注册表
pub struct MetricRegistry {
    /// 指标集合
    metrics: RwLock<HashMap<String, Metric>>,
    /// 标签建议器
    label_suggestor: RwLock<HashMap<String, HashSet<String>>>,
    /// 指标记录器
    recorders: Vec<Box<dyn MetricRecorder>>,
    /// 组件名称
    component: String,
}

/// 指标记录器
#[async_trait]
pub trait MetricRecorder: Send + Sync {
    /// 记录指标
    async fn record(&self, metrics: &[Metric]) -> Result<(), MetricError>;
    
    /// 刷新
    async fn flush(&self) -> Result<(), MetricError>;
}

/// 指标错误
#[derive(Debug, thiserror::Error)]
pub enum MetricError {
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Invalid metric type: {0}")]
    InvalidMetricType(String),
}

impl MetricRegistry {
    pub fn new(component: &str) -> Self {
        Self {
            metrics: RwLock::new(HashMap::new()),
            label_suggestor: RwLock::new(HashMap::new()),
            recorders: Vec::new(),
            component: component.to_string(),
        }
    }
    
    /// 添加指标记录器
    pub fn add_recorder(&mut self, recorder: Box<dyn MetricRecorder>) {
        self.recorders.push(recorder);
    }
    
    /// 创建计数器
    pub async fn create_counter(
        &self,
        name: &str,
        help: &str,
        labels: Labels,
    ) -> Counter {
        // 记录标签建议
        self.record_label_suggestions(name, &labels).await;
        
        // 创建计数器
        let metric = Metric {
            name: format!("{}_{}", self.component, name),
            help: help.to_string(),
            metric_type: MetricType::Counter,
            value: MetricValue::Single(0.0),
            labels,
            timestamp: Some(Utc::now()),
        };
        
        let full_name = self.get_full_metric_name(&metric.name, &metric.labels);
        
        {
            let mut metrics = self.metrics.write().await;
            metrics.insert(full_name.clone(), metric);
        }
        
        Counter {
            registry: self,
            name: format!("{}_{}", self.component, name),
            labels: HashMap::new(),
        }
    }
    
    /// 创建仪表盘
    pub async fn create_gauge(
        &self,
        name: &str,
        help: &str,
        labels: Labels,
    ) -> Gauge {
        // 记录标签建议
        self.record_label_suggestions(name, &labels).await;
        
        // 创建仪表盘
        let metric = Metric {
            name: format!("{}_{}", self.component, name),
            help: help.to_string(),
            metric_type: MetricType::Gauge,
            value: MetricValue::Single(0.0),
            labels,
            timestamp: Some(Utc::now()),
        };
        
        let full_name = self.get_full_metric_name(&metric.name, &metric.labels);
        
        {
            let mut metrics = self.metrics.write().await;
            metrics.insert(full_name.clone(), metric);
        }
        
        Gauge {
            registry: self,
            name: format!("{}_{}", self.component, name),
            labels: HashMap::new(),
        }
    }
    
    /// 创建直方图
    pub async fn create_histogram(
        &self,
        name: &str,
        help: &str,
        buckets: Vec<f64>,
        labels: Labels,
    ) -> Histogram {
        // 记录标签建议
        self.record_label_suggestions(name, &labels).await;
        
        // 创建直方图
        let metric = Metric {
            name: format!("{}_{}", self.component, name),
            help: help.to_string(),
            metric_type: MetricType::Histogram,
            value: MetricValue::Observations(Vec::new()),
            labels,
            timestamp: Some(Utc::now()),
        };
        
        let full_name = self.get_full_metric_name(&metric.name, &metric.labels);
        
        {
            let mut metrics = self.metrics.write().await;
            metrics.insert(full_name.clone(), metric);
        }
        
        Histogram {
            registry: self,
            name: format!("{}_{}", self.component, name),
            labels: HashMap::new(),
            buckets,
        }
    }
    
    /// 获取指标的完整名称（包含标签）
    fn get_full_metric_name(&self, name: &str, labels: &Labels) -> String {
        if labels.is_empty() {
            name.to_string()
        } else {
            // 排序标签以确保一致性
            let mut label_pairs: Vec<(&String, &String)> = labels.iter().collect();
            label_pairs.sort_by(|a, b| a.0.cmp(b.0));
            
            let label_str: String = label_pairs.iter()
                .map(|(k, v)| format!("{}=\"{}\"", k, v))
                .collect::<Vec<_>>()
                .join(",");
                
            format!("{}:{{{}}}", name, label_str)
        }
    }
    
    /// 记录标签建议
    async fn record_label_suggestions(&self, name: &str, labels: &Labels) {
        let metric_name = format!("{}_{}", self.component, name);
        let mut suggestor = self.label_suggestor.write().await;
        
        for (key, _) in labels {
            let entry = suggestor.entry(metric_name.clone()).or_insert_with(HashSet::new);
            entry.insert(key.clone());
        }
    }
    
    /// 获取所有指标
    pub async fn get_all_metrics(&self) -> Vec<Metric> {
        let metrics = self.metrics.read().await;
        metrics.values().cloned().collect()
    }
    
    /// 获取特定指标
    pub async fn get_metric(&self, name: &str, labels: &Labels) -> Option<Metric> {
        let metrics = self.metrics.read().await;
        let full_name = self.get_full_metric_name(name, labels);
        metrics.get(&full_name).cloned()
    }
    
    /// 更新计数器值
    pub async fn increment_counter(
        &self,
        name: &str,
        labels: &Labels,
        value: f64,
    ) -> Result<(), MetricError> {
        let full_name = self.get_full_metric_name(name, labels);
        
        {
            let mut metrics = self.metrics.write().await;
            
            if let Some(metric) = metrics.get_mut(&full_name) {
                if let MetricValue::Single(current) = &mut metric.value {
                    *current += value;
                    metric.timestamp = Some(Utc::now());
                } else {
                    return Err(MetricError::InvalidMetricType(
                        format!("Metric {} is not a counter", name)
                    ));
                }
            } else {
                // 自动创建指标
                let metric = Metric {
                    name: name.to_string(),
                    help: "Auto-created counter".to_string(),
                    metric_type: MetricType::Counter,
                    value: MetricValue::Single(value),
                    labels: labels.clone(),
                    timestamp: Some(Utc::now()),
                };
                
                metrics.insert(full_name.clone(), metric);
            }
        }
        
        // 记录指标
        self.record_metrics().await?;
        
        Ok(())
    }
    
    /// 更新仪表盘值
    pub async fn set_gauge(
        &self,
        name: &str,
        labels: &Labels,
        value: f64,
    ) -> Result<(), MetricError> {
        let full_name = self.get_full_metric_name(name, labels);
        
        {
            let mut metrics = self.metrics.write().await;
            
            if let Some(metric) = metrics.get_mut(&full_name) {
                if let MetricValue::Single(current) = &mut metric.value {
                    *current = value;
                    metric.timestamp = Some(Utc::now());
                } else {
                    return Err(MetricError::InvalidMetricType(
                        format!("Metric {} is not a gauge", name)
                    ));
                }
            } else {
                // 自动创建指标
                let metric = Metric {
                    name: name.to_string(),
                    help: "Auto-created gauge".to_string(),
                    metric_type: MetricType::Gauge,
                    value: MetricValue::Single(value),
                    labels: labels.clone(),
                    timestamp: Some(Utc::now()),
                };
                
                metrics.insert(full_name.clone(), metric);
            }
        }
        
        // 记录指标
        self.record_metrics().await?;
        
        Ok(())
    }
    
    /// 添加直方图观测值
    pub async fn observe_histogram(
        &self,
        name: &str,
        labels: &Labels,
        value: f64,
    ) -> Result<(), MetricError> {
        let full_name = self.get_full_metric_name(name, labels);
        
        {
            let mut metrics = self.metrics.write().await;
            
            if let Some(metric) = metrics.get_mut(&full_name) {
                if let MetricValue::Observations(observations) = &mut metric.value {
                    observations.push(value);
                    metric.timestamp = Some(Utc::now());
                } else {
                    return Err(MetricError::InvalidMetricType(
                        format!("Metric {} is not a histogram", name)
                    ));
                }
            } else {
                // 自动创建指标
                let metric = Metric {
                    name: name.to_string(),
                    help: "Auto-created histogram".to_string(),
                    metric_type: MetricType::Histogram,
                    value: MetricValue::Observations(vec![value]),
                    labels: labels.clone(),
                    timestamp: Some(Utc::now()),
                };
                
                metrics.insert(full_name.clone(), metric);
            }
        }
        
        // 记录指标
        self.record_metrics().await?;
        
        Ok(())
    }
    
    /// 记录指标到所有记录器
    async fn record_metrics(&self) -> Result<(), MetricError> {
        let metrics = self.get_all_metrics().await;
        
        for recorder in &self.recorders {
            recorder.record(&metrics).await?;
        }
        
        Ok(())
    }
    
    /// 刷新所有记录器
    pub async fn flush(&self) -> Result<(), MetricError> {
        for recorder in &self.recorders {
            recorder.flush().await?;
        }
        
        Ok(())
    }
}

/// 计数器
pub struct Counter<'a> {
    registry: &'a MetricRegistry,
    name: String,
    labels: Labels,
}

impl<'a> Counter<'a> {
    /// 设置标签
    pub fn with_labels(mut self, labels: Labels) -> Self {
        self.labels = labels;
        self
    }
    
    /// 增加计数器
    pub async fn inc(&self) -> Result<(), MetricError> {
        self.registry.increment_counter(&self.name, &self.labels, 1.0).await
    }
    
    /// 增加指定值
    pub async fn add(&self, value: f64) -> Result<(), MetricError> {
        self.registry.increment_counter(&self.name, &self.labels, value).await
    }
}

/// 仪表盘
pub struct Gauge<'a> {
    registry: &'a MetricRegistry,
    name: String,
    labels: Labels,
}

impl<'a> Gauge<'a> {
    /// 设置标签
    pub fn with_labels(mut self, labels: Labels) -> Self {
        self.labels = labels;
        self
    }
    
    /// 设置值
    pub async fn set(&self, value: f64) -> Result<(), MetricError> {
        self.registry.set_gauge(&self.name, &self.labels, value).await
    }
    
    /// 增加值
    pub async fn inc(&self, value: f64) -> Result<(), MetricError> {
        let current = match self.registry.get_metric(&self.name, &self.labels).await {
            Some(metric) => {
                if let MetricValue::Single(value) = metric.value {
                    value
                } else {
                    0.0
                }
            },
            None => 0.0,
        };
        
        self.registry.set_gauge(&self.name, &self.labels, current + value).await
    }
    
    /// 减少值
    pub async fn dec(&self, value: f64) -> Result<(), MetricError> {
        let current = match self.registry.get_metric(&self.name, &self.labels).await {
            Some(metric) => {
                if let MetricValue::Single(value) = metric.value {
                    value
                } else {
                    0.0
                }
            },
            None => 0.0,
        };
        
        self.registry.set_gauge(&self.name, &self.labels, current - value).await
    }
}

/// 直方图
pub struct Histogram<'a> {
    registry: &'a MetricRegistry,
    name: String,
    labels: Labels,
    buckets: Vec<f64>,
}

impl<'a> Histogram<'a> {
    /// 设置标签
    pub fn with_labels(mut self, labels: Labels) -> Self {
        self.labels = labels;
        self
    }
    
    /// 添加观测值
    pub async fn observe(&self, value: f64) -> Result<(), MetricError> {
        self.registry.observe_histogram(&self.name, &self.labels, value).await
    }
    
    /// 创建计时器
    pub fn start_timer(&self) -> HistogramTimer<'a> {
        HistogramTimer {
            histogram: self,
            start: Instant::now(),
        }
    }
}

/// 直方图计时器
pub struct HistogramTimer<'a> {
    histogram: &'a Histogram<'a>,
    start: Instant,
}

impl<'a> HistogramTimer<'a> {
    /// 观测并结束计时
    pub async fn observe_and_end(self) -> Result<Duration, MetricError> {
        let elapsed = self.start.elapsed();
        self.histogram.observe(elapsed.as_secs_f64()).await?;
        Ok(elapsed)
    }
}

/// Prometheus 指标记录器
pub struct PrometheusRecorder {
    /// 端口
    port: u16,
    /// 路径
    path: String,
    /// 缓存的指标字符串
    cached_metrics: RwLock<String>,
    /// 最后更新时间
    last_update: RwLock<Instant>,
    /// 缓存过期时间
    cache_ttl: Duration,
    /// 服务器句柄
    server_handle: Option<JoinHandle<()>>,
}

impl PrometheusRecorder {
    pub fn new(port: u16, path: String, cache_ttl: Duration) -> Self {
        Self {
            port,
            path,
            cached_metrics: RwLock::new(String::new()),
            last_update: RwLock::new(Instant::now()),
            cache_ttl,
            server_handle: None,
        }
    }
    
    /// 启动服务器
    pub async fn start_server(&mut self) -> Result<(), MetricError> {
        let port = self.port;
        let path = self.path.clone();
        let cached_metrics = self.cached_metrics.clone();
        let last_update = self.last_update.clone();
        let cache_ttl = self.cache_ttl;
        
        let server = HttpServer::new(move || {
            App::new()
                .route(&path, web::get().to(move || {
                    let cached = cached_metrics.clone();
                    let last = last_update.clone();
                    
                    async move {
                        // 检查缓存是否有效
                        let is_cache_valid = {
                            let last_time = last.read().await;
                            last_time.elapsed() < cache_ttl
                        };
                        
                        if is_cache_valid {
                            let cache = cached.read().await;
                            HttpResponse::Ok()
                                .content_type("text/plain")
                                .body(cache.clone())
                        } else {
                            // 缓存已过期，但我们仍返回旧数据
                            // 实际更新将在 record() 方法中进行
                            let cache = cached.read().await;
                            HttpResponse::Ok()
                                .content_type("text/plain")
                                .body(cache.clone())
                        }
                    }
                }))
        })
        .bind(format!("0.0.0.0:{}", port))
        .map_err(|e| MetricError::IoError(e))?
        .run();
        
        let handle = tokio::spawn(async move {
            let _ = server.await;
        });
        
        self.server_handle = Some(handle);
        
        Ok(())
    }
    
    /// 将指标转换为 Prometheus 格式字符串
    fn format_metrics(&self, metrics: &[Metric]) -> String {
        let mut result = String::new();
        
        for metric in metrics {
            // 添加指标帮助信息和类型
            result.push_str(&format!("# HELP {} {}\n", metric.name, metric.help));
            
            let type_str = match metric.metric_type {
                MetricType::Counter => "counter",
                MetricType::Gauge => "gauge",
                MetricType::Histogram => "histogram",
                MetricType::Summary => "summary",
            };
            
            result.push_str(&format!("# TYPE {} {}\n", metric.name, type_str));
            
            // 添加指标值
            match (&metric.metric_type, &metric.value) {
                (MetricType::Counter, MetricValue::Single(value)) |
                (MetricType::Gauge, MetricValue::Single(value)) => {
                    // 添加标签
                    let label_str = if metric.labels.is_empty() {
                        "".to_string()
                    } else {
                        let label_strings: Vec<String> = metric.labels.iter()
                            .map(|(k, v)| format!("{}=\"{}\"", k, v))
                            .collect();
                        format!("{{{}}}", label_strings.join(","))
                    };
                    
                    result.push_str(&format!("{}{} {}", metric.name, label_str, value));
                    
                    // 添加时间戳
                    if let Some(timestamp) = &metric.timestamp {
                        result.push_str(&format!(" {}", timestamp.timestamp_millis()));
                    }
                    
                    result.push('\n');
                },
                (MetricType::Histogram, MetricValue::Observations(observations)) => {
                    if observations.is_empty() {
                        continue;
                    }
                    
                    // 计算直方图统计
                    let mut sum = 0.0;
                    let mut count = 0;
                    
                    // 假设直方图有预定义的桶
                    let buckets = [0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0];
                    let mut bucket_counts = HashMap::new();
                    
                    for &value in observations {
                        sum += value;
                        count += 1;
                        
                        for &bucket in &buckets {
                            if value <= bucket {
                                *bucket_counts.entry(bucket).or_insert(0) += 1;
                            }
                        }
                    }
                    
                    // 添加桶
                    let base_label_str = if metric.labels.is_empty() {
                        "".to_string()
                    } else {
                        let label_strings: Vec<String> = metric.labels.iter()
                            .map(|(k, v)| format!("{}=\"{}\"", k, v))
                            .collect();
                        format!("{},", label_strings.join(","))
                    };
                    
                    let mut cumulative = 0;
                    for &bucket in &buckets {
                        let bucket_count = bucket_counts.get(&bucket).unwrap_or(&0);
                        cumulative += bucket_count;
                        
                        result.push_str(&format!(
                            "{}_bucket{{{}le=\"{}\"}} {}\n",
                            metric.name,
                            base_label_str,
                            bucket,
                            cumulative
                        ));
                    }
                    
                    // 添加 +Inf 桶
                    result.push_str(&format!(
                        "{}_bucket{{{}le=\"+Inf\"}} {}\n",
                        metric.name,
                        base_label_str,
                        count
                    ));
                    
                    // 添加 sum 和 count
                    result.push_str(&format!(
                        "{}_sum{{{}}} {}\n",
                        metric.name,
                        base_label_str.trim_end_matches(','),
                        sum
                    ));
                    
                    result.push_str(&format!(
                        "{}_count{{{}}} {}\n",
                        metric.name,
                        base_label_str.trim_end_matches(','),
                        count
                    ));
                },
                (MetricType::Summary, MetricValue::Quantiles(quantiles)) => {
                    if quantiles.is_empty() {
                        continue;
                    }
                    
                    // 添加标签
                    let base_label_str = if metric.labels.is_empty() {
                        "".to_string()
                    } else {
                        let label_strings: Vec<String> = metric.labels.iter()
                            .map(|(k, v)| format!("{}=\"{}\"", k, v))
                            .collect();
                        format!("{},", label_strings.join(","))
                    };
                    
                    // 添加分位数
                    for (&quantile, &value) in quantiles {
                        result.push_str(&format!(
                            "{}{{{}quantile=\"{}\"}} {}\n",
                            metric.name,
                            base_label_str,
                            quantile,
                            value
                        ));
                    }
                    
                    // 添加 sum 和 count (假设在 quantiles 中存在)
                    if let Some(&sum) = quantiles.get(&-1.0) {
                        result.push_str(&format!(
                            "{}_sum{{{}}} {}\n",
                            metric.name,
                            base_label_str.trim_end_matches(','),
                            sum
                        ));
                    }
                    
                    if let Some(&count) = quantiles.get(&-2.0) {
                        result.push_str(&format!(
                            "{}_count{{{}}} {}\n",
                            metric.name,
                            base_label_str.trim_end_matches(','),
                            count as i64
                        ));
                    }
                },
                _ => {
                    // 不匹配的类型/值组合
                    continue;
                }
            }
        }
        
        result
    }
}

#[async_trait]
impl MetricRecorder for PrometheusRecorder {
    async fn record(&self, metrics: &[Metric]) -> Result<(), MetricError> {
        // 更新缓存条件：每次记录都更新
        let formatted = self.format_metrics(metrics);
        
        {
            let mut cached = self.cached_metrics.write().await;
            *cached = formatted;
            
            let mut last_time = self.last_update.write().await;
            *last_time = Instant::now();
        }
        
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), MetricError> {
        // 对于Prometheus，不需要特殊处理
        Ok(())
    }
}

/// 用于聚合指标的键
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MetricKey {
    name: String,
    labels: HashMap<String, String>,
}

impl MetricKey {
    fn new(name: &str, labels: &Labels) -> Self {
        Self {
            name: name.to_string(),
            labels: labels.clone(),
        }
    }
}

/// 工作流引擎指标
pub struct WorkflowEngineMetrics {
    registry: Arc<MetricRegistry>,
    
    // 工作流执行指标
    workflows_started: Counter<'static>,
    workflows_completed: Counter<'static>,
    workflows_failed: Counter<'static>,
    workflow_duration: Histogram<'static>,
    
    // 活动执行指标
    activities_executed: Counter<'static>,
    activities_succeeded: Counter<'static>,
    activities_failed: Counter<'static>,
    activity_duration: Histogram<'static>,
    
    // 系统资源指标
    memory_usage: Gauge<'static>,
    cpu_usage: Gauge<'static>,
    disk_io: Gauge<'static>,
    
    // 调度器指标
    scheduler_queue_size: Gauge<'static>,
    scheduler_tasks_processed: Counter<'static>,
    
    // 存储指标
    events_stored: Counter<'static>,
    storage_latency: Histogram<'static>,
    storage_errors: Counter<'static>,
}

impl WorkflowEngineMetrics {
    pub async fn new(registry: Arc<MetricRegistry>) -> Self {
        let workflows_started = registry.create_counter(
            "workflows_started_total",
            "Total number of workflows started",
            HashMap::new(),
        ).await;
        
        let workflows_completed = registry.create_counter(
            "workflows_completed_total",
            "Total number of workflows completed",
            HashMap::new(),
        ).await;
        
        let workflows_failed = registry.create_counter(
            "workflows_failed_total",
            "Total number of workflows failed",
            HashMap::new(),
        ).await;
        
        let workflow_duration = registry.create_histogram(
            "workflow_duration_seconds",
            "Workflow execution duration in seconds",
            vec![0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0, 300.0, 600.0, 1800.0, 3600.0],
            HashMap::new(),
        ).await;
        
        let activities_executed = registry.create_counter(
            "activities_executed_total",
            "Total number of activities executed",
            HashMap::new(),
        ).await;
        
        let activities_succeeded = registry.create_counter(
            "activities_succeeded_total",
            "Total number of activities succeeded",
            HashMap::new(),
        ).await;
        
        let activities_failed = registry.create_counter(
            "activities_failed_total",
            "Total number of activities failed",
            HashMap::new(),
        ).await;
        
        let activity_duration = registry.create_histogram(
            "activity_duration_seconds",
            "Activity execution duration in seconds",
            vec![0.01, 0.05, 0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0, 300.0],
            HashMap::new(),
        ).await;
        
        let memory_usage = registry.create_gauge(
            "memory_usage_bytes",
            "Memory usage in bytes",
            HashMap::new(),
        ).await;
        
        let cpu_usage = registry.create_gauge(
            "cpu_usage_percent",
            "CPU usage in percentage",
            HashMap::new(),
        ).await;
        
        let disk_io = registry.create_gauge(
            "disk_io_bytes",
            "Disk I/O in bytes per second",
            HashMap::new(),
        ).await;
        
        let scheduler_queue_size = registry.create_gauge(
            "scheduler_queue_size",
            "Number of tasks in scheduler queue",
            HashMap::new(),
        ).await;
        
        let scheduler_tasks_processed = registry.create_counter(
            "scheduler_tasks_processed_total",
            "Total number of tasks processed by scheduler",
            HashMap::new(),
        ).await;
        
        let events_stored = registry.create_counter(
            "events_stored_total",
            "Total number of events stored",
            HashMap::new(),
        ).await;
        
        let storage_latency = registry.create_histogram(
            "storage_latency_seconds",
            "Storage operation latency in seconds",
            vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0],
            HashMap::new(),
        ).await;
        
        let storage_errors = registry.create_counter(
            "storage_errors_total",
            "Total number of storage errors",
            HashMap::new(),
        ).await;
        
        Self {
            registry,
            workflows_started,
            workflows_completed,
            workflows_failed,
            workflow_duration,
            activities_executed,
            activities_succeeded,
            activities_failed,
            activity_duration,
            memory_usage,
            cpu_usage,
            disk_io,
            scheduler_queue_size,
            scheduler_tasks_processed,
            events_stored,
            storage_latency,
            storage_errors,
        }
    }
    
    // 工作流指标记录方法
    
    pub async fn workflow_started(&self, workflow_id: &WorkflowId, workflow_type: &str) -> Result<(), MetricError> {
        let labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        self.workflows_started.with_labels(labels).inc().await
    }
    
    pub async fn workflow_completed(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
        duration: Duration,
    ) -> Result<(), MetricError> {
        let type_labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        let status_labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
            "status".to_string() => "completed".to_string(),
        };
        
        // 记录完成计数
        self.workflows_completed.with_labels(type_labels).inc().await?;
        
        // 记录执行时间
        self.workflow_duration
            .with_labels(status_labels)
            .observe(duration.as_secs_f64())
            .await
    }
    
    pub async fn workflow_failed(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
        error_type: &str,
        duration: Duration,
    ) -> Result<(), MetricError> {
        let type_labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        let error_labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
            "error_type".to_string() => error_type.to_string(),
        };
        
        let duration_labels = hashmap! {
            "workflow_type".to_string() => workflow_type.to_string(),
            "status".to_string() => "failed".to_string(),
        };
        
        // 记录失败计数
        self.workflows_failed.with_labels(type_labels).inc().await?;
        
        // 记录特定错误类型的失败
        self.workflows_failed.with_labels(error_labels).inc().await?;
        
        // 记录执行时间
        self.workflow_duration
            .with_labels(duration_labels)
            .observe(duration.as_secs_f64())
            .await
    }
    
    // 活动指标记录方法
    
    pub async fn activity_executed(
        &self,
        activity_type: &str,
        workflow_type: &str,
    ) -> Result<(), MetricError> {
        let labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        self.activities_executed.with_labels(labels).inc().await
    }
    
    pub async fn activity_succeeded(
        &self,
        activity_type: &str,
        workflow_type: &str,
        duration: Duration,
    ) -> Result<(), MetricError> {
        let success_labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        let duration_labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
            "status".to_string() => "succeeded".to_string(),
        };
        
        // 记录成功计数
        self.activities_succeeded.with_labels(success_labels).inc().await?;
        
        // 记录执行时间
        self.activity_duration
            .with_labels(duration_labels)
            .observe(duration.as_secs_f64())
            .await
    }
    
    pub async fn activity_failed(
        &self,
        activity_type: &str,
        workflow_type: &str,
        error_type: &str,
        duration: Duration,
    ) -> Result<(), MetricError> {
        let fail_labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
        };
        
        let error_labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
            "error_type".to_string() => error_type.to_string(),
        };
        
        let duration_labels = hashmap! {
            "activity_type".to_string() => activity_type.to_string(),
            "workflow_type".to_string() => workflow_type.to_string(),
            "status".to_string() => "failed".to_string(),
        };
        
        // 记录失败计数
        self.activities_failed.with_labels(fail_labels).inc().await?;
        
        // 记录特定错误类型的失败
        self.activities_failed.with_labels(error_labels).inc().await?;
        
        // 记录执行时间
        self.activity_duration
            .with_labels(duration_labels)
            .observe(duration.as_secs_f64())
            .await
    }
    
    // 系统资源指标记录方法
    
    pub async fn update_memory_usage(&self, bytes: u64) -> Result<(), MetricError> {
        self.memory_usage.set(bytes as f64).await
    }
    
    pub async fn update_cpu_usage(&self, percent: f64) -> Result<(), MetricError> {
        self.cpu_usage.set(percent).await
    }
    
    pub async fn update_disk_io(&self, bytes_per_second: f64) -> Result<(), MetricError> {
        self.disk_io.set(bytes_per_second).await
    }
    
    // 调度器指标记录方法
    
    pub async fn update_scheduler_queue_size(&self, size: usize) -> Result<(), MetricError> {
        self.scheduler_queue_size.set(size as f64).await
    }
    
    pub async fn scheduler_task_processed(&self) -> Result<(), MetricError> {
        self.scheduler_tasks_processed.inc().await
    }
    
    // 存储指标记录方法
    
    pub async fn event_stored(&self, event_type: &str) -> Result<(), MetricError> {
        let labels = hashmap! {
            "event_type".to_string() => event_type.to_string(),
        };
        
        self.events_stored.with_labels(labels).inc().await
    }
    
    pub async fn record_storage_latency(
        &self,
        operation: &str,
        duration: Duration,
    ) -> Result<(), MetricError> {
        let labels = hashmap! {
            "operation".to_string() => operation.to_string(),
        };
        
        self.storage_latency
            .with_labels(labels)
            .observe(duration.as_secs_f64())
            .await
    }
    
    pub async fn storage_error(&self, operation: &str, error_type: &str) -> Result<(), MetricError> {
        let labels = hashmap! {
            "operation".to_string() => operation.to_string(),
            "error_type".to_string() => error_type.to_string(),
        };
        
        self.storage_errors.with_labels(labels).inc().await
    }
}
```

### 7.3 分布式追踪实现

```rust
/// 追踪上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceContext {
    /// 追踪ID
    pub trace_id: String,
    /// Span ID
    pub span_id: String,
    /// 父Span ID
    pub parent_span_id: Option<String>,
    /// 采样决策
    pub sampled: bool,
    /// 追踪标签
    pub baggage: HashMap<String, String>,
}

/// Span状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpanStatus {
    /// 成功
    Ok,
    /// 错误
    Error(String),
    /// 未设置
    Unset,
}

/// Span类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    /// 内部操作
    Internal,
    /// 服务端操作
    Server,
    /// 客户端操作
    Client,
    /// 生产者操作
    Producer,
    /// 消费者操作
    Consumer,
}

/// Span
pub struct Span {
    /// 上下文
    ctx: TraceContext,
    /// 名称
    name: String,
    /// 类型
    kind: SpanKind,
    /// 开始时间
    start_time: DateTime<Utc>,
    /// 结束时间
    end_time: Option<DateTime<Utc>>,
    /// 属性
    attributes: HashMap<String, Value>,
    /// 事件
    events: Vec<SpanEvent>,
    /// 状态
    status: SpanStatus,
    /// 追踪器
    tracer: Arc<dyn Tracer>,
}

/// Span事件
#[derive(Debug, Clone)]
pub struct SpanEvent {
    /// 名称
    pub name: String,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 属性
    pub attributes: HashMap<String, Value>,
}

/// 属性值
#[derive(Debug, Clone)]
pub enum Value {
    /// 字符串
    String(String),
    /// 布尔值
    Bool(bool),
    /// 整数
    Int(i64),
    /// 浮点数
    Float(f64),
    /// 字符串数组
    StringArray(Vec<String>),
    /// 布尔数组
    BoolArray(Vec<bool>),
    /// 整数数组
    IntArray(Vec<i64>),
    /// 浮点数组
    FloatArray(Vec<f64>),
}

/// 追踪器接口
#[async_trait]
pub trait Tracer: Send + Sync {
    /// 创建Span
    fn create_span(
        &self,
        name: &str,
        parent_context: Option<&TraceContext>,
        kind: SpanKind,
        attributes: HashMap<String, Value>,
    ) -> Box<dyn SpanHandle>;
    
    /// 获取当前Span
    fn current_span(&self) -> Option<Box<dyn SpanHandle>>;
    
    /// 设置当前Span
    fn set_current_span(&self, span: Box<dyn SpanHandle>);
    
    /// 记录完成的Span
    async fn record_span(&self, span: CompletedSpan) -> Result<(), TraceError>;
    
    /// 注入上下文到载体
    fn inject_context<C: Carrier>(&self, context: &TraceContext, carrier: &mut C) -> Result<(), TraceError>;
    
    /// 从载体提取上下文
    fn extract_context<C: Carrier>(&self, carrier: &C) -> Result<Option<TraceContext>, TraceError>;
    
    /// 关闭追踪器
    async fn close(&self) -> Result<(), TraceError>;
}

/// 载体特质
pub trait Carrier {
    /// 获取值
    fn get(&self, key: &str) -> Option<&str>;
    
    /// 设置值
    fn set(&mut self, key: &str, value: String);
    
    /// 删除值
    fn remove(&mut self, key: &str);
    
    /// 获取所有键
    fn keys(&self) -> Vec<&str>;
}

/// Span处理接口
pub trait SpanHandle: Send + Sync {
    /// 获取上下文
    fn context(&self) -> &TraceContext;
    
    /// 设置属性
    fn set_attribute(&mut self, key: &str, value: Value);
    
    /// 添加事件
    fn add_event(&mut self, name: &str, attributes: HashMap<String, Value>);
    
    /// 设置状态
    fn set_status(&mut self, status: SpanStatus);
    
    /// 结束Span
    fn end(&mut self);
    
    /// 是否已结束
    fn is_recording(&self) -> bool;
}

/// 已完成的Span
#[derive(Debug, Clone)]
pub struct CompletedSpan {
    /// 上下文
    pub context: TraceContext,
    /// 名称
    pub name: String,
    /// 类型
    pub kind: SpanKind,
    /// 开始时间
    pub start_time: DateTime<Utc>,
    /// 结束时间
    pub end_time: DateTime<Utc>,
    /// 属性
    pub attributes: HashMap<String, Value>,
    /// 事件
    pub events: Vec<SpanEvent>,
    /// 状态
    pub status: SpanStatus,
    /// 父Span上下文
    pub parent_context: Option<TraceContext>,
}

/// 追踪错误
#[derive(Debug, thiserror::Error)]
pub enum TraceError {
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Invalid span: {0}")]
    InvalidSpan(String),
    
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Configuration error: {0}")]
    ConfigurationError(String),
}

/// OpenTelemetry追踪器
pub struct OpenTelemetryTracer {
    /// 服务名称
    service_name: String,
    /// 采样器
    sampler: Box<dyn Sampler>,
    /// ID生成器
    id_generator: Box<dyn IdGenerator>,
    /// 导出器
    exporter: Box<dyn SpanExporter>,
    /// 当前Span
    current_span: RwLock<Option<Box<dyn SpanHandle>>>,
    /// 导出缓冲区
    export_buffer: RwLock<Vec<CompletedSpan>>,
    /// 导出线程
    export_task: Option<JoinHandle<()>>,
    /// 导出触发器
    export_trigger: broadcast::Sender<()>,
    /// 配置
    config: TracerConfig,
}

/// 采样器
pub trait Sampler: Send + Sync {
    /// 决定是否采样
    fn should_sample(
        &self,
        trace_id: &str,
        span_name: &str,
        parent_context: Option<&TraceContext>,
    ) -> bool;
}

/// 始终采样
pub struct AlwaysOnSampler;

impl Sampler for AlwaysOnSampler {
    fn should_sample(
        &self,
        _trace_id: &str,
        _span_name: &str,
        _parent_context: Option<&TraceContext>,
    ) -> bool {
        true
    }
}

/// 始终不采样
pub struct AlwaysOffSampler;

impl Sampler for AlwaysOffSampler {
    fn should_sample(
        &self,
        _trace_id: &str,
        _span_name: &str,
        _parent_context: Option<&TraceContext>,
    ) -> bool {
        false
    }
}

/// 概率采样
pub struct ProbabilistcSampler {
    /// 采样率
    rate: f64,
}

impl ProbabilistcSampler {
    pub fn new(rate: f64) -> Self {
        Self {
            rate: rate.clamp(0.0, 1.0),
        }
    }
}

impl Sampler for ProbabilistcSampler {
    fn should_sample(
        &self,
        trace_id: &str,
        _span_name: &str,
        parent_context: Option<&TraceContext>,
    ) -> bool {
        // 父上下文已有采样决定，遵循父决定
        if let Some(ctx) = parent_context {
            return ctx.sampled;
        }
        
        // 基于trace_id首部字节的概率采样
        if let Ok(id_bytes) = hex::decode(trace_id) {
            if id_bytes.len() >= 8 {
                let value = u64::from_be_bytes([
                    id_bytes[0], id_bytes[1], id_bytes[2], id_bytes[3],
                    id_bytes[4], id_bytes[5], id_bytes[6], id_bytes[7],
                ]);
                
                let max = u64::MAX as f64;
                let threshold = (self.rate * max) as u64;
                
                return value < threshold;
            }
        }
        
        // 默认不采样
        false
    }
}

/// ID生成器
pub trait IdGenerator: Send + Sync {
    /// 生成追踪ID
    fn generate_trace_id(&self) -> String;
    
    /// 生成SpanID
    fn generate_span_id(&self) -> String;
}

/// 随机ID生成器
pub struct RandomIdGenerator;

impl IdGenerator for RandomIdGenerator {
    fn generate_trace_id(&self) -> String {
        let mut bytes = [0u8; 16];
        thread_rng().fill(&mut bytes);
        hex::encode(bytes)
    }
    
    fn generate_span_id(&self) -> String {
        let mut bytes = [0u8; 8];
        thread_rng().fill(&mut bytes);
        hex::encode(bytes)
    }
}

/// Span导出器
#[async_trait]
pub trait SpanExporter: Send + Sync {
    /// 导出Span
    async fn export(&self, spans: Vec<CompletedSpan>) -> Result<(), TraceError>;
    
    /// 关闭导出器
    async fn shutdown(&self) -> Result<(), TraceError>;
}

/// 追踪器配置
#[derive(Debug, Clone)]
pub struct TracerConfig {
    /// 最大缓冲区大小
    pub max_buffer_size: usize,
    /// 导出间隔
    pub export_interval: Duration,
    /// 关闭超时
    pub shutdown_timeout: Duration,
}

impl Default for TracerConfig {
    fn default() -> Self {
        Self {
            max_buffer_size: 512,
            export_interval: Duration::from_secs(5),
            shutdown_timeout: Duration::from_secs(30),
        }
    }
}

impl OpenTelemetryTracer {
    pub fn new(
        service_name: &str,
        sampler: Box<dyn Sampler>,
        id_generator: Box<dyn IdGenerator>,
        exporter: Box<dyn SpanExporter>,
        config: TracerConfig,
    ) -> Self {
        let (tx, _) = broadcast::channel(1);
        
        Self {
            service_name: service_name.to_string(),
            sampler,
            id_generator,
            exporter,
            current_span: RwLock::new(None),
            export_buffer: RwLock::new(Vec::with_capacity(config.max_buffer_size)),
            export_task: None,
            export_trigger: tx,
            config,
        }
    }
    
    /// 启动导出任务
    pub fn start_export_task(&mut self) {
        let export_interval = self.config.export_interval;
        let max_buffer_size = self.config.max_buffer_size;
        let mut rx = self.export_trigger.subscribe();
        let exporter = Arc::clone(&self.exporter);
        let buffer = Arc::clone(&self.export_buffer);
        
        let task = tokio::spawn(async move {
            let mut interval = tokio::time::interval(export_interval);
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        // 定期导出
                        Self::export_spans(buffer.clone(), exporter.clone()).await;
                    }
                    result = rx.recv() => {
                        if result.is_err() {
                            // 通道关闭，退出任务
                            break;
                        }
                        
                        // 手动触发导出
                        Self::export_spans(buffer.clone(), exporter.clone()).await;
                    }
                }
            }
        });
        
        self.export_task = Some(task);
    }
    
    /// 导出Span
    async fn export_spans(
        buffer: Arc<RwLock<Vec<CompletedSpan>>>,
        exporter: Arc<dyn SpanExporter>,
    ) {
        // 获取并清空缓冲区
        let spans = {
            let mut buffer_guard = buffer.write().await;
            if buffer_guard.is_empty() {
                return;
            }
            std::mem::take(&mut *buffer_guard)
        };
        
        // 导出Span
        if let Err(e) = exporter.export(spans).await {
            log::error!("Failed to export spans: {}", e);
        }
    }
    
    /// 创建根Span
    fn create_root_span(
        &self,
        name: &str,
        kind: SpanKind,
        attributes: HashMap<String, Value>,
    ) -> Span {
        // 生成IDs
        let trace_id = self.id_generator.generate_trace_id();
        let span_id = self.id_generator.generate_span_id();
        
        // 采样决策
        let sampled = self.sampler.should_sample(&trace_id, name, None);
        
        // 创建上下文
        let ctx = TraceContext {
            trace_id,
            span_id,
            parent_span_id: None,
            sampled,
            baggage: HashMap::new(),
        };
        
        // 创建Span
        Span {
            ctx,
            name: name.to_string(),
            kind,
            start_time: Utc::now(),
            end_time: None,
            attributes,
            events: Vec::new(),
            status: SpanStatus::Unset,
            tracer: self,
        }
    }
    
    /// 创建子Span
    fn create_child_span(
        &self,
        name: &str,
        parent_ctx: &TraceContext,
        kind: SpanKind,
        attributes: HashMap<String, Value>,
    ) -> Span {
        // 生成SpanID
        let span_id = self.id_generator.generate_span_id();
        
        // 创建上下文
        let ctx = TraceContext {
            trace_id: parent_ctx.trace_id.clone(),
            span_id,
            parent_span_id: Some(parent_ctx.span_id.clone()),
            sampled: parent_ctx.sampled,
            baggage: parent_ctx.baggage.clone(),
        };
        
        // 创建Span
        Span {
            ctx,
            name: name.to_string(),
            kind,
            start_time: Utc::now(),
            end_time: None,
            attributes,
            events: Vec::new(),
            status: SpanStatus::Unset,
            tracer: self,
        }
    }
}

#[async_trait]
impl Tracer for OpenTelemetryTracer {
    fn create_span(
        &self,
        name: &str,
        parent_context: Option<&TraceContext>,
        kind: SpanKind,
        attributes: HashMap<String, Value>,
    ) -> Box<dyn SpanHandle> {
        // 添加默认属性
        let mut all_attributes = attributes;
        all_attributes.insert("service.name".to_string(), Value::String(self.service_name.clone()));
        
        // 创建Span
        let span = match parent_context {
            Some(parent_ctx) => self.create_child_span(name, parent_ctx, kind, all_attributes),
            None => self.create_root_span(name, kind, all_attributes),
        };
        
        Box::new(span)
    }
    
    fn current_span(&self) -> Option<Box<dyn SpanHandle>> {
        let current = self.current_span.read().unwrap();
        current.as_ref().map(|s| s.clone())
    }
    
    fn set_current_span(&self, span: Box<dyn SpanHandle>) {
        let mut current = self.current_span.write().unwrap();
        *current = Some(span);
    }
    
    async fn record_span(&self, span: CompletedSpan) -> Result<(), TraceError> {
        // 检查采样决策
        if !span.context.sampled {
            return Ok(());
        }
        
        // 添加到缓冲区
        {
            let mut buffer = self.export_buffer.write().await;
            buffer.push(span);
            
            // 检查是否需要立即导出
            if buffer.len() >= self.config.max_buffer_size {
                drop(buffer); // 释放锁
                let _ = self.export_trigger.send(());
            }
        }
        
        Ok(())
    }
    
    fn inject_context<C: Carrier>(&self, context: &TraceContext, carrier: &mut C) -> Result<(), TraceError> {
        // W3C Trace Context格式
        let traceparent = format!(
            "00-{}-{}-{:02}",
            context.trace_id,
            context.span_id,
            if context.sampled { 01 } else { 00 }
        );
        
        carrier.set("traceparent", traceparent);
        
        // 添加baggage
        if !context.baggage.is_empty() {
            let baggage = context.baggage.iter()
                .map(|(k, v)| format!("{}={}", k, v))
                .collect::<Vec<_>>()
                .join(",");
                
            carrier.set("baggage", baggage);
        }
        
        Ok(())
    }
    
    fn extract_context<C: Carrier>(&self, carrier: &C) -> Result<Option<TraceContext>, TraceError> {
        // 尝试提取W3C Trace Context
        let traceparent = match carrier.get("traceparent") {
            Some(value) => value,
            None => return Ok(None),
        };
        
        // 解析traceparent
        // 格式: 00-<trace-id>-<span-id>-<flags>
        let parts: Vec<&str> = traceparent.split('-').collect();
        if parts.len() != 4 {
            return Err(TraceError::ConfigurationError(format!(
                "Invalid traceparent format: {}", traceparent
            )));
        }
        
        let trace_id = parts[1].to_string();
        let span_id = parts[2].to_string();
        let flags = u8::from_str_radix(parts[3], 16)
            .map_err(|e| TraceError::ConfigurationError(format!(
                "Invalid flags: {}", e
            )))?;
            
        let sampled = (flags & 0x01) == 0x01;
        
        // 提取baggage
        let mut baggage = HashMap::new();
        if let Some(baggage_header) = carrier.get("baggage") {
            for pair in baggage_header.split(',') {
                let kv: Vec<&str> = pair.split('=').collect();
                if kv.len() == 2 {
                    baggage.insert(kv[0].trim().to_string(), kv[1].trim().to_string());
                }
            }
        }
        
        // 创建上下文
        let context = TraceContext {
            trace_id,
            span_id,
            parent_span_id: None, // 提取时无法知道
            sampled,
            baggage,
        };
        
        Ok(Some(context))
    }
    
    async fn close(&self) -> Result<(), TraceError> {
        // 触发最后一次导出
        let _ = self.export_trigger.send(());
        
        // 等待导出任务完成
        if let Some(task) = &self.export_task {
            let timeout = self.config.shutdown_timeout;
            if tokio::time::timeout(timeout, task).await.is_err() {
                log::warn!("Export task did not complete within shutdown timeout");
            }
        }
        
        // 关闭导出器
        self.exporter.shutdown().await
    }
}

impl Span {
    /// 结束Span并记录
    pub fn end(self) -> CompletedSpan {
        let end_time = Utc::now();
        
        let completed = CompletedSpan {
            context: self.ctx.clone(),
            name: self.name,
            kind: self.kind,
            start_time: self.start_time,
            end_time,
            attributes: self.attributes,
            events: self.events,
            status: self.status,
            parent_context: self.ctx.parent_span_id.as_ref().map(|_| {
                // 构建父上下文
                TraceContext {
                    trace_id: self.ctx.trace_id.clone(),
                    span_id: self.ctx.parent_span_id.clone().unwrap(),
                    parent_span_id: None,
                    sampled: self.ctx.sampled,
                    baggage: self.ctx.baggage.clone(),
                }
            }),
        };
        
        // 异步记录完成的Span
        tokio::spawn(async move {
            if let Err(e) = self.tracer.record_span(completed.clone()).await {
                log::error!("Failed to record span: {}", e);
            }
        });
        
        completed
    }
}

impl SpanHandle for Span {
    fn context(&self) -> &TraceContext {
        &self.ctx
    }
    
    fn set_attribute(&mut self, key: &str, value: Value) {
        self.attributes.insert(key.to_string(), value);
    }
    
    fn add_event(&mut self, name: &str, attributes: HashMap<String, Value>) {
        self.events.push(SpanEvent {
            name: name.to_string(),
            timestamp: Utc::now(),
            attributes,
        });
    }
    
    fn set_status(&mut self, status: SpanStatus) {
        self.status = status;
    }
    
    fn end(&mut self) {
        if self.end_time.is_none() {
            self.end_time = Some(Utc::now());
        }
    }
    
    fn is_recording(&self) -> bool {
        self.end_time.is_none()
    }
}

// 实现Map作为载体
impl Carrier for HashMap<String, String> {
    fn get(&self, key: &str) -> Option<&str> {
        self.get(key).map(|s| s.as_str())
    }
    
    fn set(&mut self, key: &str, value: String) {
        self.insert(key.to_string(), value);
    }
    
    fn remove(&mut self, key: &str) {
        self.remove(key);
    }
    
    fn keys(&self) -> Vec<&str> {
        self.keys().map(|s| s.as_str()).collect()
    }
}

/// 控制台Span导出器
pub struct ConsoleSpanExporter;

#[async_trait]
impl SpanExporter for ConsoleSpanExporter {
    async fn export(&self, spans: Vec<CompletedSpan>) -> Result<(), TraceError> {
        for span in spans {
            let duration = span.end_time - span.start_time;
            let parent = span.parent_context.as_ref()
                .map(|ctx| ctx.span_id.clone())
                .unwrap_or_else(|| "none".to_string());
                
            println!("Span: {} ({:?})", span.name, span.kind);
            println!("  Trace ID: {}", span.context.trace_id);
            println!("  Span ID: {}", span.context.span_id);
            println!("  Parent Span ID: {}", parent);
            println!("  Duration: {:?}", duration);
            println!("  Status: {:?}", span.status);
            
            if !span.attributes.is_empty() {
                println!("  Attributes:");
                for (key, value) in &span.attributes {
                    println!("    {}: {:?}", key, value);
                }
            }
            
            if !span.events.is_empty() {
                println!("  Events:");
                for event in &span.events {
                    println!("    {} @ {}", event.name, event.timestamp);
                    if !event.attributes.is_empty() {
                        for (key, value) in &event.attributes {
                            println!("      {}: {:?}", key, value);
                        }
                    }
                }
            }
            
            println!();
        }
        
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), TraceError> {
        // 控制台导出器不需要关闭操作
        Ok(())
    }
}

/// Jaeger Span导出器
pub struct JaegerSpanExporter {
    endpoint: String,
    client: reqwest::Client,
    service_name: String,
}

impl JaegerSpanExporter {
    pub fn new(endpoint: &str, service_name: &str) -> Self {
        Self {
            endpoint: endpoint.to_string(),
            client: reqwest::Client::new(),
            service_name: service_name.to_string(),
        }
    }
    
    /// 将CompletedSpan转换为Jaeger格式
    fn to_jaeger_format(&self, spans: &[CompletedSpan]) -> Value {
        // 简化的Jaeger格式
        json!({
            "process": {
                "serviceName": self.service_name,
            },
            "spans": spans.iter().map(|span| {
                let start_time_micros = span.start_time.timestamp_micros();
                let duration_micros = (span.end_time - span.start_time).num_microseconds().unwrap_or(0);
                
                json!({
                    "traceID": span.context.trace_id,
                    "spanID": span.context.span_id,
                    "parentSpanID": span.parent_context.as_ref().map(|ctx| ctx.span_id.clone()).unwrap_or_default(),
                    "operationName": span.name,
                    "startTime": start_time_micros,
                    "duration": duration_micros,
                    "tags": span.attributes.iter().map(|(k, v)| {
                        match v {
                            Value::String(s) => json!({"key": k, "type": "string", "value": s}),
                            Value::Bool(b) => json!({"key": k, "type": "bool", "value": b}),
                            Value::Int(i) => json!({"key": k, "type": "int64", "value": i}),
                            Value::Float(f) => json!({"key": k, "type": "float64", "value": f}),
                            _ => json!({"key": k, "type": "string", "value": format!("{:?}", v)}),
                        }
                    }).collect::<Vec<_>>(),
                    "logs": span.events.iter().map(|event| {
                        json!({
                            "timestamp": event.timestamp.timestamp_micros(),
                            "fields": event.attributes.iter().map(|(k, v)| {
                                match v {
                                    Value::String(s) => json!({"key": k, "type": "string", "value": s}),
                                    Value::Bool(b) => json!({"key": k, "type": "bool", "value": b}),
                                    Value::Int(i) => json!({"key": k, "type": "int64", "value": i}),
                                    Value::Float(f) => json!({"key": k, "type": "float64", "value": f}),
                                    _ => json!({"key": k, "type": "string", "value": format!("{:?}", v)}),
                                }
                            }).collect::<Vec<_>>()
                        })
                    }).collect::<Vec<_>>()
                })
            }).collect::<Vec<_>>()
        })
    }
}

#[async_trait]
impl SpanExporter for JaegerSpanExporter {
    async fn export(&self, spans: Vec<CompletedSpan>) -> Result<(), TraceError> {
        if spans.is_empty() {
            return Ok(());
        }
        
        let jaeger_batch = self.to_jaeger_format(&spans);
        
        // 发送到Jaeger
        match self.client.post(&self.endpoint)
            .json(&jaeger_batch)
            .send()
            .await
        {
            Ok(response) => {
                if !response.status().is_success() {
                    return Err(TraceError::NetworkError(format!(
                        "Jaeger returned error: {}", response.status()
                    )));
                }
            },
            Err(e) => {
                return Err(TraceError::NetworkError(format!(
                    "Failed to send spans to Jaeger: {}", e
                )));
            }
        }
        
        Ok(())
    }
    
    async fn shutdown(&self) -> Result<(), TraceError> {
        // 简单的HTTP客户端不需要特殊的关闭操作
        Ok(())
    }
}

/// 工作流追踪助手
pub struct WorkflowTracer {
    tracer: Arc<dyn Tracer>,
}

impl WorkflowTracer {
    pub fn new(tracer: Arc<dyn Tracer>) -> Self {
        Self { tracer }
    }
    
    /// 开始工作流追踪
    pub fn start_workflow_trace(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
    ) -> Box<dyn SpanHandle> {
        let mut attributes = HashMap::new();
        attributes.insert("workflow.id".to_string(), Value::String(workflow_id.to_string()));
        attributes.insert("workflow.type".to_string(), Value::String(workflow_type.to_string()));
        
        self.tracer.create_span(
            &format!("workflow:{}", workflow_type),
            None, // 根Span
            SpanKind::Internal,
            attributes,
        )
    }
    
    /// 开始活动追踪
    pub fn start_activity_trace(
        &self,
        parent_span: &dyn SpanHandle,
        activity_type: &str,
        activity_id: &str,
    ) -> Box<dyn SpanHandle> {
        let mut attributes = HashMap::new();
        attributes.insert("activity.id".to_string(), Value::String(activity_id.to_string()));
        attributes.insert("activity.type".to_string(), Value::String(activity_type.to_string()));
        
        self.tracer.create_span(
            &format!("activity:{}", activity_type),
            Some(parent_span.context()),
            SpanKind::Internal,
            attributes,
        )
    }
    
    /// 开始状态转换追踪
    pub fn start_state_transition_trace(
        &self,
        parent_span: &dyn SpanHandle,
        from_state: &str,
        to_state: &str,
    ) -> Box<dyn SpanHandle> {
        let mut attributes = HashMap::new();
        attributes.insert("state.from".to_string(), Value::String(from_state.to_string()));
        attributes.insert("state.to".to_string(), Value::String(to_state.to_string()));
        
        self.tracer.create_span(
            &format!("state_transition:{}:{}", from_state, to_state),
            Some(parent_span.context()),
            SpanKind::Internal,
            attributes,
        )
    }
    
    /// 开始存储操作追踪
    pub fn start_storage_trace(
        &self,
        parent_span: &dyn SpanHandle,
        operation: &str,
    ) -> Box<dyn SpanHandle> {
        let mut attributes = HashMap::new();
        attributes.insert("storage.operation".to_string(), Value::String(operation.to_string()));
        
        self.tracer.create_span(
            &format!("storage:{}", operation),
            Some(parent_span.context()),
            SpanKind::Client, // 存储操作视为客户端操作
            attributes,
        )
    }
    
    /// 记录错误
    pub fn record_error(
        span: &mut dyn SpanHandle,
        error: &WorkflowError,
    ) {
        // 设置错误状态
        span.set_status(SpanStatus::Error(error.to_string()));
        
        // 添加错误事件
        let mut attributes = HashMap::new();
        attributes.insert("error.type".to_string(), Value::String(error.type_name()));
        attributes.insert("error.message".to_string(), Value::String(error.to_string()));
        
        span.add_event("error", attributes);
    }
    
    /// 从上下文中提取追踪上下文
    pub fn extract_context(&self, headers: &HashMap<String, String>) -> Option<TraceContext> {
        match self.tracer.extract_context(headers) {
            Ok(ctx) => ctx,
            Err(e) => {
                log::warn!("Failed to extract trace context: {}", e);
                None
            }
        }
    }
    
    /// 将追踪上下文注入到上下文中
    pub fn inject_context(&self, context: &TraceContext, headers: &mut HashMap<String, String>) {
        if let Err(e) = self.tracer.inject_context(context, headers) {
            log::warn!("Failed to inject trace context: {}", e);
        }
    }
}
```

### 7.4 告警与监控集成

```rust
/// 告警级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    /// 调试信息
    Debug = 0,
    /// 信息
    Info = 1,
    /// 警告
    Warning = 2,
    /// 错误
    Error = 3,
    /// 严重
    Critical = 4,
}

/// 告警
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    /// 告警ID
    pub id: String,
    /// 标题
    pub title: String,
    /// 消息
    pub message: String,
    /// 级别
    pub severity: AlertSeverity,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 上下文数据
    pub context: Value,
    /// 来源
    pub source: String,
}

/// 告警管理器接口
#[async_trait]
pub trait AlertManager: Send + Sync {
    /// 发送告警
    async fn send_alert(&self, alert: Alert) -> Result<(), AlertError>;
    
    /// 解除告警
    async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError>;
    
    /// 获取活跃告警
    async fn get_active_alerts(&self) -> Result<Vec<Alert>, AlertError>;
    
    /// 获取告警历史
    async fn get_alert_history(
        &self, 
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        severity: Option<AlertSeverity>,
    ) -> Result<Vec<Alert>, AlertError>;
}

/// 告警错误
#[derive(Debug, thiserror::Error)]
pub enum AlertError {
    #[error("Network error: {0}")]
    NetworkError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Configuration error: {0}")]
    ConfigurationError(String),
    
    #[error("Authentication error: {0}")]
    AuthenticationError(String),
}

/// 多通道告警管理器
pub struct MultiChannelAlertManager {
    channels: Vec<Box<dyn AlertChannel>>,
    alert_store: Arc<dyn AlertStore>,
    deduplication_window: Duration,
}

/// 告警通道接口
#[async_trait]
pub trait AlertChannel: Send + Sync {
    /// 发送告警
    async fn send_alert(&self, alert: &Alert) -> Result<(), AlertError>;
    
    /// 解除告警
    async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError>;
    
    /// 检查通道是否适用于给定告警
    fn is_applicable(&self, alert: &Alert) -> bool;
}

/// 告警存储接口
#[async_trait]
pub trait AlertStore: Send + Sync {
    /// 保存告警
    async fn save_alert(&self, alert: &Alert) -> Result<(), AlertError>;
    
    /// 更新告警状态
    async fn update_alert_status(&self, alert_id: &str, resolved: bool) -> Result<(), AlertError>;
    
    /// 获取活跃告警
    async fn get_active_alerts(&self) -> Result<Vec<Alert>, AlertError>;
    
    /// 获取告警历史
    async fn get_alert_history(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        severity: Option<AlertSeverity>,
    ) -> Result<Vec<Alert>, AlertError>;
    
    /// 获取最近告警
    async fn get_recent_alert_by_fingerprint(
        &self,
        fingerprint: &str,
        window: Duration,
    ) -> Result<Option<Alert>, AlertError>;
}

impl MultiChannelAlertManager {
    pub fn new(
        channels: Vec<Box<dyn AlertChannel>>,
        alert_store: Arc<dyn AlertStore>,
        deduplication_window: Duration,
    ) -> Self {
        Self {
            channels,
            alert_store,
            deduplication_window,
        }
    }
    
    /// 生成告警指纹
    fn generate_fingerprint(alert: &Alert) -> String {
        // 使用告警的关键内容创建指纹
        let fingerprint_content = format!(
            "{}:{}:{}",
            alert.source,
            alert.title,
            serde_json::to_string(&alert.context).unwrap_or_default(),
        );
        
        // 计算SHA-256哈希作为指纹
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(fingerprint_content);
        format!("{:x}", hasher.finalize())
    }
    
    /// 检查是否可以发送告警（防止重复告警）
    async fn should_send_alert(&self, alert: &Alert) -> Result<bool, AlertError> {
        let fingerprint = Self::generate_fingerprint(alert);
        
        // 检查最近是否有相同指纹的告警
        match self.alert_store.get_recent_alert_by_fingerprint(
            &fingerprint,
            self.deduplication_window,
        ).await {
            Ok(Some(_)) => Ok(false), // 存在重复告警，不应发送
            Ok(None) => Ok(true),     // 无重复告警，可以发送
            Err(e) => Err(e),
        }
    }
}

#[async_trait]
impl AlertManager for MultiChannelAlertManager {
    async fn send_alert(&self, mut alert: Alert) -> Result<(), AlertError> {
        // 生成唯一ID
        if alert.id.is_empty() {
            alert.id = Uuid::new_v4().to_string();
        }
        
        // 确保有时间戳
        if alert.timestamp.timestamp() == 0 {
            alert.timestamp = Utc::now();
        }
        
        // 检查是否应该发送告警
        if !self.should_send_alert(&alert).await? {
            return Ok(());
        }
        
        // 保存告警
        self.alert_store.save_alert(&alert).await?;
        
        // 向所有适用通道发送告警
        let mut sent = false;
        let mut errors = Vec::new();
        
        for channel in &self.channels {
            if channel.is_applicable(&alert) {
                match channel.send_alert(&alert).await {
                    Ok(()) => { sent = true; }
                    Err(e) => { errors.push(e); }
                }
            }
        }
        
        // 如果至少有一个通道成功发送，就认为整体成功
        if sent {
            Ok(())
        } else if !errors.is_empty() {
            // 返回第一个错误
            Err(errors.remove(0))
        } else {
            // 没有适用的通道
            Err(AlertError::ConfigurationError(
                "No applicable alert channels found".to_string()
            ))
        }
    }
    
    async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError> {
        // 更新告警状态
        self.alert_store.update_alert_status(alert_id, true).await?;
        
        // 通知所有通道
        let mut success = false;
        let mut errors = Vec::new();
        
        for channel in &self.channels {
            match channel.resolve_alert(alert_id).await {
                Ok(()) => { success = true; }
                Err(e) => { errors.push(e); }
            }
        }
        
        // 如果至少有一个通道成功，就认为整体成功
        if success {
            Ok(())
        } else if !errors.is_empty() {
            // 返回第一个错误
            Err(errors.remove(0))
        } else {
            Ok(()) // 没有通道处理解除告警也算成功
        }
    }
    
    async fn get_active_alerts(&self) -> Result<Vec<Alert>, AlertError> {
        self.alert_store.get_active_alerts().await
    }
    
    async fn get_alert_history(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        severity: Option<AlertSeverity>,
    ) -> Result<Vec<Alert>, AlertError> {
        self.alert_store.get_alert_history(start_time, end_time, severity).await
    }
}

/// Slack告警通道
pub struct SlackAlertChannel {
    webhook_url: String,
    client: reqwest::Client,
    min_severity: AlertSeverity,
}

impl SlackAlertChannel {
    pub fn new(webhook_url: &str, min_severity: AlertSeverity) -> Self {
        Self {
            webhook_url: webhook_url.to_string(),
            client: reqwest::Client::new(),
            min_severity,
        }
    }
    
    /// 格式化Slack消息
    fn format_message(&self, alert: &Alert) -> Value {
        // 选择颜色
        let color = match alert.severity {
            AlertSeverity::Debug => "#808080",    // 灰色
            AlertSeverity::Info => "#0000FF",     // 蓝色
            AlertSeverity::Warning => "#FFA500",  // 橙色
            AlertSeverity::Error => "#FF0000",    // 红色
            AlertSeverity::Critical => "#8B0000", // 深红色
        };
        
        // 格式化上下文
        let context_string = match serde_json::to_string_pretty(&alert.context) {
            Ok(s) => s,
            Err(_) => "无法格式化上下文".to_string(),
        };
        
        // 构建Slack消息
        json!({
            "attachments": [
                {
                    "color": color,
                    "blocks": [
                        {
                            "type": "header",
                            "text": {
                                "type": "plain_text",
                                "text": &format!("🚨 告警: {}", alert.title),
                            }
                        },
                        {
                            "type": "section",
                            "text": {
                                "type": "mrkdwn",
                                "text": &format!("*消息:* {}", alert.message)
                            }
                        },
                        {
                            "type": "section",
                            "fields": [
                                {
                                    "type": "mrkdwn",
                                    "text": &format!("*ID:* {}", alert.id)
                                },
                                {
                                    "type": "mrkdwn",
                                    "text": &format!("*严重性:* {:?}", alert.severity)
                                },
                                {
                                    "type": "mrkdwn",
                                    "text": &format!("*时间:* {}", alert.timestamp)
                                },
                                {
                                    "type": "mrkdwn",
                                    "text": &format!("*来源:* {}", alert.source)
                                }
                            ]
                        },
                        {
                            "type": "section",
                            "text": {
                                "type": "mrkdwn",
                                "text": &format!("*上下文:*\n```{}```", context_string)
                            }
                        }
                    ]
                }
            ]
        })
    }
}

#[async_trait]
impl AlertChannel for SlackAlertChannel {
    async fn send_alert(&self, alert: &Alert) -> Result<(), AlertError> {
        // 格式化Slack消息
        let message = self.format_message(alert);
        
        // 发送到Webhook
        match self.client.post(&self.webhook_url)
            .json(&message)
            .send()
            .await
        {
            Ok(response) => {
                if !response.status().is_success() {
                    return Err(AlertError::NetworkError(format!(
                        "Slack返回错误: {}", response.status()
                    )));
                }
            },
            Err(e) => {
                return Err(AlertError::NetworkError(format!(
                    "发送到Slack失败: {}", e
                )));
            }
        }
        
        Ok(())
    }
    
    async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError> {
        // 发送告警解除消息
        let message = json!({
            "text": format!("✅ 告警已解除: ID {}", alert_id)
        });
        
        // 发送到Webhook
        match self.client.post(&self.webhook_url)
            .json(&message)
            .send()
            .await
        {
            Ok(response) => {
                if !response.status().is_success() {
                    return Err(AlertError::NetworkError(format!(
                        "Slack返回错误: {}", response.status()
                    )));
                }
            },
            Err(e) => {
                return Err(AlertError::NetworkError(format!(
                    "发送到Slack失败: {}", e
                )));
            }
        }
        
        Ok(())
    }
    
    fn is_applicable(&self, alert: &Alert) -> bool {
        // 检查告警严重性是否达到通道的最低要求
        alert.severity >= self.min_severity
    }
}

/// Email告警通道
pub struct EmailAlertChannel {
    smtp_config: SmtpConfig,
    recipients: Vec<String>,
    min_severity: AlertSeverity,
}

/// SMTP配置
#[derive(Debug, Clone)]
pub struct SmtpConfig {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub password: String,
    pub from_address: String,
    pub from_name: String,
    pub enable_tls: bool,
}

impl EmailAlertChannel {
    pub fn new(
        smtp_config: SmtpConfig,
        recipients: Vec<String>,
        min_severity: AlertSeverity,
    ) -> Self {
        Self {
            smtp_config,
            recipients,
            min_severity,
        }
    }
    
    /// 格式化邮件内容
    fn format_email(&self, alert: &Alert) -> (String, String) {
        // 格式化主题
        let subject = format!(
            "[{:?}] {} - {}",
            alert.severity, 
            alert.source, 
            alert.title
        );
        
        // 格式化上下文
        let context_string = match serde_json::to_string_pretty(&alert.context) {
            Ok(s) => s,
            Err(_) => "无法格式化上下文".to_string(),
        };
        
        // 格式化邮件正文
        let body = format!(
            r#"告警详情:
            
ID: {}
标题: {}
严重性: {:?}
时间: {}
来源: {}

消息:
{}

上下文:
{}
            "#,
            alert.id,
            alert.title,
            alert.severity,
            alert.timestamp,
            alert.source,
            alert.message,
            context_string
        );
        
        (subject, body)
    }
    
    /// 发送邮件
    async fn send_email(&self, to: &[String], subject: &str, body: &str) -> Result<(), AlertError> {
        // 创建SMTP传输
        let smtp_server = format!("{}:{}", self.smtp_config.host, self.smtp_config.port);
        
        let builder = if self.smtp_config.enable_tls {
            match TlsConnector::builder().build() {
                Ok(connector) => SmtpTransport::relay(&self.smtp_config.host)
                    .unwrap()
                    .credentials(Credentials::new(
                        self.smtp_config.username.clone(),
                        self.smtp_config.password.clone(),
                    ))
                    .tls(Tls::Required)
                    .build(),
                Err(e) => {
                    return Err(AlertError::ConfigurationError(format!(
                        "TLS连接器创建失败: {}", e
                    )));
                }
            }
        } else {
            SmtpTransport::builder_unencrypted_localhost()
                .build()
        };
        
        // 构建邮件
        let email = match Message::builder()
            .from(Mailbox::new(
                Some(self.smtp_config.from_name.clone()),
                self.smtp_config.from_address.parse().map_err(|e| {
                    AlertError::ConfigurationError(format!("无效的发件人地址: {}", e))
                })?
            ))
            .subject(subject)
            .body(body.to_string())
        {
            Ok(mut message) => {
                // 添加所有收件人
                for recipient in to {
                    match recipient.parse() {
                        Ok(addr) => {
                            message = message.to(Mailbox::new(None, addr));
                        }
                        Err(e) => {
                            return Err(AlertError::ConfigurationError(format!(
                                "无效的收件人地址 {}: {}", recipient, e
                            )));
                        }
                    }
                }
                message
            }
            Err(e) => {
                return Err(AlertError::SerializationError(format!(
                    "创建邮件失败: {}", e
                )));
            }
        };
        
        // 发送邮件
        match builder.send(&email) {
            Ok(_) => Ok(()),
            Err(e) => Err(AlertError::NetworkError(format!(
                "发送邮件失败: {}", e
            ))),
        }
    }
}

#[async_trait]
impl AlertChannel for EmailAlertChannel {
    async fn send_alert(&self, alert: &Alert) -> Result<(), AlertError> {
        // 格式化邮件
        let (subject, body) = self.format_email(alert);
        
        // 发送邮件
        self.send_email(&self.recipients, &subject, &body).await
    }
    
    async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError> {
        // 发送告警解除邮件
        let subject = format!("[已解除] 告警 {}", alert_id);
        let body = format!("告警 ID {} 已解除", alert_id);
        
        self.send_email(&self.recipients, &subject, &body).await
    }
    
    fn is_applicable(&self, alert: &Alert) -> bool {
        // 检查告警严重性是否达到通道的最低要求
        alert.severity >= self.min_severity
    }
}

/// PostgreSQL告警存储
pub struct PostgresAlertStore {
    pool: Pool<PostgresConnectionManager<NoTls>>,
}

impl PostgresAlertStore {
    pub async fn new(connection_string: &str) -> Result<Self, AlertError> {
        // 创建连接管理器
        let manager = PostgresConnectionManager::new(
            connection_string.parse().map_err(|e| {
                AlertError::ConfigurationError(format!("无效的连接字符串: {}", e))
            })?,
            NoTls,
        );
        
        // 创建连接池
        let pool = Pool::builder()
            .max_size(15)
            .build(manager)
            .map_err(|e| {
                AlertError::ConfigurationError(format!("创建连接池失败: {}", e))
            })?;
        
        // 初始化数据库结构
        Self::init_schema(&pool).await?;
        
        Ok(Self { pool })
    }
    
    /// 初始化表结构
    async fn init_schema(pool: &Pool<PostgresConnectionManager<NoTls>>) -> Result<(), AlertError> {
        let conn = pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 创建告警表
        conn.execute(
            "CREATE TABLE IF NOT EXISTS alerts (
                id TEXT PRIMARY KEY,
                title TEXT NOT NULL,
                message TEXT NOT NULL,
                severity INTEGER NOT NULL,
                timestamp TIMESTAMPTZ NOT NULL,
                context JSONB NOT NULL,
                source TEXT NOT NULL,
                resolved BOOLEAN NOT NULL DEFAULT FALSE,
                fingerprint TEXT NOT NULL
            )",
            &[],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("创建表失败: {}", e))
        })?;
        
        // 创建索引
        conn.execute(
            "CREATE INDEX IF NOT EXISTS alerts_fingerprint_idx ON alerts(fingerprint)",
            &[],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("创建索引失败: {}", e))
        })?;
        
        conn.execute(
            "CREATE INDEX IF NOT EXISTS alerts_timestamp_idx ON alerts(timestamp)",
            &[],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("创建索引失败: {}", e))
        })?;
        
        conn.execute(
            "CREATE INDEX IF NOT EXISTS alerts_resolved_idx ON alerts(resolved)",
            &[],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("创建索引失败: {}", e))
        })?;
        
        Ok(())
    }
    
    /// 从数据库行构建告警对象
    fn build_alert_from_row(row: &Row) -> Result<Alert, AlertError> {
        let context: Value = row.get("context");
        
        let alert = Alert {
            id: row.get("id"),
            title: row.get("title"),
            message: row.get("message"),
            severity: Self::int_to_severity(row.get("severity")),
            timestamp: row.get("timestamp"),
            context,
            source: row.get("source"),
        };
        
        Ok(alert)
    }
    
    /// 将整数转换为告警级别
    fn int_to_severity(value: i32) -> AlertSeverity {
        match value {
            0 => AlertSeverity::Debug,
            1 => AlertSeverity::Info,
            2 => AlertSeverity::Warning,
            3 => AlertSeverity::Error,
            4 => AlertSeverity::Critical,
            _ => AlertSeverity::Info, // 默认值
        }
    }
    
    /// 将告警级别转换为整数
    fn severity_to_int(severity: AlertSeverity) -> i32 {
        severity as i32
    }
}

#[async_trait]
impl AlertStore for PostgresAlertStore {
    async fn save_alert(&self, alert: &Alert) -> Result<(), AlertError> {
        let conn = self.pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 生成指纹
        let fingerprint = MultiChannelAlertManager::generate_fingerprint(alert);
        
        // 序列化上下文
        let context_json = serde_json::to_value(&alert.context).map_err(|e| {
            AlertError::SerializationError(format!("序列化上下文失败: {}", e))
        })?;
        
        // 保存告警
        conn.execute(
            "INSERT INTO alerts (
                id, title, message, severity, timestamp, 
                context, source, resolved, fingerprint
            ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
            ON CONFLICT (id) DO UPDATE SET
                title = $2,
                message = $3,
                severity = $4,
                timestamp = $5,
                context = $6,
                source = $7",
            &[
                &alert.id,
                &alert.title,
                &alert.message,
                &Self::severity_to_int(alert.severity),
                &alert.timestamp,
                &context_json,
                &alert.source,
                &false, // 新告警未解除
                &fingerprint,
            ],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("保存告警失败: {}", e))
        })?;
        
        Ok(())
    }
    
    async fn update_alert_status(&self, alert_id: &str, resolved: bool) -> Result<(), AlertError> {
        let conn = self.pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 更新告警状态
        conn.execute(
            "UPDATE alerts SET resolved = $1 WHERE id = $2",
            &[&resolved, &alert_id],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("更新告警状态失败: {}", e))
        })?;
        
        Ok(())
    }
    
    async fn get_active_alerts(&self) -> Result<Vec<Alert>, AlertError> {
        let conn = self.pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 查询未解除的告警
        let rows = conn.query(
            "SELECT * FROM alerts WHERE resolved = FALSE ORDER BY timestamp DESC",
            &[],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("查询活跃告警失败: {}", e))
        })?;
        
        // 构建告警列表
        let mut alerts = Vec::with_capacity(rows.len());
        for row in rows {
            alerts.push(Self::build_alert_from_row(&row)?);
        }
        
        Ok(alerts)
    }
    
    async fn get_alert_history(
        &self,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
        severity: Option<AlertSeverity>,
    ) -> Result<Vec<Alert>, AlertError> {
        let conn = self.pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 构建查询
        let query = if let Some(sev) = severity {
            conn.query(
                "SELECT * FROM alerts 
                 WHERE timestamp >= $1 AND timestamp <= $2 AND severity >= $3
                 ORDER BY timestamp DESC",
                &[&start_time, &end_time, &Self::severity_to_int(sev)],
            ).await
        } else {
            conn.query(
                "SELECT * FROM alerts 
                 WHERE timestamp >= $1 AND timestamp <= $2
                 ORDER BY timestamp DESC",
                &[&start_time, &end_time],
            ).await
        }.map_err(|e| {
            AlertError::ConfigurationError(format!("查询告警历史失败: {}", e))
        })?;
        
        // 构建告警列表
        let mut alerts = Vec::with_capacity(query.len());
        for row in query {
            alerts.push(Self::build_alert_from_row(&row)?);
        }
        
        Ok(alerts)
    }
    
    async fn get_recent_alert_by_fingerprint(
        &self,
        fingerprint: &str,
        window: Duration,
    ) -> Result<Option<Alert>, AlertError> {
        let conn = self.pool.get().await.map_err(|e| {
            AlertError::ConfigurationError(format!("获取数据库连接失败: {}", e))
        })?;
        
        // 计算时间窗口
        let cutoff_time = Utc::now() - window;
        
        // 查询最近的匹配指纹的告警
        let rows = conn.query(
            "SELECT * FROM alerts 
             WHERE fingerprint = $1 AND timestamp > $2
             ORDER BY timestamp DESC LIMIT 1",
            &[&fingerprint, &cutoff_time],
        ).await.map_err(|e| {
            AlertError::ConfigurationError(format!("查询告警指纹失败: {}", e))
        })?;
        
        // 如果找到匹配的告警，转换为Alert对象
        if let Some(row) = rows.get(0) {
            Ok(Some(Self::build_alert_from_row(row)?))
        } else {
            Ok(None)
        }
    }
}

/// 工作流告警助手
pub struct WorkflowAlertHelper {
    alert_manager: Arc<dyn AlertManager>,
    service_name: String,
}

impl WorkflowAlertHelper {
    pub fn new(alert_manager: Arc<dyn AlertManager>, service_name: &str) -> Self {
        Self {
            alert_manager,
            service_name: service_name.to_string(),
        }
    }
    
    /// 发送工作流执行错误告警
    pub async fn workflow_execution_error(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
        error: &WorkflowError,
        context: Value,
    ) -> Result<String, AlertError> {
        let alert_id = Uuid::new_v4().to_string();
        
        // 根据错误类型确定严重性
        let severity = match error {
            WorkflowError::Internal(_) => AlertSeverity::Critical,
            WorkflowError::Activity(_) => AlertSeverity::Error,
            WorkflowError::Timeout(_) => AlertSeverity::Warning,
            WorkflowError::Canceled => AlertSeverity::Info,
            _ => AlertSeverity::Error,
        };
        
        // 创建告警上下文
        let mut alert_context = context;
        if let Value::Object(ref mut obj) = alert_context {
            obj.insert("workflow_id".to_string(), json!(workflow_id.to_string()));
            obj.insert("workflow_type".to_string(), json!(workflow_type));
            obj.insert("error_type".to_string(), json!(error.type_name()));
        }
        
        // 创建告警
        let alert = Alert {
            id: alert_id.clone(),
            title: format!("工作流执行错误: {}", workflow_type),
            message: format!("工作流 {} (ID: {}) 执行失败: {}", 
                workflow_type, workflow_id, error),
            severity,
            timestamp: Utc::now(),
            context: alert_context,
            source: self.service_name.clone(),
        };
        
        // 发送告警
        self.alert_manager.send_alert(alert).await?;
        
        Ok(alert_id)
    }
    
    /// 发送活动执行错误告警
    pub async fn activity_execution_error(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
        activity_type: &str,
        attempt: u32,
        error: &WorkflowError,
        context: Value,
    ) -> Result<String, AlertError> {
        let alert_id = Uuid::new_v4().to_string();
        
        // 确定严重性（多次尝试后的错误更严重）
        let severity = if attempt >= 3 {
            AlertSeverity::Error
        } else {
            AlertSeverity::Warning
        };
        
        // 创建告警上下文
        let mut alert_context = context;
        if let Value::Object(ref mut obj) = alert_context {
            obj.insert("workflow_id".to_string(), json!(workflow_id.to_string()));
            obj.insert("workflow_type".to_string(), json!(workflow_type));
            obj.insert("activity_type".to_string(), json!(activity_type));
            obj.insert("attempt".to_string(), json!(attempt));
            obj.insert("error_type".to_string(), json!(error.type_name()));
        }
        
        // 创建告警
        let alert = Alert {
            id: alert_id.clone(),
            title: format!("活动执行错误: {}", activity_type),
            message: format!(
                "工作流 {} (ID: {}) 中的活动 {} 执行失败（尝试 {} 次）: {}", 
                workflow_type, workflow_id, activity_type, attempt, error
            ),
            severity,
            timestamp: Utc::now(),
            context: alert_context,
            source: self.service_name.clone(),
        };
        
        // 发送告警
        self.alert_manager.send_alert(alert).await?;
        
        Ok(alert_id)
    }
    
    /// 发送系统资源告警
    pub async fn resource_warning(
        &self,
        resource_type: &str,
        resource_id: &str,
        usage_percent: f64,
        threshold: f64,
        context: Value,
    ) -> Result<String, AlertError> {
        let alert_id = Uuid::new_v4().to_string();
        
        // 根据资源使用率确定严重性
        let severity = if usage_percent > 90.0 {
            AlertSeverity::Critical
        } else if usage_percent > 80.0 {
            AlertSeverity::Error
        } else {
            AlertSeverity::Warning
        };
        
        // 创建告警上下文
        let mut alert_context = context;
        if let Value::Object(ref mut obj) = alert_context {
            obj.insert("resource_type".to_string(), json!(resource_type));
            obj.insert("resource_id".to_string(), json!(resource_id));
            obj.insert("usage_percent".to_string(), json!(usage_percent));
            obj.insert("threshold".to_string(), json!(threshold));
        }
        
        // 创建告警
        let alert = Alert {
            id: alert_id.clone(),
            title: format!("资源使用率警告: {}", resource_type),
            message: format!(
                "{} {} 使用率 {:.1}% 超过阈值 {:.1}%", 
                resource_type, resource_id, usage_percent, threshold
            ),
            severity,
            timestamp: Utc::now(),
            context: alert_context,
            source: self.service_name.clone(),
        };
        
        // 发送告警
        self.alert_manager.send_alert(alert).await?;
        
        Ok(alert_id)
    }
    
    /// 发送工作流延迟告警
    pub async fn workflow_latency_alert(
        &self,
        workflow_type: &str,
        latency_ms: u64,
        threshold_ms: u64,
        affected_count: u32,
        context: Value,
    ) -> Result<String, AlertError> {
        let alert_id = Uuid::new_v4().to_string();
        
        // 根据延迟和影响数量确定严重性
        let severity = if affected_count > 100 || latency_ms > threshold_ms * 5 {
            AlertSeverity::Critical
        } else if affected_count > 10 || latency_ms > threshold_ms * 2 {
            AlertSeverity::Error
        } else {
            AlertSeverity::Warning
        };
        
        // 创建告警上下文
        let mut alert_context = context;
        if let Value::Object(ref mut obj) = alert_context {
            obj.insert("workflow_type".to_string(), json!(workflow_type));
            obj.insert("latency_ms".to_string(), json!(latency_ms));
            obj.insert("threshold_ms".to_string(), json!(threshold_ms));
            obj.insert("affected_count".to_string(), json!(affected_count));
        }
        
        // 创建告警
        let alert = Alert {
            id: alert_id.clone(),
            title: format!("工作流延迟警告: {}", workflow_type),
            message: format!(
                "{} 类型工作流延迟 {} ms 超过阈值 {} ms，影响 {} 个实例", 
                workflow_type, latency_ms, threshold_ms, affected_count
            ),
            severity,
            timestamp: Utc::now(),
            context: alert_context,
            source: self.service_name.clone(),
        };
        
        // 发送告警
        self.alert_manager.send_alert(alert).await?;
        
        Ok(alert_id)
    }
    
    /// 解除告警
    pub async fn resolve_alert(&self, alert_id: &str) -> Result<(), AlertError> {
        self.alert_manager.resolve_alert(alert_id).await
    }
}
```

### 7.5 运行时指标监控

```rust
/// 工作流引擎指标
pub struct WorkflowEngineMetrics {
    registry: Arc<MetricRegistry>,
    
    // 工作流指标
    workflows_started: Counter,
    workflows_completed: Counter,
    workflows_failed: Counter,
    workflow_execution_time: Histogram,
    
    // 活动指标
    activities_started: Counter,
    activities_completed: Counter,
    activities_failed: Counter,
    activity_execution_time: Histogram,
    
    // 任务队列指标
    task_queue_length: GaugeVec,
    task_queue_processing_time: HistogramVec,
    
    // 资源使用指标
    open_workflows: Gauge,
    workflow_memory_usage: Gauge,
    
    // 工作节点指标
    worker_count: Gauge,
    worker_capacity: GaugeVec,
    worker_load: GaugeVec,
}

impl WorkflowEngineMetrics {
    pub fn new(registry: Arc<MetricRegistry>, namespace: &str) -> Self {
        let ns = namespace.to_string();
        
        // 工作流指标
        let workflows_started = registry.create_counter(
            &format!("{}_workflows_started", ns),
            "已启动的工作流总数",
        ).with_labels(&[("engine", namespace)]);
        
        let workflows_completed = registry.create_counter(
            &format!("{}_workflows_completed", ns),
            "已完成的工作流总数",
        ).with_labels(&[("engine", namespace)]);
        
        let workflows_failed = registry.create_counter(
            &format!("{}_workflows_failed", ns),
            "已失败的工作流总数",
        ).with_labels(&[("engine", namespace)]);
        
        let workflow_execution_time = registry.create_histogram(
            &format!("{}_workflow_execution_time", ns),
            "工作流执行时间（毫秒）",
            vec![50.0, 100.0, 250.0, 500.0, 1000.0, 2500.0, 5000.0, 10000.0],
        ).with_labels(&[("engine", namespace)]);
        
        // 活动指标
        let activities_started = registry.create_counter(
            &format!("{}_activities_started", ns),
            "已启动的活动总数",
        ).with_labels(&[("engine", namespace)]);
        
        let activities_completed = registry.create_counter(
            &format!("{}_activities_completed", ns),
            "已完成的活动总数",
        ).with_labels(&[("engine", namespace)]);
        
        let activities_failed = registry.create_counter(
            &format!("{}_activities_failed", ns),
            "已失败的活动总数",
        ).with_labels(&[("engine", namespace)]);
        
        let activity_execution_time = registry.create_histogram(
            &format!("{}_activity_execution_time", ns),
            "活动执行时间（毫秒）",
            vec![10.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 2500.0, 5000.0],
        ).with_labels(&[("engine", namespace)]);
        
        // 任务队列指标
        let task_queue_length = registry.create_gauge_vec(
            &format!("{}_task_queue_length", ns),
            "任务队列长度",
            &["queue_name"],
        );
        
        let task_queue_processing_time = registry.create_histogram_vec(
            &format!("{}_task_queue_processing_time", ns),
            "任务处理时间（毫秒）",
            vec![10.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 2500.0],
            &["queue_name"],
        );
        
        // 资源指标
        let open_workflows = registry.create_gauge(
            &format!("{}_open_workflows", ns),
            "当前活跃的工作流数量",
        ).with_labels(&[("engine", namespace)]);
        
        let workflow_memory_usage = registry.create_gauge(
            &format!("{}_workflow_memory_usage", ns),
            "工作流内存使用量（字节）",
        ).with_labels(&[("engine", namespace)]);
        
        // 工作节点指标
        let worker_count = registry.create_gauge(
            &format!("{}_worker_count", ns),
            "当前工作节点数量",
        ).with_labels(&[("engine", namespace)]);
        
        let worker_capacity = registry.create_gauge_vec(
            &format!("{}_worker_capacity", ns),
            "工作节点容量",
            &["worker_id", "task_type"],
        );
        
        let worker_load = registry.create_gauge_vec(
            &format!("{}_worker_load", ns),
            "工作节点负载",
            &["worker_id", "task_type"],
        );
        
        Self {
            registry,
            workflows_started,
            workflows_completed,
            workflows_failed,
            workflow_execution_time,
            activities_started,
            activities_completed,
            activities_failed,
            activity_execution_time,
            task_queue_length,
            task_queue_processing_time,
            open_workflows,
            workflow_memory_usage,
            worker_count,
            worker_capacity,
            worker_load,
        }
    }
    
    /// 记录工作流启动
    pub fn record_workflow_started(&self, workflow_type: &str) {
        self.workflows_started.increment(1);
        
        self.open_workflows.increment(1.0);
        
        // 这里可以按工作流类型进一步细分指标，但当前实现简化了
    }
    
    /// 记录工作流完成
    pub fn record_workflow_completed(
        &self,
        workflow_type: &str,
        execution_time_ms: u64,
    ) {
        self.workflows_completed.increment(1);
        
        self.open_workflows.decrement(1.0);
        
        self.workflow_execution_time.observe(execution_time_ms as f64);
    }
    
    /// 记录工作流失败
    pub fn record_workflow_failed(
        &self,
        workflow_type: &str,
        execution_time_ms: u64,
        error: &WorkflowError,
    ) {
        self.workflows_failed.increment(1);
        
        self.open_workflows.decrement(1.0);
        
        self.workflow_execution_time.observe(execution_time_ms as f64);
        
        // 这里可以按错误类型进一步细分指标，但当前实现简化了
    }
    
    /// 记录活动启动
    pub fn record_activity_started(&self, activity_type: &str) {
        self.activities_started.increment(1);
    }
    
    /// 记录活动完成
    pub fn record_activity_completed(
        &self,
        activity_type: &str,
        execution_time_ms: u64,
    ) {
        self.activities_completed.increment(1);
        
        self.activity_execution_time.observe(execution_time_ms as f64);
    }
    
    /// 记录活动失败
    pub fn record_activity_failed(
        &self,
        activity_type: &str,
        execution_time_ms: u64,
        error: &WorkflowError,
    ) {
        self.activities_failed.increment(1);
        
        self.activity_execution_time.observe(execution_time_ms as f64);
    }
    
    /// 更新任务队列长度
    pub fn update_task_queue_length(&self, queue_name: &str, length: usize) {
        self.task_queue_length.with_label_values(&[queue_name]).set(length as f64);
    }
    
    /// 记录任务处理时间
    pub fn record_task_processing_time(
        &self,
        queue_name: &str,
        processing_time_ms: u64,
    ) {
        self.task_queue_processing_time
            .with_label_values(&[queue_name])
            .observe(processing_time_ms as f64);
    }
    
    /// 更新工作流内存使用量
    pub fn update_workflow_memory_usage(&self, bytes: usize) {
        self.workflow_memory_usage.set(bytes as f64);
    }
    
    /// 更新工作节点数量
    pub fn update_worker_count(&self, count: usize) {
        self.worker_count.set(count as f64);
    }
    
    /// 更新工作节点容量
    pub fn update_worker_capacity(
        &self,
        worker_id: &str,
        task_type: &str,
        capacity: usize,
    ) {
        self.worker_capacity
            .with_label_values(&[worker_id, task_type])
            .set(capacity as f64);
    }
    
    /// 更新工作节点负载
    pub fn update_worker_load(
        &self,
        worker_id: &str,
        task_type: &str,
        load: usize,
    ) {
        self.worker_load
            .with_label_values(&[worker_id, task_type])
            .set(load as f64);
    }
}

/// 性能分析器
pub struct PerformanceProfiler {
    metrics: Arc<WorkflowEngineMetrics>,
    trace_enabled: AtomicBool,
    tracer: Option<Arc<dyn Tracer>>,
    profiling_interval: Duration,
    active_spans: RwLock<HashMap<String, Box<dyn SpanHandle>>>,
}

impl PerformanceProfiler {
    pub fn new(
        metrics: Arc<WorkflowEngineMetrics>,
        tracer: Option<Arc<dyn Tracer>>,
        profiling_interval: Duration,
    ) -> Self {
        Self {
            metrics,
            trace_enabled: AtomicBool::new(tracer.is_some()),
            tracer,
            profiling_interval,
            active_spans: RwLock::new(HashMap::new()),
        }
    }
    
    /// 设置是否启用跟踪
    pub fn set_trace_enabled(&self, enabled: bool) {
        self.trace_enabled.store(enabled, Ordering::SeqCst);
    }
    
    /// 是否启用跟踪
    pub fn is_trace_enabled(&self) -> bool {
        self.trace_enabled.load(Ordering::SeqCst)
    }
    
    /// 开始工作流性能分析
    pub fn start_workflow_profiling(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &str,
    ) -> Option<String> {
        // 记录工作流启动指标
        self.metrics.record_workflow_started(workflow_type);
        
        // 如果启用了跟踪，创建跟踪Span
        if let Some(tracer) = &self.tracer {
            if self.is_trace_enabled() {
                let profile_id = format!("workflow:{}", workflow_id);
                
                let mut attributes = HashMap::new();
                attributes.insert("workflow.id".to_string(), Value::String(workflow_id.to_string()));
                attributes.insert("workflow.type".to_string(), Value::String(workflow_type.to_string()));
                
                // 创建工作流Span
                let span = tracer.create_span(
                    &format!("workflow.{}", workflow_type),
                    None,
                    SpanKind::Internal,
                    attributes,
                );
                
                // 保存活跃Span
                let mut active_spans = self.active_spans.write().unwrap();
                active_spans.insert(profile_id.clone(), span);
                
                return Some(profile_id);
            }
        }
        
        None
    }
    
    /// 结束工作流性能分析
    pub fn end_workflow_profiling(
        &self,
        profile_id: Option<String>,
        workflow_type: &str,
        execution_time_ms: u64,
        result: &Result<(), WorkflowError>,
    ) {
        match result {
            Ok(_) => {
                // 记录工作流完成指标
                self.metrics.record_workflow_completed(workflow_type, execution_time_ms);
            }
            Err(error) => {
                // 记录工作流失败指标
                self.metrics.record_workflow_failed(workflow_type, execution_time_ms, error);
            }
        }
        
        // 如果有活跃的Span，结束它
        if let Some(id) = profile_id {
            let mut active_spans = self.active_spans.write().unwrap();
            if let Some(mut span) = active_spans.remove(&id) {
                // 设置结果状态
                match result {
                    Ok(_) => span.set_status(SpanStatus::Ok),
                    Err(error) => {
                        span.set_status(SpanStatus::Error(error.to_string()));
                        
                        // 添加错误信息
                        let mut attrs = HashMap::new();
                        attrs.insert("error.type".to_string(), Value::String(error.type_name()));
                        attrs.insert("error.message".to_string(), Value::String(error.to_string()));
                        span.add_event("error", attrs);
                    }
                }
                
                // 结束Span
                span.end();
            }
        }
    }
    
    /// 开始活动性能分析
    pub fn start_activity_profiling(
        &self,
        workflow_profile_id: Option<&str>,
        activity_id: &str,
        activity_type: &str,
    ) -> Option<String> {
        // 记录活动启动指标
        self.metrics.record_activity_started(activity_type);
        
        // 如果启用了跟踪，创建跟踪Span
        if let Some(tracer) = &self.tracer {
            if self.is_trace_enabled() {
                let profile_id = format!("activity:{}:{}", workflow_profile_id.unwrap_or(""), activity_id);
                
                let mut attributes = HashMap::new();
                attributes.insert("activity.id".to_string(), Value::String(activity_id.to_string()));
                attributes.insert("activity.type".to_string(), Value::String(activity_type.to_string()));
                
                // 获取父Span上下文
                let parent_context = if let Some(workflow_id) = workflow_profile_id {
                    let active_spans = self.active_spans.read().unwrap();
                    active_spans.get(workflow_id).map(|span| span.context())
                } else {
                    None
                };
                
                // 创建活动Span
                let span = tracer.create_span(
                    &format!("activity.{}", activity_type),
                    parent_context,
                    SpanKind::Internal,
                    attributes,
                );
                
                // 保存活跃Span
                let mut active_spans = self.active_spans.write().unwrap();
                active_spans.insert(profile_id.clone(), span);
                
                return Some(profile_id);
            }
        }
        
        None
    }
    
    /// 结束活动性能分析
    pub fn end_activity_profiling(
        &self,
        profile_id: Option<String>,
        activity_type: &str,
        execution_time_ms: u64,
        result: &Result<(), WorkflowError>,
    ) {
        match result {
            Ok(_) => {
                // 记录活动完成指标
                self.metrics.record_activity_completed(activity_type, execution_time_ms);
            }
            Err(error) => {
                // 记录活动失败指标
                self.metrics.record_activity_failed(activity_type, execution_time_ms, error);
            }
        }
        
        // 如果有活跃的Span，结束它
        if let Some(id) = profile_id {
            let mut active_spans = self.active_spans.write().unwrap();
            if let Some(mut span) = active_spans.remove(&id) {
                // 设置结果状态
                match result {
                    Ok(_) => span.set_status(SpanStatus::Ok),
                    Err(error) => {
                        span.set_status(SpanStatus::Error(error.to_string()));
                        
                        // 添加错误信息
                        let mut attrs = HashMap::new();
                        attrs.insert("error.type".to_string(), Value::String(error.type_name()));
                        attrs.insert("error.message".to_string(), Value::String(error.to_string()));
                        span.add_event("error", attrs);
                    }
                }
                
                // 结束Span
                span.end();
            }
        }
    }
    
    /// 记录任务队列性能
    pub fn record_queue_metrics(
        &self,
        queue_name: &str,
        queue_length: usize,
        processing_time_ms: Option<u64>,
    ) {
        // 更新队列长度
        self.metrics.update_task_queue_length(queue_name, queue_length);
        
        // 记录处理时间
        if let Some(time) = processing_time_ms {
            self.metrics.record_task_processing_time(queue_name, time);
        }
    }
    
    /// 周期性性能分析任务
    pub async fn start_periodic_profiling(&self) -> JoinHandle<()> {
        let metrics = self.metrics.clone();
        let interval = self.profiling_interval;
        
        tokio::spawn(async move {
            let mut ticker = tokio::time::interval(interval);
            
            loop {
                ticker.tick().await;
                
                // 收集系统指标
                if let Some(memory_usage) = Self::collect_memory_usage() {
                    metrics.update_workflow_memory_usage(memory_usage);
                }
                
                // 这里可以添加更多的系统指标收集
            }
        })
    }
    
    /// 收集内存使用情况
    fn collect_memory_usage() -> Option<usize> {
        // 在生产环境中，这里应该使用类似procfs的库来准确获取内存使用情况
        // 当前实现为简化版
        
        // 尝试获取当前进程的内存使用情况
        #[cfg(target_os = "linux")]
        {
            use std::fs::File;
            use std::io::{BufRead, BufReader};
            
            if let Ok(file) = File::open("/proc/self/status") {
                let reader = BufReader::new(file);
                
                for line in reader.lines() {
                    if let Ok(line) = line {
                        if line.starts_with("VmRSS:") {
                            // 格式: "VmRSS:   12345 kB"
                            let parts: Vec<&str> = line.split_whitespace().collect();
                            if parts.len() >= 2 {
                                if let Ok(kb) = parts[1].parse::<usize>() {
                                    return Some(kb * 1024); // 转换为字节
                                }
                            }
                        }
                    }
                }
            }
        }
        
        // 默认返回估计值
        Some(100 * 1024 * 1024) // 100 MB
    }
}

/// 工作流历史查询器
pub struct WorkflowHistoryAnalyzer {
    db_pool: Pool<PostgresConnectionManager<NoTls>>,
    metrics: Arc<WorkflowEngineMetrics>,
}

impl WorkflowHistoryAnalyzer {
    pub fn new(
        connection_string: &str,
        metrics: Arc<WorkflowEngineMetrics>,
    ) -> Result<Self, Box<dyn Error>> {
        // 创建连接管理器
        let manager = PostgresConnectionManager::new(
            connection_string.parse()?,
            NoTls,
        );
        
        // 创建连接池
        let pool = Pool::builder()
            .max_size(5)
            .build(manager)?;
        
        Ok(Self {
            db_pool: pool,
            metrics,
        })
    }
    
    /// 获取工作流执行历史
    pub async fn get_workflow_history(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<Vec<WorkflowEvent>, WorkflowError> {
        let conn = self.db_pool.get().await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "无法获取数据库连接: {}", e
            )))
        })?;
        
        // 查询工作流历史
        let rows = conn.query(
            "SELECT * FROM workflow_events 
             WHERE workflow_id = $1 
             ORDER BY sequence_number ASC",
            &[&workflow_id.to_string()],
        ).await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "查询工作流历史失败: {}", e
            )))
        })?;
        
        // 转换为WorkflowEvent
        let mut events = Vec::with_capacity(rows.len());
        for row in rows {
            let event_type: String = row.get("event_type");
            let event_data: Value = row.get("event_data");
            
            // 反序列化事件
            let event = match event_type.as_str() {
                "WorkflowStarted" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "ActivityStarted" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "ActivityCompleted" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "ActivityFailed" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "TimerStarted" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "TimerFired" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "SignalReceived" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "WorkflowCompleted" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "WorkflowFailed" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                "WorkflowCancelled" => serde_json::from_value::<WorkflowEvent>(event_data)?,
                _ => return Err(WorkflowError::Storage(StorageError::Deserialization(
                    format!("未知的事件类型: {}", event_type)
                ))),
            };
            
            events.push(event);
        }
        
        Ok(events)
    }
    
    /// 分析工作流执行延迟
    pub async fn analyze_workflow_latency(
        &self,
        workflow_type: &str,
        time_window: Duration,
    ) -> Result<WorkflowLatencyStats, WorkflowError> {
        let conn = self.db_pool.get().await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "无法获取数据库连接: {}", e
            )))
        })?;
        
        // 计算时间窗口
        let end_time = Utc::now();
        let start_time = end_time - time_window;
        
        // 查询工作流执行时间
        let rows = conn.query(
            "WITH workflow_times AS (
                SELECT 
                    workflow_id,
                    MIN(CASE WHEN event_type = 'WorkflowStarted' THEN timestamp END) as start_time,
                    MIN(CASE WHEN event_type IN ('WorkflowCompleted', 'WorkflowFailed', 'WorkflowCancelled') 
                        THEN timestamp END) as end_time
                FROM workflow_events
                WHERE 
                    timestamp BETWEEN $1 AND $2
                    AND workflow_type = $3
                GROUP BY workflow_id
            )
            SELECT
                COUNT(*) as total_count,
                COUNT(CASE WHEN end_time IS NOT NULL THEN 1 END) as completed_count,
                AVG(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as avg_duration_ms,
                MIN(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as min_duration_ms,
                MAX(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as max_duration_ms,
                PERCENTILE_CONT(0.50) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p50_ms,
                PERCENTILE_CONT(0.90) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p90_ms,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p95_ms,
                PERCENTILE_CONT(0.99) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p99_ms
            FROM workflow_times
            WHERE end_time IS NOT NULL",
            &[&start_time, &end_time, &workflow_type],
        ).await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "分析工作流延迟失败: {}", e
            )))
        })?;
        
        if let Some(row) = rows.get(0) {
            let total_count: i64 = row.get("total_count");
            let completed_count: i64 = row.get("completed_count");
            
            // 部分指标可能为NULL
            let avg_duration_ms: Option<f64> = row.get("avg_duration_ms");
            let min_duration_ms: Option<f64> = row.get("min_duration_ms");
            let max_duration_ms: Option<f64> = row.get("max_duration_ms");
            let p50_ms: Option<f64> = row.get("p50_ms");
            let p90_ms: Option<f64> = row.get("p90_ms");
            let p95_ms: Option<f64> = row.get("p95_ms");
            let p99_ms: Option<f64> = row.get("p99_ms");
            
            Ok(WorkflowLatencyStats {
                workflow_type: workflow_type.to_string(),
                period_start: start_time,
                period_end: end_time,
                total_count: total_count as u64,
                completed_count: completed_count as u64,
                avg_duration_ms: avg_duration_ms.unwrap_or(0.0) as u64,
                min_duration_ms: min_duration_ms.unwrap_or(0.0) as u64,
                max_duration_ms: max_duration_ms.unwrap_or(0.0) as u64,
                p50_ms: p50_ms.unwrap_or(0.0) as u64,
                p90_ms: p90_ms.unwrap_or(0.0) as u64,
                p95_ms: p95_ms.unwrap_or(0.0) as u64,
                p99_ms: p99_ms.unwrap_or(0.0) as u64,
            })
        } else {
            // 没有数据的情况
            Ok(WorkflowLatencyStats {
                workflow_type: workflow_type.to_string(),
                period_start: start_time,
                period_end: end_time,
                total_count: 0,
                completed_count: 0,
                avg_duration_ms: 0,
                min_duration_ms: 0,
                max_duration_ms: 0,
                p50_ms: 0,
                p90_ms: 0,
                p95_ms: 0,
                p99_ms: 0,
            })
        }
    }
    
    /// 分析活动执行延迟
    pub async fn analyze_activity_latency(
        &self,
        activity_type: &str,
        time_window: Duration,
    ) -> Result<ActivityLatencyStats, WorkflowError> {
        let conn = self.db_pool.get().await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "无法获取数据库连接: {}", e
            )))
        })?;
        
        // 计算时间窗口
        let end_time = Utc::now();
        let start_time = end_time - time_window;
        
        // 查询活动执行时间
        let rows = conn.query(
            "WITH activity_times AS (
                SELECT 
                    workflow_id,
                    activity_id,
                    MIN(CASE WHEN event_type = 'ActivityStarted' THEN timestamp END) as start_time,
                    MIN(CASE WHEN event_type IN ('ActivityCompleted', 'ActivityFailed') 
                        THEN timestamp END) as end_time,
                    MIN(CASE WHEN event_type = 'ActivityFailed' THEN 1 ELSE 0 END) as failed
                FROM workflow_events
                WHERE 
                    timestamp BETWEEN $1 AND $2
                    AND activity_type = $3
                    AND event_type IN ('ActivityStarted', 'ActivityCompleted', 'ActivityFailed')
                GROUP BY workflow_id, activity_id
            )
            SELECT
                COUNT(*) as total_count,
                COUNT(CASE WHEN end_time IS NOT NULL THEN 1 END) as completed_count,
                SUM(failed) as failed_count,
                AVG(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as avg_duration_ms,
                MIN(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as min_duration_ms,
                MAX(EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as max_duration_ms,
                PERCENTILE_CONT(0.50) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p50_ms,
                PERCENTILE_CONT(0.90) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p90_ms,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p95_ms,
                PERCENTILE_CONT(0.99) WITHIN GROUP (ORDER BY EXTRACT(EPOCH FROM (end_time - start_time)) * 1000) as p99_ms
            FROM activity_times
            WHERE end_time IS NOT NULL",
            &[&start_time, &end_time, &activity_type],
        ).await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "分析活动延迟失败: {}", e
            )))
        })?;
        
        if let Some(row) = rows.get(0) {
            let total_count: i64 = row.get("total_count");
            let completed_count: i64 = row.get("completed_count");
            let failed_count: i64 = row.get("failed_count");
            
            // 部分指标可能为NULL
            let avg_duration_ms: Option<f64> = row.get("avg_duration_ms");
            let min_duration_ms: Option<f64> = row.get("min_duration_ms");
            let max_duration_ms: Option<f64> = row.get("max_duration_ms");
            let p50_ms: Option<f64> = row.get("p50_ms");
            let p90_ms: Option<f64> = row.get("p90_ms");
            let p95_ms: Option<f64> = row.get("p95_ms");
            let p99_ms: Option<f64> = row.get("p99_ms");
            
            Ok(ActivityLatencyStats {
                activity_type: activity_type.to_string(),
                period_start: start_time,
                period_end: end_time,
                total_count: total_count as u64,
                completed_count: completed_count as u64,
                failed_count: failed_count as u64,
                avg_duration_ms: avg_duration_ms.unwrap_or(0.0) as u64,
                min_duration_ms: min_duration_ms.unwrap_or(0.0) as u64,
                max_duration_ms: max_duration_ms.unwrap_or(0.0) as u64,
                p50_ms: p50_ms.unwrap_or(0.0) as u64,
                p90_ms: p90_ms.unwrap_or(0.0) as u64,
                p95_ms: p95_ms.unwrap_or(0.0) as u64,
                p99_ms: p99_ms.unwrap_or(0.0) as u64,
            })
        } else {
            // 没有数据的情况
            Ok(ActivityLatencyStats {
                activity_type: activity_type.to_string(),
                period_start: start_time,
                period_end: end_time,
                total_count: 0,
                completed_count: 0,
                failed_count: 0,
                avg_duration_ms: 0,
                min_duration_ms: 0,
                max_duration_ms: 0,
                p50_ms: 0,
                p90_ms: 0,
                p95_ms: 0,
                p99_ms: 0,
            })
        }
    }
    
    /// 获取工作流错误统计
    pub async fn get_workflow_error_stats(
        &self,
        time_window: Duration,
    ) -> Result<HashMap<String, WorkflowErrorStats>, WorkflowError> {
        let conn = self.db_pool.get().await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "无法获取数据库连接: {}", e
            )))
        })?;
        
        // 计算时间窗口
        let end_time = Utc::now();
        let start_time = end_time - time_window;
        
        // 查询工作流错误
        let rows = conn.query(
            "SELECT 
                workflow_type,
                error_type,
                COUNT(*) as error_count
             FROM workflow_events
             WHERE 
                timestamp BETWEEN $1 AND $2
                AND event_type = 'WorkflowFailed'
             GROUP BY workflow_type, error_type
             ORDER BY error_count DESC",
            &[&start_time, &end_time],
        ).await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "获取工作流错误统计失败: {}", e
            )))
        })?;
        
        // 构建结果
        let mut result = HashMap::new();
        for row in rows {
            let workflow_type: String = row.get("workflow_type");
            let error_type: String = row.get("error_type");
            let error_count: i64 = row.get("error_count");
            
            let entry = result.entry(workflow_type.clone()).or_insert_with(|| {
                WorkflowErrorStats {
                    workflow_type,
                    period_start: start_time,
                    period_end: end_time,
                    error_counts: HashMap::new(),
                    total_errors: 0,
                }
            });
            
            entry.error_counts.insert(error_type, error_count as u64);
            entry.total_errors += error_count as u64;
        }
        
        Ok(result)
    }
    
    /// 获取活动错误统计
    pub async fn get_activity_error_stats(
        &self,
        time_window: Duration,
    ) -> Result<HashMap<String, ActivityErrorStats>, WorkflowError> {
        let conn = self.db_pool.get().await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "无法获取数据库连接: {}", e
            )))
        })?;
        
        // 计算时间窗口
        let end_time = Utc::now();
        let start_time = end_time - time_window;
        
        // 查询活动错误
        let rows = conn.query(
            "SELECT 
                activity_type,
                error_type,
                COUNT(*) as error_count
             FROM workflow_events
             WHERE 
                timestamp BETWEEN $1 AND $2
                AND event_type = 'ActivityFailed'
             GROUP BY activity_type, error_type
             ORDER BY error_count DESC",
            &[&start_time, &end_time],
        ).await.map_err(|e| {
            WorkflowError::Storage(StorageError::Database(format!(
                "获取活动错误统计失败: {}", e
            )))
        })?;
        
        // 构建结果
        let mut result = HashMap::new();
        for row in rows {
            let activity_type: String = row.get("activity_type");
            let error_type: String = row.get("error_type");
            let error_count: i64 = row.get("error_count");
            
            let entry = result.entry(activity_type.clone()).or_insert_with(|| {
                ActivityErrorStats {
                    activity_type,
                    period_start: start_time,
                    period_end: end_time,
                    error_counts: HashMap::new(),
                    total_errors: 0,
                }
            });
            
            entry.error_counts.insert(error_type, error_count as u64);
            entry.total_errors += error_count as u64;
        }
        
        Ok(result)
    }
}

/// 工作流延迟统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowLatencyStats {
    pub workflow_type: String,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub total_count: u64,
    pub completed_count: u64,
    pub avg_duration_ms: u64,
    pub min_duration_ms: u64,
    pub max_duration_ms: u64,
    pub p50_ms: u64,
    pub p90_ms: u64,
    pub p95_ms: u64,
    pub p99_ms: u64,
}

/// 活动延迟统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityLatencyStats {
    pub activity_type: String,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub total_count: u64,
    pub completed_count: u64,
    pub failed_count: u64,
    pub avg_duration_ms: u64,
    pub min_duration_ms: u64,
    pub max_duration_ms: u64,
    pub p50_ms: u64,
    pub p90_ms: u64,
    pub p95_ms: u64,
    pub p99_ms: u64,
}

/// 工作流错误统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowErrorStats {
    pub workflow_type: String,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub error_counts: HashMap<String, u64>,
    pub total_errors: u64,
}

/// 活动错误统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityErrorStats {
    pub activity_type: String,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub error_counts: HashMap<String, u64>,
    pub total_errors: u64,
}
```

### 7.6 工作流可视化与管理控制台

```rust
/// 工作流状态查询API处理器
pub struct WorkflowApiHandler {
    engine: Arc<dyn WorkflowEngine>,
    history_analyzer: Arc<WorkflowHistoryAnalyzer>,
    metrics: Arc<WorkflowEngineMetrics>,
}

impl WorkflowApiHandler {
    pub fn new(
        engine: Arc<dyn WorkflowEngine>,
        history_analyzer: Arc<WorkflowHistoryAnalyzer>,
        metrics: Arc<WorkflowEngineMetrics>,
    ) -> Self {
        Self {
            engine,
            history_analyzer,
            metrics,
        }
    }
    
    /// 创建API路由
    pub fn create_routes() -> Router {
        let handler = Self::new(
            // 这些会在实际应用中通过依赖注入提供
            Arc::new(MockWorkflowEngine),
            Arc::new(MockHistoryAnalyzer),
            Arc::new(MockMetrics),
        );
        
        Router::new()
            // 工作流管理API
            .route("/api/workflows", get(Self::list_workflows))
            .route("/api/workflows", post(Self::start_workflow))
            .route("/api/workflows/:id", get(Self::get_workflow_status))
            .route("/api/workflows/:id/history", get(Self::get_workflow_history))
            .route("/api/workflows/:id/cancel", post(Self::cancel_workflow))
            .route("/api/workflows/:id/signal", post(Self::signal_workflow))
            
            // 统计与监控API
            .route("/api/metrics/workflow/:type", get(Self::get_workflow_metrics))
            .route("/api/metrics/activity/:type", get(Self::get_activity_metrics))
            .route("/api/stats/latency", get(Self::get_latency_stats))
            .route("/api/stats/errors", get(Self::get_error_stats))
            
            // 注入共享状态
            .with_state(handler)
    }
    
    /// 获取工作流列表
    async fn list_workflows(
        State(handler): State<Self>,
        Query(params): Query<HashMap<String, String>>,
    ) -> Result<Json<Vec<WorkflowSummary>>, StatusCode> {
        // 处理查询参数
        let status = params.get("status").map(|s| s.as_str());
        let workflow_type = params.get("type").map(|s| s.as_str());
        let limit = params.get("limit")
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(100);
        let offset = params.get("offset")
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(0);
            
        // 调用引擎获取工作流列表
        match handler.engine.list_workflows(status, workflow_type, limit, offset).await {
            Ok(workflows) => Ok(Json(workflows)),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 启动新工作流
    async fn start_workflow(
        State(handler): State<Self>,
        Json(request): Json<StartWorkflowRequest>,
    ) -> Result<Json<StartWorkflowResponse>, StatusCode> {
        // 验证请求
        if request.workflow_type.is_empty() {
            return Err(StatusCode::BAD_REQUEST);
        }
        
        // 创建启动选项
        let options = WorkflowOptions {
            workflow_id: request.workflow_id.clone(),
            retry_policy: request.retry_policy.clone().unwrap_or_default(),
            task_queue: request.task_queue.clone().unwrap_or_else(|| "default".to_string()),
            ..Default::default()
        };
        
        // 启动工作流
        match handler.engine.start_workflow(
            &request.workflow_type,
            request.input.clone(),
            options,
        ).await {
            Ok(workflow_id) => Ok(Json(StartWorkflowResponse {
                workflow_id,
                status: "STARTED".to_string(),
            })),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 获取工作流状态
    async fn get_workflow_status(
        State(handler): State<Self>,
        Path(workflow_id): Path<String>,
    ) -> Result<Json<WorkflowStatus>, StatusCode> {
        // 解析工作流ID
        let id = WorkflowId::from(workflow_id);
        
        // 获取工作流状态
        match handler.engine.get_workflow_status(&id).await {
            Ok(status) => Ok(Json(status)),
            Err(WorkflowError::NotFound(_)) => Err(StatusCode::NOT_FOUND),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 获取工作流历史
    async fn get_workflow_history(
        State(handler): State<Self>,
        Path(workflow_id): Path<String>,
    ) -> Result<Json<Vec<WorkflowEvent>>, StatusCode> {
        // 解析工作流ID
        let id = WorkflowId::from(workflow_id);
        
        // 获取工作流历史
        match handler.history_analyzer.get_workflow_history(&id).await {
            Ok(history) => Ok(Json(history)),
            Err(WorkflowError::NotFound(_)) => Err(StatusCode::NOT_FOUND),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 取消工作流
    async fn cancel_workflow(
        State(handler): State<Self>,
        Path(workflow_id): Path<String>,
    ) -> Result<StatusCode, StatusCode> {
        // 解析工作流ID
        let id = WorkflowId::from(workflow_id);
        
        // 取消工作流
        match handler.engine.cancel_workflow(&id).await {
            Ok(_) => Ok(StatusCode::OK),
            Err(WorkflowError::NotFound(_)) => Err(StatusCode::NOT_FOUND),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 发送信号到工作流
    async fn signal_workflow(
        State(handler): State<Self>,
        Path(workflow_id): Path<String>,
        Json(request): Json<SignalWorkflowRequest>,
    ) -> Result<StatusCode, StatusCode> {
        // 解析工作流ID
        let id = WorkflowId::from(workflow_id);
        
        // 验证请求
        if request.signal_name.is_empty() {
            return Err(StatusCode::BAD_REQUEST);
        }
        
        // 发送信号
        match handler.engine.signal_workflow(
            &id,
            &request.signal_name,
            request.input.clone(),
        ).await {
            Ok(_) => Ok(StatusCode::OK),
            Err(WorkflowError::NotFound(_)) => Err(StatusCode::NOT_FOUND),
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 获取工作流指标
    async fn get_workflow_metrics(
        State(handler): State<Self>,
        Path(workflow_type): Path<String>,
        Query(params): Query<HashMap<String, String>>,
    ) -> Result<Json<WorkflowMetrics>, StatusCode> {
        // 处理查询参数
        let time_window = params.get("window")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(3600); // 默认1小时
            
        // 计算时间窗口
        let duration = Duration::from_secs(time_window);
        
        // 分析工作流延迟
        match handler.history_analyzer.analyze_workflow_latency(&workflow_type, duration).await {
            Ok(latency_stats) => {
                // 创建工作流指标
                let metrics = WorkflowMetrics {
                    workflow_type: workflow_type.clone(),
                    total_started: latency_stats.total_count,
                    total_completed: latency_stats.completed_count,
                    total_failed: latency_stats.total_count - latency_stats.completed_count,
                    avg_duration_ms: latency_stats.avg_duration_ms,
                    min_duration_ms: latency_stats.min_duration_ms,
                    max_duration_ms: latency_stats.max_duration_ms,
                    p50_ms: latency_stats.p50_ms,
                    p90_ms: latency_stats.p90_ms,
                    p95_ms: latency_stats.p95_ms,
                    p99_ms: latency_stats.p99_ms,
                    error_stats: HashMap::new(), // 需要另一个查询填充
                    period_start: latency_stats.period_start,
                    period_end: latency_stats.period_end,
                };
                
                Ok(Json(metrics))
            },
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 获取活动指标
    async fn get_activity_metrics(
        State(handler): State<Self>,
        Path(activity_type): Path<String>,
        Query(params): Query<HashMap<String, String>>,
    ) -> Result<Json<ActivityMetrics>, StatusCode> {
        // 处理查询参数
        let time_window = params.get("window")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(3600); // 默认1小时
            
        // 计算时间窗口
        let duration = Duration::from_secs(time_window);
        
        // 分析活动延迟
        match handler.history_analyzer.analyze_activity_latency(&activity_type, duration).await {
            Ok(latency_stats) => {
                // 创建活动指标
                let metrics = ActivityMetrics {
                    activity_type: activity_type.clone(),
                    total_scheduled: latency_stats.total_count,
                    total_completed: latency_stats.completed_count,
                    total_failed: latency_stats.failed_count,
                    avg_duration_ms: latency_stats.avg_duration_ms,
                    min_duration_ms: latency_stats.min_duration_ms,
                    max_duration_ms: latency_stats.max_duration_ms,
                    p50_ms: latency_stats.p50_ms,
                    p90_ms: latency_stats.p90_ms,
                    p95_ms: latency_stats.p95_ms,
                    p99_ms: latency_stats.p99_ms,
                    error_stats: HashMap::new(), // 需要另一个查询填充
                    period_start: latency_stats.period_start,
                    period_end: latency_stats.period_end,
                };
                
                Ok(Json(metrics))
            },
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
    
    /// 获取延迟统计
    async fn get_latency_stats(
        State(handler): State<Self>,
        Query(params): Query<HashMap<String, String>>,
    ) -> Result<Json<LatencyStatsSummary>, StatusCode> {
        // 处理查询参数
        let time_window = params.get("window")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(3600); // 默认1小时
            
        let workflow_types = params.get("workflows")
            .map(|s| s.split(',').map(|s| s.to_string()).collect::<Vec<_>>())
            .unwrap_or_else(Vec::new);
            
        let activity_types = params.get("activities")
            .map(|s| s.split(',').map(|s| s.to_string()).collect::<Vec<_>>())
            .unwrap_or_else(Vec::new);
            
        // 计算时间窗口
        let duration = Duration::from_secs(time_window);
        
        // 并行收集所有请求的统计数据
        let mut workflow_futures = Vec::new();
        for wf_type in &workflow_types {
            workflow_futures.push(handler.history_analyzer.analyze_workflow_latency(wf_type, duration));
        }
        
        let mut activity_futures = Vec::new();
        for act_type in &activity_types {
            activity_futures.push(handler.history_analyzer.analyze_activity_latency(act_type, duration));
        }
        
        // 等待所有查询完成
        let workflow_results = join_all(workflow_futures).await;
        let activity_results = join_all(activity_futures).await;
        
        // 收集工作流结果
        let mut workflow_stats = HashMap::new();
        for (wf_type, result) in workflow_types.iter().zip(workflow_results) {
            match result {
                Ok(stats) => {
                    workflow_stats.insert(wf_type.clone(), stats);
                },
                Err(_) => {
                    // 忽略错误，保持空结果
                }
            }
        }
        
        // 收集活动结果
        let mut activity_stats = HashMap::new();
        for (act_type, result) in activity_types.iter().zip(activity_results) {
            match result {
                Ok(stats) => {
                    activity_stats.insert(act_type.clone(), stats);
                },
                Err(_) => {
                    // 忽略错误，保持空结果
                }
            }
        }
        
        // 创建汇总
        let period_start = Utc::now() - duration;
        let period_end = Utc::now();
        
        let summary = LatencyStatsSummary {
            period_start,
            period_end,
            workflow_stats,
            activity_stats,
        };
        
        Ok(Json(summary))
    }
    
    /// 获取错误统计
    async fn get_error_stats(
        State(handler): State<Self>,
        Query(params): Query<HashMap<String, String>>,
    ) -> Result<Json<ErrorStatsSummary>, StatusCode> {
        // 处理查询参数
        let time_window = params.get("window")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(3600); // 默认1小时
            
        // 计算时间窗口
        let duration = Duration::from_secs(time_window);
        
        // 获取工作流和活动错误统计
        let workflow_errors_future = handler.history_analyzer.get_workflow_error_stats(duration);
        let activity_errors_future = handler.history_analyzer.get_activity_error_stats(duration);
        
        // 等待两个查询完成
        let (workflow_errors_result, activity_errors_result) = join!(
            workflow_errors_future, 
            activity_errors_future
        );
        
        // 处理结果
        let workflow_errors = match workflow_errors_result {
            Ok(stats) => stats,
            Err(_) => HashMap::new(),
        };
        
        let activity_errors = match activity_errors_result {
            Ok(stats) => stats,
            Err(_) => HashMap::new(),
        };
        
        // 创建汇总
        let period_start = Utc::now() - duration;
        let period_end = Utc::now();
        
        let summary = ErrorStatsSummary {
            period_start,
            period_end,
            workflow_errors,
            activity_errors,
        };
        
        Ok(Json(summary))
    }
}

/// 工作流摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowSummary {
    pub workflow_id: WorkflowId,
    pub workflow_type: String,
    pub status: String,
    pub start_time: DateTime<Utc>,
    pub end_time: Option<DateTime<Utc>>,
    pub last_updated: DateTime<Utc>,
}

/// 启动工作流请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StartWorkflowRequest {
    pub workflow_type: String,
    pub workflow_id: Option<String>,
    pub input: Value,
    pub retry_policy: Option<RetryPolicy>,
    pub task_queue: Option<String>,
}

/// 启动工作流响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StartWorkflowResponse {
    pub workflow_id: WorkflowId,
    pub status: String,
}

/// 信号工作流请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignalWorkflowRequest {
    pub signal_name: String,
    pub input: Value,
}

/// 工作流指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowMetrics {
    pub workflow_type: String,
    pub total_started: u64,
    pub total_completed: u64,
    pub total_failed: u64,
    pub avg_duration_ms: u64,
    pub min_duration_ms: u64,
    pub max_duration_ms: u64,
    pub p50_ms: u64,
    pub p90_ms: u64,
    pub p95_ms: u64,
    pub p99_ms: u64,
    pub error_stats: HashMap<String, u64>,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
}

/// 活动指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityMetrics {
    pub activity_type: String,
    pub total_scheduled: u64,
    pub total_completed: u64,
    pub total_failed: u64,
    pub avg_duration_ms: u64,
    pub min_duration_ms: u64,
    pub max_duration_ms: u64,
    pub p50_ms: u64,
    pub p90_ms: u64,
    pub p95_ms: u64,
    pub p99_ms: u64,
    pub error_stats: HashMap<String, u64>,
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
}

/// 延迟统计汇总
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LatencyStatsSummary {
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub workflow_stats: HashMap<String, WorkflowLatencyStats>,
    pub activity_stats: HashMap<String, ActivityLatencyStats>,
}

/// 错误统计汇总
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorStatsSummary {
    pub period_start: DateTime<Utc>,
    pub period_end: DateTime<Utc>,
    pub workflow_errors: HashMap<String, WorkflowErrorStats>,
    pub activity_errors: HashMap<String, ActivityErrorStats>,
}

/// 工作流可视化器
pub struct WorkflowVisualizer {
    engine: Arc<dyn WorkflowEngine>,
    history_analyzer: Arc<WorkflowHistoryAnalyzer>,
}

impl WorkflowVisualizer {
    pub fn new(
        engine: Arc<dyn WorkflowEngine>,
        history_analyzer: Arc<WorkflowHistoryAnalyzer>,
    ) -> Self {
        Self {
            engine,
            history_analyzer,
        }
    }
    
    /// 生成工作流DAG（有向无环图）
    pub async fn generate_workflow_dag(
        &self,
        workflow_id: &WorkflowId,
    ) -> Result<WorkflowDag, WorkflowError> {
        // 获取工作流历史
        let events = self.history_analyzer.get_workflow_history(workflow_id).await?;
        
        // 获取工作流详情
        let status = self.engine.get_workflow_status(workflow_id).await?;
        
        // 创建DAG
        let mut dag = WorkflowDag {
            workflow_id: workflow_id.clone(),
            workflow_type: status.workflow_type,
            nodes: Vec::new(),
            edges: Vec::new(),
            status: status.status,
            start_time: status.start_time,
            end_time: status.end_time,
        };
        
        // 追踪节点ID到索引的映射
        let mut node_map = HashMap::new();
        
        // 跟踪活动和计时器的开始事件
        let mut activity_starts = HashMap::new();
        let mut timer_starts = HashMap::new();
        
        // 添加工作流启动节点
        let start_node = DagNode {
            id: "workflow_start".to_string(),
            node_type: "workflow_start".to_string(),
            label: format!("开始: {}", dag.workflow_type),
            status: "completed".to_string(),
            start_time: dag.start_time,
            end_time: dag.start_time,
            details: json!({}),
        };
        
        node_map.insert(start_node.id.clone(), 0);
        dag.nodes.push(start_node);
        
        // 处理历史事件
        for event in &events {
            match event {
                WorkflowEvent::ActivityStarted { 
                    workflow_id: _, 
                    activity_id, 
                    activity_type, 
                    timestamp, 
                    input,
                    .. 
                } => {
                    // 创建活动节点
                    let node = DagNode {
                        id: format!("activity_{}", activity_id),
                        node_type: "activity".to_string(),
                        label: format!("活动: {}", activity_type),
                        status: "running".to_string(),
                        start_time: *timestamp,
                        end_time: *timestamp, // 暂时设置为开始时间，后续更新
                        details: json!({
                            "activity_id": activity_id,
                            "activity_type": activity_type,
                            "input": input,
                        }),
                    };
                    
                    // 添加到DAG
                    node_map.insert(node.id.clone(), dag.nodes.len());
                    dag.nodes.push(node);
                    
                    // 记录活动开始
                    activity_starts.insert(activity_id.clone(), dag.nodes.len() - 1);
                    
                    // 添加从工作流启动到该活动的边
                    if dag.edges.is_empty() {
                        dag.edges.push(DagEdge {
                            from: "workflow_start".to_string(),
                            to: format!("activity_{}", activity_id),
                            label: "启动".to_string(),
                        });
                    }
                },
                WorkflowEvent::ActivityCompleted { 
                    workflow_id: _, 
                    activity_id, 
                    timestamp, 
                    result,
                    .. 
                } => {
                    // 更新活动节点
                    if let Some(&idx) = activity_starts.get(activity_id) {
                        if let Some(node) = dag.nodes.get_mut(idx) {
                            node.status = "completed".to_string();
                            node.end_time = *timestamp;
                            
                            // 添加结果到详情
                            if let Value::Object(ref mut obj) = node.details {
                                obj.insert("result".to_string(), result.clone());
                                obj.insert("duration_ms".to_string(), json!((node.end_time - node.start_time).num_milliseconds()));
                            }
                        }
                    }
                },
                WorkflowEvent::ActivityFailed { 
                    workflow_id: _, 
                    activity_id, 
                    timestamp, 
                    error,
                    .. 
                } => {
                    // 更新活动节点
                    if let Some(&idx) = activity_starts.get(activity_id) {
                        if let Some(node) = dag.nodes.get_mut(idx) {
                            node.status = "failed".to_string();
                            node.end_time = *timestamp;
                            
                            // 添加错误到详情
                            if let Value::Object(ref mut obj) = node.details {
                                obj.insert("error".to_string(), json!(error));
                                obj.insert("duration_ms".to_string(), json!((node.end_time - node.start_time).num_milliseconds()));
                            }
                        }
                    }
                },
                WorkflowEvent::TimerStarted { 
                    workflow_id: _, 
                    timer_id, 
                    fire_after, 
                    timestamp,
                    .. 
                } => {
                    // 创建计时器节点
                    let node = DagNode {
                        id: format!("timer_{}", timer_id),
                        node_type: "timer".to_string(),
                        label: format!("计时器: {}ms", fire_after),
                        status: "running".to_string(),
                        start_time: *timestamp,
                        end_time: *timestamp, // 暂时设置为开始时间，后续更新
                        details: json!({
                            "timer_id": timer_id,
                            "fire_after_ms": fire_after,
                        }),
                    };
                    
                    // 添加到DAG
                    node_map.insert(node.id.clone(), dag.nodes.len());
                    dag.nodes.push(node);
                    
                    // 记录计时器开始
                    timer_starts.insert(timer_id.clone(), dag.nodes.len() - 1);
                    
                    // 如果前面有活动，添加从最后活动到计时器的边
                    let last_node_id = if !activity_starts.is_empty() {
                        let last_activity = activity_starts.iter().max_by_key(|e| e.1);
                        if let Some((activity_id, _)) = last_activity {
                            format!("activity_{}", activity_id)
                        } else {
                            "workflow_start".to_string()
                        }
                    } else {
                        "workflow_start".to_string()
                    };
                    
                    dag.edges.push(DagEdge {
                        from: last_node_id,
                        to: format!("timer_{}", timer_id),
                        label: "等待".to_string(),
                    });
                },
                WorkflowEvent::TimerFired { 
                    workflow_id: _, 
                    timer_id, 
                    timestamp,
                    .. 
                } => {
                    // 更新计时器节点
                    if let Some(&idx) = timer_starts.get(timer_id) {
                        if let Some(node) = dag.nodes.get_mut(idx) {
                            node.status = "completed".to_string();
                            node.end_time = *timestamp;
                            
                            // 添加持续时间到详情
                            if let Value::Object(ref mut obj) = node.details {
                                obj.insert("duration_ms".to_string(), json!((node.end_time - node.start_time).num_milliseconds()));
                            }
                        }
                    }
                },
                WorkflowEvent::WorkflowCompleted { 
                    workflow_id: _, 
                    timestamp, 
                    result,
                    .. 
                } => {
                    // 创建工作流完成节点
                    let node = DagNode {
                        id: "workflow_complete".to_string(),
                        node_type: "workflow_complete".to_string(),
                        label: format!("完成: {}", dag.workflow_type),
                        status: "completed".to_string(),
                        start_time: *timestamp,
                        end_time: *timestamp,
                        details: json!({
                            "result": result,
                        }),
                    };
                    
                    // 添加到DAG
                    node_map.insert(node.id.clone(), dag.nodes.len());
                    dag.nodes.push(node);
                    
                    // 添加从最后节点到完成节点的边
                    let last_node_id = if !activity_starts.is_empty() {
                        let last_activity = activity_starts.iter().max_by_key(|e| e.1);
                        if let Some((activity_id, _)) = last_activity {
                            format!("activity_{}", activity_id)
                        } else if !timer_starts.is_empty() {
                            let last_timer = timer_starts.iter().max_by_key(|e| e.1);
                            if let Some((timer_id, _)) = last_timer {
                                format!("timer_{}", timer_id)
                            } else {
                                "workflow_start".to_string()
                            }
                        } else {
                            "workflow_start".to_string()
                        }
                    } else if !timer_starts.is_empty() {
                        let last_timer = timer_starts.iter().max_by_key(|e| e.1);
                        if let Some((timer_id, _)) = last_timer {
                            format!("timer_{}", timer_id)
                        } else {
                            "workflow_start".to_string()
                        }
                    } else {
                        "workflow_start".to_string()
                    };
                    
                    dag.edges.push(DagEdge {
                        from: last_node_id,
                        to: "workflow_complete".to_string(),
                        label: "完成".to_string(),
                    });
                },
                WorkflowEvent::WorkflowFailed { 
                    workflow_id: _, 
                    timestamp, 
                    error,
                    .. 
                } => {
                    // 创建工作流失败节点
                    let node = DagNode {
                        id: "workflow_failed".to_string(),
                        node_type: "workflow_failed".to_string(),
                        label: format!("失败: {}", dag.workflow_type),
                        status: "failed".to_string(),
                        start_time: *timestamp,
                        end_time: *timestamp,
                        details: json!({
                            "error": error,
                        }),
                    };
                    
                    // 添加到DAG
                    node_map.insert(node.id.clone(), dag.nodes.len());
                    dag.nodes.push(node);
                    
                    // 添加从最后节点到失败节点的边
                    let last_node_id = if !activity_starts.is_empty() {
                        let last_activity = activity_starts.iter().max_by_key(|e| e.1);
                        if let Some((activity_id, _)) = last_activity {
                            format!("activity_{}", activity_id)
                        } else if !timer_starts.is_empty() {
                            let last_timer = timer_starts.iter().max_by_key(|e| e.1);
                            if let Some((timer_id, _)) = last_timer {
                                format!("timer_{}", timer_id)
                            } else {
                                "workflow_start".to_string()
                            }
                        } else {
                            "workflow_start".to_string()
                        }
                    } else if !timer_starts.is_empty() {
                        let last_timer = timer_starts.iter().max_by_key(|e| e.1);
                        if let Some((timer_id, _)) = last_timer {
                            format!("timer_{}", timer_id)
                        } else {
                            "workflow_start".to_string()
                        }
                    } else {
                        "workflow_start".to_string()
                    };
                    
                    dag.edges.push(DagEdge {
                        from: last_node_id,
                        to: "workflow_failed".to_string(),
                        label: "失败".to_string(),
                    });
                },
                // 其他事件类型可以根据需要添加
                _ => {}
            }
        }
        
        Ok(dag)
    }
    
    /// 生成活动依赖图
    pub fn generate_activity_dependencies(&self, workflow_type: &str) -> Result<ActivityDependencyGraph, WorkflowError> {
        // 这个示例实现假设有一个预定义的工作流结构
        // 在实际应用中，这可能需要通过分析工作流定义或历史记录来生成
        
        let mut graph = ActivityDependencyGraph {
            workflow_type: workflow_type.to_string(),
            nodes: Vec::new(),
            edges: Vec::new(),
        };
        
        // 添加示例节点（在实际应用中，这些应该从工作流定义中提取）
        match workflow_type {
            "OrderProcessing" => {
                // 添加节点
                graph.nodes.push(ActivityDependencyNode {
                    id: "verify_order".to_string(),
                    activity_type: "VerifyOrder".to_string(),
                    description: "验证订单信息".to_string(),
                    estimated_duration_ms: 500,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "process_payment".to_string(),
                    activity_type: "ProcessPayment".to_string(),
                    description: "处理支付".to_string(),
                    estimated_duration_ms: 2000,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "update_inventory".to_string(),
                    activity_type: "UpdateInventory".to_string(),
                    description: "更新库存".to_string(),
                    estimated_duration_ms: 1000,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "ship_order".to_string(),
                    activity_type: "ShipOrder".to_string(),
                    description: "安排发货".to_string(),
                    estimated_duration_ms: 1500,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "send_notification".to_string(),
                    activity_type: "SendNotification".to_string(),
                    description: "发送通知".to_string(),
                    estimated_duration_ms: 300,
                });
                
                // 添加边
                graph.edges.push(ActivityDependencyEdge {
                    from: "verify_order".to_string(),
                    to: "process_payment".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "process_payment".to_string(),
                    to: "update_inventory".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "update_inventory".to_string(),
                    to: "ship_order".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "ship_order".to_string(),
                    to: "send_notification".to_string(),
                    condition: None,
                });
            },
            "LoanApplication" => {
                // 添加节点
                graph.nodes.push(ActivityDependencyNode {
                    id: "verify_applicant".to_string(),
                    activity_type: "VerifyApplicant".to_string(),
                    description: "验证申请人信息".to_string(),
                    estimated_duration_ms: 1000,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "check_credit".to_string(),
                    activity_type: "CheckCredit".to_string(),
                    description: "检查信用记录".to_string(),
                    estimated_duration_ms: 3000,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "verify_income".to_string(),
                    activity_type: "VerifyIncome".to_string(),
                    description: "验证收入".to_string(),
                    estimated_duration_ms: 2000,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "assess_risk".to_string(),
                    activity_type: "AssessRisk".to_string(),
                    description: "评估风险".to_string(),
                    estimated_duration_ms: 1500,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "approve_loan".to_string(),
                    activity_type: "ApproveLoan".to_string(),
                    description: "批准贷款".to_string(),
                    estimated_duration_ms: 500,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "reject_loan".to_string(),
                    activity_type: "RejectLoan".to_string(),
                    description: "拒绝贷款".to_string(),
                    estimated_duration_ms: 500,
                });
                
                graph.nodes.push(ActivityDependencyNode {
                    id: "notify_decision".to_string(),
                    activity_type: "NotifyDecision".to_string(),
                    description: "通知决定".to_string(),
                    estimated_duration_ms: 300,
                });
                
                // 添加边
                graph.edges.push(ActivityDependencyEdge {
                    from: "verify_applicant".to_string(),
                    to: "check_credit".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "verify_applicant".to_string(),
                    to: "verify_income".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "check_credit".to_string(),
                    to: "assess_risk".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "verify_income".to_string(),
                    to: "assess_risk".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "assess_risk".to_string(),
                    to: "approve_loan".to_string(),
                    condition: Some("low_risk".to_string()),
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "assess_risk".to_string(),
                    to: "reject_loan".to_string(),
                    condition: Some("high_risk".to_string()),
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "approve_loan".to_string(),
                    to: "notify_decision".to_string(),
                    condition: None,
                });
                
                graph.edges.push(ActivityDependencyEdge {
                    from: "reject_loan".to_string(),
                    to: "notify_decision".to_string(),
                    condition: None,
                });
            },
            _ => {
                return Err(WorkflowError::NotFound(format!(
                    "工作流类型定义未找到: {}", workflow_type
                )));
            }
        }
        
        Ok(graph)
    }
    
    /// 将工作流DAG转换为DOT格式（用于Graphviz渲染）
    pub fn dag_to_dot(&self, dag: &WorkflowDag) -> String {
        let mut dot = String::new();
        
        // 添加图的开头
        dot.push_str(&format!("digraph \"{}\" {{\n", dag.workflow_id));
        dot.push_str("  node [shape=box style=filled];\n");
        
        // 添加节点
        for node in &dag.nodes {
            // 根据节点类型和状态设置颜色
            let color = match node.status.as_str() {
                "completed" => match node.node_type.as_str() {
                    "workflow_start" => "lightblue",
                    "workflow_complete" => "lightgreen",
                    "activity" => "palegreen",
                    "timer" => "lightyellow",
                    _ => "lightgray",
                },
                "running" => "lightblue",
                "failed" => "lightcoral",
                _ => "lightgray",
            };
            
            // 添加节点定义
            dot.push_str(&format!(
                "  \"{}\" [label=\"{}\" fillcolor=\"{}\"];\n",
                node.id,
                node.label,
                color
            ));
        }
        
        // 添加边
        for edge in &dag.edges {
            dot.push_str(&format!(
                "  \"{}\" -> \"{}\" [label=\"{}\"];\n",
                edge.from,
                edge.to,
                edge.label
            ));
        }
        
        // 添加图的结尾
        dot.push_str("}\n");
        
        dot
    }
    
    /// 将活动依赖图转换为DOT格式
    pub fn activity_deps_to_dot(&self, graph: &ActivityDependencyGraph) -> String {
        let mut dot = String::new();
        
        // 添加图的开头
        dot.push_str(&format!("digraph \"{}\" {{\n", graph.workflow_type));
        dot.push_str("  node [shape=box style=filled];\n");
        
        // 添加节点
        for node in &graph.nodes {
            // 添加节点定义
            dot.push_str(&format!(
                "  \"{}\" [label=\"{}\n{}\" fillcolor=\"lightblue\"];\n",
                node.id,
                node.activity_type,
                node.description
            ));
        }
        
        // 添加边
        for edge in &graph.edges {
            let label = edge.condition.as_ref().map_or(
                String::new(),
                |c| format!(" [label=\"{}\"]", c)
            );
            
            dot.push_str(&format!(
                "  \"{}\" -> \"{}\"{};
                \n",
                edge.from,
                edge.to,
                label
            ));
        }
        
        // 添加图的结尾
        dot.push_str("}\n");
        
        dot
    }
}

/// 工作流DAG（有向无环图）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowDag {
    pub workflow_id: WorkflowId,
    pub workflow_type: String,
    pub nodes: Vec<DagNode>,
    pub edges: Vec<DagEdge>,
    pub status: String,
    pub start_time: DateTime<Utc>,
    pub end_time: Option<DateTime<Utc>>,
}

/// DAG节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DagNode {
    pub id: String,
    pub node_type: String,
    pub label: String,
    pub status: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub details: Value,
}

/// DAG边
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DagEdge {
    pub from: String,
    pub to: String,
    pub label: String,
}

/// 活动依赖图
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityDependencyGraph {
    pub workflow_type: String,
    pub nodes: Vec<ActivityDependencyNode>,
    pub edges: Vec<ActivityDependencyEdge>,
}

/// 活动依赖节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityDependencyNode {
    pub id: String,
    pub activity_type: String,
    pub description: String,
    pub estimated_duration_ms: u64,
}

/// 活动依赖边
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActivityDependencyEdge {
    pub from: String,
    pub to: String,
    pub condition: Option<String>,
}
```

### 8. 集成示例

以下是一个完整的工作流引擎集成示例，展示如何使用我们构建的组件创建一个订单处理工作流：

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // 初始化日志系统
    let logger = ContextualLogger::new()
        .with_context("service", "workflow-engine")
        .with_context("version", "1.0.0");
    
    let file_recorder = FileLogRecorder::new("logs/workflow-engine.log", LogLevel::Debug, 1024 * 1024)?;
    let console_recorder = ConsoleLogRecorder::new(LogLevel::Info, true);
    
    logger.add_recorder(Box::new(file_recorder));
    logger.add_recorder(Box::new(console_recorder));
    
    log_info!(logger, "工作流引擎启动中...");
    
    // 初始化指标系统
    let metric_registry = Arc::new(MetricRegistry::new());
    let prometheus_recorder = PrometheusRecorder::new(9090, "/metrics", 60);
    metric_registry.add_recorder(Box::new(prometheus_recorder));
    
    // 初始化工作流引擎指标
    let engine_metrics = Arc::new(WorkflowEngineMetrics::new(
        Arc::clone(&metric_registry),
        "workflow_engine",
    ));
    
    // 初始化性能分析器
    let tracer = Some(Arc::new(OpenTelemetryTracer::new(
        "workflow-engine",
        Box::new(AlwaysOnSampler),
        Box::new(RandomIdGenerator),
        Box::new(ConsoleSpanExporter),
        TracerConfig::default(),
    )));
    
    let profiler = Arc::new(PerformanceProfiler::new(
        Arc::clone(&engine_metrics),
        tracer.clone(),
        Duration::from_secs(10),
    ));
    
    // 启动定期性能分析任务
    profiler.start_periodic_profiling().await;
    
    // 初始化事件存储
    let pg_config = "host=localhost port=5432 user=postgres password=password dbname=workflow_engine";
    let event_store = Arc::new(PostgresEventStore::new(pg_config).await?);
    
    // 初始化工作流状态存储
    let state_store = Arc::new(EventSourcedStateStore::new(
        Arc::clone(&event_store) as Arc<dyn EventStore>,
    ));
    
    // 初始化检查点存储
    let checkpoint_store = Arc::new(PostgresCheckpointStore::new(pg_config).await?);
    
    // 初始化工作流历史分析器
    let history_analyzer = Arc::new(WorkflowHistoryAnalyzer::new(
        pg_config,
        Arc::clone(&engine_metrics),
    )?);
    
    // 初始化告警管理器
    let slack_webhook = "https://hooks.slack.com/services/TXXXXXXXX/BXXXXXXXX/XXXXXXXXXXXXXXXXXX";
    let alert_channels: Vec<Box<dyn AlertChannel>> = vec![
        Box::new(SlackAlertChannel::new(slack_webhook, AlertSeverity::Warning)),
        Box::new(EmailAlertChannel::new(
            SmtpConfig {
                host: "smtp.example.com".to_string(),
                port: 587,
                username: "alerts@example.com".to_string(),
                password: "password".to_string(),
                from_address: "alerts@example.com".to_string(),
                from_name: "Workflow Alerts".to_string(),
                enable_tls: true,
            },
            vec!["admin@example.com".to_string()],
            AlertSeverity::Error,
        )),
    ];
    
    let alert_store = Arc::new(PostgresAlertStore::new(pg_config).await?);
    let alert_manager = Arc::new(MultiChannelAlertManager::new(
        alert_channels,
        Arc::clone(&alert_store) as Arc<dyn AlertStore>,
        Duration::from_mins(15),
    ));
    
    // 初始化工作流告警助手
    let workflow_alerts = Arc::new(WorkflowAlertHelper::new(
        Arc::clone(&alert_manager) as Arc<dyn AlertManager>,
        "workflow-engine",
    ));
    
    // 初始化工作流追踪助手
    let workflow_tracer = Arc::new(WorkflowTracer::new(
        tracer.clone().unwrap_or_else(|| Arc::new(MockTracer)),
    ));
    
    // 初始化锁管理器
    let lock_manager = Arc::new(LockManager::new());
    
    // 初始化事务管理器
    let transaction_manager = Arc::new(TransactionManager::new(
        Arc::clone(&event_store) as Arc<dyn EventStore>,
        Arc::clone(&lock_manager),
    ));
    
    // 初始化调度器
    let scheduler = Arc::new(WorkflowScheduler::new(
        10, // 并发工作流数
        Arc::clone(&engine_metrics),
    ));
    
    // 初始化资源管理器
    let resource_manager = Arc::new(ResourceManager::new(
        HashMap::from([
            ("cpu".to_string(), 8),
            ("memory".to_string(), 16384),
            ("network".to_string(), 1000),
        ]),
        ResourceQuotaPolicy::Strict,
    ));
    
    // 注册工作流和活动
    let mut registry = DefaultWorkflowRegistry::new();
    
    // 注册订单处理工作流
    registry.register_workflow(
        "OrderProcessing",
        Box::new(|ctx| Box::new(OrderProcessingWorkflow::new(ctx))),
    );
    
    // 注册订单处理活动
    registry.register_activity(
        "VerifyOrder",
        Box::new(|_| Box::new(VerifyOrderActivity)),
    );
    
    registry.register_activity(
        "ProcessPayment",
        Box::new(|_| Box::new(ProcessPaymentActivity)),
    );
    
    registry.register_activity(
        "UpdateInventory",
        Box::new(|_| Box::new(UpdateInventoryActivity)),
    );
    
    registry.register_activity(
        "ShipOrder",
        Box::new(|_| Box::new(ShipOrderActivity)),
    );
    
    registry.register_activity(
        "SendNotification",
        Box::new(|_| Box::new(SendNotificationActivity)),
    );
    
    // 创建工作流引擎
    let workflow_engine = Arc::new(DefaultWorkflowEngine::new(
        Arc::new(registry),
        Arc::clone(&state_store) as Arc<dyn WorkflowStateStore>,
        Arc::clone(&checkpoint_store) as Arc<dyn CheckpointStore>,
        Arc::clone(&transaction_manager),
        Arc::clone(&scheduler),
        Arc::clone(&resource_manager),
        Arc::clone(&profiler),
        Arc::clone(&workflow_alerts),
        Arc::clone(&workflow_tracer),
        EngineConfig {
            max_concurrent_workflows: 100,
            max_concurrent_activities: 500,
            default_workflow_timeout_secs: 3600,
            default_activity_timeout_secs: 300,
            checkpoint_frequency: CheckpointFrequency::EveryNEvents(10),
        },
    ));
    
    // 初始化工作流可视化器
    let visualizer = WorkflowVisualizer::new(
        Arc::clone(&workflow_engine) as Arc<dyn WorkflowEngine>,
        Arc::clone(&history_analyzer),
    );
    
    // 创建API处理器
    let api_handler = WorkflowApiHandler::new(
        Arc::clone(&workflow_engine) as Arc<dyn WorkflowEngine>,
        Arc::clone(&history_analyzer),
        Arc::clone(&engine_metrics),
    );
    
    // 创建并启动HTTP服务器
    let api_routes = api_handler.create_routes();
    
    log_info!(logger, "启动HTTP服务器在 http://0.0.0.0:8080");
    let server = axum::Server::bind(&"0.0.0.0:8080".parse().unwrap())
        .serve(api_routes.into_make_service());
        
    // 示例：启动订单处理工作流
    log_info!(logger, "启动示例订单处理工作流");
    let order_data = json!({
        "order_id": "ORD-12345",
        "customer_id": "CUST-6789",
        "items": [
            {"product_id": "PROD-1", "quantity": 2, "price": 29.99},
            {"product_id": "PROD-2", "quantity": 1, "price": 49.99}
        ],
        "shipping_address": {
            "street": "123 Main St",
            "city": "Anytown",
            "state": "CA",
            "zip": "12345"
        },
        "payment_method": {
            "type": "credit_card",
            "last_four": "1234",
            "expiry": "12/25"
        }
    });
    
    let workflow_id = workflow_engine.start_workflow(
        "OrderProcessing",
        order_data,
        WorkflowOptions {
            workflow_id: Some("order-12345".to_string()),
            task_queue: "orders".to_string(),
            ..Default::default()
        },
    ).await?;
    
    log_info!(logger, "订单处理工作流已启动，ID: {}", workflow_id);
    
    // 等待服务器运行
    server.await?;
    
    Ok(())
}

// 订单处理工作流定义
struct OrderProcessingWorkflow {
    ctx: Box<dyn WorkflowContext>,
}

impl OrderProcessingWorkflow {
    fn new(ctx: Box<dyn WorkflowContext>) -> Self {
        Self { ctx }
    }
}

#[async_trait]
impl Workflow for OrderProcessingWorkflow {
    async fn execute(&mut self, input: Value) -> Result<Value, WorkflowError> {
        // 1. 验证订单
        let order_id = input["order_id"].as_str().unwrap_or_default();
        self.ctx.log_info(&format!("开始处理订单: {}", order_id)).await?;
        
        let verify_result = self.ctx.execute_activity(
            "VerifyOrder",
            input.clone(),
            ActivityOptions {
                retry_policy: RetryPolicy {
                    initial_interval_ms: 1000,
                    backoff_coefficient: 2.0,
                    maximum_interval_ms: 10000,
                    maximum_attempts: 3,
                    non_retryable_errors: vec!["ValidationError".to_string()],
                },
                ..Default::default()
            },
        ).await?;
        
        if !verify_result["valid"].as_bool().unwrap_or(false) {
            return Err(WorkflowError::Activity(format!(
                "订单验证失败: {}", 
                verify_result["reason"].as_str().unwrap_or("未知原因")
            )));
        }
        
        // 2. 处理支付
        self.ctx.log_info(&format!("处理订单 {} 的支付", order_id)).await?;
        let payment_result = self.ctx.execute_activity(
            "ProcessPayment",
            input.clone(),
            ActivityOptions::default(),
        ).await?;
        
        if !payment_result["success"].as_bool().unwrap_or(false) {
            return Err(WorkflowError::Activity(format!(
                "支付处理失败: {}", 
                payment_result["error"].as_str().unwrap_or("未知错误")
            )));
        }
        
        let transaction_id = payment_result["transaction_id"].as_str().unwrap_or("unknown");
        self.ctx.log_info(&format!("支付成功，交易ID: {}", transaction_id)).await?;
        
        // 3. 更新库存
        self.ctx.log_info(&format!("更新订单 {} 的库存", order_id)).await?;
        let inventory_result = self.ctx.execute_activity(
            "UpdateInventory",
            input.clone(),
            ActivityOptions::default(),
        ).await?;
        
        if !inventory_result["success"].as_bool().unwrap_or(false) {
            // 如果库存更新失败，需要退款
            self.ctx.log_warning(&format!("库存更新失败，正在退款")).await?;
            
            // 这里应该有一个退款活动，但简化起见，省略了
            return Err(WorkflowError::Activity(format!(
                "库存更新失败: {}", 
                inventory_result["error"].as_str().unwrap_or("未知错误")
            )));
        }
        
        // 4. 安排发货
        self.ctx.log_info(&format!("为订单 {} 安排发货", order_id)).await?;
        let shipping_result = self.ctx.execute_activity(
            "ShipOrder",
            input.clone(),
            ActivityOptions::default(),
        ).await?;
        
        let tracking_number = shipping_result["tracking_number"].as_str().unwrap_or("unknown");
        self.ctx.log_info(&format!("发货已安排，跟踪号: {}", tracking_number)).await?;
        
        // 5. 发送通知
        let mut notification_input = input.clone();
        if let Value::Object(ref mut obj) = notification_input {
            obj.insert("tracking_number".to_string(), json!(tracking_number));
            obj.insert("transaction_id".to_string(), json!(transaction_id));
        }
        
        self.ctx.log_info(&format!("发送订单 {} 完成通知", order_id)).await?;
        let notification_result = self.ctx.execute_activity(
            "SendNotification",
            notification_input,
            ActivityOptions::default(),
        ).await?;
        
        // 6. 返回结果
        let mut result = json!({
            "order_id": order_id,
            "status": "completed",
            "transaction_id": transaction_id,
            "tracking_number": tracking_number,
        });
        
        if let Value::Object(ref mut obj) = result {
            if let Some(notification_id) = notification_result["notification_id"].as_str() {
                obj.insert("notification_id".to_string(), json!(notification_id));
            }
        }
        
        self.ctx.log_info(&format!("订单 {} 处理完成", order_id)).await?;
        Ok(result)
    }
}

// 活动实现
struct VerifyOrderActivity;

#[async_trait]
impl Activity for VerifyOrderActivity {
    type Input = Value;
    type Output = Value;
    type Error = ActivityError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 模拟验证订单的逻辑
        let order_id = input["order_id"].as_str().ok_or_else(|| {
            ActivityError::new("ValidationError", "缺少订单ID")
        })?;
        
        let items = input["items"].as_array().ok_or_else(|| {
            ActivityError::new("ValidationError", "缺少订单项")
        })?;
        
        if items.is_empty() {
            return Ok(json!({
                "valid": false,
                "reason": "订单没有商品项"
            }));
        }
        
        // 模拟API调用延迟
        tokio::time::sleep(Duration::from_millis(500)).await;
        
        Ok(json!({
            "valid": true,
            "order_id": order_id
        }))
    }
}

struct ProcessPaymentActivity;

#[async_trait]
impl Activity for ProcessPaymentActivity {
    type Input = Value;
    type Output = Value;
    type Error = ActivityError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 模拟处理支付的逻辑
        let order_id = input["order_id"].as_str().ok_or_else(|| {
            ActivityError::new("PaymentError", "缺少订单ID")
        })?;
        
        let payment_method = input["payment_method"].as_object().ok_or_else(|| {
            ActivityError::new("PaymentError", "缺少支付方式")
        })?;
        
        // 计算总金额
        let mut total = 0.0;
        if let Some(items) = input["items"].as_array() {
            for item in items {
                let quantity = item["quantity"].as_f64().unwrap_or(1.0);
                let price = item["price"].as_f64().unwrap_or(0.0);
                total += quantity * price;
            }
        }
        
        // 模拟支付处理延迟
        tokio::time::sleep(Duration::from_secs(1)).await;
        
        // 创建随机的交易ID
        let transaction_id = format!("TXN-{}-{}", 
            order_id,
            thread_rng().sample_iter(&Alphanumeric).take(8).collect::<String>()
        );
        
        Ok(json!({
            "success": true,
            "order_id": order_id,
            "amount": total,
            "transaction_id": transaction_id,
            "payment_method": payment_method["type"]
        }))
    }
}

struct UpdateInventoryActivity;

#[async_trait]
impl Activity for UpdateInventoryActivity {
    type Input = Value;
    type Output = Value;
    type Error = ActivityError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 模拟更新库存的逻辑
        let items = input["items"].as_array().ok_or_else(|| {
            ActivityError::new("InventoryError", "缺少订单项")
        })?;
        
        // 模拟库存更新延迟
        tokio::time::sleep(Duration::from_millis(800)).await;
        
        // 跟踪已更新的商品
        let mut updated_items = Vec::new();
        
        for item in items {
            let product_id = item["product_id"].as_str().unwrap_or("unknown");
            let quantity = item["quantity"].as_i64().unwrap_or(0);
            
            // 模拟库存更新
            updated_items.push(json!({
                "product_id": product_id,
                "quantity": quantity,
                "inventory_status": "updated"
            }));
        }
        
        Ok(json!({
            "success": true,
            "order_id": input["order_id"],
            "updated_items": updated_items
        }))
    }
}

struct ShipOrderActivity;

#[async_trait]
impl Activity for ShipOrderActivity {
    type Input = Value;
    type Output = Value;
    type Error = ActivityError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 模拟安排发货的逻辑
        let order_id = input["order_id"].as_str().ok_or_else(|| {
            ActivityError::new("ShippingError", "缺少订单ID")
        })?;
        
        let shipping_address = input["shipping_address"].as_object().ok_or_else(|| {
            ActivityError::new("ShippingError", "缺少收货地址")
        })?;
        
        // 模拟发货处理延迟
        tokio::time::sleep(Duration::from_secs(1)).await;
        
        // 创建随机的跟踪号
        let tracking_number = format!("TRK-{}-{}", 
            order_id,
            thread_rng().sample_iter(&Alphanumeric).take(12).collect::<String>()
        );
        
        Ok(json!({
            "success": true,
            "order_id": order_id,
            "tracking_number": tracking_number,
            "shipping_carrier": "快递公司",
            "estimated_delivery": (Utc::now() + Duration::from_days(3)).to_rfc3339()
        }))
    }
}

struct SendNotificationActivity;

#[async_trait]
impl Activity for SendNotificationActivity {
    type Input = Value;
    type Output = Value;
    type Error = ActivityError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 模拟发送通知的逻辑
        let order_id = input["order_id"].as_str().ok_or_else(|| {
            ActivityError::new("NotificationError", "缺少订单ID")
        })?;
        
        let tracking_number = input["tracking_number"].as_str().ok_or_else(|| {
            ActivityError::new("NotificationError", "缺少跟踪号")
        })?;
        
        // 模拟通知发送延迟
        tokio::time::sleep(Duration::from_millis(300)).await;
        
        // 创建随机的通知ID
        let notification_id = format!("NOTIF-{}-{}", 
            order_id,
            thread_rng().sample_iter(&Alphanumeric).take(8).collect::<String>()
        );
        
        Ok(json!({
            "success": true,
            "order_id": order_id,
            "notification_id": notification_id,
            "notification_type": "email",
            "message": format!("您的订单 {} 已发货，跟踪号: {}", order_id, tracking_number)
        }))
    }
}
```

### 9. 总结与展望

#### 9.1 关键设计决策回顾

在本工作流引擎的设计和实现过程中，我们做了几个关键的设计决策：

1. **事件溯源架构**：通过将工作流的所有状态变更作为不可变的事件记录，我们实现了可靠的状态管理、完整的执行历史和强大的可审计性。

2. **异步编程模型**：利用Rust的async/await语法和Future特性，实现了高效的并发执行模型，使工作流引擎能够有效管理大量的长时间运行的工作流。

3. **类型安全**：通过Rust的类型系统，确保了工作流和活动定义的类型安全，减少了运行时错误。

4. **故障恢复与持久性**：通过事件存储和检查点机制，实现了工作流的持久化和故障恢复能力。

5. **可扩展性**：通过模块化设计和接口抽象，使系统各个组件都可以被替换或定制，满足不同的业务需求。

6. **可观测性**：集成了日志、指标和分布式追踪系统，使得工作流执行可以被全方位监控和分析。

7. **资源管理**：实现了资源配额和优先级调度，确保系统在高负载情况下仍然可以有序运行。

#### 9.2 与现有工作流系统的比较

与现有的工作流系统相比，我们的实现有以下特点：

1. **Rust的安全性和性能**：相比于Go (Temporal)或Python/Go (Airflow)，Rust提供了更强的内存安全保证和更高的性能潜力。

2. **静态类型系统**：利用Rust的静态类型系统，我们的工作流定义更加安全，可以在编译时发现许多潜在问题。

3. **低资源消耗**：得益于Rust的零成本抽象和精细的内存管理，我们的实现在资源利用方面更加高效。

4. **嵌入式友好**：我们的设计使得工作流引擎可以作为库嵌入到其他Rust应用程序中，而不仅仅作为独立服务。

5. **中心化与分布式兼顾**：我们的设计既支持中心化部署（类似Airflow），也支持分布式执行（类似Temporal）。

#### 9.3 未来工作方向

尽管我们已经实现了一个功能完整的工作流引擎，但仍有一些值得探索的未来方向：

1. **更丰富的DSL**：开发更具表现力的工作流定义领域特定语言，可能通过过程宏实现，使工作流定义更加直观。

2. **跨语言支持**：拓展接口支持其他语言编写的活动和工作流，可能通过WebAssembly或RPC机制实现。

3. **更多存储后端**：增加对更多存储系统的支持，如MongoDB、Redis等，以适应不同的部署环境。

4. **调度算法优化**：进一步优化工作流调度算法，以提高吞吐量和资源利用率。

5. **图形化工作流编辑器**：开发一个图形化的工作流设计工具，使非开发人员也能创建和修改工作流。

6. **增强版本控制**：实现工作流定义的版本控制和兼容性管理，使得工作流可以安全地进化。

7. **混沌测试框架**：开发一个专门的混沌测试框架，用于验证工作流引擎在各种故障情况下的弹性。

#### 9.4 结论

我们的Rust工作流引擎实现了一个强大、类型安全且高性能的系统，适用于各种长时间运行的业务流程。
它综合了事件溯源、异步编程和强类型系统的优势，提供了一个可靠且可扩展的工作流执行环境。

通过深入理解异步计算模型与工作流系统之间的同构关系，我们不仅构建了一个实用的工具，
也揭示了两种范式之间的理论联系，为未来系统设计提供了新的思路。

这个实现既可以作为生产级工作流引擎使用，也可以作为学习Rust和工作流系统原理的教育资源。
随着系统的进一步发展和完善，它有潜力成为Rust生态系统中重要的工作流解决方案。

解释一下工作流引擎和Tokio调度的关系：

### 工作流引擎与Tokio调度的关系

您提出了一个很好的问题。在我们上面实现的工作流引擎中，确实存在两层调度机制：

1. **底层调度（Tokio运行时）**：
   - Tokio作为异步运行时，负责管理底层的任务调度、IO事件循环和线程池
   - 它处理所有的`Future`执行、任务唤醒和线程分配
   - Tokio不了解业务逻辑，也不知道什么是"工作流"或"活动"

2. **上层调度（工作流引擎）**：
   - 我们的工作流引擎实现了自己的调度逻辑（如`WorkflowScheduler`）
   - 它处理工作流优先级、资源管理、并发限制和依赖关系
   - 它决定哪些工作流可以运行、哪些活动可以执行、何时执行

### 两者的关系

工作流引擎通过创建Tokio任务（使用`tokio::spawn`）来执行具体的工作流和活动，
但是**何时**创建这些任务、**哪些**任务被创建，是由工作流引擎的调度器根据工作流的状态和设计来决定的。

例如，当我们的`WorkflowScheduler`决定要执行某个工作流时，它会创建一个Tokio任务：

```rust
tokio::spawn(async move {
    // 执行工作流逻辑
});
```

但是，这个工作流任务的**创建时机**和**执行顺序**是由我们的工作流调度器控制的，而不是由Tokio决定的。
Tokio只负责在有CPU资源可用时运行这些已创建的任务。

### 是否需要完全自己实现？

不需要完全抛弃Tokio重新实现。
这种分层设计是合理且高效的：

- **工作流调度器**：处理业务逻辑层面的决策（什么时候执行哪个工作流）
- **Tokio运行时**：处理系统层面的任务调度（如何高效利用CPU和IO）

如果要完全自己实现，就需要构建自己的异步运行时，处理线程管理、IO多路复用、任务队列等底层机制，
这会大大增加复杂性，且很难做得比Tokio更好。

### 定制化的需求

如果您希望进一步控制调度行为，可以考虑：

1. 实现更复杂的工作流调度策略（在现有架构中）
2. 使用Tokio的更低级API，如自定义`Executor`
3. 在工作流引擎中添加更多控制选项，如任务亲和性、工作窃取策略等

总结来说，我们的工作流引擎确实是"从Tokio手中拿走了一部分调度决策权"，
但同时也利用了Tokio高效的异步执行能力。这是一种常见且有效的分层架构设计。

您提出了一个很好的问题，关于如何在工作流系统中实现更精细的执行调度控制。
我理解您是想要更深入控制任务的执行顺序和方式，超越简单的创建任务的能力。
让我分享一些可能的方案：

### 工作流执行中的精细调度方案

#### 1. 自定义执行器覆盖Tokio调度

```rust
pub struct WorkflowExecutor {
    inner_executor: Arc<TokioExecutor>,
    workflow_priorities: Arc<RwLock<HashMap<WorkflowId, Priority>>>,
    current_running: Arc<AtomicUsize>,
    max_concurrent: usize,
}

impl WorkflowExecutor {
    // 执行具有优先级控制的任务
    pub fn spawn_workflow_task<F>(&self, workflow_id: WorkflowId, future: F) -> JoinHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let priority = {
            let priorities = self.workflow_priorities.read().unwrap();
            priorities.get(&workflow_id).cloned().unwrap_or(Priority::Normal)
        };
        
        let current = Arc::clone(&self.current_running);
        let max = self.max_concurrent;
        
        // 包装future，添加优先级和调度控制
        let controlled_future = async move {
            // 等待执行槽位可用（使用信号量或自定义逻辑）
            while current.load(Ordering::SeqCst) >= max {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
            
            current.fetch_add(1, Ordering::SeqCst);
            let result = future.await;
            current.fetch_sub(1, Ordering::SeqCst);
            
            result
        };
        
        // 根据优先级放入不同的队列
        match priority {
            Priority::High => {
                // 直接在当前线程执行或使用专用线程池
                tokio::task::spawn_blocking(move || {
                    // 阻塞执行
                    futures::executor::block_on(controlled_future)
                })
            }
            Priority::Normal => {
                // 使用普通的tokio spawn
                tokio::spawn(controlled_future)
            }
            Priority::Low => {
                // 使用背景任务池或延迟执行
                tokio::spawn(async move {
                    tokio::time::sleep(Duration::from_millis(50)).await;
                    controlled_future.await
                })
            }
        }
    }
}
```

#### 2. 使用自定义的工作流协程调度器

```rust
pub struct WorkflowCoroutineScheduler {
    task_queues: HashMap<Priority, VecDeque<WorkflowTask>>,
    running_tasks: HashMap<WorkflowId, WorkflowTaskHandle>,
    resource_limits: ResourceLimits,
    preemption_enabled: bool,
}

struct WorkflowTask {
    workflow_id: WorkflowId,
    generator: Pin<Box<dyn Generator<Yield = SchedulerCommand, Return = WorkflowResult>>>,
    state: WorkflowState,
}

enum SchedulerCommand {
    // 调度器命令，允许工作流与调度器通信
    YieldToScheduler,              // 主动让出执行权
    WaitForActivity(ActivityId),   // 等待活动完成
    LimitResourceUsage(ResourceRequest), // 请求资源限制
    CheckPreemptionPoint,          // 检查是否需要被抢占
}

impl WorkflowCoroutineScheduler {
    pub fn tick(&mut self) {
        // 1. 检查已完成的活动和事件
        self.process_completed_activities();
        
        // 2. 按优先级选择下一个要执行的任务
        let next_task = self.select_next_task();
        
        if let Some(mut task) = next_task {
            // 3. 执行任务直到产生SchedulerCommand或完成
            match task.generator.as_mut().resume(()) {
                GeneratorState::Yielded(command) => {
                    // 4. 处理调度命令
                    match command {
                        SchedulerCommand::YieldToScheduler => {
                            // 任务主动让出CPU，放回队列末尾
                            self.requeue_task(task);
                        }
                        SchedulerCommand::WaitForActivity(activity_id) => {
                            // 记录任务正在等待活动
                            task.state = WorkflowState::WaitingForActivity(activity_id);
                            self.waiting_tasks.insert(task.workflow_id.clone(), task);
                        }
                        // 处理其他命令...
                    }
                }
                GeneratorState::Complete(result) => {
                    // 工作流执行完成，处理结果
                    self.handle_workflow_completion(task.workflow_id, result);
                }
            }
        }
        
        // 5. 检查是否需要抢占长时间运行的任务
        if self.preemption_enabled {
            self.check_for_preemption();
        }
    }
    
    // 其他调度器方法...
}
```

#### 3. 基于有向无环图(DAG)的依赖执行引擎

```rust
pub struct DagExecutionEngine<T> {
    graph: DiGraph<TaskNode<T>, ()>,
    node_states: HashMap<NodeIndex, TaskState>,
    node_results: HashMap<NodeIndex, Result<T, TaskError>>,
    pending_tasks: BinaryHeap<PendingTask>,
}

impl<T: Send + 'static> DagExecutionEngine<T> {
    // 添加任务到DAG
    pub fn add_task(&mut self, task: impl FnOnce() -> Result<T, TaskError> + Send + 'static) -> NodeIndex {
        let node = TaskNode {
            task: Box::new(task),
            priority: 0,
        };
        let idx = self.graph.add_node(node);
        self.node_states.insert(idx, TaskState::NotStarted);
        idx
    }
    
    // 添加依赖关系
    pub fn add_dependency(&mut self, dependent: NodeIndex, dependency: NodeIndex) {
        self.graph.add_edge(dependency, dependent, ());
    }
    
    // 执行整个DAG
    pub async fn execute(&mut self) {
        // 1. 找出所有没有依赖的节点
        let roots = self.find_root_nodes();
        
        // 2. 将它们加入待执行队列
        for root in roots {
            self.pending_tasks.push(PendingTask {
                node: root,
                priority: self.graph[root].priority,
            });
            self.node_states.insert(root, TaskState::Pending);
        }
        
        // 3. 执行任务，直到没有更多待执行的任务
        while let Some(pending) = self.pending_tasks.pop() {
            // 获取任务
            let task = &self.graph[pending.node].task;
            
            // 更新状态
            self.node_states.insert(pending.node, TaskState::Running);
            
            // 执行任务
            let result = tokio::task::spawn_blocking(move || {
                (task)()
            }).await.unwrap();
            
            // 保存结果
            self.node_results.insert(pending.node, result);
            self.node_states.insert(pending.node, TaskState::Completed);
            
            // 检查依赖此任务的后续任务
            let dependents = self.find_dependents(pending.node);
            for dependent in dependents {
                // 检查所有依赖是否都已完成
                if self.are_dependencies_completed(dependent) {
                    self.pending_tasks.push(PendingTask {
                        node: dependent,
                        priority: self.graph[dependent].priority,
                    });
                    self.node_states.insert(dependent, TaskState::Pending);
                }
            }
        }
    }
}
```

#### 4. 混合执行模型：状态机 + 回调控制

```rust
pub struct HybridExecutionController {
    workflow_states: Arc<RwLock<HashMap<WorkflowId, WorkflowExecutionState>>>,
    continuation_store: Arc<RwLock<HashMap<StepId, Box<dyn FnOnce() + Send + 'static>>>>,
    scheduler: Arc<Mutex<TaskScheduler>>,
}

impl HybridExecutionController {
    // 启动工作流执行
    pub async fn execute_workflow(&self, workflow: WorkflowDefinition) -> Result<WorkflowResult, WorkflowError> {
        let workflow_id = workflow.id.clone();
        
        // 创建初始状态
        let initial_state = WorkflowExecutionState {
            current_step: "start".to_string(),
            data: workflow.initial_data,
            status: WorkflowStatus::Running,
        };
        
        // 存储状态
        {
            let mut states = self.workflow_states.write().await;
            states.insert(workflow_id.clone(), initial_state);
        }
        
        // 创建工作流执行的编排器
        let orchestrator = WorkflowOrchestrator::new(
            workflow_id.clone(),
            workflow.steps,
            Arc::clone(&self.workflow_states),
            Arc::clone(&self.continuation_store),
            Arc::clone(&self.scheduler),
        );
        
        // 启动编排器
        orchestrator.execute().await
    }
    
    // 恢复暂停的工作流
    pub async fn resume_workflow(&self, workflow_id: &WorkflowId, step_id: &StepId) -> Result<(), WorkflowError> {
        // 获取保存的continuation
        let continuation = {
            let mut continuations = self.continuation_store.write().await;
            continuations.remove(step_id).ok_or(WorkflowError::StepNotFound)?
        };
        
        // 更新状态
        {
            let mut states = self.workflow_states.write().await;
            if let Some(state) = states.get_mut(workflow_id) {
                state.status = WorkflowStatus::Running;
            }
        }
        
        // 调度continuation的执行
        let mut scheduler = self.scheduler.lock().await;
        scheduler.schedule(workflow_id.clone(), continuation);
        
        Ok(())
    }
}

// 工作流编排器
struct WorkflowOrchestrator {
    workflow_id: WorkflowId,
    steps: HashMap<String, WorkflowStep>,
    states: Arc<RwLock<HashMap<WorkflowId, WorkflowExecutionState>>>,
    continuations: Arc<RwLock<HashMap<StepId, Box<dyn FnOnce() + Send + 'static>>>>,
    scheduler: Arc<Mutex<TaskScheduler>>,
}

impl WorkflowOrchestrator {
    async fn execute(&self) -> Result<WorkflowResult, WorkflowError> {
        let (sender, receiver) = oneshot::channel();
        let workflow_id = self.workflow_id.clone();
        
        // 创建执行上下文
        let ctx = ExecutionContext {
            workflow_id: workflow_id.clone(),
            states: Arc::clone(&self.states),
            continuations: Arc::clone(&self.continuations),
            scheduler: Arc::clone(&self.scheduler),
        };
        
        // 从第一步开始执行
        self.execute_step("start", ctx, Some(sender)).await;
        
        // 等待最终结果
        receiver.await.map_err(|_| WorkflowError::Canceled)
    }
    
    async fn execute_step(
        &self, 
        step_name: &str, 
        ctx: ExecutionContext,
        result_sender: Option<oneshot::Sender<WorkflowResult>>,
    ) {
        let step = match self.steps.get(step_name) {
            Some(s) => s,
            None => {
                if let Some(sender) = result_sender {
                    let _ = sender.send(Err(WorkflowError::StepNotFound));
                }
                return;
            }
        };
        
        // 创建步骤执行器
        let executor = StepExecutor::new(
            step.clone(),
            ctx,
            result_sender,
            self.steps.clone(),
        );
        
        // 调度执行
        let mut scheduler = self.scheduler.lock().await;
        scheduler.schedule_with_priority(
            self.workflow_id.clone(),
            Box::new(move || {
                executor.execute();
            }),
            step.priority,
        );
    }
}
```

#### 5. 基于配额和时间片的调度器

```rust
pub struct TimeSliceScheduler {
    workflows: HashMap<WorkflowId, WorkflowRuntime>,
    time_slice_ms: u64,
    quota_manager: ResourceQuotaManager,
    active_queue: VecDeque<WorkflowId>,
    paused_queue: VecDeque<WorkflowId>,
}

impl TimeSliceScheduler {
    pub async fn run(&mut self) {
        loop {
            // 处理一个调度周期
            self.process_scheduling_cycle().await;
            
            // 让出控制权，允许其他任务执行
            tokio::task::yield_now().await;
        }
    }
    
    async fn process_scheduling_cycle(&mut self) {
        // 1. 从活跃队列获取下一个要执行的工作流
        if let Some(workflow_id) = self.active_queue.pop_front() {
            if let Some(runtime) = self.workflows.get_mut(&workflow_id) {
                // 2. 检查资源配额
                if self.quota_manager.check_quota(&workflow_id, &runtime.resource_requirements) {
                    // 3. 获取时间片
                    let time_slice = self.time_slice_ms;
                    
                    // 4. 执行工作流直到时间片用完或工作流暂停/完成
                    let execution_result = tokio::time::timeout(
                        Duration::from_millis(time_slice),
                        runtime.execute_next_step()
                    ).await;
                    
                    match execution_result {
                        Ok(StepResult::Continue) => {
                            // 工作流需要继续执行，放回队列
                            self.active_queue.push_back(workflow_id);
                        }
                        Ok(StepResult::Waiting) => {
                            // 工作流在等待某些条件，移到暂停队列
                            self.paused_queue.push_back(workflow_id);
                        }
                        Ok(StepResult::Completed) => {
                            // 工作流已完成，释放资源
                            self.quota_manager.release_resources(&workflow_id);
                            self.workflows.remove(&workflow_id);
                        }
                        Err(_) => {
                            // 时间片用完，重新放回队列末尾
                            self.active_queue.push_back(workflow_id);
                        }
                    }
                } else {
                    // 资源不足，移到暂停队列
                    self.paused_queue.push_back(workflow_id);
                }
            }
        }
        
        // 5. 检查暂停队列中的工作流，如果条件满足则移回活跃队列
        self.check_paused_workflows();
    }
    
    fn check_paused_workflows(&mut self) {
        let mut to_reactivate = Vec::new();
        
        for (i, workflow_id) in self.paused_queue.iter().enumerate() {
            if let Some(runtime) = self.workflows.get(workflow_id) {
                // 检查是否可以恢复执行
                if runtime.can_resume() && 
                   self.quota_manager.check_quota(workflow_id, &runtime.resource_requirements) {
                    to_reactivate.push(i);
                }
            }
        }
        
        // 从暂停队列移除并添加到活跃队列
        for i in to_reactivate.into_iter().rev() {
            if let Some(workflow_id) = self.paused_queue.remove(i) {
                self.active_queue.push_back(workflow_id);
            }
        }
    }
}
```

### 建议的最佳方案

基于您的需求，我推荐结合使用**方案4**（混合执行模型）和**方案5**（基于配额和时间片的调度器）。
这种组合可以提供：

1. **精细的执行控制**：通过状态机和回调，可以在任意点暂停和恢复执行
2. **资源感知**：通过配额管理确保系统稳定性
3. **公平调度**：时间片机制防止单个工作流占用过多资源
4. **优先级支持**：重要工作流可以获得更多执行机会
5. **与Tokio集成**：仍然利用Tokio强大的异步原语，但控制权在工作流引擎手中

实现这种方案需要更多工作，但会给您带来显著的控制优势，特别是在处理复杂、长时间运行的工作流时。

这种调度机制不仅可以控制工作流的执行顺序，
还能控制每个工作流内部的执行进度和资源使用情况，
实现真正的细粒度控制。

您认为这些方案中哪一个最接近您的需求？或者您有其他特定的考虑点需要进一步讨论？

## 工作流调度策略的领域特性分析

您提出了一个非常深刻的问题：如何根据不同工作流的内在特性选择最适合的调度策略。这确实是工作流引擎设计中的核心问题之一。下面我将详细分析各种工作流模式的特性，以及与之匹配的调度策略设计。

### 1. 线性序列型工作流的状态机调度

#### 1.1 特性分析

线性序列型工作流具有明确的前后执行顺序，每个步骤有明确的开始和结束，类似于流水线处理：

- 步骤之间存在严格的前序依赖关系
- 执行路径相对固定，分支较少
- 状态转换清晰可预测
- 每个状态对应一个明确的处理逻辑

#### 1.2 调度策略设计

```rust
pub struct StateMachineScheduler<S, E> {
    current_state: S,
    state_handlers: HashMap<S, Box<dyn Fn(&E) -> (TaskExecution, S)>>,
    state_transitions: HashMap<S, Vec<(Condition<E>, S)>>,
}

impl<S: Eq + Hash + Clone, E> StateMachineScheduler<S, E> {
    /// 注册状态处理器
    pub fn register_handler<F>(&mut self, state: S, handler: F)
    where
        F: Fn(&E) -> (TaskExecution, S) + 'static,
    {
        self.state_handlers.insert(state, Box::new(handler));
    }
    
    /// 注册状态转换规则
    pub fn register_transition(&mut self, from: S, condition: Condition<E>, to: S) {
        self.state_transitions
            .entry(from)
            .or_insert_with(Vec::new)
            .push((condition, to));
    }
    
    /// 执行状态机的单步转换
    pub async fn step(&mut self, context: &E) -> StepResult {
        // 1. 获取当前状态的处理器
        let handler = match self.state_handlers.get(&self.current_state) {
            Some(h) => h,
            None => return StepResult::Error(format!("无处理器: {:?}", self.current_state)),
        };
        
        // 2. 执行当前状态的业务逻辑
        let (execution, next_state_suggestion) = handler(context);
        
        // 3. 等待任务执行完成
        let execution_result = match execution {
            TaskExecution::Immediate(task) => task.await,
            TaskExecution::Deferred(future) => future.await,
            TaskExecution::Completed => Ok(()),
        };
        
        if let Err(e) = execution_result {
            return StepResult::Error(format!("执行错误: {}", e));
        }
        
        // 4. 检查是否有满足条件的状态转换
        if let Some(transitions) = self.state_transitions.get(&self.current_state) {
            for (condition, target_state) in transitions {
                if condition.evaluate(context) {
                    // 找到满足条件的转换
                    self.current_state = target_state.clone();
                    return if self.is_final_state(&target_state) {
                        StepResult::Completed
                    } else {
                        StepResult::Continue
                    };
                }
            }
        }
        
        // 5. 使用处理器建议的下一状态
        self.current_state = next_state_suggestion;
        
        if self.is_final_state(&self.current_state) {
            StepResult::Completed
        } else {
            StepResult::Continue
        }
    }
    
    /// 检查是否为终止状态
    fn is_final_state(&self, state: &S) -> bool {
        !self.state_transitions.contains_key(state) && 
        !self.state_handlers.contains_key(state)
    }
}

/// 高级调度控制：允许工作流自己控制执行时机
impl<S: Eq + Hash + Clone, E> StateMachineScheduler<S, E> {
    /// 使用优化的调度策略执行整个状态机
    pub async fn execute_optimized(&mut self, context: &mut E) -> Result<(), WorkflowError> {
        // 分析状态图，识别可以批处理的状态序列
        let batches = self.analyze_state_batches();
        
        // 执行状态批次
        for batch in batches {
            match batch {
                StateBatch::Sequential(states) => {
                    // 线性顺序执行的状态批次
                    for state in states {
                        self.current_state = state;
                        match self.step(context).await {
                            StepResult::Continue => continue,
                            StepResult::Completed => return Ok(()),
                            StepResult::Error(e) => return Err(WorkflowError::Execution(e)),
                        }
                    }
                }
                StateBatch::Parallel(states) => {
                    // 可并行执行的状态批次
                    let mut futures = Vec::new();
                    for state in states {
                        let handler = self.state_handlers.get(&state).cloned();
                        if let Some(h) = handler {
                            let ctx = context; // 在实际实现中可能需要克隆或引用计数
                            futures.push(async move {
                                let (execution, _) = h(ctx);
                                match execution {
                                    TaskExecution::Immediate(task) => task.await,
                                    TaskExecution::Deferred(future) => future.await,
                                    TaskExecution::Completed => Ok(()),
                                }
                            });
                        }
                    }
                    
                    // 等待所有并行状态完成
                    let results = join_all(futures).await;
                    if let Some(err) = results.into_iter().find_map(|r| r.err()) {
                        return Err(WorkflowError::Execution(format!("并行执行错误: {}", err)));
                    }
                    
                    // 确定下一个状态
                    // 这里需要复杂的逻辑来确定从并行批次后的下一个状态
                }
            }
        }
        
        Ok(())
    }
    
    /// 分析状态图，识别顺序和并行批次
    fn analyze_state_batches(&self) -> Vec<StateBatch<S>> {
        // 实现状态图分析算法
        // 1. 构建状态依赖图
        // 2. 识别线性序列
        // 3. 识别可并行执行的状态集
        // 4. 构建执行批次
        // ...
        
        Vec::new() // 简化实现
    }
}
```

#### 1.3 优化点

- **状态合并**：识别可以合并的连续状态，减少状态转换开销
- **延迟载入**：仅加载当前状态及其可能的下一状态的处理逻辑
- **预执行优化**：分析整个状态图，为直线路径优化调度
- **缓存状态上下文**：减少状态之间传递数据的开销

### 2. 编排型工作流的事件驱动调度

#### 2.1 特性分析

编排型工作流通常具有复杂的执行路径，包含分支、循环和并行执行：

- 执行路径可能包含条件分支和动态决策
- 活动之间可能存在复杂的依赖关系
- 执行过程中可能需要等待外部事件或信号
- 可能包含人工干预步骤

#### 2.2 事件驱动调度策略

```rust
pub struct EventDrivenScheduler {
    event_bus: Arc<EventBus>,
    workflow_states: Arc<RwLock<HashMap<WorkflowId, WorkflowState>>>,
    activity_registry: Arc<ActivityRegistry>,
    task_queues: HashMap<String, TaskQueue>,
}

impl EventDrivenScheduler {
    /// 注册工作流事件处理器
    pub fn register_event_handler<F>(&mut self, event_type: &str, handler: F) 
    where
        F: Fn(Event) -> Vec<Command> + Send + Sync + 'static
    {
        self.event_bus.register(event_type, Box::new(handler));
    }
    
    /// 发布事件
    pub async fn publish_event(&self, event: Event) {
        // 1. 发布事件到事件总线
        let commands = self.event_bus.dispatch(event.clone()).await;
        
        // 2. 处理生成的命令
        for command in commands {
            match command {
                Command::StartActivity { workflow_id, activity_id, activity_type, input } => {
                    self.schedule_activity(workflow_id, activity_id, activity_type, input).await;
                }
                Command::CompleteWorkflow { workflow_id, result } => {
                    self.complete_workflow(workflow_id, result).await;
                }
                Command::SignalWorkflow { workflow_id, signal_name, data } => {
                    self.signal_workflow(workflow_id, signal_name, data).await;
                }
                Command::Timer { workflow_id, timer_id, delay } => {
                    self.schedule_timer(workflow_id, timer_id, delay).await;
                }
                // 处理其他命令类型...
            }
        }
        
        // 3. 检查事件是否解除了某些工作流的阻塞
        self.check_blocked_workflows(event).await;
    }
    
    /// 调度活动执行
    async fn schedule_activity(
        &self, 
        workflow_id: WorkflowId, 
        activity_id: String, 
        activity_type: String,
        input: Value,
    ) {
        // 1. 获取活动实现
        let activity_impl = match self.activity_registry.get(&activity_type) {
            Some(act) => act,
            None => {
                self.publish_event(Event::ActivityFailed {
                    workflow_id,
                    activity_id,
                    error: format!("未找到活动类型: {}", activity_type),
                }).await;
                return;
            }
        };
        
        // 2. 确定任务队列
        let queue_name = self.determine_task_queue(&activity_type);
        
        // 3. 创建活动任务
        let task = ActivityTask {
            workflow_id: workflow_id.clone(),
            activity_id: activity_id.clone(),
            activity_type,
            input,
            activity_impl,
        };
        
        // 4. 将任务添加到队列
        if let Some(queue) = self.task_queues.get_mut(&queue_name) {
            // 发布开始执行事件
            self.publish_event(Event::ActivityStarted {
                workflow_id: workflow_id.clone(),
                activity_id: activity_id.clone(),
            }).await;
            
            // 调度任务执行
            queue.push(task);
        } else {
            // 队列不存在，报告失败
            self.publish_event(Event::ActivityFailed {
                workflow_id,
                activity_id,
                error: format!("任务队列不存在: {}", queue_name),
            }).await;
        }
    }
    
    /// 检查事件是否解除了工作流的阻塞
    async fn check_blocked_workflows(&self, event: Event) {
        let blocked_workflows = {
            let states = self.workflow_states.read().await;
            states.iter()
                .filter(|(_, state)| state.is_blocked_by_event(&event))
                .map(|(id, _)| id.clone())
                .collect::<Vec<_>>()
        };
        
        for workflow_id in blocked_workflows {
            // 发布工作流可继续执行事件
            self.publish_event(Event::WorkflowUnblocked {
                workflow_id,
                unblocking_event: Box::new(event.clone()),
            }).await;
        }
    }
    
    /// 动态调整任务队列
    pub fn adjust_queue_capacity(&mut self, queue_name: &str, new_capacity: usize) {
        if let Some(queue) = self.task_queues.get_mut(queue_name) {
            queue.set_capacity(new_capacity);
        }
    }
    
    /// 根据队列负载动态调整工作者数量
    pub async fn auto_scale_workers(&self) {
        for (queue_name, queue) in &self.task_queues {
            let queue_size = queue.size();
            let current_workers = queue.worker_count();
            
            // 根据队列大小和当前工作者数量决定是否需要扩缩容
            if queue_size > current_workers * 10 && current_workers < queue.max_workers() {
                // 队列负载高，增加工作者
                self.spawn_workers(queue_name, (current_workers / 2).max(1)).await;
            } else if queue_size < current_workers * 2 && current_workers > queue.min_workers() {
                // 队列负载低，减少工作者
                self.reduce_workers(queue_name, (current_workers / 3).max(1)).await;
            }
        }
    }
}

/// 针对反馈选择逻辑的调度优化
impl EventDrivenScheduler {
    /// 注册条件决策节点
    pub fn register_decision_point(
        &mut self,
        workflow_type: &str,
        decision_point: &str,
        conditions: Vec<(Condition, String)>, // 条件和目标活动映射
    ) {
        // 记录决策点信息，用于优化调度
        // ...
    }
    
    /// 优化条件分支的执行
    pub async fn optimize_decision_execution(
        &self,
        workflow_id: &WorkflowId,
        decision_point: &str,
        context: &Value,
    ) -> Option<String> {
        // 1. 获取该决策点的所有可能条件
        let conditions = self.get_decision_conditions(workflow_id, decision_point);
        
        // 2. 并行评估所有条件
        let mut futures = Vec::new();
        for (condition, target) in &conditions {
            let ctx = context.clone();
            let target_clone = target.clone();
            futures.push(async move {
                if condition.evaluate(&ctx).await {
                    Some(target_clone)
                } else {
                    None
                }
            });
        }
        
        // 3. 等待第一个满足的条件
        let results = future::select_all(futures).await;
        
        // 4. 返回第一个满足的目标活动
        results.0
    }
    
    /// 预测性调度：基于历史决策数据的预执行
    pub async fn predictive_schedule(
        &self,
        workflow_id: &WorkflowId,
        decision_point: &str,
    ) {
        // 1. 获取历史决策统计
        let decision_stats = self.get_decision_statistics(workflow_id, decision_point);
        
        // 2. 找出最可能的决策路径
        if let Some((most_likely_path, probability)) = decision_stats.most_likely_path() {
            // 只有当概率超过阈值时才进行预执行
            if probability > 0.8 {
                // 3. 预加载该路径的活动
                self.preload_activity_path(most_likely_path).await;
            }
        }
    }
}
```

#### 2.3 优化点

- **事件批处理**：批量处理相关事件，减少调度开销
- **预测性调度**：基于历史执行模式预测可能的执行路径
- **自适应队列**：根据负载自动调整任务队列容量和工作者数量
- **决策缓存**：缓存常见条件的评估结果，加速分支选择
- **动态优先级**：根据工作流进度和等待时间动态调整优先级

### 3. 事件流型工作流的公平调度策略

#### 3.1 特性分析

事件流型工作流（如Petri网模型）具有以下特性：

- 基于事件触发，无明确的控制流
- 多个并发活动可能同时活跃
- 资源竞争问题更为突出
- 需要处理事件的顺序和时序依赖

#### 3.2 公平调度策略设计

```rust
pub struct FairScheduler {
    tokens: HashMap<PlaceId, usize>,  // Petri网中的标记
    transitions: HashMap<TransitionId, Transition>,
    resource_manager: Arc<ResourceManager>,
    active_transitions: BinaryHeap<RankedTransition>,
    fairness_tracker: HashMap<TransitionId, FairnessMetrics>,
}

impl FairScheduler {
    /// 注册转换规则
    pub fn register_transition(&mut self, transition: Transition) {
        self.transitions.insert(transition.id.clone(), transition);
    }
    
    /// 放置初始标记
    pub fn place_tokens(&mut self, place_id: PlaceId, count: usize) {
        *self.tokens.entry(place_id).or_insert(0) += count;
    }
    
    /// 执行调度周期
    pub async fn schedule_cycle(&mut self) -> CycleResult {
        // 1. 找出所有已启用的转换
        self.find_enabled_transitions();
        
        // 2. 如果没有启用的转换，调度周期结束
        if self.active_transitions.is_empty() {
            return CycleResult::NoEnabledTransitions;
        }
        
        // 3. 根据公平性指标对转换进行排序（已通过优先队列实现）
        
        // 4. 选择优先级最高的转换执行
        let top_transition = match self.active_transitions.pop() {
            Some(t) => t,
            None => return CycleResult::NoEnabledTransitions,
        };
        
        // 5. 执行转换
        let result = self.fire_transition(&top_transition.id).await;
        
        // 6. 更新公平性指标
        self.update_fairness_metrics(&top_transition.id, &result);
        
        // 7. 返回执行结果
        match result {
            TransitionResult::Success => CycleResult::TransitionFired(top_transition.id),
            TransitionResult::InsufficientTokens => {
                // 标记不足，这不应该发生，因为我们已经检查了
                CycleResult::Error("标记不足".to_string())
            }
            TransitionResult::ResourceUnavailable => {
                // 资源不可用，稍后重试
                CycleResult::ResourceBlocked(top_transition.id)
            }
            TransitionResult::Error(e) => CycleResult::Error(e),
        }
    }
    
    /// 查找所有已启用的转换
    fn find_enabled_transitions(&mut self) {
        self.active_transitions.clear();
        
        for (id, transition) in &self.transitions {
            // 检查是否所有输入位置都有足够的标记
            let is_enabled = transition.inputs.iter().all(|(place_id, required)| {
                self.tokens.get(place_id).map_or(0, |count| *count) >= *required
            });
            
            if is_enabled {
                // 计算转换的优先级分数
                let fairness_metrics = self.fairness_tracker
                    .entry(id.clone())
                    .or_insert_with(FairnessMetrics::default);
                
                let priority = self.calculate_priority(transition, fairness_metrics);
                
                // 添加到活跃转换队列
                self.active_transitions.push(RankedTransition {
                    id: id.clone(),
                    priority,
                });
            }
        }
    }
    
    /// 执行转换
    async fn fire_transition(&mut self, transition_id: &TransitionId) -> TransitionResult {
        let transition = match self.transitions.get(transition_id) {
            Some(t) => t,
            None => return TransitionResult::Error(format!("转换不存在: {:?}", transition_id)),
        };
        
        // 1. 检查输入标记
        for (place_id, required) in &transition.inputs {
            if self.tokens.get(place_id).map_or(0, |count| *count) < *required {
                return TransitionResult::InsufficientTokens;
            }
        }
        
        // 2. 检查资源可用性
        if !self.resource_manager.allocate_resources(&transition.resource_requirements).await {
            return TransitionResult::ResourceUnavailable;
        }
        
        // 3. 执行转换逻辑
        let action_result = match &transition.action {
            Some(action) => action().await,
            None => Ok(()),
        };
        
        // 4. 处理执行结果
        if let Err(e) = action_result {
            // 释放已分配的资源
            self.resource_manager.release_resources(&transition.resource_requirements).await;
            return TransitionResult::Error(format!("执行错误: {}", e));
        }
        
        // 5. 移除输入标记
        for (place_id, count) in &transition.inputs {
            if let Some(tokens) = self.tokens.get_mut(place_id) {
                *tokens -= count;
            }
        }
        
        // 6. 添加输出标记
        for (place_id, count) in &transition.outputs {
            *self.tokens.entry(place_id.clone()).or_insert(0) += count;
        }
        
        // 7. 释放资源
        self.resource_manager.release_resources(&transition.resource_requirements).await;
        
        TransitionResult::Success
    }
    
    /// 计算转换优先级
    fn calculate_priority(&self, transition: &Transition, metrics: &FairnessMetrics) -> f64 {
        // 基础优先级
        let base_priority = transition.base_priority as f64;
        
        // 等待时间因子（等待越久优先级越高）
        let wait_factor = if metrics.last_execution.is_some() {
            let elapsed = metrics.last_execution.unwrap().elapsed().as_secs() as f64;
            (1.0 + elapsed / 60.0).min(5.0) // 最多提高5倍优先级
        } else {
            3.0 // 首次执行给予中等优先级提升
        };
        
        // 执行频率因子（执行次数越少优先级越高）
        let frequency_factor = 1.0 + 10.0 / (10.0 + metrics.execution_count as f64);
        
        // 资源效率因子（资源需求越少优先级越高）
        let resource_factor = 1.0 / (1.0 + transition.resource_requirements.weight() as f64 / 100.0);
        
        // 计算最终优先级
        base_priority * wait_factor * frequency_factor * resource_factor
    }
    
    /// 更新公平性指标
    fn update_fairness_metrics(&mut self, transition_id: &TransitionId, result: &TransitionResult) {
        if let Some(metrics) = self.fairness_tracker.get_mut(transition_id) {
            match result {
                TransitionResult::Success => {
                    metrics.execution_count += 1;
                    metrics.last_execution = Some(Instant::now());
                    metrics.success_count += 1;
                }
                TransitionResult::ResourceUnavailable => {
                    metrics.resource_block_count += 1;
                }
                TransitionResult::Error(_) => {
                    metrics.error_count += 1;
                }
                _ => {}
            }
        }
    }
    
    /// 防止饥饿：提升长时间未执行的转换优先级
    pub fn prevent_starvation(&mut self) {
        let now = Instant::now();
        
        for (id, metrics) in &mut self.fairness_tracker {
            if let Some(last_exec) = metrics.last_execution {
                let elapsed = now.duration_since(last_exec);
                
                // 如果超过阈值时间未执行，增加饥饿计数
                if elapsed > Duration::from_secs(300) { // 5分钟
                    metrics.starvation_level += 1;
                    
                    // 如果饥饿级别过高，强制执行
                    if metrics.starvation_level >= 3 {
                        // 下一次调度循环时将获得最高优先级
                        if let Some(transition) = self.transitions.get(id) {
                            // 临时提高基础优先级
                            let temp_transition = Transition {
                                base_priority: u8::MAX,
                                ..transition.clone()
                            };
                            self.transitions.insert(id.clone(), temp_transition);
                            
                            // 重置饥饿级别
                            metrics.starvation_level = 0;
                        }
                    }
                }
            }
        }
    }
    
    /// 自适应资源分配
    pub async fn adaptive_resource_allocation(&mut self) {
        // 分析当前系统负载
        let system_load = self.resource_manager.get_system_load().await;
        
        // 根据系统负载动态调整资源分配策略
        if system_load > 0.8 { // 高负载
            // 优先保障关键转换的资源
            self.resource_manager.prioritize_critical_transitions().await;
        } else if system_load < 0.3 { // 低负载
            // 均衡分配资源，提高公平性
            self.resource_manager.balance_resources().await;
        }
    }
}
```

#### 3.3 优化点

- **动态优先级调整**：根据执行历史自动调整转换优先级
- **资源预留**：为关键转换预留资源，确保及时执行
- **饥饿预防**：确保所有转换都有机会执行，避免某些转换长时间不被调度
- **批处理转换**：识别可同时触发的转换进行批处理
- **负载感知调度**：根据系统负载动态调整调度策略

### 4. 混合工作流的自适应调度策略

#### 4.1 特性分析

现实世界的工作流通常混合了多种模式：

- 可能包含顺序执行、条件分支、并行处理等多种结构
- 工作流可能嵌套或组合其他工作流
- 不同部分可能具有不同的执行特性和资源需求
- 执行环境和负载状况可能动态变化

#### 4.2 自适应混合调度策略

```rust
pub struct AdaptiveScheduler {
    // 包含多种调度器实现
    state_machine_scheduler: StateMachineScheduler,
    event_driven_scheduler: EventDrivenScheduler,
    fair_scheduler: FairScheduler,
    
    // 当前工作流状态
    workflow_patterns: HashMap<WorkflowId, WorkflowPattern>,
    execution_profiles: HashMap<WorkflowId, ExecutionProfile>,
    
    // 系统状态监控
    system_monitor: Arc<SystemMonitor>,
    
    // 调度策略选择器
    strategy_selector: StrategySelector,
}

impl AdaptiveScheduler {
    /// 根据工作流特性和系统状态选择最佳调度策略
    pub fn select_strategy(&self, workflow_id: &WorkflowId) -> SchedulingStrategy {
        // 1. 获取工作流模式
        let pattern = match self.workflow_patterns.get(workflow_id) {
            Some(p) => p,
            None => return SchedulingStrategy::Default, // 默认策略
        };
        
        // 2. 获取执行配置
        let profile = self.execution_profiles.get(workflow_id);
        
        // 3. 获取系统状态
        let system_state = self.system_monitor.get_current_state();
        
        // 4. 使用策略选择器选择最佳策略
        self.strategy_selector.select(pattern, profile, &system_state)
    }
    
    /// 执行工作流步骤
    pub async fn execute_step(&mut self, workflow_id: &WorkflowId) -> StepResult {
        // 选择调度策略
        let strategy = self.select_strategy(workflow_id);
        
        // 根据策略执行步骤
        match strategy {
            SchedulingStrategy::StateMachine => {
                // 使用状态机调度器
                self.state_machine_scheduler.execute_step(workflow_id).await
            }
            SchedulingStrategy::EventDriven => {
                // 使用事件
```rust
            SchedulingStrategy::EventDriven => {
                // 使用事件驱动调度器
                self.event_driven_scheduler.execute_step(workflow_id).await
            }
            SchedulingStrategy::FairScheduling => {
                // 使用公平调度器
                self.fair_scheduler.execute_step(workflow_id).await
            }
            SchedulingStrategy::Hybrid(strategies) => {
                // 混合策略：可能需要分解工作流或组合多种调度结果
                self.execute_hybrid_step(workflow_id, &strategies).await
            }
            SchedulingStrategy::Default => {
                // 默认使用事件驱动调度
                self.event_driven_scheduler.execute_step(workflow_id).await
            }
        }
    }
    
    /// 执行混合调度策略
    async fn execute_hybrid_step(
        &mut self, 
        workflow_id: &WorkflowId, 
        strategies: &[SchedulingStrategy]
    ) -> StepResult {
        // 获取工作流结构
        let workflow = match self.get_workflow(workflow_id) {
            Some(w) => w,
            None => return StepResult::Error("工作流不存在".to_string()),
        };
        
        // 将工作流分解为子组件
        let components = self.decompose_workflow(&workflow);
        
        // 为每个组件选择合适的调度策略
        let mut component_strategies = Vec::new();
        for component in &components {
            let optimal_strategy = self.strategy_selector.select_for_component(&component);
            component_strategies.push((component.clone(), optimal_strategy));
        }
        
        // 执行各组件
        let mut results = Vec::new();
        for (component, strategy) in component_strategies {
            // 根据策略执行组件
            let result = match strategy {
                SchedulingStrategy::StateMachine => {
                    self.state_machine_scheduler.execute_component(&component).await
                }
                SchedulingStrategy::EventDriven => {
                    self.event_driven_scheduler.execute_component(&component).await
                }
                SchedulingStrategy::FairScheduling => {
                    self.fair_scheduler.execute_component(&component).await
                }
                _ => {
                    // 递归处理嵌套的混合策略
                    self.execute_hybrid_component(&component).await
                }
            };
            
            results.push(result);
            
            // 如果某个组件执行失败，可以决定是否继续执行其他组件
            if let ComponentResult::Error(_) = result {
                if component.is_critical() {
                    // 关键组件失败，终止整个工作流
                    return StepResult::Error("关键组件执行失败".to_string());
                }
            }
        }
        
        // 根据所有组件的执行结果确定总体步骤结果
        self.aggregate_component_results(workflow_id, results)
    }
    
    /// 工作流分析和模式检测
    pub fn analyze_workflow(&mut self, workflow_id: &WorkflowId) {
        // 获取工作流定义
        let workflow = match self.get_workflow(workflow_id) {
            Some(w) => w,
            None => return,
        };
        
        // 分析工作流结构
        let structure_analysis = self.analyze_workflow_structure(&workflow);
        
        // 检测工作流模式
        let detected_pattern = self.detect_workflow_pattern(&structure_analysis);
        
        // 更新工作流模式记录
        self.workflow_patterns.insert(workflow_id.clone(), detected_pattern);
        
        // 创建初始执行配置
        let initial_profile = ExecutionProfile::new(workflow_id, &detected_pattern);
        self.execution_profiles.insert(workflow_id.clone(), initial_profile);
    }
    
    /// 根据执行历史更新调度策略
    pub fn update_scheduling_strategy(&mut self, workflow_id: &WorkflowId, execution_metrics: &ExecutionMetrics) {
        // 获取当前配置
        let profile = match self.execution_profiles.get_mut(workflow_id) {
            Some(p) => p,
            None => return,
        };
        
        // 更新执行指标
        profile.update_metrics(execution_metrics);
        
        // 检查是否需要调整策略
        if profile.should_adjust_strategy() {
            // 获取工作流模式
            let pattern = match self.workflow_patterns.get(workflow_id) {
                Some(p) => p,
                None => return,
            };
            
            // 计算新的最佳策略
            let new_strategy = self.strategy_selector.select(
                pattern, 
                Some(profile), 
                &self.system_monitor.get_current_state()
            );
            
            // 更新策略
            profile.set_strategy(new_strategy);
            
            log::info!("为工作流 {:?} 更新调度策略: {:?}", workflow_id, new_strategy);
        }
    }
    
    /// 适应性学习：记录策略性能并改进
    pub fn record_strategy_performance(
        &mut self, 
        workflow_id: &WorkflowId, 
        strategy: &SchedulingStrategy, 
        performance: &PerformanceMetrics
    ) {
        self.strategy_selector.record_performance(workflow_id, strategy, performance);
        
        // 如果有足够的数据，重新训练策略选择模型
        if self.strategy_selector.should_retrain() {
            self.strategy_selector.train_model();
        }
    }
    
    /// 动态资源分配和负载均衡
    pub async fn balance_resources(&mut self) {
        // 获取当前所有活跃工作流
        let active_workflows = self.get_active_workflows();
        
        // 获取系统资源状态
        let resource_state = self.system_monitor.get_resource_state().await;
        
        // 计算每个工作流的资源需求和优先级
        let mut resource_requirements = Vec::new();
        for workflow_id in active_workflows {
            let priority = self.get_workflow_priority(&workflow_id);
            let pattern = self.workflow_patterns.get(&workflow_id);
            let profile = self.execution_profiles.get(&workflow_id);
            
            let resource_needs = self.estimate_resource_needs(&workflow_id, pattern, profile);
            
            resource_requirements.push((workflow_id, resource_needs, priority));
        }
        
        // 根据优先级和资源状态分配资源
        let allocations = self.resource_allocator.allocate(
            &resource_requirements,
            &resource_state
        );
        
        // 应用资源分配
        for (workflow_id, allocation) in allocations {
            self.apply_resource_allocation(&workflow_id, allocation);
        }
    }
    
    /// 预测性调度：基于历史模式预执行
    pub async fn predictive_scheduling(&mut self) {
        // 获取所有有预测数据的工作流
        let predictable_workflows = self.get_predictable_workflows();
        
        for workflow_id in predictable_workflows {
            // 获取工作流的预测模型
            if let Some(model) = self.prediction_models.get(&workflow_id) {
                // 使用模型预测下一步可能的执行路径
                let predictions = model.predict_next_steps();
                
                // 对最可能的路径进行预处理
                for (path, probability) in predictions {
                    if probability > 0.7 { // 只预处理高概率路径
                        self.preprocess_execution_path(&workflow_id, &path).await;
                    }
                }
            }
        }
    }
}

/// 策略选择器：根据工作流特性和系统状态选择最佳调度策略
pub struct StrategySelector {
    // 性能数据记录
    performance_history: HashMap<WorkflowPattern, Vec<(SchedulingStrategy, PerformanceMetrics)>>,
    
    // 决策模型（可以使用简单规则或机器学习模型）
    decision_rules: Vec<DecisionRule>,
    ml_model: Option<Box<dyn PredictionModel>>,
    
    // 选择策略
    selection_mode: SelectionMode,
}

impl StrategySelector {
    /// 选择最佳调度策略
    pub fn select(
        &self, 
        pattern: &WorkflowPattern, 
        profile: Option<&ExecutionProfile>, 
        system_state: &SystemState,
    ) -> SchedulingStrategy {
        match self.selection_mode {
            SelectionMode::RuleBased => {
                // 使用规则引擎选择
                self.select_by_rules(pattern, profile, system_state)
            }
            SelectionMode::MachineLearning => {
                // 使用ML模型选择（如果可用）
                if let Some(model) = &self.ml_model {
                    self.select_by_ml(model, pattern, profile, system_state)
                } else {
                    // 回退到规则选择
                    self.select_by_rules(pattern, profile, system_state)
                }
            }
            SelectionMode::Hybrid => {
                // 混合策略：先尝试ML，不确定时使用规则
                if let Some(model) = &self.ml_model {
                    let (strategy, confidence) = model.predict_with_confidence(pattern, profile, system_state);
                    if confidence > 0.7 {
                        strategy
                    } else {
                        self.select_by_rules(pattern, profile, system_state)
                    }
                } else {
                    self.select_by_rules(pattern, profile, system_state)
                }
            }
        }
    }
    
    /// 基于规则选择策略
    fn select_by_rules(
        &self, 
        pattern: &WorkflowPattern, 
        profile: Option<&ExecutionProfile>, 
        system_state: &SystemState,
    ) -> SchedulingStrategy {
        // 检查每个决策规则
        for rule in &self.decision_rules {
            if rule.matches(pattern, profile, system_state) {
                return rule.get_strategy();
            }
        }
        
        // 默认策略映射
        match pattern {
            WorkflowPattern::Sequential { .. } => SchedulingStrategy::StateMachine,
            WorkflowPattern::Branching { .. } => SchedulingStrategy::EventDriven,
            WorkflowPattern::Parallel { .. } => SchedulingStrategy::EventDriven,
            WorkflowPattern::EventDriven { .. } => SchedulingStrategy::EventDriven,
            WorkflowPattern::Petri { .. } => SchedulingStrategy::FairScheduling,
            WorkflowPattern::Mixed { .. } => {
                // 针对混合模式，构建组合策略
                let mut strategies = Vec::new();
                
                if let WorkflowPattern::Mixed { components } = pattern {
                    for component in components {
                        // 递归选择每个组件的策略
                        let component_strategy = self.select_by_rules(component, profile, system_state);
                        strategies.push(component_strategy);
                    }
                }
                
                SchedulingStrategy::Hybrid(strategies)
            }
        }
    }
    
    /// 基于ML模型选择策略
    fn select_by_ml(
        &self, 
        model: &Box<dyn PredictionModel>, 
        pattern: &WorkflowPattern, 
        profile: Option<&ExecutionProfile>, 
        system_state: &SystemState,
    ) -> SchedulingStrategy {
        // 使用模型预测最佳策略
        model.predict(pattern, profile, system_state)
    }
    
    /// 记录策略性能
    pub fn record_performance(
        &mut self, 
        workflow_id: &WorkflowId, 
        strategy: &SchedulingStrategy, 
        performance: &PerformanceMetrics,
    ) {
        // 获取工作流模式
        let pattern = match self.get_workflow_pattern(workflow_id) {
            Some(p) => p,
            None => return,
        };
        
        // 记录性能数据
        self.performance_history
            .entry(pattern.clone())
            .or_insert_with(Vec::new)
            .push((strategy.clone(), performance.clone()));
            
        // 限制历史数据大小
        if let Some(history) = self.performance_history.get_mut(&pattern) {
            if history.len() > 100 {
                // 保留最近的100条记录
                *history = history.drain(history.len() - 100..).collect();
            }
        }
    }
    
    /// 检查是否应该重新训练模型
    pub fn should_retrain(&self) -> bool {
        // 如果有足够的新数据，应该重新训练
        let new_data_count = self.performance_history.values()
            .map(|v| v.len())
            .sum::<usize>();
            
        new_data_count > 1000 // 示例阈值
    }
    
    /// 训练策略选择模型
    pub fn train_model(&mut self) {
        if let Some(model) = &mut self.ml_model {
            // 准备训练数据
            let mut training_data = Vec::new();
            
            for (pattern, performances) in &self.performance_history {
                for (strategy, metrics) in performances {
                    training_data.push((
                        pattern.clone(),
                        strategy.clone(),
                        metrics.clone(),
                    ));
                }
            }
            
            // 训练模型
            model.train(&training_data);
            
            log::info!("策略选择模型已重新训练，使用 {} 条数据", training_data.len());
        }
    }
}

/// 工作流组件优化器：针对特定组件优化调度
pub struct ComponentOptimizer {
    // 组件性能历史
    component_history: HashMap<ComponentType, Vec<ExecutionRecord>>,
    
    // 优化规则
    optimization_rules: Vec<OptimizationRule>,
}

impl ComponentOptimizer {
    /// 优化组件执行
    pub fn optimize_component(
        &self,
        component: &WorkflowComponent,
        system_state: &SystemState,
    ) -> OptimizedExecution {
        // 获取组件类型
        let component_type = component.get_type();
        
        // 查找历史执行记录
        let history = self.component_history.get(&component_type);
        
        // 应用优化规则
        for rule in &self.optimization_rules {
            if rule.applies_to(&component_type) {
                if let Some(optimization) = rule.apply(component, history, system_state) {
                    return optimization;
                }
            }
        }
        
        // 默认优化
        self.default_optimization(component)
    }
    
    /// 默认组件优化
    fn default_optimization(&self, component: &WorkflowComponent) -> OptimizedExecution {
        match component.get_type() {
            ComponentType::ActivitySequence => {
                // 顺序活动优化：批处理、预取等
                OptimizedExecution {
                    batching_enabled: true,
                    prefetch_level: PrefetchLevel::Next,
                    execution_mode: ExecutionMode::Sequential,
                    ..Default::default()
                }
            }
            ComponentType::ParallelExecution => {
                // 并行执行优化：调整并发级别、负载均衡
                OptimizedExecution {
                    concurrency_level: self.calculate_optimal_concurrency(component),
                    execution_mode: ExecutionMode::Parallel,
                    load_balancing: LoadBalancingStrategy::ResourceAware,
                    ..Default::default()
                }
            }
            ComponentType::DecisionPoint => {
                // 决策点优化：预测性评估、缓存
                OptimizedExecution {
                    predictive_evaluation: true,
                    caching_enabled: true,
                    execution_mode: ExecutionMode::Priority,
                    ..Default::default()
                }
            }
            ComponentType::EventHandler => {
                // 事件处理优化：批处理、优先级队列
                OptimizedExecution {
                    event_batching: true,
                    priority_queue: true,
                    execution_mode: ExecutionMode::EventDriven,
                    ..Default::default()
                }
            }
            ComponentType::TimerBased => {
                // 定时器优化：时间窗口合并、预调度
                OptimizedExecution {
                    timer_coalescing: true,
                    pre_scheduling: true,
                    execution_mode: ExecutionMode::TimeDriven,
                    ..Default::default()
                }
            }
            ComponentType::ResourceIntensive => {
                // 资源密集型优化：资源预留、分段执行
                OptimizedExecution {
                    resource_reservation: true,
                    chunked_execution: true,
                    execution_mode: ExecutionMode::ResourceControlled,
                    ..Default::default()
                }
            }
            ComponentType::Custom => {
                // 自定义组件：使用组件自己的优化提示
                component.get_optimization_hints()
                    .unwrap_or_else(OptimizedExecution::default)
            }
        }
    }
    
    /// 计算最优并发度
    fn calculate_optimal_concurrency(&self, component: &WorkflowComponent) -> u32 {
        // 基于历史执行和当前系统状态计算最佳并发度
        
        // 1. 获取组件类型
        let component_type = component.get_type();
        
        // 2. 查找历史记录
        let avg_duration = self.component_history
            .get(&component_type)
            .map(|records| {
                let total_duration: u64 = records.iter()
                    .map(|r| r.duration.as_millis() as u64)
                    .sum();
                if records.is_empty() {
                    0
                } else {
                    total_duration / records.len() as u64
                }
            })
            .unwrap_or(100); // 默认估计
            
        // 3. 估计资源使用情况
        let estimated_resource_usage = component.estimate_resource_usage();
        
        // 4. 计算理想并发度
        let available_cores = num_cpus::get() as u32;
        let resource_limited_concurrency = if estimated_resource_usage.cpu_cores > 0.0 {
            (available_cores as f64 / estimated_resource_usage.cpu_cores).floor() as u32
        } else {
            available_cores
        };
        
        // 5. 调整并发度
        let latency_target = component.get_latency_target().unwrap_or(Duration::from_millis(500));
        let latency_based_concurrency = if avg_duration > 0 {
            (latency_target.as_millis() as u64 / avg_duration).max(1) as u32
        } else {
            4 // 默认值
        };
        
        // 6. 取两者的较小值
        resource_limited_concurrency.min(latency_based_concurrency)
    }
    
    /// 记录组件执行
    pub fn record_execution(&mut self, component_type: ComponentType, record: ExecutionRecord) {
        // 添加记录
        self.component_history
            .entry(component_type)
            .or_insert_with(Vec::new)
            .push(record);
            
        // 限制历史大小
        if let Some(history) = self.component_history.get_mut(&component_type) {
            if history.len() > 1000 {
                // 保留最近的1000条记录
                *history = history.drain(history.len() - 1000..).collect();
            }
        }
    }
}
```

#### 4.3 策略等价性与动态转换

混合调度策略的核心是了解不同策略之间的等价性，以便在不同场景下进行动态转换：

```rust
/// 策略等价性分析器
pub struct StrategyEquivalenceAnalyzer {
    // 存储已知的等价映射
    equivalence_mappings: HashMap<SchedulingStrategy, Vec<SchedulingStrategy>>,
    
    // 转换规则
    transformation_rules: Vec<TransformationRule>,
}

impl StrategyEquivalenceAnalyzer {
    /// 查找与给定策略等价的策略
    pub fn find_equivalent_strategies(
        &self, 
        strategy: &SchedulingStrategy,
        constraints: &ExecutionConstraints,
    ) -> Vec<SchedulingStrategy> {
        // 1. 检查已知等价映射
        if let Some(equivalents) = self.equivalence_mappings.get(strategy) {
            // 筛选符合约束的策略
            return equivalents.iter()
                .filter(|s| self.meets_constraints(s, constraints))
                .cloned()
                .collect();
        }
        
        // 2. 尝试使用转换规则
        let mut result = Vec::new();
        for rule in &self.transformation_rules {
            if rule.is_applicable(strategy) {
                let transformed = rule.transform(strategy);
                if self.meets_constraints(&transformed, constraints) {
                    result.push(transformed);
                }
            }
        }
        
        result
    }
    
    /// 检查策略是否满足执行约束
    fn meets_constraints(&self, strategy: &SchedulingStrategy, constraints: &ExecutionConstraints) -> bool {
        // 检查资源约束
        if let Some(max_memory) = constraints.max_memory {
            if self.estimate_memory_usage(strategy) > max_memory {
                return false;
            }
        }
        
        // 检查延迟约束
        if let Some(max_latency) = constraints.max_latency {
            if self.estimate_latency(strategy) > max_latency {
                return false;
            }
        }
        
        // 检查吞吐量约束
        if let Some(min_throughput) = constraints.min_throughput {
            if self.estimate_throughput(strategy) < min_throughput {
                return false;
            }
        }
        
        true
    }
    
    /// 在两个策略之间动态切换
    pub fn transform_strategy(
        &self,
        from: &SchedulingStrategy,
        to: &SchedulingStrategy,
        state: &WorkflowState,
    ) -> Result<TransformationPlan, TransformationError> {
        // 检查是否有直接转换规则
        for rule in &self.transformation_rules {
            if rule.can_transform(from, to) {
                return rule.create_transformation_plan(from, to, state);
            }
        }
        
        // 尝试找到转换路径
        if let Some(path) = self.find_transformation_path(from, to) {
            let mut plans = Vec::new();
            let mut current = from.clone();
            
            for target in path {
                // 为每一步创建转换计划
                for rule in &self.transformation_rules {
                    if rule.can_transform(&current, &target) {
                        match rule.create_transformation_plan(&current, &target, state) {
                            Ok(plan) => {
                                plans.push(plan);
                                current = target.clone();
                                break;
                            }
                            Err(e) => return Err(e),
                        }
                    }
                }
            }
            
            // 合并所有计划
            return Ok(TransformationPlan::compose(plans));
        }
        
        Err(TransformationError::NoTransformationPath)
    }
    
    /// 找到从一个策略到另一个策略的转换路径
    fn find_transformation_path(
        &self,
        from: &SchedulingStrategy,
        to: &SchedulingStrategy,
    ) -> Option<Vec<SchedulingStrategy>> {
        // 使用广度优先搜索寻找路径
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        let mut parent_map = HashMap::new();
        
        // 初始状态
        queue.push_back(from.clone());
        visited.insert(from.clone());
        
        while let Some(current) = queue.pop_front() {
            // 找到目标
            if current == *to {
                // 重建路径
                let mut path = Vec::new();
                let mut current = current;
                
                while current != *from {
                    path.push(current.clone());
                    current = parent_map[&current].clone();
                }
                
                // 反转路径
                path.reverse();
                return Some(path);
            }
            
            // 探索相邻策略
            for rule in &self.transformation_rules {
                if rule.is_applicable(&current) {
                    let next = rule.transform(&current);
                    
                    if !visited.contains(&next) {
                        visited.insert(next.clone());
                        parent_map.insert(next.clone(), current.clone());
                        queue.push_back(next);
                    }
                }
            }
        }
        
        None
    }
}
```

#### 4.4 优化点

- **自适应策略选择**：基于工作流特性和执行历史动态选择调度策略
- **组件级优化**：针对工作流中的不同组件使用不同的调度策略
- **负载感知**：根据系统负载动态调整调度方式
- **预测性执行**：基于历史模式预测执行路径，进行预处理
- **在线学习**：记录不同策略的性能，不断改进策略选择模型

### 5. 综合分析：统一调度框架的可能性

前面我们讨论了针对不同工作流类型的专用调度策略，
现在我们来探讨是否可以设计一个统一的调度框架，
为所有类型的工作流提供优化的执行环境。

#### 5.1 工作流本质的思考

不同类型的工作流（线性序列、事件驱动、Petri网等）在本质上可以视为同一种计算模型的不同表现形式。
它们都关注：

1. **计算单元**：活动、转换、状态处理器等
2. **依赖关系**：前序依赖、事件触发、资源竞争等
3. **执行条件**：满足何种条件才能开始/继续执行
4. **资源需求**：需要何种资源，使用多少

#### 5.2 统一调度框架设计

```rust
/// 统一工作流调度框架
pub struct UnifiedSchedulingFramework {
    // 核心调度引擎
    core_scheduler: CoreScheduler,
    
    // 专业化调度适配器
    adapters: HashMap<WorkflowType, Box<dyn SchedulerAdapter>>,
    
    // 执行优化器
    optimizer: ExecutionOptimizer,
    
    // 资源管理器
    resource_manager: Arc<ResourceManager>,
    
    // 系统监控
    system_monitor: Arc<SystemMonitor>,
}

impl UnifiedSchedulingFramework {
    /// 调度工作流执行
    pub async fn schedule(
        &mut self,
        workflow_id: &WorkflowId,
        context: &ExecutionContext,
    ) -> ExecutionResult {
        // 1. 获取工作流类型
        let workflow_type = self.determine_workflow_type(workflow_id);
        
        // 2. 获取适当的调度适配器
        let adapter = match self.adapters.get(&workflow_type) {
            Some(a) => a,
            None => {
                // 使用默认适配器
                self.adapters.get(&WorkflowType::Default).unwrap()
            }
        };
        
        // 3. 获取系统状态
        let system_state = self.system_monitor.get_current_state();
        
        // 4. 确定调度策略
        let strategy = self.optimizer.select_strategy(
            workflow_id,
            &workflow_type,
            &system_state,
        );
        
        // 5. 使用适配器创建执行计划
        let execution_plan = adapter.create_execution_plan(
            workflow_id,
            context,
            &strategy,
        ).await?;
        
        // 6. 分配资源
        let resource_allocation = self.resource_manager
            .allocate_resources(workflow_id, &execution_plan.resource_requirements)
            .await?;
            
        // 7. 提交到核心调度器执行
        let result = self.core_scheduler.execute_plan(
            workflow_id,
            execution_plan,
            resource_allocation,
        ).await;
        
        // 8. 记录执行指标
        self.record_execution_metrics(workflow_id, &result);
        
        // 9. 释放资源
        self.resource_manager.release_resources(workflow_id).await;
        
        result
    }
    
    /// 确定工作流类型
    fn determine_workflow_type(&self, workflow_id: &WorkflowId) -> WorkflowType {
        // 获取工作流定义
        let workflow = match self.get_workflow_definition(workflow_id) {
            Some(w) => w,
            None => return WorkflowType::Default,
        
```rust
        let workflow = match self.get_workflow_definition(workflow_id) {
            Some(w) => w,
            None => return WorkflowType::Default,
        };
        
        // 分析工作流结构
        let analysis = self.analyze_workflow_structure(&workflow);
        
        // 基于结构特征确定类型
        if analysis.is_predominantly_sequential() {
            WorkflowType::Sequential
        } else if analysis.has_significant_event_handling() {
            WorkflowType::EventDriven
        } else if analysis.resembles_petri_net() {
            WorkflowType::PetriNet
        } else if analysis.has_complex_branching() {
            WorkflowType::DecisionOriented
        } else if analysis.has_high_parallelism() {
            WorkflowType::Parallel
        } else {
            // 混合或无法确定
            WorkflowType::Mixed
        }
    }
    
    /// 动态调整调度参数
    pub async fn adjust_scheduling_parameters(&mut self) {
        // 获取当前系统状态
        let system_state = self.system_monitor.get_current_state();
        
        // 获取所有活跃工作流
        let active_workflows = self.get_active_workflows();
        
        // 计算最佳资源分配
        let resource_allocation = self.optimizer.calculate_optimal_allocation(
            &active_workflows,
            &system_state,
        );
        
        // 更新核心调度器参数
        self.core_scheduler.update_parameters(CoreSchedulerParameters {
            max_concurrent_workflows: resource_allocation.max_concurrent_workflows,
            max_concurrent_tasks: resource_allocation.max_concurrent_tasks,
            time_slice_ms: resource_allocation.time_slice_ms,
            preemption_enabled: resource_allocation.preemption_enabled,
            priority_boost_interval: resource_allocation.priority_boost_interval,
        });
        
        // 更新各适配器参数
        for (workflow_type, adapter) in &mut self.adapters {
            let adapter_params = resource_allocation.adapter_parameters.get(workflow_type)
                .cloned()
                .unwrap_or_default();
                
            adapter.update_parameters(adapter_params);
        }
    }
    
    /// 执行优化
    pub async fn optimize(&mut self) {
        // 获取执行统计
        let execution_stats = self.get_execution_statistics();
        
        // 检测瓶颈
        let bottlenecks = self.optimizer.detect_bottlenecks(&execution_stats);
        
        // 应用优化措施
        for bottleneck in bottlenecks {
            match bottleneck {
                Bottleneck::ResourceContention(resource_type) => {
                    // 处理资源竞争
                    self.resource_manager.optimize_allocation(resource_type).await;
                }
                Bottleneck::SchedulingOverhead => {
                    // 减少调度开销
                    self.core_scheduler.reduce_context_switching();
                }
                Bottleneck::ExcessivePreemption => {
                    // 降低抢占频率
                    self.core_scheduler.adjust_preemption_threshold(1.5);
                }
                Bottleneck::IneffectiveParallelism => {
                    // 优化并行度
                    self.optimizer.adjust_parallelism_strategy();
                }
                Bottleneck::HighLatency(workflow_type) => {
                    // 针对特定工作流类型优化延迟
                    if let Some(adapter) = self.adapters.get_mut(&workflow_type) {
                        adapter.optimize_for_latency();
                    }
                }
                Bottleneck::LowThroughput(workflow_type) => {
                    // 针对特定工作流类型优化吞吐量
                    if let Some(adapter) = self.adapters.get_mut(&workflow_type) {
                        adapter.optimize_for_throughput();
                    }
                }
            }
        }
    }
    
    /// 实现工作流调度的适应性学习
    pub async fn adaptive_learning_cycle(&mut self) {
        // 收集执行数据
        let execution_data = self.collect_execution_data();
        
        // 更新性能模型
        self.optimizer.update_performance_models(&execution_data);
        
        // 检查是否有更好的调度策略
        let strategy_improvements = self.optimizer.identify_strategy_improvements();
        
        // 应用策略改进
        for (workflow_type, new_strategy) in strategy_improvements {
            log::info!("为工作流类型 {:?} 采用新的调度策略: {:?}", workflow_type, new_strategy);
            
            // 获取该类型的所有活跃工作流
            let affected_workflows = self.get_workflows_by_type(&workflow_type);
            
            // 对每个工作流应用新策略
            for workflow_id in affected_workflows {
                self.apply_new_strategy(&workflow_id, &new_strategy).await;
            }
            
            // 更新适配器的默认策略
            if let Some(adapter) = self.adapters.get_mut(&workflow_type) {
                adapter.set_default_strategy(new_strategy);
            }
        }
    }
    
    /// 为特定工作流应用新策略
    async fn apply_new_strategy(&mut self, workflow_id: &WorkflowId, strategy: &SchedulingStrategy) {
        // 获取当前执行状态
        let state = self.get_workflow_state(workflow_id);
        
        // 创建转换计划
        let current_strategy = self.get_current_strategy(workflow_id);
        let transformation = self.optimizer.strategy_transformer
            .transform_strategy(&current_strategy, strategy, &state);
            
        match transformation {
            Ok(plan) => {
                // 应用转换计划
                self.execute_transformation_plan(workflow_id, plan).await;
            }
            Err(e) => {
                // 转换失败，记录错误
                log::warn!(
                    "无法为工作流 {:?} 转换策略: {:?} -> {:?}: {:?}",
                    workflow_id, current_strategy, strategy, e
                );
                
                // 尝试在下一个安全点切换
                self.schedule_strategy_switch_at_safe_point(workflow_id, strategy.clone());
            }
        }
    }
}

/// 核心调度器 - 处理所有类型工作流的底层执行
pub struct CoreScheduler {
    // 执行队列
    high_priority_queue: VecDeque<ScheduledTask>,
    normal_priority_queue: VecDeque<ScheduledTask>,
    low_priority_queue: VecDeque<ScheduledTask>,
    
    // 当前执行的任务
    active_tasks: HashMap<TaskId, ActiveTask>,
    
    // 调度参数
    parameters: CoreSchedulerParameters,
    
    // 执行统计
    stats: SchedulerStats,
}

impl CoreScheduler {
    /// 执行计划
    pub async fn execute_plan(
        &mut self,
        workflow_id: &WorkflowId,
        plan: ExecutionPlan,
        resources: ResourceAllocation,
    ) -> ExecutionResult {
        // 1. 准备执行上下文
        let context = ExecutionContext {
            workflow_id: workflow_id.clone(),
            resources,
            start_time: Instant::now(),
            progress_tracker: ProgressTracker::new(&plan),
        };
        
        // 2. 将计划转换为任务
        let tasks = self.create_tasks_from_plan(plan, context.clone());
        
        // 3. 将任务添加到合适的队列
        for task in tasks {
            self.enqueue_task(task);
        }
        
        // 4. 创建结果接收器
        let (tx, rx) = oneshot::channel();
        
        // 5. 注册完成回调
        self.register_completion_callback(workflow_id.clone(), tx);
        
        // 6. 等待执行完成
        rx.await.unwrap_or_else(|_| {
            ExecutionResult::Error(ExecutionError::Canceled)
        })
    }
    
    /// 将任务添加到合适的队列
    fn enqueue_task(&mut self, task: ScheduledTask) {
        match task.priority {
            TaskPriority::High => self.high_priority_queue.push_back(task),
            TaskPriority::Normal => self.normal_priority_queue.push_back(task),
            TaskPriority::Low => self.low_priority_queue.push_back(task),
        }
    }
    
    /// 调度循环 - 选择并执行下一个任务
    pub async fn scheduling_loop(&mut self) {
        loop {
            // 1. 选择下一个要执行的任务
            let next_task = self.select_next_task();
            
            if let Some(task) = next_task {
                // 2. 准备执行
                let task_id = task.id.clone();
                let workflow_id = task.workflow_id.clone();
                
                // 3. 标记为活跃
                self.active_tasks.insert(task_id.clone(), ActiveTask {
                    task: task.clone(),
                    start_time: Instant::now(),
                    progress: 0.0,
                });
                
                // 4. 执行任务
                let execution_future = task.execute();
                
                // 5. 使用tokio spawn执行任务
                tokio::spawn({
                    let task_id = task_id.clone();
                    let workflow_id = workflow_id.clone();
                    let self_ref = self.get_weak_self();
                    
                    async move {
                        let result = execution_future.await;
                        
                        // 6. 更新执行状态
                        if let Some(scheduler) = self_ref.upgrade() {
                            scheduler.handle_task_completion(task_id, workflow_id, result).await;
                        }
                    }
                });
            } else {
                // 没有可执行的任务，休息一下
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
            
            // 检查是否需要抢占
            if self.parameters.preemption_enabled {
                self.check_for_preemption().await;
            }
            
            // 更新统计信息
            self.update_stats();
        }
    }
    
    /// 选择下一个要执行的任务
    fn select_next_task(&mut self) -> Option<ScheduledTask> {
        // 检查当前是否有足够资源执行更多任务
        if self.active_tasks.len() >= self.parameters.max_concurrent_tasks {
            return None;
        }
        
        // 按优先级顺序检查队列
        if let Some(task) = self.high_priority_queue.pop_front() {
            return Some(task);
        }
        
        if let Some(task) = self.normal_priority_queue.pop_front() {
            return Some(task);
        }
        
        if let Some(task) = self.low_priority_queue.pop_front() {
            return Some(task);
        }
        
        None
    }
    
    /// 检查是否需要抢占长时间运行的任务
    async fn check_for_preemption(&mut self) {
        let now = Instant::now();
        let time_slice = Duration::from_millis(self.parameters.time_slice_ms);
        
        let tasks_to_preempt = self.active_tasks.iter()
            .filter(|(_, task)| {
                // 判断任务是否运行时间过长
                now.duration_since(task.start_time) > time_slice &&
                // 只抢占支持的任务
                task.task.preemptable
            })
            .map(|(id, _)| id.clone())
            .collect::<Vec<_>>();
            
        for task_id in tasks_to_preempt {
            if let Some(task) = self.active_tasks.remove(&task_id) {
                // 创建抢占信号
                let preempt_signal = PreemptSignal {
                    task_id: task_id.clone(),
                    reason: PreemptReason::TimeSliceExpired,
                };
                
                // 发送抢占信号
                if let Err(_) = task.task.preempt_sender.send(preempt_signal) {
                    // 无法发送抢占信号，任务可能已结束
                    continue;
                }
                
                // 重新入队
                self.enqueue_task(task.task);
                
                // 更新统计信息
                self.stats.preemption_count += 1;
            }
        }
    }
    
    /// 处理任务完成
    async fn handle_task_completion(
        &mut self,
        task_id: TaskId,
        workflow_id: WorkflowId,
        result: TaskResult,
    ) {
        // 从活跃任务中移除
        self.active_tasks.remove(&task_id);
        
        // 更新统计信息
        match &result {
            TaskResult::Success(_) => self.stats.successful_tasks += 1,
            TaskResult::Error(_) => self.stats.failed_tasks += 1,
            TaskResult::Preempted => self.stats.preempted_tasks += 1,
        }
        
        // 检查工作流是否完成
        self.check_workflow_completion(&workflow_id, task_id, result).await;
    }
    
    /// 检查工作流是否完成
    async fn check_workflow_completion(
        &mut self,
        workflow_id: &WorkflowId,
        task_id: TaskId,
        result: TaskResult,
    ) {
        // 获取工作流状态
        let mut workflow_state = self.get_workflow_state(workflow_id);
        
        // 更新任务结果
        workflow_state.update_task_result(task_id, result.clone());
        
        // 根据任务结果和工作流定义创建后续任务
        let next_tasks = match result {
            TaskResult::Success(output) => {
                self.create_successor_tasks(workflow_id, &task_id, output, &workflow_state)
            }
            TaskResult::Error(error) => {
                self.create_error_handling_tasks(workflow_id, &task_id, error, &workflow_state)
            }
            TaskResult::Preempted => {
                // 任务已被抢占并重新入队，无需创建后续任务
                Vec::new()
            }
        };
        
        // 将后续任务添加到队列
        for task in next_tasks {
            self.enqueue_task(task);
        }
        
        // 检查工作流是否已完成
        if workflow_state.is_completed() {
            // 发送完成信号
            if let Some(callback) = self.get_completion_callback(workflow_id) {
                let _ = callback.send(
                    if workflow_state.is_successful() {
                        ExecutionResult::Success(workflow_state.get_result())
                    } else {
                        ExecutionResult::Error(workflow_state.get_error())
                    }
                );
            }
            
            // 清理工作流资源
            self.cleanup_workflow(workflow_id);
        }
        
        // 保存更新后的工作流状态
        self.save_workflow_state(workflow_id, workflow_state);
    }
    
    /// 更新调度参数
    pub fn update_parameters(&mut self, parameters: CoreSchedulerParameters) {
        // 确保参数在有效范围内
        let validated_params = CoreSchedulerParameters {
            max_concurrent_workflows: parameters.max_concurrent_workflows.clamp(1, 1000),
            max_concurrent_tasks: parameters.max_concurrent_tasks.clamp(1, 10000),
            time_slice_ms: parameters.time_slice_ms.clamp(10, 10000),
            preemption_enabled: parameters.preemption_enabled,
            priority_boost_interval: parameters.priority_boost_interval.clamp(100, 100000),
        };
        
        // 更新参数
        self.parameters = validated_params;
        
        log::info!("更新核心调度器参数: {:?}", self.parameters);
    }
    
    /// 减少上下文切换
    pub fn reduce_context_switching(&mut self) {
        // 增加时间片长度，减少抢占频率
        self.parameters.time_slice_ms = (self.parameters.time_slice_ms * 15) / 10;
        
        log::info!("增加时间片长度到 {}ms 以减少上下文切换", self.parameters.time_slice_ms);
    }
    
    /// 调整抢占阈值
    pub fn adjust_preemption_threshold(&mut self, factor: f32) {
        let new_time_slice = (self.parameters.time_slice_ms as f32 * factor) as u64;
        self.parameters.time_slice_ms = new_time_slice.clamp(10, 10000);
        
        log::info!("调整抢占阈值: 新时间片 = {}ms", self.parameters.time_slice_ms);
    }
}

/// 调度适配器接口 - 为特定类型的工作流提供专用调度逻辑
#[async_trait]
pub trait SchedulerAdapter: Send + Sync {
    /// 创建执行计划
    async fn create_execution_plan(
        &self,
        workflow_id: &WorkflowId,
        context: &ExecutionContext,
        strategy: &SchedulingStrategy,
    ) -> Result<ExecutionPlan, PlanningError>;
    
    /// 更新适配器参数
    fn update_parameters(&mut self, parameters: AdapterParameters);
    
    /// 设置默认调度策略
    fn set_default_strategy(&mut self, strategy: SchedulingStrategy);
    
    /// 优化延迟
    fn optimize_for_latency(&mut self);
    
    /// 优化吞吐量
    fn optimize_for_throughput(&mut self);
}

/// 执行优化器 - 优化工作流执行
pub struct ExecutionOptimizer {
    // 性能模型
    performance_models: HashMap<WorkflowType, Box<dyn PerformanceModel>>,
    
    // 策略转换器
    strategy_transformer: StrategyTransformer,
    
    // 调度策略选择器
    strategy_selector: StrategySelector,
    
    // 学习模块
    learning_engine: AdaptiveLearningEngine,
}

impl ExecutionOptimizer {
    /// 选择调度策略
    pub fn select_strategy(
        &self,
        workflow_id: &WorkflowId,
        workflow_type: &WorkflowType,
        system_state: &SystemState,
    ) -> SchedulingStrategy {
        // 1. 检查是否有工作流特定的最佳策略
        if let Some(strategy) = self.get_workflow_specific_strategy(workflow_id) {
            return strategy;
        }
        
        // 2. 使用策略选择器为该类型工作流选择最佳策略
        self.strategy_selector.select_strategy(workflow_type, system_state)
    }
    
    /// 计算最佳资源分配
    pub fn calculate_optimal_allocation(
        &self,
        active_workflows: &[WorkflowId],
        system_state: &SystemState,
    ) -> ResourceAllocationPlan {
        // 获取每个工作流的当前状态和类型
        let workflow_states = active_workflows.iter()
            .filter_map(|id| {
                let workflow_type = self.get_workflow_type(id)?;
                let state = self.get_workflow_state(id)?;
                Some((id.clone(), workflow_type, state))
            })
            .collect::<Vec<_>>();
            
        // 计算总体资源需求
        let mut total_cpu = 0.0;
        let mut total_memory = 0;
        let mut workflow_resource_needs = Vec::new();
        
        for (id, workflow_type, state) in &workflow_states {
            // 使用性能模型估计资源需求
            if let Some(model) = self.performance_models.get(workflow_type) {
                let resource_estimate = model.estimate_resource_needs(&state);
                
                total_cpu += resource_estimate.cpu_cores;
                total_memory += resource_estimate.memory_mb;
                
                workflow_resource_needs.push((id.clone(), resource_estimate));
            }
        }
        
        // 获取可用资源
        let available_resources = system_state.get_available_resources();
        
        // 计算分配比例（如果资源超额认购）
        let cpu_ratio = (available_resources.cpu_cores / total_cpu).min(1.0);
        let memory_ratio = (available_resources.memory_mb as f64 / total_memory as f64).min(1.0);
        let allocation_ratio = cpu_ratio.min(memory_ratio);
        
        // 为每个工作流分配资源
        let mut allocations = HashMap::new();
        for (id, estimate) in workflow_resource_needs {
            let allocated_resources = ResourceAllocation {
                cpu_cores: (estimate.cpu_cores * allocation_ratio) as u32,
                memory_mb: (estimate.memory_mb as f64 * allocation_ratio) as usize,
                io_priority: estimate.io_priority,
            };
            
            allocations.insert(id, allocated_resources);
        }
        
        // 计算总体分配计划
        ResourceAllocationPlan {
            workflow_allocations: allocations,
            // 设置核心调度器参数
            max_concurrent_workflows: (workflow_states.len() * 2).min(100),
            max_concurrent_tasks: (workflow_states.len() * 10).min(1000),
            time_slice_ms: self.calculate_optimal_time_slice(system_state),
            preemption_enabled: true,
            priority_boost_interval: 5000,
            // 为不同类型的工作流设置适配器参数
            adapter_parameters: self.calculate_adapter_parameters(&workflow_states, system_state),
        }
    }
    
    /// 计算最佳时间片长度
    fn calculate_optimal_time_slice(&self, system_state: &SystemState) -> u64 {
        // 基于系统负载调整时间片
        let load = system_state.get_cpu_load();
        
        if load > 0.8 {
            // 高负载：较短时间片，更频繁切换
            50
        } else if load > 0.5 {
            // 中等负载：平衡时间片
            100
        } else {
            // 低负载：较长时间片，减少切换开销
            200
        }
    }
    
    /// 计算适配器参数
    fn calculate_adapter_parameters(
        &self,
        workflow_states: &[(WorkflowId, WorkflowType, WorkflowState)],
        system_state: &SystemState,
    ) -> HashMap<WorkflowType, AdapterParameters> {
        let mut result = HashMap::new();
        
        // 计算每种类型的工作流数量
        let mut type_counts = HashMap::new();
        for (_, workflow_type, _) in workflow_states {
            *type_counts.entry(workflow_type.clone()).or_insert(0) += 1;
        }
        
        // 为每种类型设置参数
        for (workflow_type, count) in type_counts {
            let params = match workflow_type {
                WorkflowType::Sequential => AdapterParameters {
                    batch_size: 10,
                    concurrency: 1,
                    prefetch_count: 5,
                    ..Default::default()
                },
                WorkflowType::EventDriven => AdapterParameters {
                    batch_size: 50,
                    concurrency: count * 2,
                    priority_levels: 3,
                    ..Default::default()
                },
                WorkflowType::PetriNet => AdapterParameters {
                    fairness_enabled: true,
                    starvation_threshold: 5000,
                    priority_aging: true,
                    ..Default::default()
                },
                WorkflowType::Parallel => AdapterParameters {
                    concurrency: num_cpus::get() * 2,
                    load_balancing: true,
                    work_stealing: true,
                    ..Default::default()
                },
                _ => AdapterParameters::default(),
            };
            
            result.insert(workflow_type, params);
        }
        
        result
    }
    
    /// 检测执行瓶颈
    pub fn detect_bottlenecks(&self, stats: &ExecutionStatistics) -> Vec<Bottleneck> {
        let mut bottlenecks = Vec::new();
        
        // 检查资源相关瓶颈
        if stats.resource_wait_time > stats.execution_time * 0.3 {
            // 资源等待时间超过总执行时间的30%
            bottlenecks.push(Bottleneck::ResourceContention(
                self.identify_contended_resource(stats)
            ));
        }
        
        // 检查调度开销
        if stats.scheduling_overhead > stats.execution_time * 0.1 {
            // 调度开销超过总执行时间的10%
            bottlenecks.push(Bottleneck::SchedulingOverhead);
        }
        
        // 检查抢占问题
        if stats.preemption_count > stats.task_count / 5 {
            // 抢占次数超过任务总数的20%
            bottlenecks.push(Bottleneck::ExcessivePreemption);
        }
        
        // 检查并行效率
        if stats.average_parallelism < stats.potential_parallelism * 0.7 {
            // 实际并行度低于潜在并行度的70%
            bottlenecks.push(Bottleneck::IneffectiveParallelism);
        }
        
        // 检查各类型工作流的性能
        for (workflow_type, type_stats) in &stats.by_workflow_type {
            // 检查延迟
            if type_stats.average_latency > type_stats.latency_target * 1.5 {
                // 平均延迟超过目标的150%
                bottlenecks.push(Bottleneck::HighLatency(workflow_type.clone()));
            }
            
            // 检查吞吐量
            if type_stats.throughput < type_stats.throughput_target * 0.7 {
                // 吞吐量低于目标的70%
                bottlenecks.push(Bottleneck::LowThroughput(workflow_type.clone()));
            }
        }
        
        bottlenecks
    }
    
    /// 识别争用的资源类型
    fn identify_contended_resource(&self, stats: &ExecutionStatistics) -> ResourceType {
        // 检查各种资源指标，确定主要瓶颈
        if stats.cpu_queue_time > stats.io_wait_time && 
           stats.cpu_queue_time > stats.memory_wait_time {
            ResourceType::CPU
        } else if stats.io_wait_time > stats.cpu_queue_time && 
                  stats.io_wait_time > stats.memory_wait_time {
            ResourceType::IO
        } else if stats.memory_wait_time > stats.cpu_queue_time && 
                  stats.memory_wait_time > stats.io_wait_time {
            ResourceType::Memory
        } else {
            ResourceType::Unknown
        }
    }
    
    /// 调整并行策略
    pub fn adjust_parallelism_strategy(&mut self) {
        // 根据系统特性和工作流类型调整并行策略
        // ...
        
        log::info!("调整并行执行策略以提高资源利用率");
    }
    
    /// 标识可能的策略改进
    pub fn identify_strategy_improvements(&self) -> HashMap<WorkflowType, SchedulingStrategy> {
        // 使用学习引擎分析历史性能数据，识别可能的改进
        self.learning_engine.identify_improvements()
    }
    
    /// 更新性能模型
    pub fn update_performance_models(&mut self, execution_data: &ExecutionData) {
        // 为每种类型更新性能模型
        for (workflow_type, type_data) in &execution_data.by_type {
            if let Some(model) = self.performance_models.get_mut(workflow_type) {
                model.update(type_data);
            }
        }
        
        // 更新学习引擎
        self.learning_engine.update_from_data(execution_data);
    }
}

/// 展示统一调度框架如何处理不同类型的工作流
fn example_workflow_handling() {
    // 1. 创建统一调度框架
    let mut framework = UnifiedSchedulingFramework::new();
    
    // 2. 注册不同类型的调度适配器
    framework.register_adapter(WorkflowType::Sequential, Box::new(StateMachineAdapter::new()));
    framework.register_adapter(WorkflowType::EventDriven, Box::new(EventDrivenAdapter::new()));
    framework.register_adapter(WorkflowType::PetriNet, Box::new(FairSchedulingAdapter::new()));
    framework.register_adapter(WorkflowType::Parallel, Box::new(Paral
```rust
    framework.register_adapter(WorkflowType::Parallel, Box::new(ParallelExecutionAdapter::new()));
    framework.register_adapter(WorkflowType::Mixed, Box::new(HybridAdapter::new()));
    
    // 3. 启动调度引擎
    tokio::spawn(async move {
        framework.start().await;
    });
    
    // 4. 示例：提交线性序列工作流
    let sequential_workflow = WorkflowDefinition {
        id: WorkflowId::new("sequential-1"),
        workflow_type: "order_processing".to_string(),
        steps: vec![
            Step::new("verify_order"),
            Step::new("process_payment"),
            Step::new("update_inventory"),
            Step::new("ship_order"),
            Step::new("send_notification"),
        ],
    };
    
    framework.submit_workflow(sequential_workflow).await;
    
    // 5. 示例：提交事件驱动工作流
    let event_driven_workflow = WorkflowDefinition {
        id: WorkflowId::new("event-driven-1"),
        workflow_type: "subscription_management".to_string(),
        steps: vec![
            Step::new("create_subscription")
                .with_event_handlers([
                    ("payment_failed", "handle_payment_failure"),
                    ("subscription_canceled", "process_cancellation"),
                ]),
            Step::new("activate_subscription")
                .with_timer("renewal", Duration::from_days(30)),
            Step::new("process_renewal")
                .with_event_handlers([
                    ("renewal_failure", "handle_renewal_failure"),
                ]),
        ],
    };
    
    framework.submit_workflow(event_driven_workflow).await;
    
    // 6. 示例：提交Petri网工作流
    let petri_workflow = PetriNetWorkflow::new("inventory-control")
        .with_place("raw_materials", 10) // 初始标记：10个原材料单位
        .with_place("work_in_progress", 0)
        .with_place("finished_goods", 0)
        .with_place("available_workers", 5) // 5个工人
        
        .with_transition("start_production")
            .input("raw_materials", 1)
            .input("available_workers", 1)
            .output("work_in_progress", 1)
            .action(|| async { 
                // 生产逻辑
                Ok(()) 
            })
            
        .with_transition("finish_production")
            .input("work_in_progress", 1)
            .output("finished_goods", 1)
            .output("available_workers", 1)
            .action(|| async { 
                // 完成生产逻辑
                Ok(()) 
            })
            
        .with_transition("restock")
            .output("raw_materials", 5)
            .action(|| async { 
                // 补货逻辑
                Ok(()) 
            })
            
        .build();
    
    framework.submit_petri_workflow(petri_workflow).await;
    
    // 7. 示例：提交混合工作流
    let mixed_workflow = WorkflowDefinition {
        id: WorkflowId::new("mixed-1"),
        workflow_type: "loan_processing".to_string(),
        steps: vec![
            // 顺序部分
            Step::new("validate_application"),
            
            // 并行部分
            Step::new("parallel_checks")
                .with_parallel_tasks([
                    "check_credit_score",
                    "verify_employment",
                    "verify_identity",
                    "check_property_value",
                ]),
                
            // 决策部分
            Step::new("risk_assessment")
                .with_decisions([
                    ("low_risk", "approve_loan"),
                    ("medium_risk", "manual_review"),
                    ("high_risk", "reject_loan"),
                ]),
                
            // 事件等待部分
            Step::new("await_manual_review")
                .with_event_handlers([
                    ("review_approved", "approve_loan"),
                    ("review_rejected", "reject_loan"),
                    ("additional_info_required", "request_more_info"),
                ]),
                
            // 子工作流
            Step::new("approve_loan")
                .with_sub_workflow("loan_approval_process"),
                
            Step::new("reject_loan")
                .with_sub_workflow("loan_rejection_process"),
        ],
    };
    
    framework.submit_workflow(mixed_workflow).await;
}
```

### 6. 工作流调度策略的等价性分析

通过上述各种调度策略的讨论，我们可以分析它们之间的等价性和转换可能性：

#### 6.1 状态机模型与事件驱动模型的等价性

状态机模型和事件驱动模型在某些条件下是可以相互转换的：

**状态机 → 事件驱动转换**：

- 每个状态转换可以映射为一个事件处理器
- 状态可以表示为事件处理器之间的依赖关系
- 输入条件可以转换为事件触发条件

**事件驱动 → 状态机转换**：

- 每个事件处理器可以映射为一个状态处理逻辑
- 事件可以表示为状态转换条件
- 事件处理器依赖关系可以转换为状态转换图

**例如**：一个简单的订单处理状态机可以等价表示为：

1. **状态机模型**：有`创建订单`→`处理支付`→`发货`→`完成`四个状态，每个状态有明确的转换条件
2. **事件驱动模型**：有`订单创建事件`→`支付成功事件`→`发货完成事件`→`订单完成事件`，每个事件有对应的处理器

这种等价性意味着我们可以根据系统负载和执行环境，动态地在这两种模型之间切换，以获得最佳性能。

#### 6.2 公平调度与其他模型的关系

Petri网模型的公平调度策略与其他模型相比有一些本质区别：

- **资源竞争处理**：公平调度更擅长处理资源竞争，而状态机和事件驱动模型往往假设资源充足
- **非确定性**：公平调度支持非确定性执行顺序，而其他模型通常有更确定的执行路径
- **死锁处理**：公平调度内置了对死锁和饥饿的处理机制

这些区别使得公平调度更适合于高并发、资源受限的场景，但在简单、线性场景中可能引入不必要的复杂性。

#### 6.3 混合策略的优势

混合策略的关键优势在于能够根据工作流不同部分的特性，应用最合适的调度策略：

- 对于线性部分，使用简单高效的状态机调度
- 对于事件响应部分，使用事件驱动调度
- 对于资源竞争部分，使用公平调度
- 对于并行计算部分，使用专用的并行调度

这种"对症下药"的方法可以显著提高整个工作流的执行效率。
通过对工作流进行分解和模式识别，我们可以自动确定最佳的混合策略。

### 7. 统一的设计方案

经过上述分析，我认为是可以设计一个统一的调度框架，能够适应各种工作流类型并动态选择最佳策略。
这个框架应具备：

1. **工作流分析能力**：能够识别工作流的结构特征和执行模式
2. **多策略支持**：内置多种调度策略，适应不同类型的工作流
3. **自适应选择**：根据工作流特性和系统状态动态选择最佳策略
4. **无缝转换**：在不同策略之间平滑切换，不中断工作流执行
5. **资源感知**：根据系统资源状态动态调整调度行为
6. **学习优化**：从执行历史中学习，不断改进调度决策

关键是要认识到，调度策略的选择不应该是工作流开发者的负担，
而应该是调度系统根据工作流特性和运行环境自动做出的决策。
这样，开发者可以专注于业务逻辑，而系统则负责提供最优的执行环境。

### 8. 结论

通过深入分析不同类型工作流的调度需求，我们可以得出以下结论：

1. **不同工作流模式确实需要不同的调度策略**：线性序列型工作流适合状态机调度，复杂分支工作流适合事件驱动调度，资源竞争型工作流适合公平调度。

2. **调度策略之间存在一定程度的等价性**：在特定条件下，一种调度模型可以转换为另一种，这为动态切换策略提供了理论基础。

3. **混合调度是复杂工作流的最佳选择**：真实世界的工作流通常包含多种模式，采用混合调度策略可以获得最佳性能。

4. **统一调度框架是可行的**：通过适当的抽象和设计，可以构建一个能够适应各种工作流类型并自动选择最佳调度策略的统一框架。

5. **自适应学习是关键**：随着工作流执行数据的积累，系统应该能够学习并改进其调度决策，不断提高执行效率。

综上所述，工作流调度不应该是"一刀切"的选择，而应该是一个动态、自适应的过程，
能够根据工作流特性和执行环境灵活选择最佳策略，从而实现最优的执行效率和资源利用率。

## 工作流形式化模型与控制/执行流统一分析

您提出了一个非常深刻的问题，触及到工作流系统设计的核心理论基础。
确实，工作流的编排、类型推理、分类识别和转换需要在编译前静态分析和运行时动态感知两个层面结合。
针对这种需求，确实存在一些形式化模型可以统一解决这类问题。

### 形式化模型概述

以下是几种可以用于统一分析处理工作流的形式化模型：

#### 1. 进程演算(Process Calculi)

**π演算(π-calculus)**和**CCS(Calculus of Communicating Systems)**提供了描述并发系统的形式化基础，
特别适合表达工作流中的通信和并发方面：

```rust
// π演算表示的简单工作流
W = νc.(A(c) | c(x).B(x) | c(y).C(y))
```

**优势**：

- 提供了严格的数学基础来描述并发行为
- 可以表达动态通道创建和传递，适合描述动态工作流
- 支持形式化验证和等价性证明

**应用场景**：

- 对工作流并发行为进行静态分析
- 证明不同工作流实现的行为等价性
- 识别潜在的死锁和竞态条件

#### 2. Petri网模型扩展

**着色Petri网(Colored Petri Nets)**和**时间Petri网(Timed Petri Nets)**提供了综合表达工作流控制流和数据流的能力：

```rust
// CPN ML语言表示的着色Petri网片段
colset TaskStatus = with Ready | Running | Completed | Failed;
colset TaskID = INT;
colset Task = product TaskID * TaskStatus;
var t: Task;
var id: TaskID;
var status: TaskStatus;

transition Execute
  guard (status = Ready)
  input (TaskQueue, 1`(id, status))
  output (ExecutionPool, 1`(id, Running));
```

**优势**：

- 直观的图形表示结合形式化语义
- 可以表达数据相关的控制流决策
- 支持分层模型，适合表达嵌套工作流
- 有成熟的分析工具和技术

**应用场景**：

- 静态工作流结构分析和验证
- 资源竞争和死锁检测
- 性能和吞吐量分析

#### 3. 进程代数与类型系统的结合

**会话类型(Session Types)**和**线性类型(Linear Types)**与进程代数结合，可以保证通信协议正确性：

```rust
// 会话类型表示的服务交互协议
type PaymentProtocol = 
  !{initiate: ?{amount: Money}.
              !{process: ?{result: PaymentResult}.
                         End}}
```

**优势**：

- 在类型系统层面保证通信安全性
- 可以在编译时检测协议违规
- 支持模块化组合和验证

**应用场景**：

- 服务编排的静态验证
- 工作流组件间接口兼容性检查
- 确保异步通信的正确性

#### 4. 时态逻辑(Temporal Logic)

**CTL(计算树逻辑)**和**LTL(线性时态逻辑)**可以用于表达和验证工作流的时序属性：

```rust
// CTL表达的工作流属性
AG(request → AF response)  // 任何请求最终都会得到响应
AG(critical_section → AX ¬critical_section)  // 关键区域访问不会连续发生
```

**优势**：

- 可以表达复杂的时序约束和活性属性
- 支持自动化模型检验
- 适合验证安全和生命周期属性

**应用场景**：

- 工作流正确性验证
- 确保终止性和无死锁
- 验证事务和补偿行为的正确性

#### 5. 类型化反应系统(Typed Reactive Systems)

结合反应式编程模型和强类型系统：

```haskell
-- 反应式系统中的工作流表示
data WorkflowEvent 
  = TaskStarted TaskId 
  | TaskCompleted TaskId Result 
  | TaskFailed TaskId Error

workflow :: Reactive WorkflowEvent WorkflowState
workflow = do
  TaskStarted taskId <- await
  -- 处理任务开始
  (TaskCompleted taskId result <|> TaskFailed taskId err) <- await
  -- 处理完成或失败
```

**优势**：

- 天然适合事件驱动的工作流模型
- 类型安全保证在编译时捕获错误
- 组合性好，支持复杂工作流构建

**应用场景**：

- 事件驱动工作流的建模和验证
- 异步工作流的正确性检查
- 工作流状态转换的类型安全保证

### 统一分析与推理框架

基于上述模型，可以构建一个统一的工作流分析和推理框架，具备以下能力：

#### 1. 工作流结构分析与推理

通过将工作流转换为形式化模型，可以进行：

```rust
pub struct WorkflowGraph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    properties: HashMap<String, Property>,
}

impl WorkflowGraph {
    /// 将工作流转换为进程代数表示
    pub fn to_process_algebra(&self) -> ProcessExpression {
        // 转换算法实现
    }
    
    /// 将工作流转换为Petri网模型
    pub fn to_petri_net(&self) -> PetriNet {
        // 转换算法实现
    }
    
    /// 识别工作流模式
    pub fn identify_patterns(&self) -> Vec<WorkflowPattern> {
        // 模式识别算法
    }
    
    /// 检测控制流反模式
    pub fn detect_anti_patterns(&self) -> Vec<ControlFlowIssue> {
        // 反模式检测
    }
    
    /// 结构简化和规范化
    pub fn normalize(&self) -> WorkflowGraph {
        // 图结构规范化
    }
}
```

#### 2. 静态/动态分析的统一

关键是建立一个模型，既能用于静态分析，又能在运行时更新和验证：

```rust
pub struct UnifiedWorkflowModel {
    static_model: FormalModel,        // 静态结构模型
    runtime_state: RuntimeState,      // 运行时状态
    behavioral_properties: Vec<Property>, // 行为属性
}

impl UnifiedWorkflowModel {
    /// 静态分析工作流性质
    pub fn analyze_statically(&self) -> AnalysisResult {
        // 使用形式化方法对静态模型进行分析
    }
    
    /// 根据运行时观察更新模型
    pub fn update_from_runtime(&mut self, events: &[RuntimeEvent]) {
        // 根据运行时事件更新模型
    }
    
    /// 验证当前状态是否满足预期性质
    pub fn verify_properties(&self) -> VerificationResult {
        // 针对更新后的模型验证性质
    }
    
    /// 预测未来可能的执行路径
    pub fn predict_execution_paths(&self) -> Vec<ExecutionPath> {
        // 基于当前状态预测未来执行
    }
    
    /// 推荐最优调度策略
    pub fn recommend_scheduling_strategy(&self) -> SchedulingStrategy {
        // 基于模型推荐调度策略
    }
}
```

#### 3. 同构分析与转换(Isomorphic Analysis and Transformation)

为了解决不同工作流表示之间的转换问题：

```rust
pub trait IsomorphicTransformable {
    /// 检查两个工作流模型是否同构
    fn is_isomorphic_to(&self, other: &Self) -> bool;
    
    /// 寻找最小的同构转换
    fn find_minimal_transformation(&self, target: &Self) -> TransformationPlan;
    
    /// 将一种调度策略下的工作流转换为另一种策略
    fn transform_scheduling_strategy(
        &self, 
        from: SchedulingStrategy,
        to: SchedulingStrategy
    ) -> Self;
    
    /// 找出控制流等价的表示
    fn find_control_flow_equivalent(&self) -> Vec<Self>;
}
```

#### 4. 工作流类型系统(Workflow Type System)

使用类型系统来表达和验证工作流的行为特性：

```rust
// 工作流类型和类型推导
pub trait WorkflowTyped {
    type Input;
    type Output;
    type Effect;  // 副作用类型
    
    /// 推导工作流类型
    fn infer_type(&self) -> WorkflowType<Self::Input, Self::Output, Self::Effect>;
    
    /// 检查工作流是否与类型兼容
    fn type_check(&self, expected: &WorkflowType<Self::Input, Self::Output, Self::Effect>) -> bool;
    
    /// 类型细化 - 从执行中学习更精确的类型
    fn refine_type(&mut self, observations: &[RuntimeObservation]);
}
```

### 具体实现方案

为解决您提出的统一分析处理需求，我建议结合几种形式化模型构建分层架构：

#### 1. 核心表示层：图结构与π演算

用统一的图表示捕获工作流结构，同时维护π演算表示以处理动态行为：

```rust
/// 统一工作流表示
pub struct UnifiedWorkflowRepresentation {
    // 静态结构表示
    graph: DirectedGraph<ActivityNode, DependencyEdge>,
    
    // 动态行为表示
    pi_calculus: PiCalculusExpression,
    
    // 资源和数据流
    data_flow: DataFlowGraph,
    resource_requirements: ResourceRequirements,
    
    // 时序约束
    temporal_constraints: Vec<TemporalConstraint>,
}
```

#### 2. 分析与推理层

```rust
/// 工作流分析引擎
pub struct WorkflowAnalysisEngine {
    // 各种分析器
    structural_analyzer: StructuralAnalyzer,
    behavioral_analyzer: BehavioralAnalyzer,
    type_inferer: TypeInferer,
    pattern_recognizer: PatternRecognizer,
    
    // 验证引擎
    model_checker: ModelChecker,
    type_checker: TypeChecker,
    
    // 转换引擎
    transformation_engine: TransformationEngine,
}

impl WorkflowAnalysisEngine {
    /// 进行全面分析
    pub fn analyze(&self, workflow: &UnifiedWorkflowRepresentation) -> AnalysisResult {
        // 结构分析
        let structural = self.structural_analyzer.analyze(workflow);
        
        // 行为分析
        let behavioral = self.behavioral_analyzer.analyze(workflow);
        
        // 类型推导
        let type_info = self.type_inferer.infer(workflow);
        
        // 模式识别
        let patterns = self.pattern_recognizer.recognize(workflow);
        
        // 将结果整合
        AnalysisResult {
            structural,
            behavioral,
            type_info,
            patterns,
        }
    }
    
    /// 生成最优调度策略
    pub fn generate_optimal_scheduling(
        &self, 
        workflow: &UnifiedWorkflowRepresentation,
        runtime_info: Option<&RuntimeInfo>
    ) -> SchedulingStrategy {
        // 1. 分析工作流特性
        let analysis = self.analyze(workflow);
        
        // 2. 确定基本调度策略
        let base_strategy = self.determine_base_strategy(&analysis);
        
        // 3. 如果有运行时信息，进一步优化
        let optimized_strategy = if let Some(runtime) = runtime_info {
            self.optimize_strategy(base_strategy, runtime, &analysis)
        } else {
            base_strategy
        };
        
        // 4. 验证策略的正确性
        assert!(self.verify_strategy(&optimized_strategy, workflow));
        
        optimized_strategy
    }
    
    /// 检测工作流是否可以在不同调度策略之间转换
    pub fn can_transform_strategy(
        &self,
        workflow: &UnifiedWorkflowRepresentation,
        from: &SchedulingStrategy,
        to: &SchedulingStrategy
    ) -> bool {
        self.transformation_engine.is_transformable(workflow, from, to)
    }
    
    /// 生成策略转换计划
    pub fn generate_transformation_plan(
        &self,
        workflow: &UnifiedWorkflowRepresentation,
        from: &SchedulingStrategy,
        to: &SchedulingStrategy
    ) -> Option<TransformationPlan> {
        if !self.can_transform_strategy(workflow, from, to) {
            return None;
        }
        
        Some(self.transformation_engine.create_plan(workflow, from, to))
    }
}
```

#### 3. 运行时监控与自适应层

```rust
/// 运行时工作流监控器
pub struct WorkflowRuntimeMonitor {
    model: UnifiedWorkflowRepresentation,
    analysis_engine: WorkflowAnalysisEngine,
    current_state: WorkflowState,
    execution_history: Vec<ExecutionEvent>,
    
    // 学习组件
    learning_engine: AdaptiveLearningEngine,
}

impl WorkflowRuntimeMonitor {
    /// 处理新的执行事件
    pub fn process_event(&mut self, event: ExecutionEvent) {
        // 记录事件
        self.execution_history.push(event.clone());
        
        // 更新当前状态
        self.current_state.update(&event);
        
        // 更新学习引擎
        self.learning_engine.observe(event);
        
        // 检查是否需要调整调度策略
        if self.should_adjust_strategy() {
            self.adjust_scheduling_strategy();
        }
    }
    
    /// 确定是否需要调整调度策略
    fn should_adjust_strategy(&self) -> bool {
        // 基于性能指标、资源利用率等决定
        // ...
        
        false // 简化实现
    }
    
    /// 调整调度策略
    fn adjust_scheduling_strategy(&mut self) {
        // 从学习引擎获取建议
        let suggestion = self.learning_engine.suggest_strategy();
        
        // 获取当前策略
        let current = self.get_current_strategy();
        
        // 检查是否可以转换
        if self.analysis_engine.can_transform_strategy(&self.model, &current, &suggestion) {
            // 生成转换计划
            if let Some(plan) = self.analysis_engine.generate_transformation_plan(
                &self.model, &current, &suggestion
            ) {
                // 执行转换
                self.execute_transformation(plan);
            }
        }
    }
    
    /// 预测未来执行路径
    pub fn predict_execution(&self) -> Vec<PredictedPath> {
        // 基于当前状态和历史生成预测
        self.analysis_engine.predict_execution(&self.model, &self.current_state)
    }
}
```

### 理论基础

这种统一框架的理论基础来自几个关键领域：

1. **范畴论(Category Theory)**：提供了不同形式化模型之间转换的数学基础，尤其是通过函子(Functor)和自然变换(Natural Transformation)建立不同表示之间的同态映射。

2. **抽象解释(Abstract Interpretation)**：允许我们在不同抽象级别分析工作流行为，既可以进行粗粒度的静态分析，也可以进行细粒度的动态分析。

3. **过程语义学(Process Semantics)**：为并发系统提供了严格的形式化语义，使我们能够推理工作流的行为特性。

4. **双向类型推导(Bidirectional Type Inference)**：结合静态类型推导和运行时类型精化，为工作流提供强大的类型安全保证。

### 结论与实施建议

构建一个能够统一分析处理工作流的形式化模型确实是可行的，但需要综合运用多种理论工具。
我建议采取以下步骤实施：

1. **选择核心形式化模型**：我建议以π演算扩展作为核心形式化模型，因为它能够表达动态创建和通信，非常适合现代工作流系统。

2. **构建多视图表示**：维护工作流的多种互补表示（图结构、进程代数表达式、类型注解等），同时保持它们之间的一致性。

3. **实现增量分析**：既支持编译前的全面静态分析，也支持运行时的增量分析，通过共享底层形式化模型实现无缝集成。

4. **开发同构转换库**：实现不同调度策略之间的工作流转换算法，保证转换前后的行为等价性。

5. **集成自适应学习**：通过运行时观察不断优化分析结果和调度决策，形成闭环反馈系统。

这样的统一框架不仅能满足您提出的"工作流编排、类型推理、分类识别、转换"等需求，还能为工作流系统提供坚实的理论基础，确保其正确性和高效性。

最重要的是，这种方法将静态分析和动态感知有机结合，让工作流系统既能在设计时提供强保证，又能在运行时灵活适应变化。
