# 面向端-边缘-云分布式环境的智能家居工作流融合架构

## 目录

- [面向端-边缘-云分布式环境的智能家居工作流融合架构](#面向端-边缘-云分布式环境的智能家居工作流融合架构)
  - [目录](#目录)
  - [一、分布式工作流融合的挑战模型](#一分布式工作流融合的挑战模型)
    - [1. 工作流融合的维度与挑战](#1-工作流融合的维度与挑战)
    - [2. 工作流融合的关键设计者困境](#2-工作流融合的关键设计者困境)
  - [二、端-边缘-云工作流融合架构模型](#二端-边缘-云工作流融合架构模型)
    - [1. 分层工作流融合架构](#1-分层工作流融合架构)
    - [2. 工作流分解与融合逻辑](#2-工作流分解与融合逻辑)
  - [三、数据流融合模型](#三数据流融合模型)
    - [1. 多层数据流融合策略](#1-多层数据流融合策略)
    - [2. 数据冲突解决策略](#2-数据冲突解决策略)
  - [四、执行流融合模型](#四执行流融合模型)
    - [1. 执行位置决策引擎](#1-执行位置决策引擎)
    - [2. 执行状态迁移与恢复](#2-执行状态迁移与恢复)
  - [五、控制流融合模型](#五控制流融合模型)
    - [1. 分层控制流决策模型](#1-分层控制流决策模型)
    - [2. 跨层控制流协调与委派](#2-跨层控制流协调与委派)
  - [六、容错与一致性融合模型](#六容错与一致性融合模型)
    - [1. 多层容错机制](#1-多层容错机制)
    - [2. 一致性保障协议](#2-一致性保障协议)
  - [七、自动化工作流设计与优化](#七自动化工作流设计与优化)
    - [1. 工作流自动生成器](#1-工作流自动生成器)
    - [2. 工作流自动优化器](#2-工作流自动优化器)
  - [八、实现权衡与最佳实践总结](#八实现权衡与最佳实践总结)
    - [1. 端-边缘-云工作流设计决策指南](#1-端-边缘-云工作流设计决策指南)
      - [执行位置决策框架](#执行位置决策框架)
      - [分层工作流设计模式](#分层工作流设计模式)
    - [2. 数据流与一致性权衡指南](#2-数据流与一致性权衡指南)
      - [数据同步模式选择](#数据同步模式选择)
      - [一致性协议选择](#一致性协议选择)
    - [3. 可靠性与弹性设计指南](#3-可靠性与弹性设计指南)
      - [多层容错策略](#多层容错策略)
      - [网络弹性设计](#网络弹性设计)
    - [4. 性能优化指南](#4-性能优化指南)
      - [工作流分配优化](#工作流分配优化)
      - [资源效率优化](#资源效率优化)
  - [总结：多层工作流设计的关键原则](#总结多层工作流设计的关键原则)
    - [1. 明确的责任边界](#1-明确的责任边界)
    - [2. 自适应执行决策](#2-自适应执行决策)
    - [3. 分层容错与恢复](#3-分层容错与恢复)
    - [4. 智能数据流管理](#4-智能数据流管理)
    - [5. 一致性与性能平衡](#5-一致性与性能平衡)

## 一、分布式工作流融合的挑战模型

### 1. 工作流融合的维度与挑战

| 融合维度 | 端侧挑战 | 边缘层挑战 | 云端挑战 | 跨层融合挑战 |
|---------|---------|-----------|---------|------------|
| **数据流融合** | 资源受限\间歇性连接\有限存储 | 数据聚合\中间状态维护\本地缓存管理 | 大规模处理\历史数据分析\数据一致性 | 数据版本冲突\同步时机选择\带宽限制 |
| **执行流融合** | 实时响应需求\低功耗执行\有限算力 | 任务调度\负载均衡\优先级管理 | 弹性计算资源\长时间执行\全局最优化 | 执行位置决策\迁移成本\状态传递 |
| **控制流融合** | 简单逻辑\直接反应\安全防护 | 区域协调\多设备编排\条件评估 | 复杂协调\AI决策\全局规则 | 控制权转移\指令冲突\分层决策 |
| **容错与一致性** | 自我恢复\本地备份\安全模式 | 部分设备失败处理\区域一致性\连接丢失恢复 | 分布式事务\全局一致性\灾备恢复 | 不同恢复策略协调\部分成功处理\最终一致性保障 |

### 2. 工作流融合的关键设计者困境

```text
+-----------------------------------+     +-----------------------------------+
| 集中式设计倾向                    |<--->| 分布式设计倾向                    |
| - 简化管理与监控                  |     | - 提高响应速度与可靠性           |
| - 全局最优决策                    |     | - 降低网络依赖                   |
| - 一致性更易保障                  |     | - 支持离线操作                   |
+-----------------------------------+     +-----------------------------------+

+-----------------------------------+     +-----------------------------------+
| 静态工作流划分                    |<--->| 动态工作流迁移                    |
| - 明确的责任边界                  |     | - 适应网络和负载变化             |
| - 简化实现与测试                  |     | - 优化资源利用                   |
| - 可预测的性能                    |     | - 提高系统弹性                   |
+-----------------------------------+     +-----------------------------------+

+-----------------------------------+     +-----------------------------------+
| 强一致性要求                      |<--->| 高性能与可用性要求                |
| - 可靠的状态管理                  |     | - 低延迟响应                     |
| - 避免不一致操作                  |     | - 持续服务可用                   |
| - 明确的故障处理                  |     | - 负载峰值处理                   |
+-----------------------------------+     +-----------------------------------+
```

## 二、端-边缘-云工作流融合架构模型

### 1. 分层工作流融合架构

```text
+-----------------+   +-----------------+   +-----------------+
| 云端工作流引擎   |   | 边缘工作流引擎   |   | 端侧工作流执行器 |
+-----------------+   +-----------------+   +-----------------+
| • 全局编排层     |   | • 区域协调层     |   | • 设备执行层    |
| • 跨家庭优化     |   | • 房间级编排     |   | • 原子操作     |
| • AI决策支持     |   | • 本地触发器     |   | • 状态报告     |
+-----------------+   +-----------------+   +-----------------+
        ^                     ^                     ^
        |                     |                     |
        v                     v                     v
+-----------------+   +-----------------+   +-----------------+
| • 策略定义      |   | • 工作流缓存     |   | • 行为模板     |
| • 全局状态存储   |   | • 中间状态存储   |   | • 本地参数    |
| • 历史分析      |   | • 边缘计算       |   | • 传感数据    |
+-----------------+   +-----------------+   +-----------------+
```

### 2. 工作流分解与融合逻辑

```go
// 工作流分解器 - 根据复杂度、时效性和资源需求划分工作流
func DecomposeWorkflow(workflowDef WorkflowDefinition) *DecomposedWorkflow {
    decomposed := &DecomposedWorkflow{
        CloudComponents:  []WorkflowComponent{},
        EdgeComponents:   []WorkflowComponent{},
        DeviceComponents: []WorkflowComponent{},
        DataFlows:        []DataFlowDefinition{},
        SyncPoints:       []SyncPointDefinition{},
    }
    
    // 1. 识别设备层原子操作
    for _, action := range workflowDef.Actions {
        if isAtomicDeviceAction(action) {
            decomposed.DeviceComponents = append(decomposed.DeviceComponents, 
                WorkflowComponent{
                    ID:         generateComponentID("device", action),
                    Type:       "device_action",
                    Action:     action,
                    Properties: extractProperties(action, "device"),
                })
        }
    }
    
    // 2. 识别边缘层协调逻辑
    for _, coordination := range workflowDef.Coordinations {
        if isLocalCoordination(coordination) {
            decomposed.EdgeComponents = append(decomposed.EdgeComponents, 
                WorkflowComponent{
                    ID:             generateComponentID("edge", coordination),
                    Type:           "edge_coordination",
                    Coordination:   coordination,
                    Properties:     extractProperties(coordination, "edge"),
                    ChildActions:   findRelatedActions(coordination, workflowDef),
                })
        }
    }
    
    // 3. 识别云端层全局逻辑
    for _, orchestration := range workflowDef.Orchestrations {
        decomposed.CloudComponents = append(decomposed.CloudComponents, 
            WorkflowComponent{
                ID:             generateComponentID("cloud", orchestration),
                Type:           "cloud_orchestration",
                Orchestration:  orchestration,
                Properties:     extractProperties(orchestration, "cloud"),
                Dependencies:   findDependencies(orchestration, workflowDef),
            })
    }
    
    // 4. 定义组件间数据流
    decomposed.DataFlows = defineDataFlows(decomposed, workflowDef)
    
    // 5. 确定同步点
    decomposed.SyncPoints = defineSyncPoints(decomposed, workflowDef)
    
    return decomposed
}

// 工作流融合器 - 定义层间协作方式
func FuseWorkflowComponents(decomposed *DecomposedWorkflow) *FusedWorkflow {
    fused := &FusedWorkflow{
        CloudWorkflows:  []CloudWorkflow{},
        EdgeWorkflows:   []EdgeWorkflow{},
        DeviceWorkflows: []DeviceWorkflow{},
        SyncStrategies:  map[string]SyncStrategy{},
        FallbackPlans:   map[string]FallbackPlan{},
    }
    
    // 1. 创建设备工作流
    fused.DeviceWorkflows = createDeviceWorkflows(decomposed.DeviceComponents)
    
    // 2. 创建边缘工作流，并关联设备工作流
    fused.EdgeWorkflows = createEdgeWorkflows(decomposed.EdgeComponents, fused.DeviceWorkflows)
    
    // 3. 创建云端工作流，并关联边缘工作流
    fused.CloudWorkflows = createCloudWorkflows(decomposed.CloudComponents, fused.EdgeWorkflows)
    
    // 4. 定义数据同步策略
    for _, dataFlow := range decomposed.DataFlows {
        syncStrategy := defineSyncStrategy(dataFlow)
        fused.SyncStrategies[dataFlow.ID] = syncStrategy
    }
    
    // 5. 定义故障恢复计划
    for _, syncPoint := range decomposed.SyncPoints {
        fallbackPlan := defineFallbackPlan(syncPoint, decomposed)
        fused.FallbackPlans[syncPoint.ID] = fallbackPlan
    }
    
    return fused
}
```

## 三、数据流融合模型

### 1. 多层数据流融合策略

```go
// 定义数据流融合策略
type DataFlowFusionStrategy struct {
    // 数据传输方向: up(设备->云), down(云->设备), bidirectional
    Direction      string
    
    // 数据重要性: critical, important, normal, background
    Importance     string
    
    // 同步模式: realtime, eventual, periodic, ondemand
    SyncMode       string
    
    // 缓存策略
    CachingPolicy  CachingPolicy
    
    // 冲突解决策略
    ConflictPolicy ConflictPolicy
    
    // 批处理策略
    BatchingPolicy BatchingPolicy
}

// 实现数据流融合逻辑
func implementDataFlowFusion(ctx workflow.Context, dataFlow DataFlowDefinition, 
    strategy DataFlowFusionStrategy) error {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("执行数据流融合", "dataFlowID", dataFlow.ID, "direction", strategy.Direction)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: getTimeoutForImportance(strategy.Importance),
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: getRetryCountForImportance(strategy.Importance),
            InitialInterval: 1 * time.Second,
            MaximumInterval: 10 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 根据同步模式实现不同的数据流处理
    switch strategy.SyncMode {
    case "realtime":
        return implementRealtimeSync(ctx, dataFlow, strategy)
    case "eventual":
        return implementEventualSync(ctx, dataFlow, strategy)
    case "periodic":
        return implementPeriodicSync(ctx, dataFlow, strategy)
    case "ondemand":
        return implementOnDemandSync(ctx, dataFlow, strategy)
    default:
        return fmt.Errorf("不支持的同步模式: %s", strategy.SyncMode)
    }
}

// 实时同步实现
func implementRealtimeSync(ctx workflow.Context, dataFlow DataFlowDefinition, 
    strategy DataFlowFusionStrategy) error {
    
    // 1. 设置数据监听
    signalChan := workflow.GetSignalChannel(ctx, dataFlow.ID + "_data_signal")
    
    // 2. 监听数据变更并立即同步
    for {
        var dataUpdate DataUpdateSignal
        signalChan.Receive(ctx, &dataUpdate)
        
        // 3. 根据方向执行同步
        if strategy.Direction == "up" || strategy.Direction == "bidirectional" {
            err := workflow.ExecuteActivity(ctx, activities.SyncDataUpstream, 
                UpstreamSyncParams{
                    DataID: dataFlow.ID,
                    Data: dataUpdate.Data,
                    Timestamp: dataUpdate.Timestamp,
                    Source: dataUpdate.Source,
                }).Get(ctx, nil)
            
            if err != nil {
                // 记录错误但继续处理
                workflow.GetLogger(ctx).Error("上行数据同步失败", 
                    "dataFlowID", dataFlow.ID, "error", err)
            }
        }
        
        if strategy.Direction == "down" || strategy.Direction == "bidirectional" {
            // 如果有更新，向下同步
            if dataUpdate.NeedsDownstreamSync {
                err := workflow.ExecuteActivity(ctx, activities.SyncDataDownstream, 
                    DownstreamSyncParams{
                        DataID: dataFlow.ID,
                        Data: dataUpdate.Data,
                        Timestamp: dataUpdate.Timestamp,
                        Target: dataUpdate.Target,
                    }).Get(ctx, nil)
                
                if err != nil {
                    workflow.GetLogger(ctx).Error("下行数据同步失败", 
                        "dataFlowID", dataFlow.ID, "error", err)
                }
            }
        }
    }
}

// 最终一致性同步实现
func implementEventualSync(ctx workflow.Context, dataFlow DataFlowDefinition, 
    strategy DataFlowFusionStrategy) error {
    
    // 1. 初始化同步状态
    var syncState DataSyncState
    err := workflow.ExecuteActivity(ctx, activities.InitializeSyncState, 
        dataFlow.ID).Get(ctx, &syncState)
    
    // 2. 设置批处理参数
    batchSize := strategy.BatchingPolicy.BatchSize
    if batchSize <= 0 {
        batchSize = 50 // 默认批大小
    }
    
    // 3. 周期性检查并同步数据变更
    for {
        // 等待积累足够的变更或时间间隔
        timer := workflow.NewTimer(ctx, workflow.Now(ctx).Add(30*time.Second))
        
        // 创建选择器处理事件
        selector := workflow.NewSelector(ctx)
        
        // 添加定时器处理
        selector.AddFuture(timer.Future, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            // 时间触发，执行同步逻辑
        })
        
        // 等待触发
        selector.Select(ctx)
        
        // 4. 获取待同步的数据变更
        var pendingChanges []DataChange
        err := workflow.ExecuteActivity(ctx, activities.GetPendingDataChanges, 
            PendingChangesParams{
                DataFlowID: dataFlow.ID,
                BatchSize: batchSize,
                LastSyncState: syncState,
            }).Get(ctx, &pendingChanges)
        
        if err != nil {
            workflow.GetLogger(ctx).Error("获取待同步数据变更失败", 
                "dataFlowID", dataFlow.ID, "error", err)
            continue
        }
        
        if len(pendingChanges) == 0 {
            // 没有变更，继续等待
            continue
        }
        
        // 5. 执行批量同步
        var syncResult BatchSyncResult
        err = workflow.ExecuteActivity(ctx, activities.BatchSyncDataChanges, 
            BatchSyncParams{
                DataFlowID: dataFlow.ID,
                Changes: pendingChanges,
                Direction: strategy.Direction,
                ConflictPolicy: strategy.ConflictPolicy,
            }).Get(ctx, &syncResult)
        
        if err != nil {
            workflow.GetLogger(ctx).Error("批量同步数据变更失败", 
                "dataFlowID", dataFlow.ID, "error", err)
            continue
        }
        
        // 6. 更新同步状态
        syncState = syncResult.NewSyncState
    }
}
```

### 2. 数据冲突解决策略

```go
// 定义冲突解决策略
type ConflictPolicy struct {
    // 策略类型: timestamp_wins, priority_wins, merge, custom
    PolicyType      string
    
    // 默认赢家: cloud, edge, device
    DefaultWinner   string
    
    // 自定义合并逻辑
    MergeLogic      string
    
    // 冲突通知
    NotifyOnConflict bool
}

// 解决数据冲突
func resolveDataConflict(ctx workflow.Context, conflict DataConflict, 
    policy ConflictPolicy) (resolvedData interface{}, err error) {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("解决数据冲突", "dataID", conflict.DataID, 
        "policy", policy.PolicyType)
    
    // 基于时间戳的冲突解决
    if policy.PolicyType == "timestamp_wins" {
        if conflict.CloudData.Timestamp.After(conflict.EdgeData.Timestamp) &&
           conflict.CloudData.Timestamp.After(conflict.DeviceData.Timestamp) {
            return conflict.CloudData.Value, nil
        } else if conflict.EdgeData.Timestamp.After(conflict.DeviceData.Timestamp) {
            return conflict.EdgeData.Value, nil
        } else {
            return conflict.DeviceData.Value, nil
        }
    }
    
    // 基于优先级的冲突解决
    if policy.PolicyType == "priority_wins" {
        switch policy.DefaultWinner {
        case "cloud":
            return conflict.CloudData.Value, nil
        case "edge":
            return conflict.EdgeData.Value, nil
        case "device":
            return conflict.DeviceData.Value, nil
        }
    }
    
    // 数据合并策略
    if policy.PolicyType == "merge" {
        var mergedData interface{}
        err := workflow.ExecuteActivity(ctx, activities.MergeConflictingData, 
            MergeParams{
                Conflict: conflict,
                MergeLogic: policy.MergeLogic,
            }).Get(ctx, &mergedData)
        
        if err != nil {
            logger.Error("合并冲突数据失败", "error", err)
            // 如果合并失败，使用默认赢家的数据
            switch policy.DefaultWinner {
            case "cloud":
                return conflict.CloudData.Value, nil
            case "edge":
                return conflict.EdgeData.Value, nil
            case "device":
                return conflict.DeviceData.Value, nil
            }
        }
        
        return mergedData, nil
    }
    
    // 自定义冲突解决
    if policy.PolicyType == "custom" {
        var resolvedData interface{}
        err := workflow.ExecuteActivity(ctx, activities.ResolveConflictWithCustomLogic, 
            CustomResolutionParams{
                Conflict: conflict,
                Logic: policy.MergeLogic,
            }).Get(ctx, &resolvedData)
        
        if err != nil {
            logger.Error("自定义冲突解决失败", "error", err)
            return nil, err
        }
        
        return resolvedData, nil
    }
    
    return nil, fmt.Errorf("不支持的冲突解决策略: %s", policy.PolicyType)
}
```

## 四、执行流融合模型

### 1. 执行位置决策引擎

```go
// 执行位置决策引擎
type ExecutionPlacementEngine struct {
    // 决策因素权重
    Weights struct {
        Latency       float64 // 响应时间敏感度权重
        ResourceUsage float64 // 资源使用权重
        Reliability   float64 // 可靠性要求权重
        DataLocality  float64 // 数据本地性权重
        BatteryImpact float64 // 电池影响权重
    }
    
    // 运行时状态
    RuntimeState struct {
        NetworkLatency     map[string]float64 // 当前网络延迟
        CloudAvailability  float64            // 云端可用性
        EdgeAvailability   map[string]float64 // 边缘节点可用性
        DeviceBatteryLevel map[string]float64 // 设备电池电量
        DeviceLoad         map[string]float64 // 设备负载
        EdgeLoad           map[string]float64 // 边缘节点负载
        CloudLoad          float64            // 云端负载
    }
}

// 决定工作流组件的最佳执行位置
func (e *ExecutionPlacementEngine) DecideExecutionPlacement(
    component WorkflowComponent, context ExecutionContext) ExecutionPlacement {
    
    // 计算每个执行位置的得分
    deviceScore := e.calculateDeviceScore(component, context)
    edgeScore := e.calculateEdgeScore(component, context)
    cloudScore := e.calculateCloudScore(component, context)
    
    // 选择得分最高的位置
    if deviceScore >= edgeScore && deviceScore >= cloudScore {
        return ExecutionPlacement{
            Component: component.ID,
            Location: "device",
            DeviceID: selectBestDevice(component, context),
            Score: deviceScore,
        }
    } else if edgeScore >= cloudScore {
        return ExecutionPlacement{
            Component: component.ID,
            Location: "edge",
            EdgeNodeID: selectBestEdgeNode(component, context),
            Score: edgeScore,
        }
    } else {
        return ExecutionPlacement{
            Component: component.ID,
            Location: "cloud",
            Score: cloudScore,
        }
    }
}

// 计算设备端执行得分
func (e *ExecutionPlacementEngine) calculateDeviceScore(
    component WorkflowComponent, context ExecutionContext) float64 {
    
    // 检查组件是否可在设备上执行
    if !canExecuteOnDevice(component) {
        return -1.0 // 不可能在设备上执行
    }
    
    // 基础分数 - 设备执行通常有最低延迟
    score := 50.0
    
    // 响应时间因素 - 设备执行通常有最低延迟
    score += e.Weights.Latency * 10.0
    
    // 电池影响
    deviceID := getTargetDevice(component, context)
    batteryLevel := e.RuntimeState.DeviceBatteryLevel[deviceID]
    if batteryLevel < 0.2 { // 低于20%电量
        score -= e.Weights.BatteryImpact * (0.2 - batteryLevel) * 100
    }
    
    // 设备负载
    deviceLoad := e.RuntimeState.DeviceLoad[deviceID]
    if deviceLoad > 0.7 { // 高负载
        score -= e.Weights.ResourceUsage * (deviceLoad - 0.7) * 100
    }
    
    // 数据本地性 - 如果数据已在设备上，提高得分
    if hasLocalData(component, deviceID, context) {
        score += e.Weights.DataLocality * 5.0
    }
    
    // 设备可用性
    // 某些设备可能不总是可靠（如传感器可能有故障）
    deviceReliability := getDeviceReliability(deviceID, context)
    score *= e.Weights.Reliability * deviceReliability
    
    return score
}

// 计算边缘节点执行得分
func (e *ExecutionPlacementEngine) calculateEdgeScore(
    component WorkflowComponent, context ExecutionContext) float64 {
    
    // 检查组件是否可在边缘节点上执行
    if !canExecuteOnEdge(component) {
        return -1.0 // 不可能在边缘节点上执行
    }
    
    // 基础分数
    score := 40.0
    
    // 确定最佳边缘节点
    edgeNodeID := selectBestEdgeNode(component, context)
    
    // 响应时间因素 - 边缘执行通常比云端快，但比设备慢
    networkLatency := e.RuntimeState.NetworkLatency["device_to_edge"]
    score += e.Weights.Latency * (10.0 - networkLatency)
    
    // 边缘节点负载
    edgeLoad := e.RuntimeState.EdgeLoad[edgeNodeID]
    if edgeLoad > 0.8 { // 高负载
        score -= e.Weights.ResourceUsage * (edgeLoad - 0.8) * 100
    } else {
        // 有足够资源，提高得分
        score += e.Weights.ResourceUsage * (0.8 - edgeLoad) * 20
    }
    
    // 数据本地性 - 如果数据已在边缘节点，提高得分
    if hasLocalData(component, edgeNodeID, context) {
        score += e.Weights.DataLocality * 5.0
    }
    
    // 边缘节点可用性
    edgeAvailability := e.RuntimeState.EdgeAvailability[edgeNodeID]
    score *= e.Weights.Reliability * edgeAvailability
    
    return score
}

// 计算云端执行得分
func (e *ExecutionPlacementEngine) calculateCloudScore(
    component WorkflowComponent, context ExecutionContext) float64 {
    
    // 几乎所有组件都可在云端执行
    
    // 基础分数
    score := 30.0
    
    // 响应时间因素 - 云端执行通常延迟较高
    totalNetworkLatency := e.RuntimeState.NetworkLatency["device_to_edge"] + 
                          e.RuntimeState.NetworkLatency["edge_to_cloud"]
    score -= e.Weights.Latency * totalNetworkLatency
    
    // 资源利用 - 云端资源通常更丰富
    score += e.Weights.ResourceUsage * 8.0
    
    // 云端可用性
    cloudAvailability := e.RuntimeState.CloudAvailability
    if cloudAvailability < 0.95 { // 降低云可用性对关键操作的影响
        score *= e.Weights.Reliability * cloudAvailability
    }
    
    // 如果组件需要全局数据或AI处理，云端得分提高
    if requiresGlobalData(component) || requiresAIProcessing(component) {
        score += 20.0
    }
    
    return score
}
```

### 2. 执行状态迁移与恢复

```go
// 工作流状态迁移控制器
type WorkflowStateMigrationController struct {
    // 迁移决策引擎
    PlacementEngine *ExecutionPlacementEngine
    
    // 跟踪活跃工作流的当前执行位置
    ActiveWorkflows map[string]ExecutionPlacement
    
    // 迁移策略
    MigrationPolicy MigrationPolicy
}

// 迁移策略
type MigrationPolicy struct {
    // 触发迁移的阈值
    ScoreThresholdDiff      float64  // 新位置得分必须高出多少才迁移
    MinBatteryForMigration  float64  // 最低电池电量要求
    NetworkStabilityPeriod  time.Duration // 网络稳定时间要求
    
    // 状态传输大小限制
    MaxStateSizeForMigration int     // 迁移状态的最大字节数
    
    // 迁移冷却期
    MigrationCooldown       time.Duration // 两次迁移之间的最小间隔
}

// 评估并执行工作流迁移
func (c *WorkflowStateMigrationController) EvaluateAndMigrate(
    ctx workflow.Context, workflowID string, currentState WorkflowExecutionState) error {
    
    logger := workflow.GetLogger(ctx)
    
    // 1. 获取当前执行位置
    currentPlacement, exists := c.ActiveWorkflows[workflowID]
    if !exists {
        return fmt.Errorf("未找到工作流执行位置: %s", workflowID)
    }
    
    // 2. 获取执行上下文
    executionContext := buildExecutionContext(workflowID, currentState)
    
    // 3. 重新评估最佳执行位置
    component := getWorkflowComponent(workflowID)
    newPlacement := c.PlacementEngine.DecideExecutionPlacement(component, executionContext)
    
    // 4. 判断是否需要迁移
    if !shouldMigrate(currentPlacement, newPlacement, c.MigrationPolicy) {
        logger.Info("不需要迁移工作流", "workflowID", workflowID,
            "currentScore", currentPlacement.Score, "newScore", newPlacement.Score)
        return nil
    }
    
    logger.Info("决定迁移工作流", "workflowID", workflowID,
        "from", currentPlacement.Location, "to", newPlacement.Location,
        "scoreDiff", newPlacement.Score - currentPlacement.Score)
    
    // 5. 执行迁移
    return migrateWorkflow(ctx, workflowID, currentPlacement, newPlacement, currentState)
}

// 判断是否应该迁移工作流
func shouldMigrate(current, new ExecutionPlacement, policy MigrationPolicy) bool {
    // 位置相同，不需要迁移
    if current.Location == new.Location {
        if current.Location == "edge" && current.EdgeNodeID != new.EdgeNodeID {
            // 不同的边缘节点，需要评估是否值得迁移
            scoreDiff := new.Score - current.Score
            return scoreDiff > policy.ScoreThresholdDiff
        }
        return false
    }
    
    // 得分差异是否足够大
    scoreDiff := new.Score - current.Score
    if scoreDiff <= policy.ScoreThresholdDiff {
        return false
    }
    
    // 检查迁移限制条件
    // 1. 如果要迁移到电池供电的设备，检查电池电量是否足够
    if new.Location == "device" {
        deviceBatteryLevel := getDeviceBatteryLevel(new.DeviceID)
        if deviceBatteryLevel < policy.MinBatteryForMigration {
            return false
        }
    }
    
    // 2. 检查网络稳定性
    networkStableTime := getNetworkStableTime(current.Location, new.Location)
    if networkStableTime < policy.NetworkStabilityPeriod {
        return false
    }
    
    // 3. 检查迁移冷却期
    lastMigrationTime := getLastMigrationTime(current.Component)
    if time.Since(lastMigrationTime) < policy.MigrationCooldown {
        return false
    }
    
    return true
}

// 迁移工作流执行
func migrateWorkflow(ctx workflow.Context, workflowID string, 
    from, to ExecutionPlacement, currentState WorkflowExecutionState) error {
    
    logger := workflow.GetLogger(ctx)
    
    // 1. 准备迁移元数据
    migrationMeta := WorkflowMigrationMeta{
        WorkflowID:      workflowID,
        SourceLocation:  from.Location,
        TargetLocation:  to.Location,
        StateSize:       estimateStateSize(currentState),
        Timestamp:       time.Now(),
    }
    
    if from.Location == "device" {
        migrationMeta.SourceID = from.DeviceID
    } else if from.Location == "edge" {
        migrationMeta.SourceID = from.EdgeNodeID
    }
    
    if to.Location == "device" {
        migrationMeta.TargetID = to.DeviceID
    } else if to.Location == "edge" {
        migrationMeta.TargetID = to.EdgeNodeID
    }
    
    // 2. 序列化工作流状态
    serializedState, err := serializeWorkflowState(currentState)
    if err != nil {
        return fmt.Errorf("序列化工作流状态失败: %w", err)
    }
    
    // 3. 传输状态到目标位置
    transferOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
            InitialInterval: 1 * time.Second,
            MaximumInterval: 10 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    transferCtx := workflow.WithActivityOptions(ctx, transferOptions)
    
    var transferResult StateTransferResult
    err = workflow.ExecuteActivity(transferCtx, activities.TransferWorkflowState, 
        StateTransferRequest{
            MigrationMeta: migrationMeta,
            SerializedState: serializedState,
        }).Get(transferCtx, &transferResult)
    
    if err != nil {
        return fmt.Errorf("传输工作流状态失败: %w", err)
    }
    
    // 4. 在目标位置启动工作流
    startOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
        },
    }
    startCtx := workflow.WithActivityOptions(ctx, startOptions)
    
    var startResult WorkflowStartResult
    err = workflow.ExecuteActivity(startCtx, activities.StartMigratedWorkflow, 
        WorkflowStartRequest{
            MigrationMeta: migrationMeta,
            StateReference: transferResult.StateReference,
        }).Get(startCtx, &startResult)
    
    if err != nil {
        logger.Error("启动迁移的工作流失败", "error", err)
        
        // 5. 如果启动失败，尝试回滚
        _ = workflow.ExecuteActivity(ctx, activities.RollbackWorkflowMigration, 
            RollbackRequest{
                MigrationMeta: migrationMeta,
                TransferResult: transferResult,
            }).Get(ctx, nil)
        
        return fmt.Errorf("启动迁移的工作流失败: %w", err)
    }
    
    // 6. 确认迁移完成并终止源工作流
    confirmOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
    }
    confirmCtx := workflow.WithActivityOptions(ctx, confirmOptions)
    
    err = workflow.ExecuteActivity(confirmCtx, activities.ConfirmWorkflowMigration, 
        ConfirmMigrationRequest{
            MigrationMeta: migrationMeta,
            StartResult: startResult,
        }).Get(confirmCtx, nil)
    
    if err != nil {
        logger.Error("确认工作流迁移失败", "error", err)
        // 即使确认失败，迁移可能已成功，记录但不返回错误
    }
    
    logger.Info("工作流迁移成功", "workflowID", workflowID, 
        "from", from.Location, "to", to.Location)
    
    return nil
}
```

## 五、控制流融合模型

### 1. 分层控制流决策模型

```go
// 分层控制流决策模型
type ControlFlowHierarchy struct {
    // 控制决策层级
    Layers []ControlLayer
    
    // 层间通信规则
    LayerCommunication map[string]CommunicationRule
    
    // 决策冲突解决策略
    ConflictResolution ConflictResolutionStrategy
}

// 控制层定义
type ControlLayer struct {
    // 层标识
    ID            string
    
    // 执行位置: cloud, edge, device
    Location      string
    
    // 决策范围
    Scope         ControlScope
    
    // 决策优先级 (1-100)
    Priority      int
    
    // 自主决策能力
    Autonomy      AutonomyLevel
    
    // 授权控制列表
    Permissions   []Permission
}

// 控制范围
type ControlScope struct {
    // 空间范围: global, home, room, device
    SpatialScope   string
    
    // 时间范围: long_term, daily, immediate
    TemporalScope  string
    
    // 影响范围: system, subsystem, component
    ImpactScope    string
}

// 自主程度
type AutonomyLevel struct {
    // 自主决策级别: full, supervised, restricted, none
    Level          string
    
    // 需要确认的情况
    ConfirmationRequired []string
    
    // 授权超时时间
    AuthorizationTTL     time.Duration
}

// 实现分层控制流决策
func implementHierarchicalControl(ctx workflow.Context, 
    hierarchy ControlFlowHierarchy, request ControlRequest) (ControlDecision, error) {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("执行分层控制决策", "requestType", request.Type)
    
    // 1. 确定适用的控制层
    applicableLayers := findApplicableLayers(hierarchy, request)
    
    // 如果没有适用的层，返回错误
    if len(applicableLayers) == 0 {
        return ControlDecision{}, fmt.Errorf("没有适用的控制层处理请求: %s", request.Type)
    }
    
    // 2. 从最高优先级的层开始尝试决策
    sort.Slice(applicableLayers, func(i, j int) bool {
        return applicableLayers[i].Priority > applicableLayers[j].Priority
    })
    
    var finalDecision ControlDecision
    var decisionMade bool
    
    for _, layer := range applicableLayers {
        // 检查层是否有权限处理该请求
        if !hasPermission(layer, request) {
            continue
        }
        
        // 在适当的位置执行决策
        var layerDecision ControlDecision
        var err error
        
        switch layer.Location {
        case "cloud":
            layerDecision, err = executeCloudDecision(ctx, layer, request)
        case "edge":
            layerDecision, err = executeEdgeDecision(ctx, layer, request)
        case "device":
            layerDecision, err = executeDeviceDecision(ctx, layer, request)
        }
        
        if err != nil {
            logger.Error("控制层决策失败", "layer", layer.ID, "error", err)
            continue
        }
        
        // 3. 检查是否需要更高层级确认
        if requiresConfirmation(layer, layerDecision) {
            confirmed, err := requestConfirmation(ctx, layer, layerDecision, hierarchy)
            if err != nil || !confirmed {
                logger.Info("决策未获确认，尝试下一层", "layer", layer.ID)
                continue
            }
        }
        
        // 4. 决策冲突检查
        if decisionMade {
            // 已有决策，检查冲突
            if decisionsConflict(finalDecision, layerDecision) {
                // 解决冲突
                finalDecision = resolveDecisionConflict(finalDecision, layerDecision, 
                    hierarchy.ConflictResolution)
            } else {
                // 合并决策
                finalDecision = mergeDecisions(finalDecision, layerDecision)
            }
        } else {
            finalDecision = layerDecision
            decisionMade = true
        }
        
        // 如果是最高权限层且决策是最终的，不再继续
        if layer.Priority >= 90 && layerDecision.IsFinal {
            break
        }
    }
    
    if !decisionMade {
        return ControlDecision{}, fmt.Errorf("所有适用层均未能做出决策")
    }
    
    // 5. 记录最终决策
    _ = workflow.ExecuteActivity(ctx, activities.RecordControlDecision, 
        DecisionRecord{
            RequestID: request.ID,
            Decision: finalDecision,
            Timestamp: workflow.Now(ctx),
        }).Get(ctx, nil)
    
    return finalDecision, nil
}

// 云端决策实现
func executeCloudDecision(ctx workflow.Context, layer ControlLayer, 
    request ControlRequest) (ControlDecision, error) {
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    var decision ControlDecision
    
    // 全局AI决策
    if layer.Scope.SpatialScope == "global" {
        err := workflow.ExecuteActivity(ctx, activities.ExecuteGlobalAIDecision, 
            GlobalDecisionParams{
                Request: request,
                Layer: layer,
            }).Get(ctx, &decision)
        
        if err != nil {
            return ControlDecision{}, fmt.Errorf("全局AI决策失败: %w", err)
        }
    } else {
        // 家庭级规则决策
        err := workflow.ExecuteActivity(ctx, activities.ExecuteCloudRuleBasedDecision, 
            CloudRuleParams{
                Request: request,
                Layer: layer,
            }).Get(ctx, &decision)
        
        if err != nil {
            return ControlDecision{}, fmt.Errorf("云端规则决策失败: %w", err)
        }
    }
    
    return decision, nil
}

// 边缘决策实现
func executeEdgeDecision(ctx workflow.Context, layer ControlLayer, 
    request ControlRequest) (ControlDecision, error) {
    
    // 设置活动选项，较短超时
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
            InitialInterval: 500 * time.Millisecond,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    var decision ControlDecision
    
    // 区域协调决策
    if layer.Scope.SpatialScope == "room" {
        err := workflow.ExecuteActivity(ctx, activities.ExecuteRoomCoordinationDecision, 
            RoomCoordinationParams{
                Request: request,
                RoomID: request.RoomID,
                Layer: layer,
            }).Get(ctx, &decision)
        
        if err != nil {
            return ControlDecision{}, fmt.Errorf("房间协调决策失败: %w", err)
        }
    } else {
        // 家庭本地决策
        err := workflow.ExecuteActivity(ctx, activities.ExecuteEdgeLocalDecision, 
            EdgeLocalParams{
                Request: request,
                HomeID: request.HomeID,
                Layer: layer,
            }).Get(ctx, &decision)
        
        if err != nil {
            return ControlDecision{}, fmt.Errorf("边缘本地决策失败: %w", err)
        }
    }
    
    return decision, nil
}

// 设备决策实现
func executeDeviceDecision(ctx workflow.Context, layer ControlLayer, 
    request ControlRequest) (ControlDecision, error) {
    
    // 设置活动选项，非常短的超时
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 3 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
            InitialInterval: 200 * time.Millisecond,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    var decision ControlDecision
    
    // 设备直接决策
    err := workflow.ExecuteActivity(ctx, activities.ExecuteDeviceDirectDecision, 
        DeviceDirectParams{
            Request: request,
            DeviceID: request.DeviceID,
            Layer: layer,
        }).Get(ctx, &decision)
    
    if err != nil {
        return ControlDecision{}, fmt.Errorf("设备直接决策失败: %w", err)
    }
    
    return decision, nil
}
```

### 2. 跨层控制流协调与委派

```go
// 实现跨层控制流协调
func coordinateControlFlowAcrossLayers(ctx workflow.Context, 
    request ControlRequest, hierarchy ControlFlowHierarchy) error {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("开始跨层控制流协调", "requestID", request.ID)
    
    // 1. 初始化协调状态
    coordinationState := CoordinationState{
        RequestID: request.ID,
        StartTime: workflow.Now(ctx),
        Status: "in_progress",
        CompletedSteps: []string{},
    }
    
    // 2. 制定协调计划
    var coordinationPlan CoordinationPlan
    err := workflow.ExecuteActivity(ctx, activities.CreateCoordinationPlan, 
        CoordinationPlanRequest{
            Request: request,
            Hierarchy: hierarchy,
        }).Get(ctx, &coordinationPlan)
    
    if err != nil {
        return fmt.Errorf("创建协调计划失败: %w", err)
    }
    
    logger.Info("创建协调计划", "steps", len(coordinationPlan.Steps))
    
    // 3. 执行协调步骤
    for i, step := range coordinationPlan.Steps {
        logger.Info("执行协调步骤", "step", i+1, "type", step.Type, "layer", step.LayerID)
        
        switch step.Type {
        case "decision":
            // 在指定层执行决策
            err = executeDecisionStep(ctx, step, request, hierarchy)
            
        case "delegation":
            // 委派决策给其他层
            err = executeDelegationStep(ctx, step, request, hierarchy)
            
        case "confirmation":
            // 请求上层确认
            err = executeConfirmationStep(ctx, step, request, hierarchy)
            
        case "notification":
            // 通知其他层
            err = executeNotificationStep(ctx, step, request, hierarchy)
            
        case "synchronization":
            // 等待多层同步
            err = executeSynchronizationStep(ctx, step, request, hierarchy)
        }
        
        if err != nil {
            logger.Error("协调步骤执行失败", "step", i+1, "error", err)
            
            // 检查步骤是否关键
            if step.IsCritical {
                return fmt.Errorf("关键协调步骤失败: %w", err)
            }
            
            // 非关键步骤失败，继续执行
            continue
        }
        
        // 更新协调状态
        coordinationState.CompletedSteps = append(coordinationState.CompletedSteps, step.ID)
    }
    
    // 4. 完成协调
    coordinationState.Status = "completed"
    coordinationState.EndTime = workflow.Now(ctx)
    
    // 记录协调完成
    _ = workflow.ExecuteActivity(ctx, activities.RecordCoordinationCompletion, 
        coordinationState).Get(ctx, nil)
    
    return nil
}

// 执行委派决策步骤
func executeDelegationStep(ctx workflow.Context, step CoordinationStep, 
    request ControlRequest, hierarchy ControlFlowHierarchy) error {
    
    logger := workflow.GetLogger(ctx)
    
    // 1. 找到目标层
    targetLayer := findLayerByID(hierarchy, step.TargetLayerID)
    if targetLayer == nil {
        return fmt.Errorf("未找到目标控制层: %s", step.TargetLayerID)
    }
    
    // 2. 准备委派请求
    delegationRequest := ControlDelegationRequest{
        OriginalRequestID: request.ID,
        DelegationID: step.ID,
        FromLayerID: step.LayerID,
        ToLayerID: step.TargetLayerID,
        Scope: step.Scope,
        Parameters: step.Parameters,
        Constraints: step.Constraints,
        Timestamp: workflow.Now(ctx),
    }
    
    // 3. 发送委派请求
    var delegationResponse ControlDelegationResponse
    var err error
    
    switch targetLayer.Location {
    case "cloud":
        // 委派给云端
        err = workflow.ExecuteActivity(ctx, activities.DelegateToCloud, 
            delegationRequest).Get(ctx, &delegationResponse)
            
    case "edge":
        // 委派给边缘
        err = workflow.ExecuteActivity(ctx, activities.DelegateToEdge, 
            delegationRequest).Get(ctx, &delegationResponse)
            
    case "device":
        // 委派给设备
        err = workflow.ExecuteActivity(ctx, activities.DelegateToDevice, 
            delegationRequest).Get(ctx, &delegationResponse)
    }
    
    if err != nil {
        return fmt.Errorf("委派决策失败: %w", err)
    }
    
    // 4. 处理委派响应
    if !delegationResponse.Accepted {
        logger.Info("委派被拒绝", "reason", delegationResponse.Reason)
        return fmt.Errorf("委派被拒绝: %s", delegationResponse.Reason)
    }
    
    // 5. 如果委派成功但需要等待结果
    if step.WaitForResult {
        logger.Info("等待委派结果", "delegationID", delegationRequest.DelegationID)
        
        // 设置结果等待
        resultChan := workflow.GetSignalChannel(ctx, fmt.Sprintf("delegation_result_%s", delegationRequest.DelegationID))
        
        // 设置超时
        timeout := 60 * time.Second
        if step.ResponseTimeout > 0 {
            timeout = step.ResponseTimeout
        }
        timer := workflow.NewTimer(ctx, workflow.Now(ctx).Add(timeout))
        
        // 等待结果或超时
        selector := workflow.NewSelector(ctx)
        
        var delegationResult ControlDelegationResult
        var resultReceived bool
        
        selector.AddReceive(resultChan, func(c workflow.ReceiveChannel, more bool) {
            c.Receive(ctx, &delegationResult)
            resultReceived = true
        })
        
        selector.AddFuture(timer.Future, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            // 超时
        })
        
        selector.Select(ctx)
        
        if !resultReceived {
            return fmt.Errorf("等待委派结果超时")
        }
        
        logger.Info("收到委派结果", "status", delegationResult.Status)
        
        if delegationResult.Status != "success" {
            return fmt.Errorf("委派执行失败: %s", delegationResult.Error)
        }
    }
    
    return nil
}

// 执行确认步骤
func executeConfirmationStep(ctx workflow.Context, step CoordinationStep, 
    request ControlRequest, hierarchy ControlFlowHierarchy) error {
    
    logger := workflow.GetLogger(ctx)
    
    // 1. 找到确认层
    confirmationLayer := findLayerByID(hierarchy, step.TargetLayerID)
    if confirmationLayer == nil {
        return fmt.Errorf("未找到确认控制层: %s", step.TargetLayerID)
    }
    
    // 2. 准备确认请求
    confirmationRequest := ControlConfirmationRequest{
        RequestID: request.ID,
        ConfirmationID: step.ID,
        FromLayerID: step.LayerID,
        ToLayerID: step.TargetLayerID,
        DecisionSummary: step.Parameters["decision_summary"].(string),
        JustificationData: step.Parameters["justification"].(map[string]interface{}),
        Timestamp: workflow.Now(ctx),
    }
    
    // 3. 发送确认请求
    var confirmationResponse ControlConfirmationResponse
    var err error
    
    switch confirmationLayer.Location {
    case "cloud":
        // 向云端请求确认
        err = workflow.ExecuteActivity(ctx, activities.RequestCloudConfirmation, 
            confirmationRequest).Get(ctx, &confirmationResponse)
            
    case "edge":
        // 向边缘请求确认
        err = workflow.ExecuteActivity(ctx, activities.RequestEdgeConfirmation, 
            confirmationRequest).Get(ctx, &confirmationResponse)
            
    case "device":
        // 向设备请求确认
        err = workflow.ExecuteActivity(ctx, activities.RequestDeviceConfirmation, 
            confirmationRequest).Get(ctx, &confirmationResponse)
    }
    
    if err != nil {
        return fmt.Errorf("请求确认失败: %w", err)
    }
    
    // 4. 处理确认响应
    logger.Info("收到确认响应", "confirmed", confirmationResponse.Confirmed)
    
    if !confirmationResponse.Confirmed {
        return fmt.Errorf("决策未获确认: %s", confirmationResponse.Reason)
    }
    
    return nil
}
```

## 六、容错与一致性融合模型

### 1. 多层容错机制

```go
// 多层容错管理器
type MultiLevelFaultManager struct {
    // 容错策略
    Strategies map[string]FaultToleranceStrategy
    
    // 错误分类器
    ErrorClassifier ErrorClassifier
    
    // 恢复策略选择器
    RecoverySelector RecoveryStrategySelector
    
    // 层间协调器
    CoordinationManager CoordinationManager
}

// 故障恢复执行工作流
func FaultRecoveryWorkflow(ctx workflow.Context, params FaultRecoveryParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动故障恢复工作流", "faultID", params.FaultID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取故障详情
    var faultDetails FaultDetails
    err := workflow.ExecuteActivity(ctx, activities.GetFaultDetails, 
        params.FaultID).Get(ctx, &faultDetails)
    if err != nil {
        return fmt.Errorf("获取故障详情失败: %w", err)
    }
    
    // 2. 错误分类
    var faultClassification FaultClassification
    err = workflow.ExecuteActivity(ctx, activities.ClassifyFault, 
        faultDetails).Get(ctx, &faultClassification)
    if err != nil {
        return fmt.Errorf("故障分类失败: %w", err)
    }
    
    logger.Info("故障分类结果", "type", faultClassification.Type, 
        "severity", faultClassification.Severity, "layer", faultClassification.Layer)
    
    // 3. 选择恢复策略
    var recoveryStrategy RecoveryStrategy
    err = workflow.ExecuteActivity(ctx, activities.SelectRecoveryStrategy, 
        SelectStrategyParams{
            Classification: faultClassification,
            FaultDetails: faultDetails,
        }).Get(ctx, &recoveryStrategy)
    
    if err != nil {
        return fmt.Errorf("选择恢复策略失败: %w", err)
    }
    
    logger.Info("选择恢复策略", "strategyID", recoveryStrategy.ID, 
        "approach", recoveryStrategy.Approach)
    
    // 4. 执行恢复步骤
    var recoverySuccess bool = true
    for i, step := range recoveryStrategy.Steps {
        logger.Info("执行恢复步骤", "step", i+1, "type", step.Type)
        
        // 设置步骤超时
        stepCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
            StartToCloseTimeout: step.Timeout,
            RetryPolicy: &temporal.RetryPolicy{
                MaximumAttempts: step.RetryCount,
            },
        })
        
        var stepResult RecoveryStepResult
        var stepErr error
        
        // 根据步骤类型调用不同活动
        switch step.Type {
        case "device_reset":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.ResetDevice, 
                step.Parameters).Get(stepCtx, &stepResult)
                
        case "service_restart":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.RestartService, 
                step.Parameters).Get(stepCtx, &stepResult)
                
        case "connection_repair":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.RepairConnection, 
                step.Parameters).Get(stepCtx, &stepResult)
                
        case "state_rollback":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.RollbackState, 
                step.Parameters).Get(stepCtx, &stepResult)
                
        case "alternative_path":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.ActivateAlternativePath, 
                step.Parameters).Get(stepCtx, &stepResult)
                
        case "user_notification":
            stepErr = workflow.ExecuteActivity(stepCtx, activities.NotifyUser, 
                step.Parameters).Get(stepCtx, &stepResult)
        }
        
        if stepErr != nil {
            logger.Error("恢复步骤失败", "step", i+1, "error", stepErr)
            
            // 如果是必要步骤，标记恢复失败
            if step.Critical {
                recoverySuccess = false
                break
            }
            
            // 非关键步骤，继续执行
            continue
        }
        
        // 检查步骤结果
        if !stepResult.Success {
            logger.Error("恢复步骤不成功", "step", i+1, "reason", stepResult.FailureReason)
            
            if step.Critical {
                recoverySuccess = false
                break
            }
        }
    }
    
    // 5. 根据恢复结果更新系统状态
    if recoverySuccess {
        logger.Info("故障恢复成功")
        
        // 记录恢复成功
        _ = workflow.ExecuteActivity(ctx, activities.RecordRecoverySuccess, 
            RecoveryRecord{
                FaultID: params.FaultID,
                RecoveryStrategy: recoveryStrategy.ID,
                StartTime: workflow.GetInfo(ctx).StartTime,
                EndTime: workflow.Now(ctx),
                OutcomeDetails: "所有必要步骤成功执行",
            }).Get(ctx, nil)
        
        // 恢复相关工作流
        if faultDetails.AffectedWorkflows != nil && len(faultDetails.AffectedWorkflows) > 0 {
            resumeCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
                StartToCloseTimeout: 60 * time.Second,
            })
            
            _ = workflow.ExecuteActivity(resumeCtx, activities.ResumeAffectedWorkflows, 
                ResumeParams{
                    WorkflowIDs: faultDetails.AffectedWorkflows,
                    FaultID: params.FaultID,
                }).Get(resumeCtx, nil)
        }
    } else {
        logger.Error("故障恢复失败")
        
        // 记录恢复失败
        _ = workflow.ExecuteActivity(ctx, activities.RecordRecoveryFailure, 
            RecoveryRecord{
                FaultID: params.FaultID,
                RecoveryStrategy: recoveryStrategy.ID,
                StartTime: workflow.GetInfo(ctx).StartTime,
                EndTime: workflow.Now(ctx),
                OutcomeDetails: "恢复过程中关键步骤失败",
            }).Get(ctx, nil)
        
        // 实施退化策略
        if recoveryStrategy.DegradationPlan != nil {
            degradeCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
                StartToCloseTimeout: 60 * time.Second,
            })
            
            _ = workflow.ExecuteActivity(degradeCtx, activities.ImplementDegradationPlan, 
                DegradationParams{
                    Plan: *recoveryStrategy.DegradationPlan,
                    FaultID: params.FaultID,
                }).Get(degradeCtx, nil)
        }
        
        // 如果需要人工干预，触发通知
        if faultClassification.Severity >= 8 { // 高严重性
            _ = workflow.ExecuteActivity(ctx, activities.TriggerUrgentAlert, 
                AlertParams{
                    FaultID: params.FaultID,
                    Classification: faultClassification,
                    Message: "自动恢复失败，需要人工干预",
                    Priority: "high",
                }).Get(ctx, nil)
        }
    }
    
    // 无论成功失败，都更新故障状态
    _ = workflow.ExecuteActivity(ctx, activities.UpdateFaultStatus, 
        StatusUpdateParams{
            FaultID: params.FaultID,
            NewStatus: recoverySuccess ? "resolved" : "recovery_failed",
            Timestamp: workflow.Now(ctx),
        }).Get(ctx, nil)
    
    return nil
}

// 分层故障检测工作流
func MultiLayerFaultDetectionWorkflow(ctx workflow.Context, params FaultDetectionParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动分层故障检测工作流", "homeID", params.HomeID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 20 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 设置检测间隔
    checkInterval := 5 * time.Minute
    if params.CheckInterval > 0 {
        checkInterval = params.CheckInterval
    }
    
    // 初始化上次检查状态
    var lastCheckState CheckpointState
    err := workflow.ExecuteActivity(ctx, activities.InitializeFaultCheckState, 
        params.HomeID).Get(ctx, &lastCheckState)
    if err != nil {
        logger.Error("初始化检查状态失败", "error", err)
        // 使用空状态继续
        lastCheckState = CheckpointState{
            Timestamp: time.Now().Add(-checkInterval),
        }
    }
    
    // 主检测循环
    for {
        // 1. 设备层故障检测
        var deviceFaults []FaultIndicator
        err := workflow.ExecuteActivity(ctx, activities.DetectDeviceFaults, 
            DeviceFaultParams{
                HomeID: params.HomeID,
                LastCheckTime: lastCheckState.Timestamp,
            }).Get(ctx, &deviceFaults)
        
        if err != nil {
            logger.Error("设备层故障检测失败", "error", err)
        } else if len(deviceFaults) > 0 {
            logger.Info("检测到设备层故障", "count", len(deviceFaults))
            
            // 处理每个设备故障
            for _, fault := range deviceFaults {
                processFaultIndicator(ctx, fault, "device")
            }
        }
        
        // 2. 边缘层故障检测
        var edgeFaults []FaultIndicator
        err = workflow.ExecuteActivity(ctx, activities.DetectEdgeFaults, 
            EdgeFaultParams{
                HomeID: params.HomeID,
                LastCheckTime: lastCheckState.Timestamp,
            }).Get(ctx, &edgeFaults)
        
        if err != nil {
            logger.Error("边缘层故障检测失败", "error", err)
        } else if len(edgeFaults) > 0 {
            logger.Info("检测到边缘层故障", "count", len(edgeFaults))
            
            // 处理每个边缘故障
            for _, fault := range edgeFaults {
                processFaultIndicator(ctx, fault, "edge")
            }
        }
        
        // 3. 云端层故障检测
        var cloudFaults []FaultIndicator
        err = workflow.ExecuteActivity(ctx, activities.DetectCloudFaults, 
            CloudFaultParams{
                HomeID: params.HomeID,
                LastCheckTime: lastCheckState.Timestamp,
            }).Get(ctx, &cloudFaults)
        
        if err != nil {
            logger.Error("云端层故障检测失败", "error", err)
        } else if len(cloudFaults) > 0 {
            logger.Info("检测到云端层故障", "count", len(cloudFaults))
            
            // 处理每个云端故障
            for _, fault := range cloudFaults {
                processFaultIndicator(ctx, fault, "cloud")
            }
        }
        
        // 4. 跨层关联分析 - 识别相关故障
        if len(deviceFaults) > 0 || len(edgeFaults) > 0 || len(cloudFaults) > 0 {
            var combinedFaults []FaultIndicator
            combinedFaults = append(combinedFaults, deviceFaults...)
            combinedFaults = append(combinedFaults, edgeFaults...)
            combinedFaults = append(combinedFaults, cloudFaults...)
            
            var correlationResults []FaultCorrelation
            _ = workflow.ExecuteActivity(ctx, activities.CorrelateMultiLayerFaults, 
                combinedFaults).Get(ctx, &correlationResults)
            
            // 处理相关故障组
            for _, correlation := range correlationResults {
                processCorrelatedFaults(ctx, correlation)
            }
        }
        
        // 5. 更新检查点状态
        newCheckState := CheckpointState{
            Timestamp: workflow.Now(ctx),
            DeviceFaultCount: len(deviceFaults),
            EdgeFaultCount: len(edgeFaults),
            CloudFaultCount: len(cloudFaults),
        }
        
        _ = workflow.ExecuteActivity(ctx, activities.UpdateFaultCheckState, 
            UpdateCheckStateParams{
                HomeID: params.HomeID,
                NewState: newCheckState,
            }).Get(ctx, nil)
        
        lastCheckState = newCheckState
        
        // 等待下次检查
        _ = workflow.Sleep(ctx, checkInterval)
    }
    
    return nil
}

// 处理单个故障指示器
func processFaultIndicator(ctx workflow.Context, fault FaultIndicator, layer string) {
    logger := workflow.GetLogger(ctx)
    logger.Info("处理故障指示器", "faultType", fault.Type, "layer", layer)
    
    // 1. 验证故障
    var validationResult FaultValidationResult
    err := workflow.ExecuteActivity(ctx, activities.ValidateFaultIndicator, 
        ValidationParams{
            Fault: fault,
            Layer: layer,
        }).Get(ctx, &validationResult)
    
    if err != nil {
        logger.Error("故障验证失败", "error", err)
        return
    }
    
    if !validationResult.IsValid {
        logger.Info("故障指示器无效", "reason", validationResult.Reason)
        return
    }
    
    // 2. 注册验证的故障
    var faultID string
    err = workflow.ExecuteActivity(ctx, activities.RegisterFault, 
        RegisterFaultParams{
            Fault: fault,
            Layer: layer,
            ValidationResult: validationResult,
        }).Get(ctx, &faultID)
    
    if err != nil {
        logger.Error("注册故障失败", "error", err)
        return
    }
    
    // 3. 根据故障类型和严重性决定处理方式
    if fault.Severity >= 7 { // 高严重性
        // 启动子工作流处理严重故障
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("fault-recovery-%s", faultID),
        }
        childCtx := workflow.WithChildOptions(ctx, cwo)
        
        _ = workflow.ExecuteChildWorkflow(childCtx, FaultRecoveryWorkflow, 
            FaultRecoveryParams{
                FaultID: faultID,
            })
    } else if fault.Severity >= 4 { // 中等严重性
        // 安排异步恢复
        _ = workflow.ExecuteActivity(ctx, activities.ScheduleFaultRecovery, 
            ScheduleRecoveryParams{
                FaultID: faultID,
                ScheduleDelay: 5 * time.Minute,
            }).Get(ctx, nil)
    } else { // 低严重性
        // 记录不需要立即处理的低严重性故障
        _ = workflow.ExecuteActivity(ctx, activities.LogMinorFault, 
            faultID).Get(ctx, nil)
    }
}

// 处理关联故障
func processCorrelatedFaults(ctx workflow.Context, correlation FaultCorrelation) {
    logger := workflow.GetLogger(ctx)
    logger.Info("处理关联故障", "rootCause", correlation.RootCauseID, 
        "relatedFaults", len(correlation.RelatedFaultIDs))
    
    // 1. 创建关联故障组
    var correlationGroupID string
    err := workflow.ExecuteActivity(ctx, activities.CreateFaultCorrelationGroup, 
        correlation).Get(ctx, &correlationGroupID)
    
    if err != nil {
        logger.Error("创建故障关联组失败", "error", err)
        return
    }
    
    // 2. 分析恢复依赖关系
    var recoveryPlan RecoveryPlan
    err = workflow.ExecuteActivity(ctx, activities.CreateCorrelatedRecoveryPlan, 
        correlationGroupID).Get(ctx, &recoveryPlan)
    
    if err != nil {
        logger.Error("创建恢复计划失败", "error", err)
        return
    }
    
    // 3. 执行协调恢复
    cwo := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("correlated-recovery-%s", correlationGroupID),
    }
    childCtx := workflow.WithChildOptions(ctx, cwo)
    
    _ = workflow.ExecuteChildWorkflow(childCtx, CoordinatedRecoveryWorkflow, 
        CoordinatedRecoveryParams{
            CorrelationGroupID: correlationGroupID,
            RecoveryPlan: recoveryPlan,
        })
}
```

### 2. 一致性保障协议

```go
// 一致性保障工作流
func ConsistencyProtocolWorkflow(ctx workflow.Context, params ConsistencyParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动一致性保障工作流", "operationType", params.OperationType)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 5, // 一致性活动需要更多重试次数
            InitialInterval: 1 * time.Second,
            MaximumInterval: 10 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 根据操作类型选择一致性协议
    var protocol ConsistencyProtocol
    err := workflow.ExecuteActivity(ctx, activities.SelectConsistencyProtocol, 
        params).Get(ctx, &protocol)
    
    if err != nil {
        return fmt.Errorf("选择一致性协议失败: %w", err)
    }
    
    logger.Info("选择一致性协议", "protocol", protocol.Type)
    
    // 2. 根据协议类型执行不同的一致性流程
    switch protocol.Type {
    case "two_phase_commit":
        return executeTwoPhaseCommit(ctx, params, protocol)
        
    case "three_phase_commit":
        return executeThreePhaseCommit(ctx, params, protocol)
        
    case "saga":
        return executeSagaProtocol(ctx, params, protocol)
        
    case "eventual_consistency":
        return executeEventualConsistency(ctx, params, protocol)
        
    case "leased_consistency":
        return executeLeasedConsistency(ctx, params, protocol)
        
    default:
        return fmt.Errorf("不支持的一致性协议类型: %s", protocol.Type)
    }
}

// 执行两阶段提交协议
func executeTwoPhaseCommit(ctx workflow.Context, params ConsistencyParams, 
    protocol ConsistencyProtocol) error {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("开始执行两阶段提交协议")
    
    // 1. 准备阶段参与者列表
    var participants []string
    if participantsParam, ok := protocol.Parameters["participants"].([]string); ok {
        participants = participantsParam
    } else {
        // 如果未指定，根据影响范围自动确定参与者
        err := workflow.ExecuteActivity(ctx, activities.DetermineParticipants, 
            DetermineParams{
                OperationType: params.OperationType,
                TargetIDs: params.TargetIDs,
                OperationScope: params.OperationScope,
            }).Get(ctx, &participants)
        
        if err != nil {
            return fmt.Errorf("确定参与者失败: %w", err)
        }
    }
    
    logger.Info("确定参与者", "count", len(participants))
    
    // 2. 创建事务上下文
    var txContext TransactionContext
    err := workflow.ExecuteActivity(ctx, activities.CreateTransactionContext, 
        CreateTxParams{
            TransactionID: uuid.New().String(),
            OperationType: params.OperationType,
            Participants: participants,
            OperationParams: params.OperationParams,
        }).Get(ctx, &txContext)
    
    if err != nil {
        return fmt.Errorf("创建事务上下文失败: %w", err)
    }
    
    // 3. 阶段一：准备阶段 - 询问所有参与者是否可以执行事务
    prepareRequest := PrepareRequest{
        TransactionID: txContext.TransactionID,
        OperationType: params.OperationType,
        OperationParams: params.OperationParams,
    }
    
    // 并行发送准备请求给所有参与者
    prepareResponses := make(map[string]PrepareResponse)
    prepareResults := make(map[string]error)
    
    futures := make(map[string]workflow.Future)
    for _, participant := range participants {
        // 为每个参与者创建准备请求
        participantRequest := prepareRequest
        participantRequest.ParticipantID = participant
        
        futures[participant] = workflow.ExecuteActivity(ctx, activities.SendPrepareRequest, 
            SendPrepareParams{
                Participant: participant,
                Request: participantRequest,
            })
    }
    
    // 收集所有准备响应
    allPrepared := true
    for participant, future := range futures {
        var response PrepareResponse
        err := future.Get(ctx, &response)
        
        prepareResults[participant] = err
        if err != nil {
            logger.Error("参与者准备请求失败", "participant", participant, "error", err)
            allPrepared = false
        } else {
            prepareResponses[participant] = response
            if !response.Prepared {
                logger.Info("参与者拒绝准备", "participant", participant, "reason", response.Reason)
                allPrepared = false
            }
        }
    }
    
    // 4. 阶段二：提交或中止阶段
    if allPrepared {
        logger.Info("所有参与者已准备，开始提交阶段")
        
        // 4.1 发送提交请求
        commitRequest := CommitRequest{
            TransactionID: txContext.TransactionID,
        }
        
        commitFutures := make(map[string]workflow.Future)
        for _, participant := range participants {
            participantCommitRequest := commitRequest
            participantCommitRequest.ParticipantID = participant
            
            commitFutures[participant] = workflow.ExecuteActivity(ctx, activities.SendCommitRequest, 
                SendCommitParams{
                    Participant: participant,
                    Request: participantCommitRequest,
                })
        }
        
        // 4.2 收集提交结果
        commitResults := make(map[string]CommitResponse)
        commitErrors := make(map[string]error)
        
        for participant, future := range commitFutures {
            var response CommitResponse
            err := future.Get(ctx, &response)
            
            if err != nil {
                logger.Error("参与者提交请求失败", "participant", participant, "error", err)
                commitErrors[participant] = err
            } else {
                commitResults[participant] = response
                if !response.Committed {
                    logger.Error("参与者提交失败", "participant", participant, "reason", response.Reason)
                }
            }
        }
        
        // 4.3 处理部分提交的情况
        if len(commitErrors) > 0 {
            logger.Error("部分参与者提交失败", "errorCount", len(commitErrors))
            
            // 记录不一致状态
            _ = workflow.ExecuteActivity(ctx, activities.RecordInconsistentState, 
                InconsistencyRecord{
                    TransactionID: txContext.TransactionID,
                    InconsistentParticipants: getKeysFromMap(commitErrors),
                    Timestamp: workflow.Now(ctx),
                    Operation: params.OperationType,
                }).Get(ctx, nil)
            
            // 启动恢复工作流处理不一致
            cwo := workflow.ChildWorkflowOptions{
                WorkflowID: fmt.Sprintf("consistency-recovery-%s", txContext.TransactionID),
            }
            childCtx := workflow.WithChildOptions(ctx, cwo)
            
            _ = workflow.ExecuteChildWorkflow(childCtx, ConsistencyRecoveryWorkflow, 
                ConsistencyRecoveryParams{
                    TransactionID: txContext.TransactionID,
                    InconsistentParticipants: getKeysFromMap(commitErrors),
                    ConsistentParticipants: getKeysFromCommitResults(commitResults),
                    OperationType: params.OperationType,
                })
            
            return fmt.Errorf("两阶段提交部分失败")
        }
        
        // 提交成功
        logger.Info("两阶段提交成功完成", "transactionID", txContext.TransactionID)
        
        _ = workflow.ExecuteActivity(ctx, activities.RecordTransactionSuccess, 
            txContext.TransactionID).Get(ctx, nil)
        
        return nil
    } else {
        logger.Info("有参与者准备失败，开始中止事务")
        
        // 向所有已成功准备的参与者发送中止请求
        abortRequest := AbortRequest{
            TransactionID: txContext.TransactionID,
        }
        
        for participant, response := range prepareResponses {
            if response.Prepared {
                participantAbortRequest := abortRequest
                participantAbortRequest.ParticipantID = participant
                
                _ = workflow.ExecuteActivity(ctx, activities.SendAbortRequest, 
                    SendAbortParams{
                        Participant: participant,
                        Request: participantAbortRequest,
                    }).Get(ctx, nil)
            }
        }
        
        // 记录事务中止
        _ = workflow.ExecuteActivity(ctx, activities.RecordTransactionAbort, 
            RecordAbortParams{
                TransactionID: txContext.TransactionID,
                Reason: "参与者准备阶段失败",
                PrepareResults: prepareResults,
            }).Get(ctx, nil)
        
        return fmt.Errorf("两阶段提交中止：参与者准备阶段失败")
    }
}

// 执行 Saga 协议
func executeSagaProtocol(ctx workflow.Context, params ConsistencyParams, 
    protocol ConsistencyProtocol) error {
    
    logger := workflow.GetLogger(ctx)
    logger.Info("开始执行 Saga 协议")
    
    // 1. 解析操作序列和补偿操作
    var operationSequence []SagaOperation
    err := workflow.ExecuteActivity(ctx, activities.DecomposeSagaOperations, 
        DecomposeParams{
            OperationType: params.OperationType,
            OperationParams: params.OperationParams,
        }).Get(ctx, &operationSequence)
    
    if err != nil {
        return fmt.Errorf("分解 Saga 操作失败: %w", err)
    }
    
    logger.Info("分解 Saga 操作", "operationCount", len(operationSequence))
    
    // 2. 创建 Saga 上下文
    var sagaContext SagaContext
    err = workflow.ExecuteActivity(ctx, activities.CreateSagaContext, 
        CreateSagaParams{
            SagaID: uuid.New().String(),
            OperationType: params.OperationType,
            Operations: operationSequence,
        }).Get(ctx, &sagaContext)
    
    if err != nil {
        return fmt.Errorf("创建 Saga 上下文失败: %w", err)
    }
    
    // 3. 按顺序执行操作，记录已执行操作以便补偿
    var executedOperations []SagaOperation
    var sagaResult SagaResult
    
    for i, operation := range operationSequence {
        logger.Info("执行 Saga 操作", "step", i+1, "operation", operation.Name)
        
        // 执行操作
        var opResult OperationResult
        err := workflow.ExecuteActivity(ctx, activities.ExecuteSagaOperation, 
            ExecuteOpParams{
                SagaID: sagaContext.SagaID,
                Operation: operation,
                StepIndex: i,
            }).Get(ctx, &opResult)
        
        if err != nil {
            logger.Error("Saga 操作执行失败", "operation", operation.Name, "error", err)
            sagaResult = SagaResult{
                Success: false,
                FailedOperation: operation.Name,
                FailedAtStep: i,
                ErrorMessage: err.Error(),
            }
            break
        }
        
        if !opResult.Success {
            logger.Error("Saga 操作不成功", "operation", operation.Name, "reason", opResult.Reason)
            sagaResult = SagaResult{
                Success: false,
                FailedOperation: operation.Name,
                FailedAtStep: i,
                ErrorMessage: opResult.Reason,
            }
            break
        }
        
        // 记录成功执行的操作
        executedOperations = append(executedOperations, operation)
        
        // 更新 Saga 进度
        _ = workflow.ExecuteActivity(ctx, activities.UpdateSagaProgress, 
            UpdateProgressParams{
                SagaID: sagaContext.SagaID,
                CompletedSteps: i + 1,
                LastCompletedOperation: operation.Name,
            }).Get(ctx, nil)
    }
    
    // 4. 处理执行结果
    if len(executedOperations) == len(operationSequence) {
        // 所有操作成功执行
        logger.Info("Saga 协议成功完成", "sagaID", sagaContext.SagaID)
        
        sagaResult = SagaResult{
            Success: true,
            CompletedOperations: len(operationSequence),
        }
        
        _ = workflow.ExecuteActivity(ctx, activities.RecordSagaSuccess, 
            sagaContext.SagaID).Get(ctx, nil)
        
        return nil
    } else {
        // 有操作失败，需要执行补偿操作
        logger.Info("开始执行 Saga 补偿操作", "executedCount", len(executedOperations))
        
        // 逆序执行补偿操作
        for i := len(executedOperations) - 1; i >= 0; i-- {
            operation := executedOperations[i]
            
            if operation.HasCompensation {
                logger.Info("执行补偿操作", "forOperation", operation.Name)
                
                // 执行补偿操作
                err := workflow.ExecuteActivity(ctx, activities.ExecuteSagaCompensation, 
                    CompensationParams{
                        SagaID: sagaContext.SagaID,
                        Operation: operation,
                        StepIndex: i,
                    }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("补偿操作失败", "operation", operation.Name, "error", err)
                    
                    // 记录补偿错误但继续尝试其他补偿
                    _ = workflow.ExecuteActivity(ctx, activities.RecordCompensationError, 
                        RecordCompErrorParams{
                            SagaID: sagaContext.SagaID,
                            Operation: operation.Name,
                            Error: err.Error(),
                        }).Get(ctx, nil)
                }
            }
        }
        
        // 记录 Saga 完成（带补偿）
        _ = workflow.ExecuteActivity(ctx, activities.RecordSagaWithCompensation, 
            RecordSagaCompParams{
                SagaID: sagaContext.SagaID,
                Result: sagaResult,
            }).Get(ctx, nil)
        
        return fmt.Errorf("Saga 协议需要补偿: %s", sagaResult.ErrorMessage)
    }
}

// 辅助函数：从map中获取键列表
func getKeysFromMap(m map[string]error) []string {
    keys := make([]string, 0, len(m))
    for k := range m {
        keys = append(keys, k)
    }
    return keys
}

// 辅助函数：从CommitResponse map中获取键列表
func getKeysFromCommitResults(m map[string]CommitResponse) []string {
    keys := make([]string, 0, len(m))
    for k, v := range m {
        if v.Committed {
            keys = append(keys, k)
        }
    }
    return keys
}
```

## 七、自动化工作流设计与优化

### 1. 工作流自动生成器

```go
// 工作流自动生成工作流
func WorkflowGeneratorWorkflow(ctx workflow.Context, params GeneratorParams) (GeneratedWorkflowResult, error) {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动工作流自动生成工作流", "targetType", params.TargetType)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 60 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 分析输入规格，确定工作流复杂度和结构
    var specAnalysis SpecAnalysisResult
    err := workflow.ExecuteActivity(ctx, activities.AnalyzeWorkflowSpec, 
        params.Specification).Get(ctx, &specAnalysis)
    
    if err != nil {
        return GeneratedWorkflowResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("分析工作流规格失败: %v", err),
        }, nil
    }
    
    logger.Info("规格分析结果", "complexity", specAnalysis.Complexity, 
        "estimatedComponents", specAnalysis.EstimatedComponents)
    
    // 2. 获取合适的工作流模板
    var workflowTemplate WorkflowTemplate
    err = workflow.ExecuteActivity(ctx, activities.SelectWorkflowTemplate, 
        SelectTemplateParams{
            TargetType: params.TargetType,
            Complexity: specAnalysis.Complexity,
            FeaturesRequired: specAnalysis.RequiredFeatures,
        }).Get(ctx, &workflowTemplate)
    
    if err != nil {
        return GeneratedWorkflowResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("选择工作流模板失败: %v", err),
        }, nil
    }
    
    // 3. 根据规格参数化模板
    var parameterizedTemplate ParameterizedTemplate
    err = workflow.ExecuteActivity(ctx, activities.ParameterizeTemplate, 
        ParameterizeParams{
            Template: workflowTemplate,
            Specification: params.Specification,
            AnalysisResult: specAnalysis,
        }).Get(ctx, &parameterizedTemplate)
    
    if err != nil {
        return GeneratedWorkflowResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("参数化模板失败: %v", err),
        }, nil
    }
    
    // 4. 根据设备和系统限制优化工作流
    var optimizedTemplate OptimizedTemplate
    err = workflow.ExecuteActivity(ctx, activities.OptimizeTemplate, 
        OptimizeParams{
            Template: parameterizedTemplate,
            DeviceConstraints: params.DeviceConstraints,
            SystemLimits: params.SystemLimits,
            OptimizationGoals: params.OptimizationGoals,
        }).Get(ctx, &optimizedTemplate)
    
    if err != nil {
        logger.Warn("优化模板失败，使用未优化版本", "error", err)
        optimizedTemplate = OptimizedTemplate{
            Template: parameterizedTemplate.Template,
            IsOptimized: false,
        }
    }
    
    // 5. 生成具体实现代码
    var generatedCode GeneratedCode
    err = workflow.ExecuteActivity(ctx, activities.GenerateWorkflowCode, 
        CodeGenParams{
            Template: optimizedTemplate,
            TargetType: params.TargetType,
            TargetLanguage: params.TargetLanguage,
            IncludeComments: params.IncludeComments,
        }).Get(ctx, &generatedCode)
    
    if err != nil {
        return GeneratedWorkflowResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("生成工作流代码失败: %v", err),
        }, nil
    }
    
    // 6. 验证生成的代码
    var validationResult CodeValidationResult
    err = workflow.ExecuteActivity(ctx, activities.ValidateGeneratedCode, 
        ValidationParams{
            GeneratedCode: generatedCode,
            Specification: params.Specification,
            ValidationType: params.ValidationType,
        }).Get(ctx, &validationResult)
    
    if err != nil || !validationResult.IsValid {
        var errorMsg string
        if err != nil {
            errorMsg = fmt.Sprintf("代码验证过程失败: %v", err)
        } else {
            errorMsg = fmt.Sprintf("代码验证不通过: %s", validationResult.FailureReason)
        }
        
        return GeneratedWorkflowResult{
            Success: false,
            ErrorMessage: errorMsg,
            GeneratedCode: generatedCode,
            ValidationIssues: validationResult.Issues,
        }, nil
    }
    
    // 7. 生成单元测试代码
    var testCode GeneratedTestCode
    err = workflow.ExecuteActivity(ctx, activities.GenerateWorkflowTests, 
        TestGenParams{
            WorkflowCode: generatedCode,
            Specification: params.Specification,
            TestCoverage: params.TestCoverage,
        }).Get(ctx, &testCode)
    
    if err != nil {
        logger.Warn("生成测试代码失败", "error", err)
        // 测试生成失败不阻止返回主工作流代码
    }
    
    // 8. 生成部署配置
    var deploymentConfig DeploymentConfig
    err = workflow.ExecuteActivity(ctx, activities.GenerateDeploymentConfig, 
        DeployConfigParams{
            WorkflowType: params.TargetType,
            RuntimeEnvironment: params.TargetEnvironment,
            Specification: params.Specification,
        }).Get(ctx, &deploymentConfig)
    
    if err != nil {
        logger.Warn("生成部署配置失败", "error", err)
        // 部署配置生成失败不阻止返回主工作流代码
    }
    
    // 9. 编译结果
    result := GeneratedWorkflowResult{
        Success: true,
        GeneratedCode: generatedCode,
        TestCode: testCode,
        DeploymentConfig: deploymentConfig,
        OptimizationApplied: optimizedTemplate.IsOptimized,
        GenerationMetrics: GenerationMetrics{
            Complexity: specAnalysis.Complexity,
            ComponentCount: specAnalysis.EstimatedComponents,
            GenerationTime: time.Since(workflow.GetInfo(ctx).StartTime),
        },
    }
    
    // 记录生成结果
    _ = workflow.ExecuteActivity(ctx, activities.RecordWorkflowGeneration, 
        GenRecordParams{
            SpecificationID: params.SpecificationID,
            Result: result,
        }).Get(ctx, nil)
    
    return result, nil
}
```

### 2. 工作流自动优化器

```go
// 工作流优化工作流
func WorkflowOptimizerWorkflow(ctx workflow.Context, params OptimizerParams) (OptimizationResult, error) {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动工作流优化工作流", "workflowID", params.WorkflowID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 60 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取工作流定义
    var workflowDef WorkflowDefinition
    err := workflow.ExecuteActivity(ctx, activities.GetWorkflowDefinition, 
        params.WorkflowID).Get(ctx, &workflowDef)
    
    if err != nil {
        return OptimizationResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("获取工作流定义失败: %v", err),
        }, nil
    }
    
    // 2. 分析工作流性能和特性
    var workflowAnalysis WorkflowAnalysis
    err = workflow.ExecuteActivity(ctx, activities.AnalyzeWorkflow, 
        AnalyzeParams{
            WorkflowDef: workflowDef,
            AnalysisType: params.AnalysisType,
        }).Get(ctx, &workflowAnalysis)
    
    if err != nil {
        return OptimizationResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("分析工作流失败: %v", err),
        }, nil
    }
    
    logger.Info("工作流分析结果", "currentLatency", workflowAnalysis.EstimatedLatency,
        "resourceUsage", workflowAnalysis.ResourceUsage,
        "bottlenecks", len(workflowAnalysis.Bottlenecks))
    
    // 3. 识别优化机会
    var optimizationOpportunities []OptimizationOpportunity
    err = workflow.ExecuteActivity(ctx, activities.IdentifyOptimizationOpportunities, 
        IdentifyOpParams{
            Analysis: workflowAnalysis,
            Goals: params.OptimizationGoals,
            Constraints: params.OptimizationConstraints,
        }).Get(ctx, &optimizationOpportunities)
    
    if err != nil {
        return OptimizationResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("识别优化机会失败: %v", err),
        }, nil
    }
    
    // 如果没有找到优化机会，直接返回
    if len(optimizationOpportunities) == 0 {
        return OptimizationResult{
            Success: true,
            IsOptimized: false,
            Message: "未发现优化机会",
            OriginalWorkflow: workflowDef,
        }, nil
    }
    
    logger.Info("识别到优化机会", "count", len(optimizationOpportunities))
    
    // 4. 针对每个优化机会生成优化建议
    var optimizationStrategies []OptimizationStrategy
    for _, opportunity := range optimizationOpportunities {
        var strategies []OptimizationStrategy
        err := workflow.ExecuteActivity(ctx, activities.GenerateOptimizationStrategies, 
            GenStrategyParams{
                Opportunity: opportunity,
                WorkflowDef: workflowDef,
                Analysis: workflowAnalysis,
            }).Get(ctx, &strategies)
        
        if err != nil {
            logger.Error("为优化机会生成策略失败", "opportunity", opportunity.Type, "error", err)
            continue
        }
        
        optimizationStrategies = append(optimizationStrategies, strategies...)
    }
    
    // 5. 评估和排序优化策略
    var rankedStrategies []RankedStrategy
    err = workflow.ExecuteActivity(ctx, activities.RankOptimizationStrategies, 
        RankParams{
            Strategies: optimizationStrategies,
            Goals: params.OptimizationGoals,
            Analysis: workflowAnalysis,
        }).Get(ctx, &rankedStrategies)
    
    if err != nil {
        return OptimizationResult{
            Success: false,
            ErrorMessage: fmt.Sprintf("评估优化策略失败: %v", err),
        }, nil
    }
    
    // 6. 应用优化策略，获得优化后的工作流定义
    var optimizedWorkflow WorkflowDefinition
    var appliedStrategies []AppliedStrategy
    
    // 使用当前的工作流作为基础
    currentWorkflow := workflowDef
    
    // 应用排序后的策略
    for i, rankedStrategy := range rankedStrategies {
        // 如果达到最大优化策略数，停止应用
        if len(appliedStrategies) >= params.MaxOptimizations {
            break
        }
        
        logger.Info("应用优化策略", "strategy", rankedStrategy.Strategy.Name, 
            "rank", i+1, "estimatedImprovement", rankedStrategy.EstimatedImprovement)
        
        var optimizationResult OptimizationApplyResult
        err := workflow.ExecuteActivity(ctx, activities.ApplyOptimizationStrategy, 
            ApplyParams{
                Workflow: currentWorkflow,
                Strategy: rankedStrategy.Strategy,
            }).Get(ctx, &optimizationResult)
        
        if err != nil {
            logger.Error("应用优化策略失败", "strategy", rankedStrategy.Strategy.Name, "error", err)
            continue
        }
        
        if !optimizationResult.Success {
            logger.Error("优化策略应用不成功", "strategy", rankedStrategy.Strategy.Name, 
                "reason", optimizationResult.FailureReason)
            continue
        }
        
        // 更新当前工作流为优化后的版本
        currentWorkflow = optimizationResult.OptimizedWorkflow
        
        // 记录应用的策略
        appliedStrategies = append(appliedStrategies, AppliedStrategy{
            Strategy: rankedStrategy.Strategy,
            ImprovementMetrics: optimizationResult.ImprovementMetrics,
        })
    }
    
    // 如果没有成功应用任何策略，返回原始工作流
    if len(appliedStrategies) == 0 {
        return OptimizationResult{
            Success: true,
            IsOptimized: false,
            Message: "没有成功应用任何优化策略",
            OriginalWorkflow: workflowDef,
        }, nil
    }
    
    optimizedWorkflow = currentWorkflow
    
    // 7. 验证优化后的工作流
    var validationResult OptimizationValidationResult
    err = workflow.ExecuteActivity(ctx, activities.ValidateOptimizedWorkflow, 
        ValidateOptParams{
            OriginalWorkflow: workflowDef,
            OptimizedWorkflow: optimizedWorkflow,
            ValidationCriteria: params.ValidationCriteria,
        }).Get(ctx, &validationResult)
    
    if err != nil || !validationResult.IsValid {
        var errorMsg string
        if err != nil {
            errorMsg = fmt.Sprintf("验证优化工作流失败: %v", err)
        } else {
            errorMsg = fmt.Sprintf("优化工作流验证不通过: %s", validationResult.FailureReason)
        }
        
        return OptimizationResult{
            Success: false,
            ErrorMessage: errorMsg,
            OriginalWorkflow: workflowDef,
            AppliedStrategies: appliedStrategies,
        }, nil
    }
    
    // 8. 预估优化效果
    var estimatedImpact OptimizationImpact
    err = workflow.ExecuteActivity(ctx, activities.EstimateOptimizationImpact, 
        EstimateImpactParams{
            OriginalWorkflow: workflowDef,
            OptimizedWorkflow: optimizedWorkflow,
            OriginalAnalysis: workflowAnalysis,
            AppliedStrategies: appliedStrategies,
        }).Get(ctx, &estimatedImpact)
    
    if err != nil {
        logger.Error("估算优化影响失败", "error", err)
        // 继续，使用有限的影响信息
    }
    
    // 9. 保存优化后的工作流
    if params.AutoSave {
        var saveResult SaveOptimizedResult
        err = workflow.ExecuteActivity(ctx, activities.SaveOptimizedWorkflow, 
            SaveOptParams{
                OriginalID: params.WorkflowID,
                OptimizedWorkflow: optimizedWorkflow,
                ImpactSummary: estimatedImpact,
                AppliedStrategies: appliedStrategies,
            }).Get(ctx, &saveResult)
        
        if err != nil {
            logger.Error("保存优化工作流失败", "error", err)
            // 继续，用户仍可以查看优化建议
        }
    }
    
    // 10. 组装结果
    result := OptimizationResult{
        Success: true,
        IsOptimized: true,
        OriginalWorkflow: workflowDef,
        OptimizedWorkflow: optimizedWorkflow,
        AppliedStrategies: appliedStrategies,
        EstimatedImpact: estimatedImpact,
        ValidationResults: validationResult,
    }
    
    if params.AutoSave && len(result.OptimizedWorkflowID) > 0 {
        result.Message = fmt.Sprintf("成功优化并保存工作流，新ID: %s", result.OptimizedWorkflowID)
    } else {
        result.Message = "成功优化工作流，但未自动保存"
    }
    
    // 记录优化结果
    _ = workflow.ExecuteActivity(ctx, activities.RecordWorkflowOptimization, 
        OptRecordParams{
            WorkflowID: params.WorkflowID,
            Result: result,
        }).Get(ctx, nil)
    
    return result, nil
}
```

## 八、实现权衡与最佳实践总结

### 1. 端-边缘-云工作流设计决策指南

#### 执行位置决策框架

```text
1. 设备端执行优先（适用条件）:
   - 需要最低延迟响应（< 100ms）
   - 对网络连接依赖低
   - 操作范围仅限单设备
   - 安全关键操作
   - 有足够设备算力和电量

2. 边缘节点执行优先（适用条件）:
   - 需要低延迟响应（100-500ms）
   - 需要协调多个设备但位于同一区域
   - 对网络连接可靠性有中等要求
   - 数据不需要离开本地网络
   - 设备资源受限但操作复杂度适中

3. 云端执行优先（适用条件）:
   - 延迟要求不高（> 500ms）
   - 需要全局数据访问或AI处理
   - 跨多个区域/家庭的协调
   - 计算密集型操作
   - 需要长期历史数据分析
```

#### 分层工作流设计模式

```text
1. 三层工作流协作模式:
   - 端层: 原子操作执行、本地安全保障、快速响应
   - 边缘层: 区域协调、本地缓存、家庭级别场景编排
   - 云层: 全局决策、AI分析、跨家庭优化、用户偏好学习

2. 边缘自治模式:
   - 云端制定高级策略和规则
   - 边缘节点自主执行和调整
   - 设备直接响应本地条件
   - 定期与云同步但不依赖实时连接

3. 自适应执行位置模式:
   - 基于网络条件、设备资源和操作特性动态调整执行位置
   - 实现工作流迁移能力
   - 维护执行状态的可序列化表示
   - 定义清晰的决策点和迁移触发器
```

### 2. 数据流与一致性权衡指南

#### 数据同步模式选择

```text
1. 实时同步模式 (适用场景):
   - 安全关键更新
   - 跨设备协调要求
   - 用户直接交互响应
   - 网络条件良好
   
   权衡: 较高网络负载，电池消耗增加

2. 批量同步模式 (适用场景):
   - 非关键数据积累
   - 数据统计和分析
   - 电池供电设备
   - 间歇性网络连接
   
   权衡: 数据新鲜度降低，可能需要更复杂的冲突解决

3. 优先级差异化同步 (适用场景):
   - 混合关键和非关键数据
   - 资源受限环境
   - 需要平衡数据一致性和系统性能
   
   权衡: 增加实现复杂度，需要清晰的优先级定义
```

#### 一致性协议选择

```text
1. 强一致性协议 (适用场景):
   - 跨设备原子性操作
   - 金融/安全交易
   - 网络良好且设备可靠
   
   推荐: 两阶段提交，仅用于关键场景

2. 最终一致性协议 (适用场景):
   - 大多数智能家居场景
   - 展示性数据和状态更新
   - 设备状态同步
   
   推荐: 版本化状态、时间戳合并策略

3. 混合一致性 (适用场景):
   - 复杂场景编排
   - 不同重要性的操作组合
   - 资源差异大的设备网络
   
   推荐: Saga模式，补偿事务设计
```

### 3. 可靠性与弹性设计指南

#### 多层容错策略

```text
1. 设备层容错:
   - 本地重试逻辑
   - 安全降级模式
   - 自动恢复功能
   - 隔离故障组件
   - 看门狗定时器

2. 边缘层容错:
   - 请求超时管理
   - 服务发现与负载均衡
   - 熔断器模式
   - 队列缓冲区
   - 本地存储备份

3. 云层容错:
   - 区域故障转移
   - 实例冗余
   - 数据复制
   - 故障预测
   - 远程恢复能力
```

#### 网络弹性设计

```text
1. 离线操作支持:
   - 本地缓存关键数据
   - 离线执行工作流
   - 事件队列和重放
   - 定义清晰的自治边界
   - 优雅的功能降级

2. 连接恢复策略:
   - 指数退避重连
   - 批量同步优化
   - 冲突检测与解决
   - 变更日志合并
   - 优先级排序更新
```

### 4. 性能优化指南

#### 工作流分配优化

```text
1. 静态分析优化:
   - 工作流提前分解
   - 基于历史模式的预分配
   - 依据设备能力固定分配
   - 提前编译的决策树
   - 工作流模板优化

2. 动态运行时优化:
   - 实时负载监控
   - 自适应任务分配
   - 迁移成本评估
   - 资源预留机制
   - 执行预测与预取
```

#### 资源效率优化

```text
1. 计算优化:
   - 轻量级执行引擎
   - 按需计算策略
   - 异步处理非关键任务
   - 复用计算结果
   - 根据耗电优化执行

2. 网络优化:
   - 减少通信频率
   - 压缩数据传输
   - 批处理更新
   - 差异同步
   - 本地缓存策略
```

## 总结：多层工作流设计的关键原则

### 1. 明确的责任边界

- 每层具有清晰定义的职责和权限
- 减少层间紧耦合，提高系统弹性
- 允许部分独立升级和维护

### 2. 自适应执行决策

- 基于多因素动态决定执行位置
- 考虑延迟、资源、网络和数据位置
- 支持透明的工作流状态迁移

### 3. 分层容错与恢复

- 每层实现匹配其职责的容错机制
- 协调跨层故障检测和恢复
- 优先保障核心功能的可靠性

### 4. 智能数据流管理

- 差异化数据同步策略
- 冲突检测与自动解决
- 资源感知的缓存策略

### 5. 一致性与性能平衡

- 根据业务需求选择适当的一致性级别
- 关键操作强一致性，普通操作最终一致性
- 透明实现底层协议细节

端-边缘-云分布式工作流架构最大的优势在于结合了低延迟本地响应、区域协调和全局智能优化的能力，
为智能家居系统提供全面的自动化解决方案，同时有效应对网络不稳定、设备多样性和资源限制等挑战。
