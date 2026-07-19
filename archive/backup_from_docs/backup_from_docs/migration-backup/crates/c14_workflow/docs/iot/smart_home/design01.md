# 智能家居系统与Temporal工作流框架集成详解

## 目录

- [智能家居系统与Temporal工作流框架集成详解](#智能家居系统与temporal工作流框架集成详解)
  - [目录](#目录)
  - [1. 领域模型适配](#1-领域模型适配)
    - [Temporal核心概念到智能家居映射](#temporal核心概念到智能家居映射)
    - [工作流定义示例](#工作流定义示例)
    - [活动实现示例](#活动实现示例)
    - [适配层实现](#适配层实现)
  - [2. 状态管理差异](#2-状态管理差异)
    - [Temporal状态管理模型](#temporal状态管理模型)
    - [状态管理策略](#状态管理策略)
  - [3. 部署架构调整](#3-部署架构调整)
    - [Temporal服务组件](#temporal服务组件)
    - [混合部署架构](#混合部署架构)
    - [Kubernetes部署配置](#kubernetes部署配置)
    - [工作者实现](#工作者实现)
  - [4. 边缘计算考虑](#4-边缘计算考虑)
    - [本地优先策略](#本地优先策略)
    - [边缘-云协同模型](#边缘-云协同模型)
    - [轻量级本地工作流引擎](#轻量级本地工作流引擎)
  - [5. 混合架构实现方案](#5-混合架构实现方案)
    - [5.1 组件职责划分](#51-组件职责划分)
    - [5.2 数据流和状态同步](#52-数据流和状态同步)
    - [5.3 实际部署示例](#53-实际部署示例)
    - [5.4 实施路径与里程碑](#54-实施路径与里程碑)
  - [智能家居系统与Temporal集成架构（文本版）](#智能家居系统与temporal集成架构文本版)
  - [1. 混合部署架构图（文本形式）](#1-混合部署架构图文本形式)
  - [2. 实际部署组件关系图（文本形式）](#2-实际部署组件关系图文本形式)
  - [3. 数据流和状态同步流程图（文本形式）](#3-数据流和状态同步流程图文本形式)
  - [4. 组件逻辑关系图（文本形式）](#4-组件逻辑关系图文本形式)
  - [5. 临时状态决策过程（文本形式）](#5-临时状态决策过程文本形式)
  - [6. 工作流分层关系（文本形式）](#6-工作流分层关系文本形式)

## 1. 领域模型适配

### Temporal核心概念到智能家居映射

| Temporal概念 | 智能家居映射 | 说明 |
|------------|------------|------|
| Workflow | 场景(Scene)、自动化规则(Automation) | 长时间运行的业务流程，维护状态 |
| Activity | 设备动作(DeviceAction)、通知(Notification) | 单次执行的任务，可重试 |
| Query | 设备状态查询、场景状态查询 | 获取工作流当前状态 |
| Signal | 用户触发、设备事件、条件满足 | 向工作流发送外部事件 |
| Timer | 定时触发、延迟执行 | 时间相关的触发器 |

### 工作流定义示例

```go
// 使用Temporal Go SDK定义智能家居场景工作流
func SceneWorkflow(ctx workflow.Context, sceneRequest SceneExecutionRequest) (SceneExecutionResult, error) {
    // 场景执行结果
    result := SceneExecutionResult{
        SceneID:     sceneRequest.SceneID,
        StartTime:   workflow.Now(ctx),
        ActionResults: make(map[string]ActionResult),
    }
    
    // 设置场景级别的重试策略
    options := workflow.ActivityOptions{
        StartToCloseTimeout: time.Minute,
        RetryPolicy: &temporal.RetryPolicy{
            InitialInterval:    time.Second,
            BackoffCoefficient: 1.5,
            MaximumInterval:    time.Minute,
            MaximumAttempts:    3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, options)
    
    // 获取场景定义
    var sceneDefinition SceneDefinition
    err := workflow.ExecuteActivity(ctx, GetSceneDefinitionActivity, sceneRequest.SceneID).Get(ctx, &sceneDefinition)
    if err != nil {
        return result, err
    }
    
    // 验证前置条件
    if len(sceneDefinition.Conditions) > 0 {
        var conditionResult ConditionEvaluationResult
        err := workflow.ExecuteActivity(ctx, EvaluateConditionsActivity, sceneDefinition.Conditions).Get(ctx, &conditionResult)
        if err != nil {
            return result, err
        }
        
        if !conditionResult.Satisfied {
            result.Success = false
            result.Message = "条件不满足"
            return result, nil
        }
    }
    
    // 根据执行策略处理动作
    switch sceneDefinition.ExecutionStrategy {
    case "sequential":
        for i, action := range sceneDefinition.Actions {
            actionID := fmt.Sprintf("action-%d", i)
            var actionResult ActionResult
            
            // 允许为不同设备设置不同的执行选项
            activityOptions := customizeActivityOptions(options, action)
            activityCtx := workflow.WithActivityOptions(ctx, activityOptions)
            
            err := workflow.ExecuteActivity(activityCtx, ExecuteDeviceCommandActivity, action).Get(ctx, &actionResult)
            result.ActionResults[actionID] = actionResult
            
            if err != nil && sceneDefinition.StopOnError {
                result.Success = false
                result.Message = fmt.Sprintf("执行动作失败: %v", err)
                return result, err
            }
        }
    case "parallel":
        // 并行执行所有动作
        futures := make(map[string]workflow.Future)
        for i, action := range sceneDefinition.Actions {
            actionID := fmt.Sprintf("action-%d", i)
            activityOptions := customizeActivityOptions(options, action)
            activityCtx := workflow.WithActivityOptions(ctx, activityOptions)
            
            futures[actionID] = workflow.ExecuteActivity(activityCtx, ExecuteDeviceCommandActivity, action)
        }
        
        // 等待所有动作完成
        for actionID, future := range futures {
            var actionResult ActionResult
            err := future.Get(ctx, &actionResult)
            result.ActionResults[actionID] = actionResult
            
            if err != nil && sceneDefinition.StopOnError {
                result.Success = false
                result.Message = fmt.Sprintf("执行动作失败: %v", err)
                return result, err
            }
        }
    }
    
    // 记录场景执行结果
    err = workflow.ExecuteActivity(ctx, RecordSceneExecutionActivity, result).Get(ctx, nil)
    if err != nil {
        // 仅记录错误但不影响场景执行结果
        workflow.GetLogger(ctx).Error("记录场景执行结果失败", "error", err)
    }
    
    result.Success = true
    result.EndTime = workflow.Now(ctx)
    result.Duration = result.EndTime.Sub(result.StartTime)
    
    return result, nil
}
```

### 活动实现示例

```go
// 设备命令执行活动
func ExecuteDeviceCommandActivity(ctx context.Context, action Action) (ActionResult, error) {
    // 活动实现依赖注入
    deviceService := activity.GetWorkerInjectedDependency(ctx, "deviceService").(DeviceService)
    
    result := ActionResult{
        DeviceID:   action.DeviceID,
        Capability: action.Capability,
        Command:    action.Command,
        StartTime:  time.Now(),
    }
    
    // 执行设备命令
    response, err := deviceService.ExecuteCommand(
        ctx,
        action.DeviceID,
        action.Capability,
        action.Command,
        action.Parameters,
    )
    
    result.EndTime = time.Now()
    result.Duration = result.EndTime.Sub(result.StartTime)
    
    if err != nil {
        result.Success = false
        result.Error = err.Error()
        return result, err
    }
    
    result.Success = true
    result.Response = response
    
    return result, nil
}
```

### 适配层实现

我们需要创建一个适配层，将现有智能家居系统与Temporal桥接：

```go
// 智能家居Temporal适配器
type TemporalAdapter struct {
    client        client.Client
    workerFactory worker.Factory
    namespace     string
    taskQueue     string
}

// 创建Temporal适配器
func NewTemporalAdapter(config TemporalConfig) (*TemporalAdapter, error) {
    c, err := client.NewClient(client.Options{
        HostPort:  config.HostPort,
        Namespace: config.Namespace,
    })
    if err != nil {
        return nil, err
    }
    
    // 创建工作器工厂
    workerFactory := worker.NewFactory(
        c,
        worker.FactoryOptions{
            WorkerOptions: worker.Options{
                MaxConcurrentActivityExecutionSize: config.MaxConcurrentActivities,
                MaxConcurrentWorkflowTaskExecutionSize: config.MaxConcurrentWorkflows,
            },
        },
    )
    
    return &TemporalAdapter{
        client:        c,
        workerFactory: workerFactory,
        namespace:     config.Namespace,
        taskQueue:     config.TaskQueue,
    }, nil
}

// 执行场景
func (a *TemporalAdapter) ExecuteScene(ctx context.Context, request SceneExecutionRequest) (string, error) {
    workflowOptions := client.StartWorkflowOptions{
        ID:                  fmt.Sprintf("scene-%s-%s", request.SceneID, uuid.New().String()),
        TaskQueue:           a.taskQueue,
        WorkflowRunTimeout:  time.Minute * 10,
        WorkflowIDReusePolicy: enumspb.WORKFLOW_ID_REUSE_POLICY_ALLOW_DUPLICATE,
    }
    
    run, err := a.client.ExecuteWorkflow(ctx, workflowOptions, SceneWorkflow, request)
    if err != nil {
        return "", err
    }
    
    return run.GetID(), nil
}

// 获取场景执行状态
func (a *TemporalAdapter) GetSceneExecutionStatus(ctx context.Context, executionID string) (*SceneExecutionStatus, error) {
    workflow, err := a.client.DescribeWorkflowExecution(ctx, executionID, "")
    if err != nil {
        return nil, err
    }
    
    status := &SceneExecutionStatus{
        ID:        executionID,
        Status:    string(workflow.WorkflowExecutionInfo.Status),
        StartTime: workflow.WorkflowExecutionInfo.StartTime.AsTime(),
    }
    
    // 如果工作流已完成，获取结果
    if workflow.WorkflowExecutionInfo.Status == enumspb.WORKFLOW_EXECUTION_STATUS_COMPLETED {
        var result SceneExecutionResult
        err = a.client.GetWorkflowResult(ctx, executionID, "", &result)
        if err != nil {
            return nil, err
        }
        status.Result = &result
    }
    
    return status, nil
}
```

## 2. 状态管理差异

### Temporal状态管理模型

Temporal提供了强大的工作流状态持久化机制：

1. **事件溯源**：所有工作流决策都以事件记录，支持完整重建
2. **内置持久性**：工作流状态自动保存在Temporal数据库中
3. **故障自动恢复**：节点故障时自动重新调度工作流执行
4. **确定性要求**：工作流代码必须是确定性的，以便在重放事件时得到相同结果

### 状态管理策略

针对智能家居系统与Temporal集成，推荐以下状态管理策略：

1. **职责划分**
   - Temporal负责：工作流执行状态、活动结果、重试逻辑
   - 业务系统负责：设备持久状态、用户配置、历史数据分析

2. **双重存储模式**
   - 工作流执行细节：存储在Temporal
   - 业务成果数据：存储在应用数据库

```go
// 工作流执行后的状态同步活动
func SynchronizeStateActivity(ctx context.Context, executionResult SceneExecutionResult) error {
    // 从DI获取存储服务
    stateManager := activity.GetWorkerInjectedDependency(ctx, "stateManager").(StateManager)
    
    // 构建状态更新
    updates := make([]StateUpdate, 0)
    for _, actionResult := range executionResult.ActionResults {
        if !actionResult.Success {
            continue
        }
        
        // 从动作结果中提取状态更新
        deviceUpdates := extractDeviceStateUpdates(actionResult)
        updates = append(updates, deviceUpdates...)
    }
    
    // 批量更新设备状态
    if err := stateManager.ApplyStateUpdates(ctx, updates); err != nil {
        return fmt.Errorf("状态同步失败: %w", err)
    }
    
    // 记录执行历史
    historyEntry := SceneExecutionHistory{
        SceneID:   executionResult.SceneID,
        ExecutionID: executionResult.ExecutionID,
        StartTime: executionResult.StartTime,
        EndTime:   executionResult.EndTime,
        Success:   executionResult.Success,
        // 存储简化的执行结果，避免重复大量数据
        Summary:   summarizeExecutionResult(executionResult),
    }
    
    if err := stateManager.RecordSceneExecution(ctx, historyEntry); err != nil {
        return fmt.Errorf("记录执行历史失败: %w", err)
    }
    
    return nil
}
```

1. **缓存策略优化**
   - 维护本地设备状态缓存，减少数据库查询
   - 使用发布-订阅机制同步状态变更
   - 对于频繁访问的状态，考虑使用Redis等分布式缓存

```go
// 设备状态缓存管理器
type DeviceStateCacheManager struct {
    redis      *redis.Client
    pubsub     *redis.PubSub
    localCache *lru.Cache
    ttl        time.Duration
}

// 获取设备状态（优先从缓存获取）
func (m *DeviceStateCacheManager) GetDeviceState(ctx context.Context, deviceID string) (*DeviceState, error) {
    // 尝试从本地缓存获取
    if state, ok := m.localCache.Get(deviceID); ok {
        return state.(*DeviceState), nil
    }
    
    // 尝试从Redis获取
    data, err := m.redis.Get(ctx, fmt.Sprintf("device:state:%s", deviceID)).Bytes()
    if err == nil {
        var state DeviceState
        if err := json.Unmarshal(data, &state); err == nil {
            // 更新本地缓存
            m.localCache.Add(deviceID, &state)
            return &state, nil
        }
    }
    
    // 从数据库获取
    // ...
    
    return nil, fmt.Errorf("设备状态不存在")
}

// 更新设备状态并广播变更
func (m *DeviceStateCacheManager) UpdateDeviceState(ctx context.Context, deviceID string, state *DeviceState) error {
    // 序列化状态
    data, err := json.Marshal(state)
    if err != nil {
        return err
    }
    
    // 更新Redis
    key := fmt.Sprintf("device:state:%s", deviceID)
    if err := m.redis.Set(ctx, key, data, m.ttl).Err(); err != nil {
        return err
    }
    
    // 更新本地缓存
    m.localCache.Add(deviceID, state)
    
    // 发布状态变更事件
    event := DeviceStateChangedEvent{
        DeviceID:  deviceID,
        State:     state,
        Timestamp: time.Now(),
    }
    
    eventData, _ := json.Marshal(event)
    return m.redis.Publish(ctx, "device:state:changed", eventData).Err()
}
```

## 3. 部署架构调整

### Temporal服务组件

完整的Temporal部署包括多个服务组件：

1. **Frontend Service**：处理客户端API请求
2. **History Service**：管理工作流历史和状态
3. **Matching Service**：将任务分配给工作器
4. **Worker Service**：执行工作流和活动代码

### 混合部署架构

为了适应智能家居系统需求，推荐以下混合部署架构：

[混合部署架构图]

1. **云端Temporal集群**：
   - 部署在云平台(AWS/Azure/GCP)的Kubernetes集群
   - 处理高复杂度、低时间敏感的工作流
   - 管理所有工作流历史和状态
   - 提供集中监控和可观测性

2. **边缘层Temporal工作器**：
   - 部署在本地网关或家庭服务器
   - 执行时间敏感的活动任务
   - 与本地设备直接通信
   - 在网络断开时维持基本功能

3. **设备层轻量工作流**：
   - 极简的工作流引擎在智能设备上运行
   - 处理时效性极高的自动化（如动作检测触发照明）
   - 定期与边缘层同步状态

### Kubernetes部署配置

```yaml
# kubernetes/temporal-cluster.yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: temporal-frontend
spec:
  serviceName: temporal-frontend
  replicas: 2
  selector:
    matchLabels:
      app: temporal
      component: frontend
  template:
    metadata:
      labels:
        app: temporal
        component: frontend
    spec:
      containers:
      - name: frontend
        image: temporalio/server:1.21.0
        args:
        - temporal-server
        - --services=frontend
        env:
        - name: DYNAMIC_CONFIG_FILE_PATH
          value: "/etc/temporal/config/dynamicconfig/development.yaml"
        resources:
          limits:
            cpu: "1"
            memory: "1Gi"
          requests:
            cpu: "200m"
            memory: "512Mi"
        ports:
        - containerPort: 7233
        volumeMounts:
        - name: config
          mountPath: /etc/temporal/config
      volumes:
      - name: config
        configMap:
          name: temporal-config

---
# 其他Temporal服务组件（history, matching等）配置类似
# ...

---
# Edge Worker部署
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: smart-home-edge-worker
spec:
  selector:
    matchLabels:
      app: smart-home
      component: edge-worker
  template:
    metadata:
      labels:
        app: smart-home
        component: edge-worker
    spec:
      nodeSelector:
        node-role.kubernetes.io/edge: "true"
      containers:
      - name: temporal-worker
        image: smart-home/edge-worker:latest
        env:
        - name: TEMPORAL_HOST
          value: "temporal-frontend.temporal.svc.cluster.local:7233"
        - name: TEMPORAL_NAMESPACE
          value: "smart-home"
        - name: TASK_QUEUE
          value: "edge-activities"
        - name: LOCAL_ZONE_ID
          valueFrom:
            fieldRef:
              fieldPath: metadata.labels['home.zone']
        resources:
          limits:
            cpu: "500m"
            memory: "500Mi"
          requests:
            cpu: "100m"
            memory: "200Mi"
        volumeMounts:
        - name: device-config
          mountPath: /etc/smart-home/devices
      volumes:
      - name: device-config
        configMap:
          name: device-config
```

### 工作者实现

```go
// Edge工作者实现
func startEdgeWorker(config WorkerConfig) error {
    // 创建Temporal客户端
    c, err := client.NewClient(client.Options{
        HostPort:  config.TemporalHostPort,
        Namespace: config.Namespace,
        Logger:    zapAdapter,
    })
    if err != nil {
        return fmt.Errorf("无法创建Temporal客户端: %w", err)
    }
    defer c.Close()
    
    // 创建设备服务
    deviceService := device.NewService(config.DeviceConfig)
    
    // 创建状态管理器
    stateManager := state.NewEdgeStateManager(config.StateConfig)
    
    // 创建工作者
    w := worker.New(c, config.TaskQueue, worker.Options{
        MaxConcurrentActivityExecutionSize: config.ConcurrencyLimit,
        DisableWorkflowWorker: true, // Edge节点只运行活动，不运行工作流
    })
    
    // 注册活动
    w.RegisterActivity(ExecuteDeviceCommandActivity)
    w.RegisterActivity(EvaluateConditionsActivity)
    w.RegisterActivity(GetDeviceStateActivity)
    
    // 注入依赖
    w.SetWorkerInjectedDependency("deviceService", deviceService)
    w.SetWorkerInjectedDependency("stateManager", stateManager)
    
    // 启动工作者
    if err := w.Start(); err != nil {
        return fmt.Errorf("启动工作者失败: %w", err)
    }
    
    // 监听停止信号
    c := make(chan os.Signal, 1)
    signal.Notify(c, os.Interrupt, syscall.SIGTERM)
    <-c
    
    // 优雅关闭
    w.Stop()
    log.Info("工作者已停止")
    
    return nil
}
```

## 4. 边缘计算考虑

智能家居系统需要在边缘设备上运行重要功能，即使云服务不可用。

### 本地优先策略

1. **关键功能本地化**
   - 基本设备控制和状态监控
   - 安全相关功能（门锁、监控等）
   - 定时执行的自动化
   - 根据本地传感器的简单条件触发

2. **断网韧性**
   - 本地事件队列缓冲
   - 状态变更本地持久化
   - 重连时自动同步

```go
// 边缘节点事件队列
type EdgeEventQueue struct {
    eventStore     *badger.DB
    maxQueueSize   int
    flushInterval  time.Duration
    isConnected    atomic.Bool
    pendingCount   atomic.Int32
    cloudAdapter   CloudAdapter
}

// 将事件推送到云端或本地队列
func (q *EdgeEventQueue) PushEvent(ctx context.Context, event Event) error {
    // 如果连接正常，直接发送
    if q.isConnected.Load() {
        err := q.cloudAdapter.SendEvent(ctx, event)
        if err == nil {
            return nil
        }
        // 发送失败，标记为离线
        q.isConnected.Store(false)
        // 启动重连逻辑
        go q.startReconnection()
    }
    
    // 离线模式，存储到本地
    return q.storeEventLocally(event)
}

// 存储事件到本地
func (q *EdgeEventQueue) storeEventLocally(event Event) error {
    // 检查队列大小限制
    if q.pendingCount.Load() >= int32(q.maxQueueSize) {
        return errors.New("事件队列已满")
    }
    
    // 生成唯一ID
    eventID := fmt.Sprintf("evt_%d_%s", time.Now().UnixNano(), uuid.New().String())
    
    // 序列化事件
    data, err := json.Marshal(event)
    if err != nil {
        return err
    }
    
    // 存储到本地数据库
    err = q.eventStore.Update(func(txn *badger.Txn) error {
        return txn.Set([]byte(eventID), data)
    })
    
    if err == nil {
        q.pendingCount.Add(1)
    }
    
    return err
}

// 重连并同步事件
func (q *EdgeEventQueue) syncPendingEvents(ctx context.Context) error {
    // 设置最大批次大小
    batchSize := 50
    
    // 获取所有待处理事件
    var pendingEvents []Event
    
    err := q.eventStore.View(func(txn *badger.Txn) error {
        it := txn.NewIterator(badger.DefaultIteratorOptions)
        defer it.Close()
        
        count := 0
        for it.Rewind(); it.Valid() && count < batchSize; it.Next() {
            item := it.Item()
            
            var event Event
            err := item.Value(func(val []byte) error {
                return json.Unmarshal(val, &event)
            })
            
            if err != nil {
                return err
            }
            
            pendingEvents = append(pendingEvents, event)
            count++
        }
        
        return nil
    })
    
    if err != nil {
        return err
    }
    
    // 无待处理事件
    if len(pendingEvents) == 0 {
        return nil
    }
    
    // 批量发送事件
    succeeded := make([]string, 0)
    
    for _, event := range pendingEvents {
        // 尝试发送到云端
        err := q.cloudAdapter.SendEvent(ctx, event)
        if err != nil {
            // 发送失败，可能仍未连接
            return err
        }
        
        // 标记为成功
        succeeded = append(succeeded, event.ID)
    }
    
    // 删除已成功发送的事件
    err = q.eventStore.Update(func(txn *badger.Txn) error {
        for _, id := range succeeded {
            if err := txn.Delete([]byte(id)); err != nil {
                return err
            }
        }
        return nil
    })
    
    if err != nil {
        return err
    }
    
    // 更新计数
    q.pendingCount.Add(-int32(len(succeeded)))
    
    return nil
}
```

### 边缘-云协同模型

1. **工作流分区**
   - 高频/简单/时效性高：边缘执行
   - 低频/复杂/协调性高：云端执行

2. **活动路由策略**
   - 活动根据类型路由到合适执行环境
   - 本地活动(Local Activity)执行对云端透明

3. **数据同步策略**
   - 设备状态实时同步
   - 配置定期同步
   - 历史数据批量同步

```go
// 活动路由管理器
type ActivityRouter struct {
    localClient    client.Client
    cloudClient    client.Client
    routingRules   map[string]string // 活动名称 -> 执行位置
    networkMonitor NetworkMonitor
}

// 路由活动执行
func (r *ActivityRouter) RouteActivity(ctx context.Context, activityName string, params interface{}) (interface{}, error) {
    // 检查网络状态
    isOnline := r.networkMonitor.IsCloudConnected()
    
    // 确定执行位置
    executionTarget := r.routingRules[activityName]
    if executionTarget == "" {
        executionTarget = "auto" // 默认自动路由
    }
    
    // 如果离线且配置为云端执行，尝试降级策略
    if !isOnline && executionTarget == "cloud" {
        // 检查是否有本地降级版本
        localVersion := activityName + "Local"
        if _, exists := r.routingRules[localVersion
```go
    // 如果离线且配置为云端执行，尝试降级策略
    if !isOnline && executionTarget == "cloud" {
        // 检查是否有本地降级版本
        localVersion := activityName + "Local"
        if _, exists := r.routingRules[localVersion]; exists {
            log.Info("降级到本地活动版本", "activity", activityName, "localVersion", localVersion)
            activityName = localVersion
            executionTarget = "edge"
        } else {
            return nil, fmt.Errorf("网络离线，无法执行云端活动 %s", activityName)
        }
    }
    
    // 选择执行客户端
    var client client.Client
    var options client.ActivityOptions
    
    switch executionTarget {
    case "cloud":
        client = r.cloudClient
        options = client.ActivityOptions{
            TaskQueue: "cloud-activities",
            StartToCloseTimeout: time.Minute * 5,
            RetryPolicy: &temporal.RetryPolicy{
                InitialInterval:    time.Second,
                BackoffCoefficient: 2.0,
                MaximumInterval:    time.Minute,
                MaximumAttempts:    5,
            },
        }
    case "edge", "auto":
        client = r.localClient
        options = client.ActivityOptions{
            TaskQueue: "edge-activities",
            StartToCloseTimeout: time.Minute,
            RetryPolicy: &temporal.RetryPolicy{
                InitialInterval:    time.Second,
                BackoffCoefficient: 1.5,
                MaximumInterval:    time.Second * 10,
                MaximumAttempts:    3,
            },
        }
    default:
        return nil, fmt.Errorf("未知的执行目标: %s", executionTarget)
    }
    
    // 执行活动
    ctx = context.WithActivityOptions(ctx, options)
    future := client.ExecuteActivity(ctx, activityName, params)
    
    // 等待结果
    var result interface{}
    err := future.Get(ctx, &result)
    
    return result, err
}
```

### 轻量级本地工作流引擎

为了在设备层提供轻量级工作流执行能力，我们设计一个简化的工作流引擎：

```go
// 轻量级设备工作流引擎
type LightWorkflowEngine struct {
    workflows      map[string]*DeviceWorkflow
    executor       *workflowExecutor
    eventListener  EventListener
    stateManager   StateManager
    mu             sync.RWMutex
}

// 设备级工作流定义
type DeviceWorkflow struct {
    ID          string
    Name        string
    Version     int
    Trigger     TriggerDefinition
    Conditions  []ConditionDefinition
    Actions     []ActionDefinition
    Options     WorkflowOptions
}

// 工作流选项
type WorkflowOptions struct {
    Priority        int
    MaxExecutionTime time.Duration
    StopOnError     bool
    LocalOnly       bool
}

// 创建轻量级工作流引擎
func NewLightWorkflowEngine(config LightEngineConfig) (*LightWorkflowEngine, error) {
    engine := &LightWorkflowEngine{
        workflows:    make(map[string]*DeviceWorkflow),
        executor:     newWorkflowExecutor(config.ExecutorConfig),
        stateManager: config.StateManager,
    }
    
    // 加载预定义工作流
    if err := engine.loadWorkflows(); err != nil {
        return nil, err
    }
    
    // 启动事件监听
    if err := engine.startEventListener(config.EventSource); err != nil {
        return nil, err
    }
    
    return engine, nil
}

// 加载工作流定义
func (e *LightWorkflowEngine) loadWorkflows() error {
    workflowDefs, err := e.stateManager.LoadWorkflowDefinitions()
    if err != nil {
        return err
    }
    
    e.mu.Lock()
    defer e.mu.Unlock()
    
    for _, def := range workflowDefs {
        e.workflows[def.ID] = def
    }
    
    return nil
}

// 启动事件监听
func (e *LightWorkflowEngine) startEventListener(eventSource EventSource) error {
    e.eventListener = NewEventListener(eventSource)
    
    // 注册事件处理器
    e.eventListener.RegisterHandler(func(event Event) {
        e.handleEvent(event)
    })
    
    // 启动监听
    return e.eventListener.Start()
}

// 处理收到的事件
func (e *LightWorkflowEngine) handleEvent(event Event) {
    // 查找匹配的工作流
    matchingWorkflows := e.findMatchingWorkflows(event)
    if len(matchingWorkflows) == 0 {
        return
    }
    
    // 按优先级排序
    sort.Slice(matchingWorkflows, func(i, j int) bool {
        return matchingWorkflows[i].Options.Priority > matchingWorkflows[j].Options.Priority
    })
    
    // 执行匹配的工作流
    for _, workflow := range matchingWorkflows {
        // 创建执行上下文
        ctx := newWorkflowContext(workflow, event)
        
        // 异步执行
        go func(wf *DeviceWorkflow, ctx *WorkflowContext) {
            result, err := e.executor.ExecuteWorkflow(ctx, wf)
            if err != nil {
                log.Error("工作流执行失败", "workflowId", wf.ID, "error", err)
                return
            }
            
            // 记录执行结果
            e.stateManager.SaveExecutionResult(result)
            
            // 如果工作流不是本地专属，且在线，则同步到云端
            if !wf.Options.LocalOnly && e.isCloudConnected() {
                go e.syncExecutionToCloud(result)
            }
        }(workflow, ctx)
    }
}

// 找到与事件匹配的工作流
func (e *LightWorkflowEngine) findMatchingWorkflows(event Event) []*DeviceWorkflow {
    e.mu.RLock()
    defer e.mu.RUnlock()
    
    matching := make([]*DeviceWorkflow, 0)
    
    for _, workflow := range e.workflows {
        if matchesTrigger(event, workflow.Trigger) {
            matching = append(matching, workflow)
        }
    }
    
    return matching
}

// 检查事件是否匹配触发器
func matchesTrigger(event Event, trigger TriggerDefinition) bool {
    // 检查事件类型
    if event.Type != trigger.EventType {
        return false
    }
    
    // 检查设备ID（如果指定）
    if trigger.DeviceID != "" && event.SourceID != trigger.DeviceID {
        return false
    }
    
    // 检查其他触发条件
    for k, v := range trigger.Conditions {
        eventValue, exists := event.Attributes[k]
        if !exists || eventValue != v {
            return false
        }
    }
    
    return true
}

// 工作流执行器
type workflowExecutor struct {
    deviceService  DeviceService
    stateManager   StateManager
    timeProvider   TimeProvider
}

// 执行工作流
func (e *workflowExecutor) ExecuteWorkflow(ctx *WorkflowContext, workflow *DeviceWorkflow) (*WorkflowExecutionResult, error) {
    startTime := e.timeProvider.Now()
    
    result := &WorkflowExecutionResult{
        WorkflowID:  workflow.ID,
        ExecutionID: generateUUID(),
        StartTime:   startTime,
        ActionResults: make(map[string]ActionResult),
    }
    
    // 设置执行超时
    var cancel context.CancelFunc
    if workflow.Options.MaxExecutionTime > 0 {
        ctx.Context, cancel = context.WithTimeout(ctx.Context, workflow.Options.MaxExecutionTime)
        defer cancel()
    }
    
    // 评估条件
    if len(workflow.Conditions) > 0 {
        satisfied, err := e.evaluateConditions(ctx, workflow.Conditions)
        if err != nil {
            result.Error = fmt.Sprintf("条件评估失败: %v", err)
            result.Success = false
            result.EndTime = e.timeProvider.Now()
            return result, err
        }
        
        if !satisfied {
            // 条件不满足，工作流不执行
            result.Message = "条件不满足"
            result.Success = true // 这不算执行失败
            result.EndTime = e.timeProvider.Now()
            return result, nil
        }
    }
    
    // 执行动作
    for i, action := range workflow.Actions {
        actionID := fmt.Sprintf("action-%d", i)
        
        actionResult, err := e.executeAction(ctx, action)
        result.ActionResults[actionID] = actionResult
        
        if err != nil {
            if workflow.Options.StopOnError {
                result.Error = fmt.Sprintf("动作执行失败: %v", err)
                result.Success = false
                result.EndTime = e.timeProvider.Now()
                return result, err
            }
            
            // 继续执行后续动作
            log.Warn("动作执行失败但继续工作流", "workflowId", workflow.ID, "actionId", actionID, "error", err)
        }
    }
    
    result.Success = true
    result.EndTime = e.timeProvider.Now()
    result.Duration = result.EndTime.Sub(result.StartTime)
    
    return result, nil
}
```

## 5. 混合架构实现方案

将上述各部分整合，我们形成一个完整的混合架构实现方案：

### 5.1 组件职责划分

1. **云端组件**
   - Temporal服务集群
   - 复杂工作流定义与调度
   - 历史数据存储与分析
   - 机器学习模型训练
   - 全局状态维护
   - 用户界面服务

2. **边缘层组件**
   - Temporal Worker节点
   - 设备命令执行活动
   - 本地状态缓存
   - 事件收集与转发
   - 离线功能保障
   - 轻量级分析

3. **设备层组件**
   - 轻量级工作流引擎
   - 设备直接控制逻辑
   - 基本状态存储
   - 时效性触发器处理

### 5.2 数据流和状态同步

```go
// 智能家居系统主接口
type SmartHomeSystem struct {
    config Config
    
    // 云端组件
    temporalClient    *client.Client
    cloudStateManager *CloudStateManager
    
    // 边缘组件
    edgeEngine       *EdgeWorkflowEngine
    deviceManager    *DeviceManager
    localStateCache  *LocalStateCache
    
    // 同步组件
    syncManager      *StateSyncManager
    eventRouter      *EventRouter
}

// 初始化系统
func NewSmartHomeSystem(config Config) (*SmartHomeSystem, error) {
    system := &SmartHomeSystem{
        config: config,
    }
    
    // 初始化组件
    if err := system.initializeComponents(); err != nil {
        return nil, err
    }
    
    // 连接组件
    if err := system.connectComponents(); err != nil {
        return nil, err
    }
    
    return system, nil
}

// 状态同步管理器
type StateSyncManager struct {
    localCache   *LocalStateCache
    cloudStorage *CloudStateStorage
    deviceManager *DeviceManager
    syncInterval time.Duration
    isOnline     atomic.Bool
}

// 开始状态同步
func (m *StateSyncManager) StartSync(ctx context.Context) error {
    // 启动设备状态同步
    go m.syncDeviceStates(ctx)
    
    // 启动配置同步
    go m.syncConfigurations(ctx)
    
    // 启动历史数据同步
    go m.syncHistoricalData(ctx)
    
    // 监听网络状态变化
    go m.monitorConnectivity(ctx)
    
    return nil
}

// 同步设备状态
func (m *StateSyncManager) syncDeviceStates(ctx context.Context) {
    ticker := time.NewTicker(m.syncInterval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ctx.Done():
            return
        case <-ticker.C:
            if !m.isOnline.Load() {
                continue
            }
            
            // 获取本地状态变更
            changes, err := m.localCache.GetUnsynedStateChanges()
            if err != nil {
                log.Error("获取未同步状态变更失败", "error", err)
                continue
            }
            
            if len(changes) == 0 {
                continue
            }
            
            // 将变更推送到云端
            if err := m.cloudStorage.UpdateDeviceStates(ctx, changes); err != nil {
                log.Error("同步设备状态到云端失败", "error", err)
                continue
            }
            
            // 标记为已同步
            if err := m.localCache.MarkSyncedChanges(changes); err != nil {
                log.Error("标记已同步状态失败", "error", err)
            }
        }
    }
}

// 事件路由器
type EventRouter struct {
    localHandler  EventHandler
    cloudHandler  EventHandler
    eventBuffer   *EventBuffer
    isOnline      atomic.Bool
}

// 处理事件
func (r *EventRouter) HandleEvent(event Event) error {
    // 本地优先处理
    if err := r.localHandler.HandleEvent(event); err != nil {
        log.Error("本地事件处理失败", "error", err)
        // 本地处理失败不阻止云端处理
    }
    
    // 如果在线，发送到云端
    if r.isOnline.Load() {
        if err := r.cloudHandler.HandleEvent(event); err != nil {
            // 云端处理失败，放入缓冲区
            log.Warn("云端事件处理失败，添加到缓冲区", "error", err)
            return r.eventBuffer.AddEvent(event)
        }
    } else {
        // 离线，放入缓冲区
        return r.eventBuffer.AddEvent(event)
    }
    
    return nil
}
```

### 5.3 实际部署示例

[实际部署图]

包含云端、网关和本地设备的一个典型部署示例：

1. **云平台服务**
   - Temporal服务器集群（Frontend、History、Matching等）
   - 智能家居业务服务（API服务、用户管理、数据分析等）
   - 数据存储（关系型数据库、时序数据库、对象存储等）
   - 消息队列和事件总线

2. **家庭网关**
   - 边缘计算节点（树莓派或专用网关）
   - Temporal Worker进程
   - 本地设备管理服务
   - 本地状态缓存和数据库
   - 工作流优化引擎

3. **智能设备**
   - 轻量级工作流引擎
   - 本地控制逻辑
   - 设备状态缓存
   - 通信适配器

### 5.4 实施路径与里程碑

为了实现这一混合架构，建议按以下阶段进行：

-**阶段1：基础架构与概念验证（2-3个月）**

- 建立Temporal集群并验证基本功能
- 实现简单的设备控制工作流
- 开发原型级边缘节点组件
- 建立基本监控和观测能力

-**阶段2：核心功能实现（3-4个月）**

- 完善工作流定义和活动实现
- 开发设备集成层和协议适配器
- 构建边缘节点完整功能
- 实现状态同步与事件路由
- 部署测试环境并验证端到端功能

-**阶段3：高级功能与生产准备（3-4个月）**

- 实现轻量级设备工作流引擎
- 开发完整的离线功能支持
- 构建高级监控和自动恢复能力
- 性能优化和负载测试
- 完善文档和运维工具

-**阶段4：优化与扩展（持续）**

- 基于用户反馈进行优化
- 支持更多设备类型和协议
- 增强AI和机器学习能力
- 改进开发者工具和SDK

通过这种混合架构，我们可以充分利用Temporal工作流引擎的强大功能，同时保持智能家居系统所需的响应性和可靠性。边缘计算能力确保了本地功能在网络中断时仍能可靠运行，而云端的强大计算和存储能力则支持更复杂的分析和优化功能。

## 智能家居系统与Temporal集成架构（文本版）

## 1. 混合部署架构图（文本形式）

```text
+-------------------------------------------+
|             云端平台层                     |
+-------------------------------------------+
|                                           |
|  +---------------+    +---------------+   |
|  | Temporal集群  |    | 智能家居业务服务 |   |
|  |               |    |               |   |
|  | - Frontend    |    | - API服务     |   |
|  | - History     |<-->| - 用户管理    |   |
|  | - Matching    |    | - 数据分析    |   |
|  | - Worker      |    | - 机器学习    |   |
|  +---------------+    +---------------+   |
|           ^                   ^           |
|           |                   |           |
|  +---------------+    +---------------+   |
|  | 云存储服务    |    | 消息队列服务  |   |
|  |               |    |               |   |
|  | - 时序数据库  |    | - Kafka/RabbitMQ |
|  | - 关系型数据库|    | - 事件总线    |   |
|  | - 对象存储    |    |               |   |
|  +---------------+    +---------------+   |
|                                           |
+-------------------+-------------------------
               ^    |
               |    v
+-------------------------------------------+
|             网关/边缘层                    |
+-------------------------------------------+
|                                           |
|  +---------------+    +---------------+   |
|  | Temporal Worker|    | 边缘管理服务  |   |
|  |               |    |               |   |
|  | - 活动执行    |<-->| - 设备管理    |   |
|  | - 本地工作流  |    | - 状态同步    |   |
|  | - 状态缓存    |    | - 离线处理    |   |
|  +---------------+    +---------------+   |
|           ^                   ^           |
|           |                   |           |
|  +---------------+    +---------------+   |
|  | 本地数据存储  |    | 事件路由器    |   |
|  |               |    |               |   |
|  | - 设备状态    |    | - 事件缓冲    |   |
|  | - 工作流状态  |    | - 优先级处理  |   |
|  | - 历史记录    |    | - 离线队列    |   |
|  +---------------+    +---------------+   |
|                                           |
+-------------------+-------------------------
               ^    |
               |    v
+-------------------------------------------+
|              设备层                        |
+-------------------------------------------+
|                                           |
|  +---------------+    +---------------+   |
|  | 轻量级工作流  |    | 通信适配器    |   |
|  |               |    |               |   |
|  | - 简单触发    |<-->| - WiFi/蓝牙   |   |
|  | - 本地条件    |    | - ZigBee      |   |
|  | - 快速响应    |    | - Z-Wave      |   |
|  +---------------+    +---------------+   |
|           ^                   ^           |
|           |                   |           |
|  +---------------+    +---------------+   |
|  | 本地控制逻辑  |    | 设备状态缓存  |   |
|  |               |    |               |   |
|  | - 直接控制    |    | - 最新状态    |   |
|  | - 安全保障    |    | - 有限历史    |   |
|  +---------------+    +---------------+   |
|                                           |
+-------------------------------------------+
```

## 2. 实际部署组件关系图（文本形式）

```text
+------------------+    +-----------------+    +------------------+
| 云端服务器集群   |<-->| 数据中心存储    |<-->| 监控与管理系统   |
+------------------+    +-----------------+    +------------------+
         ^
         |
         v
+------------------+    +-----------------+    +------------------+
| 边缘计算网关     |<-->| 本地数据缓存    |<-->| 家庭WiFi/以太网  |
| (树莓派/专用硬件) |    | (SSD/内存)     |    | 路由器          |
+------------------+    +-----------------+    +------------------+
         ^
         |
         v
+------------------+    +-----------------+    +------------------+
| 智能灯具控制器   |    | 温控设备        |    | 安防设备        |
| - 灯具组         |    | - 温度传感器    |    | - 门窗传感器    |
| - 灯带           |    | - 恒温器        |    | - 运动探测器    |
| - 智能开关       |    | - 空调控制      |    | - 摄像头        |
+------------------+    +-----------------+    +------------------+
```

## 3. 数据流和状态同步流程图（文本形式）

```text
设备状态变更流程:
设备 -> 状态变更 -> 本地缓存 -> 边缘节点处理 -> 触发本地工作流 
                                            -> 同步到云端 -> 云端工作流处理
                                                         -> 数据分析与存储
                                                         -> 用户UI更新

场景执行流程:
用户/触发器 -> 执行请求 -> 路由决策 (本地/云端?) 
     |                   |-> 本地执行 -> 设备命令 -> 状态更新 -> 同步到云端
     |                   |-> 云端执行 -> 分配给边缘工作器 -> 设备命令 -> 状态更新
     V                                                                  |
 执行结果 <- 状态更新 <------------------------------------------------+

离线同步流程:
网络中断检测 -> 进入离线模式 -> 本地工作流继续运行
                            -> 事件与状态缓存
网络恢复检测 -> 退出离线模式 -> 同步缓存事件 <- 解决冲突
                            -> 更新本地工作流 <- 获取云端更新
```

## 4. 组件逻辑关系图（文本形式）

```text
+------------------------------+
| 智能家居系统核心组件          |
+------------------------------+
|                              |
| +------------+  +----------+ |
| | 用户界面   |  | API服务  | |
| +------------+  +----------+ |
|        ^             ^       |
|        |             |       |
| +------------+  +----------+ |
| | 场景管理   |  | 设备管理 | |
| +------------+  +----------+ |
|        ^             ^       |
|        |             |       |
| +-------------------------+  |
| |    工作流管理系统       |  |
| |                         |  |
| | +---------------------+ |  |
| | | Temporal工作流引擎  | |  |
| | |                     | |  |
| | | +---------------+   | |  |
| | | | 云端工作流    |   | |  |
| | | +---------------+   | |  |
| | |                     | |  |
| | | +---------------+   | |  |
| | | | 边缘工作流    |   | |  |
| | | +---------------+   | |  |
| | |                     | |  |
| | | +---------------+   | |  |
| | | | 轻量工作流    |   | |  |
| | | +---------------+   | |  |
| | +---------------------+ |  |
| +-------------------------+  |
|        ^             ^       |
|        |             |       |
| +------------+  +----------+ |
| | 状态同步   |  | 事件路由 | |
| +------------+  +----------+ |
|        ^             ^       |
|        |             |       |
| +------------+  +----------+ |
| | 数据存储   |  | 监控系统 | |
| +------------+  +----------+ |
|                              |
+------------------------------+
```

## 5. 临时状态决策过程（文本形式）

```text
当设备事件发生时的决策流程:

[设备事件] --> 是否需要立即响应?
               |
               +--> 是 --> 使用轻量级工作流处理
               |
               +--> 否 --> 是否涉及多设备协调?
                            |
                            +--> 是 --> 云端是否可用?
                            |           |
                            |           +--> 是 --> 使用云端工作流处理
                            |           |
                            |           +--> 否 --> 使用边缘工作流处理
                            |
                            +--> 否 --> 使用边缘工作流处理
```

## 6. 工作流分层关系（文本形式）

```text
云端工作流层:
- 复杂场景协调
- 多家庭/多地点协同
- 数据分析驱动决策
- 长期运行工作流
- 资源密集型处理

边缘工作流层:
- 房间级场景管理
- 多设备协调
- 中等复杂度条件评估
- 本地数据分析
- 离线可靠性保障

设备工作流层:
- 单设备逻辑
- 简单触发响应
- 最小延迟要求
- 安全关键操作
- 极低资源消耗
```

这些文本形式的架构图描述了智能家居系统与Temporal工作流引擎的集成方案，
包括系统的物理部署、组件关系、数据流程和决策逻辑。
该架构充分利用了云端、边缘和设备三层结构的优势，确保系统的响应性和可靠性，同时满足智能家居场景的复杂需求。
