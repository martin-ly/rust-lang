# golang与工作流架构的深入分析

## 目录

1. **工作流架构概述**
   - 1.1 工作流模型基础
   - 1.2 工作流架构设计原则
   - 1.3 工作流引擎关键功能

2. **Golang控制流机制**
   - 2.1 控制结构
   - 2.2 错误处理
   - 2.3 接口与多态
   - 2.4 并发机制
   - 2.5 上下文管理

3. **Golang与工作流模型的映射**
   - 3.1 类型系统映射
   - 3.2 控制流与工作流状态转换
   - 3.3 资源管理映射
   - 3.4 事件驱动工作流

4. **工作流模型的Golang实现**
   - 4.1 状态图工作流的Golang实现
   - 4.2 Petri网模型的Golang实现
   - 4.3 BPMN模型的Golang实现
   - 4.4 工作流可视化与监控
   - 4.5 Golang工作流实现的总结与实践建议

## 2. Golang控制流机制

### 2.1 控制结构

Golang提供了简洁但强大的控制流结构，支持工作流中的决策和迭代处理：

```go
// 条件语句
func conditionalFlow(status string) string {
    if status == "PENDING" {
        return "处理待处理订单"
    } else if status == "PROCESSING" {
        return "继续处理中的订单"
    } else {
        return "处理其他状态订单"
    }
}

// 多条件分支
func switchFlow(status string) string {
    switch status {
    case "PENDING":
        return "处理待处理订单"
    case "PROCESSING":
        return "继续处理中的订单"
    case "COMPLETED":
        return "订单已完成"
    case "CANCELLED":
        return "订单已取消"
    default:
        return "未知订单状态"
    }
}

// 循环处理
func iterationFlow(items []string) {
    // 基本for循环
    for i := 0; i < len(items); i++ {
        fmt.Printf("处理项目 %d: %s\n", i, items[i])
    }
    
    // 范围循环
    for index, item := range items {
        fmt.Printf("范围处理项目 %d: %s\n", index, item)
    }
    
    // 无限循环（带条件退出）
    count := 0
    for {
        if count >= 5 {
            break
        }
        fmt.Printf("循环计数: %d\n", count)
        count++
    }
}
```

### 2.2 错误处理

Golang的错误处理方式非常适合工作流中的错误管理和异常流程：

```go
// 基本错误处理
func processOrder(orderID string) error {
    order, err := loadOrder(orderID)
    if err != nil {
        return fmt.Errorf("加载订单失败: %w", err)
    }
    
    err = validateOrder(order)
    if err != nil {
        return fmt.Errorf("订单验证失败: %w", err)
    }
    
    err = processPayment(order)
    if err != nil {
        return fmt.Errorf("支付处理失败: %w", err)
    }
    
    return nil
}

// 自定义错误类型
type OrderError struct {
    OrderID string
    Message string
    Code    int
}

func (e *OrderError) Error() string {
    return fmt.Sprintf("订单 %s 错误(%d): %s", e.OrderID, e.Code, e.Message)
}

// 错误类型检查
func handleOrderProcessing(orderID string) {
    err := processOrder(orderID)
    if err != nil {
        var orderErr *OrderError
        if errors.As(err, &orderErr) {
            fmt.Printf("订单特定错误处理: %v\n", orderErr)
        } else if errors.Is(err, ErrInsufficientFunds) {
            fmt.Println("资金不足错误处理")
        } else {
            fmt.Printf("通用错误处理: %v\n", err)
        }
    }
}

// 使用defer进行清理
func processWithCleanup(filename string) error {
    file, err := os.Open(filename)
    if err != nil {
        return err
    }
    defer file.Close() // 确保函数返回前关闭文件
    
    // 文件处理逻辑...
    return nil
}
```

### 2.3 接口与多态

Golang的接口系统非常适合工作流组件的抽象和替换：

```go
// 活动接口
type Activity interface {
    Execute(ctx context.Context) error
    GetName() string
}

// 具体活动实现
type PaymentActivity struct {
    Amount   float64
    CustomerID string
}

func (a *PaymentActivity) Execute(ctx context.Context) error {
    fmt.Printf("处理客户 %s 的 %.2f 支付\n", a.CustomerID, a.Amount)
    // 实际支付处理逻辑
    return nil
}

func (a *PaymentActivity) GetName() string {
    return "支付处理"
}

// 另一个活动实现
type ShippingActivity struct {
    OrderID   string
    Address   string
}

func (a *ShippingActivity) Execute(ctx context.Context) error {
    fmt.Printf("为订单 %s 创建发货到 %s\n", a.OrderID, a.Address)
    // 实际物流处理逻辑
    return nil
}

func (a *ShippingActivity) GetName() string {
    return "物流处理"
}

// 工作流执行器
type WorkflowExecutor struct {
    activities []Activity
}

func (w *WorkflowExecutor) AddActivity(activity Activity) {
    w.activities = append(w.activities, activity)
}

func (w *WorkflowExecutor) ExecuteAll(ctx context.Context) error {
    for _, activity := range w.activities {
        fmt.Printf("执行活动: %s\n", activity.GetName())
        if err := activity.Execute(ctx); err != nil {
            return fmt.Errorf("活动 %s 执行失败: %w", activity.GetName(), err)
        }
    }
    return nil
}
```

### 2.4 并发机制

Golang的goroutines和channels为工作流提供了强大的并发处理能力：

```go
// 并行活动执行
func executeParallelActivities(ctx context.Context, activities []Activity) error {
    var wg sync.WaitGroup
    errChan := make(chan error, len(activities))
    
    for _, activity := range activities {
        wg.Add(1)
        go func(act Activity) {
            defer wg.Done()
            fmt.Printf("并行执行活动: %s\n", act.GetName())
            if err := act.Execute(ctx); err != nil {
                errChan <- fmt.Errorf("活动 %s 执行失败: %w", act.GetName(), err)
            }
        }(activity)
    }
    
    // 等待所有活动完成
    wg.Wait()
    close(errChan)
    
    // 检查错误
    for err := range errChan {
        return err // 返回第一个错误
    }
    
    return nil
}

// 使用channel进行协调
func coordinatedActivities(ctx context.Context, activities []Activity) error {
    results := make(chan struct{
        name string
        err  error
    }, len(activities))
    
    for _, activity := range activities {
        go func(act Activity) {
            err := act.Execute(ctx)
            results <- struct {
                name string
                err  error
            }{act.GetName(), err}
        }(activity)
    }
    
    // 收集结果
    for i := 0; i < len(activities); i++ {
        result := <-results
        if result.err != nil {
            return fmt.Errorf("活动 %s 失败: %w", result.name, result.err)
        }
        fmt.Printf("活动 %s 已完成\n", result.name)
    }
    
    return nil
}

// 使用select处理多种情况
func selectTimeout(ctx context.Context, activity Activity, timeout time.Duration) error {
    resultChan := make(chan error, 1)
    
    go func() {
        resultChan <- activity.Execute(ctx)
    }()
    
    select {
    case err := <-resultChan:
        return err
    case <-time.After(timeout):
        return fmt.Errorf("活动 %s 执行超时", activity.GetName())
    case <-ctx.Done():
        return ctx.Err()
    }
}
```

### 2.5 上下文管理

Golang的context包为工作流提供了取消、超时和值传递机制：

```go
// 带超时的上下文
func executeWithTimeout(activity Activity, timeout time.Duration) error {
    ctx, cancel := context.WithTimeout(context.Background(), timeout)
    defer cancel() // 确保资源释放
    
    return activity.Execute(ctx)
}

// 带取消的上下文
func executeCancellable(activities []Activity) error {
    ctx, cancel := context.WithCancel(context.Background())
    defer cancel()
    
    for i, activity := range activities {
        if err := activity.Execute(ctx); err != nil {
            fmt.Printf("活动 %d 失败，取消后续活动\n", i)
            cancel() // 取消所有挂起的活动
            return err
        }
    }
    
    return nil
}

// 上下文值传递
func executeWithValues(activity Activity, userID, traceID string) error {
    ctx := context.Background()
    ctx = context.WithValue(ctx, "userID", userID)
    ctx = context.WithValue(ctx, "traceID", traceID)
    
    return activity.Execute(ctx)
}

// 使用上下文值
type LoggingActivity struct {
    Name string
}

func (a *LoggingActivity) Execute(ctx context.Context) error {
    userID, ok := ctx.Value("userID").(string)
    if !ok {
        userID = "unknown"
    }
    
    traceID, _ := ctx.Value("traceID").(string)
    
    fmt.Printf("[用户: %s, 跟踪ID: %s] 执行活动: %s\n", 
               userID, traceID, a.Name)
    return nil
}

func (a *LoggingActivity) GetName() string {
    return a.Name
}
```

## 3. Golang与工作流模型的映射

### 3.1 类型系统映射

Golang的类型系统可以有效表示工作流中的各种实体：

```go
// 工作流状态定义
type WorkflowStatus string

const (
    StatusCreated    WorkflowStatus = "CREATED"
    StatusProcessing WorkflowStatus = "PROCESSING"
    StatusCompleted  WorkflowStatus = "COMPLETED"
    StatusFailed     WorkflowStatus = "FAILED"
)

// 工作流节点类型
type NodeType string

const (
    NodeTypeTask      NodeType = "TASK"
    NodeTypeDecision  NodeType = "DECISION"
    NodeTypeParallel  NodeType = "PARALLEL"
    NodeTypeJoin      NodeType = "JOIN"
    NodeTypeStart     NodeType = "START"
    NodeTypeEnd       NodeType = "END"
)

// 工作流定义
type WorkflowDefinition struct {
    ID          string
    Name        string
    Description string
    Nodes       map[string]*WorkflowNode
    Edges       []*WorkflowEdge
    StartNode   string
}

// 工作流节点
type WorkflowNode struct {
    ID          string
    Name        string
    Type        NodeType
    Properties  map[string]interface{}
    Activity    Activity // 可执行活动
}

// 工作流边（连接）
type WorkflowEdge struct {
    ID          string
    SourceNode  string
    TargetNode  string
    Condition   func(ctx WorkflowContext) bool // 可选条件
}

// 工作流实例上下文
type WorkflowContext struct {
    InstanceID  string
    Status      WorkflowStatus
    Variables   map[string]interface{}
    CurrentNode string
    History     []string // 节点执行历史
}

// 工作流活动
type Activity interface {
    Execute(ctx context.Context, wfCtx *WorkflowContext) error
    Compensate(ctx context.Context, wfCtx *WorkflowContext) error // 补偿活动
}
```

### 3.2 控制流与工作流状态转换

```go
// 工作流引擎
type WorkflowEngine struct {
    definitions map[string]*WorkflowDefinition
    instances   map[string]*WorkflowContext
    activities  map[string]Activity
}

// 创建新工作流引擎
func NewWorkflowEngine() *WorkflowEngine {
    return &WorkflowEngine{
        definitions: make(map[string]*WorkflowDefinition),
        instances:   make(map[string]*WorkflowContext),
        activities:  make(map[string]Activity),
    }
}

// 注册工作流定义
func (engine *WorkflowEngine) RegisterWorkflow(workflow *WorkflowDefinition) {
    engine.definitions[workflow.ID] = workflow
}

// 注册活动
func (engine *WorkflowEngine) RegisterActivity(id string, activity Activity) {
    engine.activities[id] = activity
}

// 启动工作流实例
func (engine *WorkflowEngine) StartWorkflow(definitionID string, variables map[string]interface{}) (string, error) {
    definition, ok := engine.definitions[definitionID]
    if !ok {
        return "", fmt.Errorf("工作流定义不存在: %s", definitionID)
    }
    
    instanceID := fmt.Sprintf("%s-%s", definitionID, uuid.New().String())
    
    // 创建工作流上下文
    wfCtx := &WorkflowContext{
        InstanceID:  instanceID,
        Status:      StatusCreated,
        Variables:   variables,
        CurrentNode: definition.StartNode,
        History:     []string{},
    }
    
    engine.instances[instanceID] = wfCtx
    
    // 执行开始节点
    return instanceID, engine.executeNode(context.Background(), instanceID, definition.StartNode)
}

// 执行节点
func (engine *WorkflowEngine) executeNode(ctx context.Context, instanceID, nodeID string) error {
    wfCtx, ok := engine.instances[instanceID]
    if !ok {
        return fmt.Errorf("工作流实例不存在: %s", instanceID)
    }
    
    definition, ok := engine.definitions[strings.Split(instanceID, "-")[0]]
    if !ok {
        return fmt.Errorf("工作流定义不存在")
    }
    
    node, ok := definition.Nodes[nodeID]
    if !ok {
        return fmt.Errorf("节点不存在: %s", nodeID)
    }
    
    // 更新工作流状态
    wfCtx.Status = StatusProcessing
    wfCtx.CurrentNode = nodeID
    wfCtx.History = append(wfCtx.History, nodeID)
    
    fmt.Printf("执行节点: %s (%s)\n", node.Name, node.ID)
    
    // 根据节点类型处理
    switch node.Type {
    case NodeTypeTask:
        activityID, ok := node.Properties["activityRef"].(string)
        if !ok {
            return fmt.Errorf("任务节点缺少活动引用")
        }
        
        activity, ok := engine.activities[activityID]
        if !ok {
            return fmt.Errorf("活动不存在: %s", activityID)
        }
        
        // 执行活动
        if err := activity.Execute(ctx, wfCtx); err != nil {
            wfCtx.Status = StatusFailed
            return fmt.Errorf("活动执行失败: %w", err)
        }
        
    case NodeTypeDecision:
        // 不执行任何活动，只评估条件
    
    case NodeTypeParallel:
        // 并行执行所有出边
        var wg sync.WaitGroup
        errChan := make(chan error, len(definition.Edges))
        
        for _, edge := range definition.Edges {
            if edge.SourceNode == nodeID {
                wg.Add(1)
                go func(targetNodeID string) {
                    defer wg.Done()
                    if err := engine.executeNode(ctx, instanceID, targetNodeID); err != nil {
                        errChan <- err
                    }
                }(edge.TargetNode)
            }
        }
        
        wg.Wait()
        close(errChan)
        
        // 检查错误
        for err := range errChan {
            wfCtx.Status = StatusFailed
            return err
        }
        
        return nil
        
    case NodeTypeJoin:
        // 检查所有入边是否都已执行
        // 这里简化处理，实际应该检查所有入边源节点是否都已执行
        
    case NodeTypeEnd:
        wfCtx.Status = StatusCompleted
        return nil
    }
    
    // 查找并执行下一个节点
    for _, edge := range definition.Edges {
        if edge.SourceNode == nodeID {
            // 如果有条件，评估条件
            if edge.Condition != nil {
                if !edge.Condition(*wfCtx) {
                    continue // 条件不满足，跳过此边
                }
            }
            
            // 执行下一个节点
            return engine.executeNode(ctx, instanceID, edge.TargetNode)
        }
    }
    
    // 如果没有出边且不是结束节点，可能是配置错误
    if node.Type != NodeTypeEnd {
        return fmt.Errorf("节点没有出边: %s", nodeID)
    }
    
    return nil
}
```

### 3.3 资源管理映射

```go
// 资源管理器
type ResourceManager struct {
    mu sync.RWMutex
    resources map[string]interface{}
    locks     map[string]bool
}

func NewResourceManager() *ResourceManager {
    return &ResourceManager{
        resources: make(map[string]interface{}),
        locks:     make(map[string]bool),
    }
}

// 分配资源
func (rm *ResourceManager) Allocate(resourceID string, value interface{}) error {
    rm.mu.Lock()
    defer rm.mu.Unlock()
    
    if _, exists := rm.resources[resourceID]; exists {
        return fmt.Errorf("资源已存在: %s", resourceID)
    }
    
    rm.resources[resourceID] = value
    return nil
}

// 获取资源
func (rm *ResourceManager) Get(resourceID string) (interface{}, error) {
    rm.mu.RLock()
    defer rm.mu.RUnlock()
    
    resource, exists := rm.resources[resourceID]
    if !exists {
        return nil, fmt.Errorf("资源不存在: %s", resourceID)
    }
    
    return resource, nil
}

// 更新资源
func (rm *ResourceManager) Update(resourceID string, value interface{}) error {
    rm.mu.Lock()
    defer rm.mu.Unlock()
    
    if _, exists := rm.resources[resourceID]; !exists {
        return fmt.Errorf("资源不存在: %s", resourceID)
    }
    
    rm.resources[resourceID] = value
    return nil
}

// 释放资源
func (rm *ResourceManager) Release(resourceID string) error {
    rm.mu.Lock()
    defer rm.mu.Unlock()
    
    if _, exists := rm.resources[resourceID]; !exists {
        return fmt.Errorf("资源不存在: %s", resourceID)
    }
    
    delete(rm.resources, resourceID)
    return nil
}

// 锁定资源（用于事务）
func (rm *ResourceManager) Lock(resourceID string) error {
    rm.mu.Lock()
    defer rm.mu.Unlock()
    
    if locked, exists := rm.locks[resourceID]; exists && locked {
        return fmt.Errorf("资源已锁定: %s", resourceID)
    }
    
    rm.locks[resourceID] = true
    return nil
}

// 解锁资源
func (rm *ResourceManager) Unlock(resourceID string) error {
    rm.mu.Lock()
    defer rm.mu.Unlock()
    
    if locked, exists := rm.locks[resourceID]; !exists || !locked {
        return fmt.Errorf("资源未锁定: %s", resourceID)
    }
    
    rm.locks[resourceID] = false
    return nil
}

// 资源管理活动
type ResourceActivity struct {
    ResourceManager *ResourceManager
    ResourceID      string
    Operation       string // "allocate", "update", "release"
    Value           interface{}
}

func (a *ResourceActivity) Execute(ctx context.Context, wfCtx *WorkflowContext) error {
    switch a.Operation {
    case "allocate":
        return a.ResourceManager.Allocate(a.ResourceID, a.Value)
    case "update":
        return a.ResourceManager.Update(a.ResourceID, a.Value)
    case "release":
        return a.ResourceManager.Release(a.ResourceID)
    default:
        return fmt.Errorf("未知资源操作: %s", a.Operation)
    }
}

func (a *ResourceActivity) Compensate(ctx context.Context, wfCtx *WorkflowContext) error {
    // 补偿逻辑取决于操作类型
    switch a.Operation {
    case "allocate":
        return a.ResourceManager.Release(a.ResourceID)
    case "update":
        // 从上下文中获取原始值
        originalValue, ok := wfCtx.Variables["original_"+a.ResourceID]
        if !ok {
            return fmt.Errorf("无法补偿更新，找不到原始值")
        }
        return a.ResourceManager.Update(a.ResourceID, originalValue)
    case "release":
        // 释放的补偿是重新分配，但需要原始值
        originalValue, ok := wfCtx.Variables["original_"+a.ResourceID]
        if !ok {
            return fmt.Errorf("无法补偿释放，找不到原始值")
        }
        return a.ResourceManager.Allocate(a.ResourceID, originalValue)
    default:
        return fmt.Errorf("未知资源操作: %s", a.Operation)
    }
}
```

### 3.4 事件驱动工作流

```go
// 事件类型
type EventType string

const (
    EventOrderCreated     EventType = "ORDER_CREATED"
    EventPaymentReceived  EventType = "PAYMENT_RECEIVED"
    EventInventoryUpdated EventType = "INVENTORY_UPDATED"
    EventOrderShipped     EventType = "ORDER_SHIPPED"
    EventOrderCompleted   EventType = "ORDER_COMPLETED"
)

// 事件结构
type Event struct {
    Type      EventType
    Payload   map[string]interface{}
    Timestamp time.Time
}

// 事件处理器接口
type EventHandler interface {
    HandleEvent(ctx context.Context, event Event) error
}

// 事件发布者
type EventPublisher struct {
    subscribers map[EventType][]EventHandler
    mu          sync.RWMutex
}

func NewEventPublisher() *EventPublisher {
    return &EventPublisher{
        subscribers: make(map[EventType][]EventHandler),
    }
}

// 订阅事件
func (pub *EventPublisher) Subscribe(eventType EventType, handler EventHandler) {
    pub.mu.Lock()
    defer pub.mu.Unlock()
    
    pub.subscribers[eventType] = append(pub.subscribers[eventType], handler)
}

// 发布事件
func (pub *EventPublisher) Publish(ctx context.Context, event Event) error {
    pub.mu.RLock()
    handlers, exists := pub.subscribers[event.Type]
    pub.mu.RUnlock()
    
    if !exists {
        return nil // 没有订阅者，不是错误
    }
    
    var wg sync.WaitGroup
    errChan := make(chan error, len(handlers))
    
    for _, handler := range handlers {
        wg.Add(1)
        go func(h EventHandler) {
            defer wg.Done()
            if err := h.HandleEvent(ctx, event); err != nil {
                errChan <- err
            }
        }(handler)
    }
    
    wg.Wait()
    close(errChan)
    
    // 收集错误
    var errs []error
    for err := range errChan {
        errs = append(errs, err)
    }
    
    if len(errs) > 0 {
        return fmt.Errorf("事件处理错误: %v", errs)
    }
    
    return nil
}

// 工作流事件处理器
type WorkflowEventHandler struct {
    Engine *WorkflowEngine
    WorkflowID string
    NodeMapping map[EventType]string // 事件类型到节点ID的映射
}

func (wh *WorkflowEventHandler) HandleEvent(ctx context.Context, event Event) error {
    nodeID, exists := wh.NodeMapping[event.Type]
    if !exists {
        return fmt.Errorf("事件类型未映射到工作流节点: %s", event.Type)
    }
    
    // 查找工作流实例
    instanceID := ""
    for id, instance := range wh.Engine.instances {
        if strings.HasPrefix(id, wh.WorkflowID+"-") {
            // 找到一个匹配的实例
            // 在实际应用中，可能需要更精确的匹配逻辑
            instanceID = id
            break
        }
    }
    
    if instanceID == "" {
        // 创建新的工作流实例
        var err error
        instanceID, err = wh.Engine.StartWorkflow(wh.WorkflowID, event.Payload)
        if err != nil {
            return fmt.Errorf("无法启动工作流: %w", err)
        }
    } else {
        // 更新现有实例的变量
        instance := wh.Engine.instances[instanceID]
        for key, value := range event.Payload {
            instance.Variables[key] = value
        }
        
        // 触发指定节点
        if err := wh.Engine.executeNode(ctx, instanceID, nodeID); err != nil {
            return fmt.Errorf("无法执行节点: %w", err)
        }
    }
    
    return nil
}

// 异步工作流执行
func executeWorkflowAsync(engine *WorkflowEngine, definitionID string, variables map[string]interface{}) chan error {
    resultChan := make(chan error, 1)
    
    go func() {
        instanceID, err := engine.StartWorkflow(definitionID, variables)
        if err != nil {
            resultChan <- err
            return
        }
        
        // 轮询工作流完成状态
        ticker := time.NewTicker(500 * time.Millisecond)
        defer ticker.Stop()
        
        timeout := time.After(5 * time.Minute)
        
        for {
            select {
            case <-ticker.C:
                instance, exists := engine.instances[instanceID]
                if !exists {
                    resultChan <- fmt.Errorf("工作流实例不存在")
                    return
                }
                
                if instance.Status == StatusCompleted {
                    resultChan <- nil
                    return
                } else if instance.Status == StatusFailed {
                    resultChan <- fmt.Errorf("工作流执行失败")
                    return
                }
                
            case <-timeout:
                resultChan <- fmt.Errorf("工作流执行超时")
                return
            }
        }
    }()
    
    return resultChan
}
```

## 4. 工作流模型的Golang实现

### 4.1 状态图工作流的Golang实现

```go
// 状态定义
type State struct {
    ID        string
    Name      string
    IsInitial bool
    IsFinal   bool
}

// 事件定义
type Event struct {
    ID   string
    Name string
}

// 守卫条件
type Guard struct {
    ID        string
    Condition string
    Evaluate  func(context map[string]string) bool
}

// 动作定义
type Action struct {
    ID      string
    Name    string
    Execute func(context map[string]string) error
}

// 转换定义
type Transition struct {
    ID      string
    Source  State
    Target  State
    Event   Event
    Guard   *Guard
    Actions []Action
}

// 状态机定义
type StateMachine struct {
    ID           string
    Name         string
    States       map[string]State
    Events       map[string]Event
    Transitions  map[string]Transition
    CurrentState *State
    Context      map[string]string
}

// 创建新状态机
func NewStateMachine(id, name string) *StateMachine {
    return &StateMachine{
        ID:          id,
        Name:        name,
        States:      make(map[string]State),
        Events:      make(map[string]Event),
        Transitions: make(map[string]Transition),
        Context:     make(map[string]string),
    }
}

// 添加状态
func (sm *StateMachine) AddState(id, name string, isInitial, isFinal bool) State {
    state := State{
        ID:        id,
        Name:      name,
        IsInitial: isInitial,
        IsFinal:   isFinal,
    }
    
    sm.States[id] = state
    
    if isInitial && sm.CurrentState == nil {
        sm.CurrentState = &state
    }
    
    return state
}

// 添加事件
func (sm *StateMachine) AddEvent(id, name string) Event {
    event := Event{
        ID:   id,
        Name: name,
    }
    
    sm.Events[id] = event
    return event
}

// 添加守卫条件
func (sm *StateMachine) AddGuard(id, condition string, evaluate func(context map[string]string) bool) Guard {
    guard := Guard{
        ID:        id,
        Condition: condition,
        Evaluate:  evaluate,
    }
    
    return guard
}

// 添加动作
func (sm *StateMachine) AddAction(id, name string, execute func(context map[string]string) error) Action {
    action := Action{
        ID:      id,
        Name:    name,
        Execute: execute,
    }
    
    return action
}

// 添加转换
func (sm *StateMachine) AddTransition(id string, source, target State, event Event, guard *Guard, actions []Action) Transition {
    transition := Transition{
        ID:      id,
        Source:  source,
        Target:  target,
        Event:   event,
        Guard:   guard,
        Actions: actions,
    }
    
    sm.Transitions[id] = transition
    return transition
}

// 初始化状态机
func (sm *StateMachine) Initialize() error {
    // 查找初始状态
    var initialState *State
    for _, state := range sm.States {
        if state.IsInitial {
            stateCopy := state
            initialState = &stateCopy
            break
        }
    }
    
    if initialState == nil {
        return fmt.Errorf("没有定义初始状态")
    }
    
    sm.CurrentState = initialState
    return nil
}

// 触发事件
func (sm *StateMachine) Trigger(eventID string) (*State, error) {
    if sm.CurrentState == nil {
        return nil, fmt.Errorf("状态机未初始化")
    }
    
    // 查找匹配的转换
    var applicableTransitions []Transition
    for _, transition := range sm.Transitions {
        if transition.Source.ID == sm.CurrentState.ID && transition.Event.ID == eventID {
            applicableTransitions = append(applicableTransitions, transition)
        }
    }
    
    if len(applicableTransitions) == 0 {
        return nil, fmt.Errorf("当前状态 %s 下没有找到事件 %s 的转换", 
                             sm.CurrentState.Name, eventID)
    }
    
    // 查找第一个满足守卫条件的转换
    var selectedTransition *Transition
    for _, transition := range applicableTransitions {
        transitionCopy := transition
        if transitionCopy.Guard == nil || transitionCopy.Guard.Evaluate(sm.Context) {
            selectedTransition = &transitionCopy
            break
        }
    }
    
    if selectedTransition == nil {
        return nil, fmt.Errorf("未找到满足条件的转换")
    }
    
    // 执行转换上的动作
    for _, action := range selectedTransition.Actions {
        if err := action.Execute(sm.Context); err != nil {
            return nil, fmt.Errorf("执行动作 %s 失败: %w", action.Name, err)
        }
    }
    
    // 更新当前状态
    targetState := sm.States[selectedTransition.Target.ID]
    sm.CurrentState = &targetState
    
    return sm.CurrentState, nil
}

// 检查是否处于最终状态
func (sm *StateMachine) IsCompleted() bool {
    if sm.CurrentState == nil {
        return false
    }
    
    return sm.CurrentState.IsFinal
}

// 获取当前状态
func (sm *StateMachine) GetCurrentState() *State {
    return sm.CurrentState
}

// 获取上下文变量
func (sm *StateMachine) GetContext() map[string]string {
    return sm.Context
}

// 设置上下文变量
func (sm *StateMachine) SetContextVar(key, value string) {
    sm.Context[key] = value
}

// 工作流状态图构建器
type WorkflowStateMachineBuilder struct {
    stateMachine *StateMachine
}

func NewWorkflowStateMachineBuilder(id, name string) *WorkflowStateMachineBuilder {
    return &WorkflowStateMachineBuilder{
        stateMachine: NewStateMachine(id, name),
    }
}

// 添加工作流状态
func (b *WorkflowStateMachineBuilder) AddWorkflowState(id, name string, isInitial, isFinal bool) State {
    return b.stateMachine.AddState(id, name, isInitial, isFinal)
}

// 添加工作流事件
func (b *WorkflowStateMachineBuilder) AddWorkflowEvent(id, name string) Event {
    return b.stateMachine.AddEvent(id, name)
}

// 添加工作流守卫条件
func (b *WorkflowStateMachineBuilder) AddWorkflowGuard(id, condition string) Guard {
    return b.stateMachine.AddGuard(id, condition, func(context map[string]string) bool {
        // 简化实现，实际应用中应使用更复杂的条件评估器
        switch condition {
        case "payment_verified":
            return context["payment_status"] == "verified"
        case "inventory_available":
            return context["inventory_status"] == "available"
        case "amount_over_threshold":
            amount, err := strconv.ParseFloat(context["amount"], 64)
            if err != nil {
                return false
            }
            return amount > 1000.0
        default:
            return false
        }
    })
}

// 添加工作流动作
func (b *WorkflowStateMachineBuilder) AddWorkflowAction(id, name string) Action {
    return b.stateMachine.AddAction(id, name, func(context map[string]string) error {
        // 模拟执行动作
        fmt.Printf("执行动作: %s\n", name)
        
        switch name {
        case "process_payment":
            context["payment_status"] = "processing"
            // 模拟处理延迟
            time.Sleep(100 * time.Millisecond)
            context["payment_status"] = "verified"
            return nil
            
        case "check_inventory":
            context["inventory_status"] = "checking"
            // 模拟处理延迟
            time.Sleep(50 * time.Millisecond)
            context["inventory_status"] = "available"
            return nil
            
        case "reserve_inventory":
            if context["inventory_status"] == "available" {
                context["inventory_status"] = "reserved"
                return nil
            }
            return fmt.Errorf("库存不可用")
            
        case "ship_order":
            context["shipping_status"] = "shipped"
            context["tracking_number"] = "TRK12345"
            return nil
            
        case "send_confirmation":
            context["notification_sent"] = "true"
            return nil
            
        case "cancel_order":
            context["order_status"] = "cancelled"
            return nil
            
        default:
            return fmt.Errorf("未知动作: %s", name)
        }
    })
}

// 添加工作流转换
func (b *WorkflowStateMachineBuilder) AddWorkflowTransition(
    id string, 
    source State, 
    target State, 
    event Event,
    guard *Guard,
    actions []Action,
) Transition {
    return b.stateMachine.AddTransition(id, source, target, event, guard, actions)
}

// 构建订单处理工作流
func (b *WorkflowStateMachineBuilder) BuildOrderProcessingWorkflow() *WorkflowStateMachineBuilder {
    // 添加状态
    created := b.AddWorkflowState("created", "订单创建", true, false)
    validated := b.AddWorkflowState("validated", "订单验证", false, false)
    paymentProcessing := b.AddWorkflowState("payment_processing", "支付处理中", false, false)
    inventoryChecking := b.AddWorkflowState("inventory_checking", "库存检查中", false, false)
    readyForShipment := b.AddWorkflowState("ready_for_shipment", "准备发货", false, false)
    shipped := b.AddWorkflowState("shipped", "已发货", false, false)
    completed := b.AddWorkflowState("completed", "已完成", false, true)
    cancelled := b.AddWorkflowState("cancelled", "已取消", false, true)
    
    // 添加事件
    validate := b.AddWorkflowEvent("validate", "验证订单")
    processPayment := b.AddWorkflowEvent("process_payment", "处理支付")
    checkInventory := b.AddWorkflowEvent("check_inventory", "检查库存")
    prepareShipment := b.AddWorkflowEvent("prepare_shipment", "准备发货")
    ship := b.AddWorkflowEvent("ship", "发货")
    complete := b.AddWorkflowEvent("complete", "完成订单")
    cancel := b.AddWorkflowEvent("cancel", "取消订单")
    
    // 添加守卫
    paymentVerified := b.AddWorkflowGuard("payment_verified", "payment_verified")
    inventoryAvailable := b.AddWorkflowGuard("inventory_available", "inventory_available")
    
    // 添加动作
    processPaymentAction := b.AddWorkflowAction("process_payment", "process_payment")
    checkInventoryAction := b.AddWorkflowAction("check_inventory", "check_inventory")
    reserveInventoryAction := b.AddWorkflowAction("reserve_inventory", "reserve_inventory")
    shipOrderAction := b.AddWorkflowAction("ship_order", "ship_order")
    sendConfirmationAction := b.AddWorkflowAction("send_confirmation", "send_confirmation")
    cancelOrderAction := b.AddWorkflowAction("cancel_order", "cancel_order")
    
    // 添加转换
    b.AddWorkflowTransition(
        "validate_order", 
        created, 
        validated, 
        validate, 
        nil, 
        []Action{},
    )
    
    b.AddWorkflowTransition(
        "start_payment", 
        validated, 
        paymentProcessing, 
        processPayment, 
        nil, 
        []Action{processPaymentAction},
    )
    
    b.AddWorkflowTransition(
        "payment_successful", 
        paymentProcessing, 
        inventoryChecking, 
        checkInventory, 
        &paymentVerified, 
        []Action{checkInventoryAction},
    )
    
    b.AddWorkflowTransition(
        "payment_failed", 
        paymentProcessing, 
        cancelled, 
        cancel, 
        nil, 
        []Action{cancelOrderAction},
    )
    
    b.AddWorkflowTransition(
        "inventory_confirmed", 
        inventoryChecking, 
        readyForShipment, 
        prepareShipment, 
        &inventoryAvailable, 
        []Action{reserveInventoryAction},
    )
    
    b.AddWorkflowTransition(
        "inventory_unavailable", 
        inventoryChecking, 
        cancelled, 
        cancel, 
        nil, 
        []Action{cancelOrderAction},
    )
    
    b.AddWorkflowTransition(
        "ship_order", 
        readyForShipment, 
        shipped, 
        ship, 
        nil, 
        []Action{shipOrderAction},
    )
    
    b.AddWorkflowTransition(
        "complete_order", 
        shipped, 
        completed, 
        complete, 
        nil, 
        []Action{sendConfirmationAction},
    )
    
    b.AddWorkflowTransition(
        "cancel_at_any_time", 
        validated, 
        cancelled, 
        cancel, 
        nil, 
        []Action{cancelOrderAction},
    )
    
    return b
}

// 获取构建的状态机
func (b *WorkflowStateMachineBuilder) Build() *StateMachine {
    return b.stateMachine
}

// 状态图分析工具
type StateMachineAnalyzer struct {
    stateMachine *StateMachine
}

func NewStateMachineAnalyzer(stateMachine *StateMachine) *StateMachineAnalyzer {
    return &StateMachineAnalyzer{
        stateMachine: stateMachine,
    }
}

// 检查可达性
func (a *StateMachineAnalyzer) CheckReachability() map[string]bool {
    reachable := make(map[string]bool)
    
    // 初始状态一定可达
    var initialState *State
    for _, state := range a.stateMachine.States {
        stateCopy := state
        reachable[state.ID] = false
        if state.IsInitial {
            initialState = &stateCopy
        }
    }
    
    if initialState == nil {
        return reachable
    }
    
    // 初始状态标记为可达
    reachable[initialState.ID] = true
    
    // 宽度优先搜索所有可达状态
    queue := []string{initialState.ID}
    for len(queue) > 0 {
        current := queue[0]
        queue = queue[1:]
        
        // 查找从当前状态出发的所有转换
        for _, transition := range a.stateMachine.Transitions {
            if transition.Source.ID == current {
                targetID := transition.Target.ID
                if !reachable[targetID] {
                    reachable[targetID] = true
                    queue = append(queue, targetID)
                }
            }
        }
    }
    
    return reachable
}

// 检查死锁状态（非终止且无出边）
func (a *StateMachineAnalyzer) DetectDeadlocks() []State {
    var deadlocks []State
    
    for _, state := range a.stateMachine.States {
        if state.IsFinal {
            continue // 终止状态不是死锁
        }
        
        // 检查是否有从此状态出发的转换
        hasOutgoing := false
        for _, transition := range a.stateMachine.Transitions {
            if transition.Source.ID == state.ID {
                hasOutgoing = true
                break
            }
        }
        
        if !hasOutgoing {
            deadlocks = append(deadlocks, state)
        }
    }
    
    return deadlocks
}

// 检查终止状态是否可达
func (a *StateMachineAnalyzer) CheckTermination() bool {
    reachability := a.CheckReachability()
    
    // 检查是否所有终止状态都可达
    var terminalStates []State
    for _, state := range a.stateMachine.States {
        if state.IsFinal {
            terminalStates = append(terminalStates, state)
        }
    }
    
    if len(terminalStates) == 0 {
        return false // 没有终止状态
    }
    
    // 检查是否至少有一个终止状态可达
    for _, state := range terminalStates {
        if reachable := reachability[state.ID]; reachable {
            return true
        }
    }
    
    return false
}

// 生成路径覆盖测试用例
func (a *StateMachineAnalyzer) GeneratePathCoverageTests() [][]Event {
    var testCases [][]Event
    var initialState *State
    
    for _, state := range a.stateMachine.States {
        if state.IsInitial {
            stateCopy := state
            initialState = &stateCopy
            break
        }
    }
    
    if initialState == nil {
        return testCases
    }
    
    visited := make(map[string]bool)
    var path []Event
    
    a.generatePaths(initialState.ID, path, visited, &testCases)
    
    return testCases
}

func (a *StateMachineAnalyzer) generatePaths(
    currentID string, 
    path []Event, 
    visited map[string]bool,
    testCases *[][]Event,
) {
    // 避免循环
    if visited[currentID] {
        return
    }
    
    visited[currentID] = true
    defer func() { visited[currentID] = false }()
    
    // 如果是终止状态，记录路径
    currentState := a.stateMachine.States[currentID]
    if currentState.IsFinal {
        pathCopy := make([]Event, len(path))
        copy(pathCopy, path)
        *testCases = append(*testCases, pathCopy)
    }
    
    // 遍历所有从当前状态出发的转换
    for _, transition := range a.stateMachine.Transitions {
        if transition.Source.ID == currentID {
            newPath := append(path, transition.Event)
            a.generatePaths(transition.Target.ID, newPath, visited, testCases)
        }
    }
}

// 验证状态机属性
func (a *StateMachineAnalyzer) Verify() (bool, []string) {
    var errors []string
    
    // 检查初始状态
    var initialStates []State
    for _, state := range a.stateMachine.States {
        if state.IsInitial {
            initialStates = append(initialStates, state)
        }
    }
    
    if len(initialStates) == 0 {
        errors = append(errors, "没有定义初始状态")
    } else if len(initialStates) > 1 {
        var stateNames []string
        for _, state := range initialStates {
            stateNames = append(stateNames, state.Name)
        }
        errors = append(errors, fmt.Sprintf("定义了多个初始状态: %v", stateNames))
    }
    
    // 检查终止状态
    var finalStates []State
    for _, state := range a.stateMachine.States {
        if state.IsFinal {
            finalStates = append(finalStates, state)
        }
    }
    
    if len(finalStates) == 0 {
        errors = append(errors, "没有定义终止状态")
    }
    
    // 检查可达性
    reachability := a.CheckReachability()
    var unreachableStates []string
    
    for stateID, reachable := range reachability {
        if !reachable {
            stateName := a.stateMachine.States[stateID].Name
            unreachableStates = append(unreachableStates, stateName)
        }
    }
    
    if len(unreachableStates) > 0 {
        errors = append(errors, fmt.Sprintf("检测到不可达状态: %v", unreachableStates))
    }
    
    // 检查死锁
    deadlocks := a.DetectDeadlocks()
    if len(deadlocks) > 0 {
        var deadlockNames []string
        for _, state := range deadlocks {
            deadlockNames = append(deadlockNames, state.Name)
        }
        errors = append(errors, fmt.Sprintf("检测到死锁状态: %v", deadlockNames))
    }
    
    // 检查终止性
    if !a.CheckTermination() {
        errors = append(errors, "终止问题: 不是所有路径都通向终止状态")
    }
    
    return len(errors) == 0, errors
}

// 状态图仿真运行
func SimulateOrderWorkflow() {
    builder := NewWorkflowStateMachineBuilder("order_workflow", "订单处理工作流")
    builder.BuildOrderProcessingWorkflow()
    
    workflow := builder.Build()
    err := workflow.Initialize()
    if err != nil {
        fmt.Printf("初始化工作流失败: %v\n", err)
        return
    }
    
    fmt.Printf("初始状态: %s\n", workflow.GetCurrentState().Name)
    
    // 设置订单金额
    workflow.SetContextVar("amount", "500.0")
    
    // 执行工作流
    events := []string{
        "validate",
        "process_payment",
        "check_inventory",
        "prepare_shipment",
        "ship",
        "complete",
    }
    
    for _, eventID := range events {
        newState, err := workflow.Trigger(eventID)
        if err != nil {
            fmt.Printf("触发事件 '%s' 失败: %v\n", eventID, err)
            break
        }
        
        fmt.Printf("触发事件 '%s', 新状态: %s\n", eventID, newState.Name)
        fmt.Printf("上下文: %v\n", workflow.GetContext())
    }
    
    fmt.Printf("工作流已完成: %v\n", workflow.IsCompleted())
}

// 分析工作流
func AnalyzeOrderWorkflow() {
    builder := NewWorkflowStateMachineBuilder("order_workflow", "订单处理工作流")
    builder.BuildOrderProcessingWorkflow()
    
    workflow := builder.Build()
    analyzer := NewStateMachineAnalyzer(workflow)
    
    isValid, errors := analyzer.Verify()
    if isValid {
        fmt.Println("工作流验证通过")
    } else {
        fmt.Println("工作流验证失败:")
        for _, err := range errors {
            fmt.Printf("  - %s\n", err)
        }
    }
    
    // 生成测试用例
    testCases := analyzer.GeneratePathCoverageTests()
    fmt.Printf("为路径覆盖生成了 %d 个测试用例\n", len(testCases))
    
    for i, testCase := range testCases {
        fmt.Printf("测试用例 #%d:\n", i+1)
        for j, event := range testCase {
            fmt.Printf("  步骤 %d: 触发事件 '%s'\n", j+1, event.Name)
        }
    }
}
```

### 4.2 Petri网模型的Golang实现

```go
// 库位（Place）定义
type Place struct {
    ID    string
    Name  string
    Tokens int
}

// 变迁（Transition）定义
type Transition struct {
    ID   string
    Name string
}

// 弧（Arc）定义
type Arc struct {
    ID        string
    Source    string // 源库位/变迁ID
    Target    string // 目标库位/变迁ID
    Weight    int    // 权重
    IsInhibit bool   // 是否为抑制弧
}

// 标识（Marking）定义
type Marking map[string]int

// Petri网定义
type PetriNet struct {
    ID           string
    Name         string
    Places       map[string]*Place
    Transitions  map[string]*Transition
    Arcs         map[string]*Arc
    InitialMarking Marking
    CurrentMarking Marking
}

// 创建新的Petri网
func NewPetriNet(id, name string) *PetriNet {
    return &PetriNet{
        ID:             id,
        Name:           name,
        Places:         make(map[string]*Place),
        Transitions:    make(map[string]*Transition),
        Arcs:           make(map[string]*Arc),
        InitialMarking: make(Marking),
        CurrentMarking: make(Marking),
    }
}

// 添加库位
func (pn *PetriNet) AddPlace(id, name string, initialTokens int) *Place {
    place := &Place{
        ID:     id,
        Name:   name,
        Tokens: initialTokens,
    }
    
    pn.Places[id] = place
    pn.InitialMarking[id] = initialTokens
    pn.CurrentMarking[id] = initialTokens
    
    return place
}

// 添加变迁
func (pn *PetriNet) AddTransition(id, name string) *Transition {
    transition := &Transition{
        ID:   id,
        Name: name,
    }
    
    pn.Transitions[id] = transition
    return transition
}

// 添加弧
func (pn *PetriNet) AddArc(id, source, target string, weight int, isInhibit bool) *Arc {
    arc := &Arc{
        ID:        id,
        Source:    source,
        Target:    target,
        Weight:    weight,
        IsInhibit: isInhibit,
    }
    
    pn.Arcs[id] = arc
    return arc
}

// 获取输入库位
func (pn *PetriNet) GetInputPlaces(transitionID string) []*Arc {
    var inputArcs []*Arc
    
    for _, arc := range pn.Arcs {
        if arc.Target == transitionID {
            // 源必须是库位
            if _, ok := pn.Places[arc.Source]; ok {
                inputArcs = append(inputArcs, arc)
            }
        }
    }
    
    return inputArcs
}

// 获取输出库位
func (pn *PetriNet) GetOutputPlaces(transitionID string) []*Arc {
    var outputArcs []*Arc
    
    for _, arc := range pn.Arcs {
        if arc.Source == transitionID {
            // 目标必须是库位
            if _, ok := pn.Places[arc.Target]; ok {
                outputArcs = append(outputArcs, arc)
            }
        }
    }
    
    return outputArcs
}

// 检查变迁是否激活
func (pn *PetriNet) IsEnabled(transitionID string) bool {
    inputArcs := pn.GetInputPlaces(transitionID)
    
    for _, arc := range inputArcs {
        placeID := arc.Source
        placeTokens := pn.CurrentMarking[placeID]
        
        if arc.IsInhibit {
            // 抑制弧: 如果库位标记 >= 权重，则变迁被禁用
            if placeTokens >= arc.Weight {
                return false
            }
        } else {
            // 普通弧: 如果库位标记 < 权重，则变迁被禁用
            if placeTokens < arc.Weight {
                return false
            }
        }
    }
    
    return true
}

// 触发变迁
func (pn *PetriNet) FireTransition(transitionID string) (bool, error) {
    // 检查变迁是否存在
    transition, ok := pn.Transitions[transitionID]
    if !ok {
        return false, fmt.Errorf("变迁不存在: %s", transitionID)
    }
    
    // 检查变迁是否激活
    if !pn.IsEnabled(transitionID) {
        return false, nil // 变迁未激活
    }
    
    // 获取输入和输出库位
    inputArcs := pn.GetInputPlaces(transitionID)
    outputArcs := pn.GetOutputPlaces(transitionID)
    
    // 创建新标识的副本
    newMarking := make(Marking)
    for placeID, tokens := range pn.CurrentMarking {
        newMarking[placeID] = tokens
    }
    
    // 从输入库位中移除标记
    for _, arc := range inputArcs {
        if !arc.IsInhibit { // 抑制弧不消耗标记
            placeID := arc.Source
            newMarking[placeID] -= arc.Weight
        }
    }
    
    // 向输出库位添加标记
    for _, arc := range outputArcs {
        placeID := arc.Target
        newMarking[placeID] += arc.Weight
    }
    
    // 更新当前标识
    pn.CurrentMarking = newMarking
    
    fmt.Printf("触发变迁: %s\n", transition.Name)
    return true, nil
}

// 重置网络到初始标识
func (pn *PetriNet) Reset() {
    // 复制初始标识
    pn.CurrentMarking = make(Marking)
    for placeID, tokens := range pn.InitialMarking {
        pn.CurrentMarking[placeID] = tokens
    }
}

// 获取当前标识
func (pn *PetriNet) GetMarking() Marking {
    marking := make(Marking)
    for placeID, tokens := range pn.CurrentMarking {
        marking[placeID] = tokens
    }
    return marking
}

// 获取激活的变迁
func (pn *PetriNet) GetEnabledTransitions() []*Transition {
    var enabled []*Transition
    
    for id, transition := range pn.Transitions {
        if pn.IsEnabled(id) {
            enabled = append(enabled, transition)
        }
    }
    
    return enabled
}

// 执行可达性分析
func (pn *PetriNet) AnalyzeReachability() map[string]bool {
    // 复制当前标识
    originalMarking := pn.GetMarking()
    
    // 重置到初始标识
    pn.Reset()
    
    // 已访问的标识集合
    visited := make(map[string]bool)
    
    // BFS队列
    var queue []Marking
    queue = append(queue, pn.GetMarking())
    
    // 标识序列化函数（用于map键）
    serializeMarking := func(m Marking) string {
        keys := make([]string, 0, len(m))
        for k := range m {
            keys = append(keys, k)
        }
        sort.Strings(keys)
        
        var sb strings.Builder
        for _, k := range keys {
            sb.WriteString(fmt.Sprintf("%s:%d,", k, m[k]))
        }
        return sb.String()
    }
    
    // BFS遍历
    for len(queue) > 0 {
        // 取队首标识
        currentMarking := queue[0]
        queue = queue[1:]
        
        // 设置当前标识
        pn.CurrentMarking = currentMarking
        
        // 序列化当前标识
        currentKey := serializeMarking(currentMarking)
        
        // 检查是否已访问
        if visited[currentKey] {
            continue
        }
        
        // 标记为已访问
        visited[currentKey] = true
        
        // 获取当前激活的变迁
        enabledTransitions := pn.GetEnabledTransitions()
        
        // 对每个激活的变迁，计算下一个标识
        for _, transition := range enabledTransitions {
            // 保存当前标识
            tempMarking := pn.GetMarking()
            
            // 触发变迁
            fired, _ := pn.FireTransition(transition.ID)
            if fired {
                // 添加新标识到队列
                nextMarking := pn.GetMarking()
                queue = append(queue, nextMarking)
            }
            
            // 恢复标识
            pn.CurrentMarking = tempMarking
        }
    }
    
    // 恢复原始标识
    pn.CurrentMarking = originalMarking
    
    // 返回可达性结果
    return visited
}

// 检查死锁状态
func (pn *PetriNet) DetectDeadlocks() []Marking {
    // 复制当前标识
    originalMarking := pn.GetMarking()
    
    // 重置到初始标识
    pn.Reset()
    
    // 已访问的标识集合
    visited := make(map[string]bool)
    // 死锁标识集合
    var deadlocks []Marking
    
    // BFS队列
    var queue []Marking
    queue = append(queue, pn.GetMarking())
    
    // 标识序列化函数
    serializeMarking := func(m Marking) string {
        keys := make([]string, 0, len(m))
        for k := range m {
            keys = append(keys, k)
        }
        sort.Strings(keys)
        
        var sb strings.Builder
        for _, k := range keys {
            sb.WriteString(fmt.Sprintf("%s:%d,", k, m[k]))
        }
        return sb.String()
    }
    
    // BFS遍历
    for len(queue) > 0 {
        // 取队首标识
        currentMarking := queue[0]
        queue = queue[1:]
        
        // 设置当前标识
        pn.CurrentMarking = currentMarking
        
        // 序列化当前标识
        currentKey := serializeMarking(currentMarking)
        
        // 检查是否已访问
        if visited[currentKey] {
            continue
        }
        
        // 标记为已访问
        visited[currentKey] = true
        
        // 获取当前激活的变迁
        enabledTransitions := pn.GetEnabledTransitions()
        
        // 如果没有激活的变迁，则为死锁
        if len(enabledTransitions) == 0 {
            // 检查是否为预期的终止状态
            isExpectedTermination := false
            // 这里可以添加检查逻辑，例如检查某些特定库位是否有标记
            
            if !isExpectedTermination {
                deadlocks = append(deadlocks, currentMarking)
            }
        } else {
            // 对每个激活的变迁，计算下一个标识
            for _, transition := range enabledTransitions {
                // 保存当前标识
                tempMarking := pn.GetMarking()
                
                // 触发变迁
                fired, _ := pn.FireTransition(transition.ID)
                if fired {
                    // 添加新标识到队列
                    nextMarking := pn.GetMarking()
                    queue = append(queue, nextMarking)
                }
                
                // 恢复标识
                pn.CurrentMarking = tempMarking
            }
        }
    }
    
    // 恢复原始标识
    pn.CurrentMarking = originalMarking
    
    return deadlocks
}

// 分析活性
func (pn *PetriNet) AnalyzeLiveness() map[string]bool {
    // 活性结果: 变迁ID -> 是否活跃
    result := make(map[string]bool)
    
    // 初始化所有变迁为非活跃
    for id := range pn.Transitions {
        result[id] = false
    }
    
    // 复制当前标识
    originalMarking := pn.GetMarking()
    
    // 可达标识集合
    reachabilitySet := pn.AnalyzeReachability()
    
    // 解析标识字符串为Marking对象
    parseMarking := func(s string) Marking {
        marking := make(Marking)
        parts := strings.Split(s, ",")
        for _, part := range parts {
            if part == "" {
                continue
            }
            pv := strings.Split(part, ":")
            if len(pv) == 2 {
                placeID := pv[0]
                tokens, _ := strconv.Atoi(pv[1])
                marking[placeID] = tokens
            }
        }
        return marking
    }
    
    // 检查每个变迁是否可以在某个可达标识中激活
    for markingStr := range reachabilitySet {
        m := parseMarking(markingStr)
        pn.CurrentMarking = m
        
        for id := range pn.Transitions {
            if pn.IsEnabled(id) {
                result[id] = true
            }
        }
    }
    
    // 恢复原始标识
    pn.CurrentMarking = originalMarking
    
    return result
}

// 工作流网
type WorkflowNet struct {
    PetriNet *PetriNet
    SourcePlace string
    SinkPlace  string
}

// 创建新的工作流网
func NewWorkflowNet(id, name string) *WorkflowNet {
    pn := NewPetriNet(id, name)
    
    // 添加源库位和汇库位
    source := pn.AddPlace("source", "Source", 1)
    sink := pn.AddPlace("sink", "Sink", 0)
    
    return &WorkflowNet{
        PetriNet:    pn,
        SourcePlace: source.ID,
        SinkPlace:   sink.ID,
    }
}

// 添加顺序活动
func (wn *WorkflowNet) AddSequentialActivity(id, name string) (*Place, *Place, *Transition) {
    pn := wn.PetriNet
    
    // 添加变迁
    transition := pn.AddTransition(id, name)
    
    // 添加输入输出库位
    inputPlace := pn.AddPlace(id+"_in", name+" Input", 0)
    outputPlace := pn.AddPlace(id+"_out", name+" Output", 0)
    
    // 添加弧
    pn.AddArc(id+"_arc1", inputPlace.ID, transition.ID, 1, false)
    pn.AddArc(id+"_arc2", transition.ID, outputPlace.ID, 1, false)
    
    return inputPlace, outputPlace, transition
}

// 添加AND分支
func (wn *WorkflowNet) AddAndSplit(id, name string, numBranches int) (*Place, []*Place, *Transition) {
    pn := wn.PetriNet
    
    // 添加分支变迁
    transition := pn.AddTransition(id, name)
    
    // 添加输入库位
    inputPlace := pn.AddPlace(id+"_in", name+" Input", 0)
    
    // 添加输出库位
    var outputPlaces []*Place
    for i := 0; i < numBranches; i++ {
        place := pn.AddPlace(fmt.Sprintf("%s_out_%d", id, i), fmt.Sprintf("%s Output %d", name, i), 0)
        outputPlaces = append(outputPlaces, place)
    }
    
    // 添加弧
    pn.AddArc(id+"_arc_in", inputPlace.ID, transition.ID, 1, false)
    
    for i, place := range outputPlaces {
        pn.AddArc(fmt.Sprintf("%s_arc_out_%d", id, i), transition.ID, place.ID, 1, false)
    }
    
    return inputPlace, outputPlaces, transition
}

// 添加AND汇合
func (wn *WorkflowNet) AddAndJoin(id, name string, inputPlaces []*Place) (*Place, *Transition) {
    pn := wn.PetriNet
    
    // 添加汇合变迁
    transition := pn.AddTransition(id, name)
    
    // 添加输出库位
    outputPlace := pn.AddPlace(id+"_out", name+" Output", 0)
    
    // 添加弧
    for i, place := range inputPlaces {
        pn.AddArc(fmt.Sprintf("%s_arc_in_%d", id, i), place.ID, transition.ID, 1, false)
    }
    
    pn.AddArc(id+"_arc_out", transition.ID, outputPlace.ID, 1, false)
    
    return outputPlace, transition
}

// 添加XOR分支
func (wn *WorkflowNet) AddXorSplit(id, name string, numBranches int) (*Place, []*Place, []*Transition) {
    pn := wn.PetriNet
    
    // 添加输入库位
    inputPlace := pn.AddPlace(id+"_in", name+" Input", 0)
    
    // 添加分支变迁和输出库位
    var outputPlaces []*Place
    var transitions []*Transition
    
    for i := 0; i < numBranches; i++ {
        transition := pn.AddTransition(fmt.Sprintf("%s_t_%d", id, i), fmt.Sprintf("%s Branch %d", name, i))
        place := pn.AddPlace(fmt.Sprintf("%s_out_%d", id, i), fmt.Sprintf("%s Output %d", name, i), 0)
        
        // 添加弧
        pn.AddArc(fmt.Sprintf("%s_arc_in_%d", id, i), inputPlace.ID, transition.ID, 1, false)
        pn.AddArc(fmt.Sprintf("%s_arc_out_%d", id, i), transition.ID, place.ID, 1, false)
        
        outputPlaces = append(outputPlaces, place)
        transitions = append(transitions, transition)
    }
    
    return inputPlace, outputPlaces, transitions
}

// 添加XOR汇合
func (wn *WorkflowNet) AddXorJoin(id, name string, inputPlaces []*Place) (*Place, []*Transition) {
    pn := wn.PetriNet
    
    // 添加输出库位
    outputPlace := pn.AddPlace(id+"_out", name+" Output", 0)
    
    // 为每个输入库位添加变迁
    var transitions []*Transition
    
    for i, place := range inputPlaces {
        transition := pn.AddTransition(fmt.Sprintf("%s_t_%d", id, i), fmt.Sprintf("%s Join %d", name, i))
        
        // 添加弧
        pn.AddArc(fmt.Sprintf("%s_arc_in_%d", id, i), place.ID, transition.ID, 1, false)
        pn.AddArc(fmt.Sprintf("%s_arc_out_%d", id, i), transition.ID, outputPlace.ID, 1, false)
        
        transitions = append(transitions, transition)
    }
    
    return outputPlace, transitions
}

// 连接两个节点
func (wn *WorkflowNet) Connect(sourceID, targetID string) *Arc {
    pn := wn.PetriNet
    
    arcID := fmt.Sprintf("arc_%s_to_%s", sourceID, targetID)
    return pn.AddArc(arcID, sourceID, targetID, 1, false)
}

// 检查工作流可靠性
func (wn *WorkflowNet) CheckSoundness() (bool, []string) {
    var issues []string
    
    // 1. 从初始标识开始，应该能到达最终标识
    reachabilitySet := wn.PetriNet.AnalyzeReachability()
    
    // 检查是否存在一个标识，其中只有汇库位有一个标记
    foundFinalMarking := false
    finalMarkingStr := ""
    
    // 解析标识字符串
    for markingStr := range reachabilitySet {
        parts := strings.Split(markingStr, ",")
        sinkTokens := 0
        otherTokens := 0
        
        for _, part := range parts {
            if part == "" {
                continue
            }
            
            pv := strings.Split(part, ":")
            if len(pv) == 2 {
                placeID := pv[0]
                tokens, _ := strconv.Atoi(pv[1])
                
                if placeID == wn.SinkPlace {
                    sinkTokens = tokens
                } else {
                    otherTokens += tokens
                }
            }
        }
        
        if sinkTokens == 1 && otherTokens == 0 {
            foundFinalMarking = true
            finalMarkingStr = markingStr
            break
        }
    }
    
    if !foundFinalMarking {
        issues = append(issues, "无法到达只有汇库位包含一个标记的标识")
    }
    
    // 2. 检查死锁状态
    deadlocks := wn.PetriNet.DetectDeadlocks()
    if len(deadlocks) > 0 {
        issues = append(issues, fmt.Sprintf("检测到 %d 个死锁状态", len(deadlocks)))
    }
    
    // 3. 检查变迁活性
    liveness := wn.PetriNet.AnalyzeLiveness()
    for id, isLive := range liveness {
        if !isLive {
            transition := wn.PetriNet.Transitions[id]
            issues = append(issues, fmt.Sprintf("变迁 '%s' (%s) 不是活跃的", transition.Name, id))
        }
    }
    
    return len(issues) == 0, issues
}

// 模拟工作流执行
func (wn *WorkflowNet) Simulate(maxSteps int) (bool, []string, error) {
    // 重置网络
    wn.PetriNet.Reset()
    
    var executionTrace []string
    completed := false
    
    for step := 0; step < maxSteps; step++ {
        // 获取激活的变迁
        enabled := wn.PetriNet.GetEnabledTransitions()
        
        if len(enabled) == 0 {
            // 检查是否到达终止状态
            marking := wn.PetriNet.GetMarking()
            sinkTokens := marking[wn.SinkPlace]
            otherTokens := 0
            
            for placeID, tokens := range marking {
                if placeID != wn.SinkPlace {
                    otherTokens += tokens
                }
            }
            
            if sinkTokens == 1 && otherTokens == 0 {
                completed = true
                executionTrace = append(executionTrace, "工作流成功完成")
            } else {
                return false, executionTrace, fmt.Errorf("工作流在步骤 %d 陷入死锁", step)
            }
            break
        }
        
        // 随机选择一个激活的变迁
        idx := rand.Intn(len(enabled))
        transition := enabled[idx]
        
        // 触发变迁
        fired, err := wn.PetriNet.FireTransition(transition.ID)
        if err != nil {
            return false, executionTrace, err
        }
        
        if fired {
            executionTrace = append(executionTrace, fmt.Sprintf("步骤 %d: 触发变迁 '%s'", step+1, transition.Name))
        }
    }
    
    if !completed && maxSteps > 0 {
        return false, executionTrace, fmt.Errorf("工作流在 %d 步后仍未完成", maxSteps)
    }
    
    return completed, executionTrace, nil
}

// 创建订单处理工作流Petri网
func CreateOrderProcessingPetriNet() *WorkflowNet {
    wn := NewWorkflowNet("order_process", "订单处理工作流")
    pn := wn.PetriNet
    
    // 创建顺序活动
    validateInput, validateOutput, _ := wn.AddSequentialActivity("validate", "验证订单")
    paymentInput, paymentOutput, _ := wn.AddSequentialActivity("payment", "处理支付")
    shipInput, shipOutput, _ := wn.AddSequentialActivity("shipping", "处理物流")
    notifyInput, notifyOutput, _ := wn.AddSequentialActivity("notify", "通知客户")
    
    // 连接活动
    wn.Connect(wn.SourcePlace, validateInput.ID)
    wn.Connect(validateOutput.ID, paymentInput.ID)
    wn.Connect(paymentOutput.ID, shipInput.ID)
    wn.Connect(shipOutput.ID, notifyInput.ID)
    wn.Connect(notifyOutput.ID, wn.SinkPlace)
    
    // 添加支付检查分支
    paymentCheckInput, paymentCheckOutputs, paymentCheckTransitions := wn.AddXorSplit("payment_check", "支付检查", 2)
    
    // 连接支付检查
    wn.Connect(paymentOutput.ID, paymentCheckInput.ID)
    
    // 添加支付成功路径
    wn.Connect(paymentCheckOutputs[0].ID, shipInput.ID)
    
    // 添加支付失败路径和取消订单活动
    cancelInput, cancelOutput, _ := wn.AddSequentialActivity("cancel", "取消订单")
    wn.Connect(paymentCheckOutputs[1].ID, cancelInput.ID)
    wn.Connect(cancelOutput.ID, wn.SinkPlace)
    
    return wn
}

// 分析订单处理工作流
func AnalyzeOrderProcessingWorkflow() {
    wn := CreateOrderProcessingPetriNet()
    
    fmt.Println("订单处理工作流Petri网分析")
    fmt.Println("==========================")
    
    // 检查工作流可靠性
    sound, issues := wn.CheckSoundness()
    if sound {
        fmt.Println("工作流是可靠的（Sound）")
    } else {
        fmt.Println("工作流不可靠:")
        for _, issue := range issues {
            fmt.Printf("- %s\n", issue)
        }
    }
    
    // 工作流仿真
    fmt.Println("\n工作流仿真:")
    completed, trace, err := wn.Simulate(100)
    
    if err != nil {
        fmt.Printf("仿真错误: %v\n", err)
    } else if completed {
        fmt.Println("工作流仿真成功完成")
    } else {
        fmt.Println("工作流仿真未完成")
    }
    
    fmt.Println("\n执行轨迹:")
    for _, step := range trace {
        fmt.Println(step)
    }
}
```

### 4.3 BPMN模型的Golang实现

```go
// BPMN元素类型
type BpmnElementType string

const (
    ElementProcess          BpmnElementType = "process"
    ElementStartEvent       BpmnElementType = "startEvent"
    ElementEndEvent         BpmnElementType = "endEvent"
    ElementTask             BpmnElementType = "task"
    ElementServiceTask      BpmnElementType = "serviceTask"
    ElementUserTask         BpmnElementType = "userTask"
    ElementManualTask       BpmnElementType = "manualTask"
    ElementScriptTask       BpmnElementType = "scriptTask"
    ElementBusinessRuleTask BpmnElementType = "businessRuleTask"
    ElementExclusiveGateway BpmnElementType = "exclusiveGateway"
    ElementParallelGateway  BpmnElementType = "parallelGateway"
    ElementInclusiveGateway BpmnElementType = "inclusiveGateway"
    ElementEventBasedGateway BpmnElementType = "eventBasedGateway"
    ElementSequenceFlow     BpmnElementType = "sequenceFlow"
    ElementMessageFlow      BpmnElementType = "messageFlow"
    ElementAssociation      BpmnElementType = "association"
    ElementDataObject       BpmnElementType = "dataObject"
    ElementDataStore        BpmnElementType = "dataStore"
    ElementPool             BpmnElementType = "pool"
    ElementLane             BpmnElementType = "lane"
)

// BPMN元素
type BpmnElement struct {
    ID         string
    Name       string
    ElementType BpmnElementType
    Properties map[string]string
}

// BPMN流元素
type BpmnFlowElement struct {
    ID                 string
    Name               string
    ElementType        BpmnElementType
    SourceRef          string
    TargetRef          string
    ConditionExpression string
}

// BPMN流程
type BpmnProcess struct {
    ID             string
    Name           string
    Elements       map[string]*BpmnElement
    FlowElements   map[string]*BpmnFlowElement
    IncomingFlows  map[string][]string
    OutgoingFlows  map[string][]string
}

// BPMN执行上下文
type BpmnExecutionContext struct {
    ProcessID        string
    Tokens           map[string]bool
    Variables        map[string]interface{}
    CompletedElements map[string]bool
}

// 创建新的BPMN流程
func NewBpmnProcess(id, name string) *BpmnProcess {
    return &BpmnProcess{
        ID:             id,
        Name:           name,
        Elements:       make(map[string]*BpmnElement),
        FlowElements:   make(map[string]*BpmnFlowElement),
        IncomingFlows:  make(map[string][]string),
        OutgoingFlows:  make(map[string][]string),
    }
}

// 添加BPMN元素
func (bp *BpmnProcess) AddElement(id, name string, elementType BpmnElementType) *BpmnElement {
    element := &BpmnElement{
        ID:         id,
        Name:       name,
        ElementType: elementType,
        Properties: make(map[string]string),
    }
    
    bp.Elements[id] = element
    
    // 初始化流连接
    bp.IncomingFlows[id] = []string{}
    bp.OutgoingFlows[id] = []string{}
    
    return element
}

// 添加BPMN流元素
func (bp *BpmnProcess) AddFlowElement(
    id, name string,
    elementType BpmnElementType,
    sourceRef, targetRef string,
    conditionExpression string,
) *BpmnFlowElement {
    flowElement := &BpmnFlowElement{
        ID:                 id,
        Name:               name,
        ElementType:        elementType,
        SourceRef:          sourceRef,
        TargetRef:          targetRef,
        ConditionExpression: conditionExpression,
    }
    
    bp.FlowElements[id] = flowElement
    
    // 更新连接索引
    bp.IncomingFlows[targetRef] = append(bp.IncomingFlows[targetRef], id)
    bp.OutgoingFlows[sourceRef] = append(bp.OutgoingFlows[sourceRef], id)
    
    return flowElement
}

// 获取所有开始事件
func (bp *BpmnProcess) GetStartEvents() []*BpmnElement {
    var startEvents []*BpmnElement
    
    for _, element := range bp.Elements {
        if element.ElementType == ElementStartEvent {
            startEvents = append(startEvents, element)
        }
    }
    
    return startEvents
}

// 获取所有结束事件
func (bp *BpmnProcess) GetEndEvents() []*BpmnElement {
    var endEvents []*BpmnElement
    
    for _, element := range bp.Elements {
        if element.ElementType == ElementEndEvent {
            endEvents = append(endEvents, element)
        }
    }
    
    return endEvents
}

// 获取元素的入边
func (bp *BpmnProcess) GetIncomingFlows(elementID string) []*BpmnFlowElement {
    var flows []*BpmnFlowElement
    
    for _, flowID := range bp.IncomingFlows[elementID] {
        if flow, ok := bp.FlowElements[flowID]; ok {
            flows = append(flows, flow)
        }
    }
    
    return flows
}

// 获取元素的出边
func (bp *BpmnProcess) GetOutgoingFlows(elementID string) []*BpmnFlowElement {
    var flows []*BpmnFlowElement
    
    for _, flowID := range bp.OutgoingFlows[elementID] {
        if flow, ok := bp.FlowElements[flowID]; ok {
            flows = append(flows, flow)
        }
    }
    
    return flows
}

// 验证流程
func (bp *BpmnProcess) Validate() (bool, []string) {
    var errors []string
    
    // 检查是否有开始事件
    startEvents := bp.GetStartEvents()
    if len(startEvents) == 0 {
        errors = append(errors, "流程中没有开始事件")
    }
    
    // 检查是否有结束事件
    endEvents := bp.GetEndEvents()
    if len(endEvents) == 0 {
        errors = append(errors, "流程中没有结束事件")
    }
    
    // 检查每个元素是否都可以从开始事件到达
    reachable := bp.ComputeReachability()
    for id, element := range bp.Elements {
        // 忽略开始事件
        if element.ElementType == ElementStartEvent {
            continue
        }
        
        if !reachable[id] {
            errors = append(errors, fmt.Sprintf("元素 '%s' (%s) 不可达", element.Name, id))
        }
    }
    
    // 检查是否有无出边的非终止节点
    for id, element := range bp.Elements {
        if element.ElementType == ElementEndEvent {
            continue // 结束事件不需要出边
        }
        
        outgoingFlows := bp.GetOutgoingFlows(id)
        if len(outgoingFlows) == 0 {
            errors = append(errors, fmt.Sprintf("非终止节点 '%s' (%s) 没有出边", element.Name, id))
        }
    }
    
    // 检查是否有无入边的非开始节点
    for id, element := range bp.Elements {
        if element.ElementType == ElementStartEvent {
            continue // 开始事件不需要入边
        }
        
        incomingFlows := bp.GetIncomingFlows(id)
        if len(incomingFlows) == 0 {
            errors = append(errors, fmt.Sprintf("非开始节点 '%s' (%s) 没有入边", element.Name, id))
        }
    }
    
    return len(errors) == 0, errors
}

// 计算从开始事件可达的所有节点
func (bp *BpmnProcess) ComputeReachability() map[string]bool {
    reachable := make(map[string]bool)
    
    // 初始标记所有元素为不可达
    for id := range bp.Elements {
        reachable[id] = false
    }
    
    // 开始事件一定可达
    startEvents := bp.GetStartEvents()
    var queue []string
    
    for _, startEvent := range startEvents {
        reachable[startEvent.ID] = true
        queue = append(queue, startEvent.ID)
    }
    
    // 广度优先搜索
    for len(queue) > 0 {
        current := queue[0]
        queue = queue[1:]
        
        // 查找所有出边
        outgoingFlows := bp.GetOutgoingFlows(current)
        for _, flow := range outgoingFlows {
            targetID := flow.TargetRef
            if !reachable[targetID] {
                reachable[targetID] = true
                queue = append(queue, targetID)
            }
        }
    }
    
    return reachable
}

// BPMN执行引擎
type BpmnExecutionEngine struct {
    Process  *BpmnProcess
    Handlers map[BpmnElementType]func(*BpmnElement, *BpmnExecutionContext) error
}

// 创建新的BPMN执行引擎
func NewBpmnExecutionEngine(process *BpmnProcess) *BpmnExecutionEngine {
    engine := &BpmnExecutionEngine{
        Process:  process,
        Handlers: make(map[BpmnElementType]func(*BpmnElement, *BpmnExecutionContext) error),
    }
    
    // 注册默认处理器
    engine.RegisterDefaultHandlers()
    
    return engine
}

// 注册元素处理器
func (engine *BpmnExecutionEngine) RegisterHandler(
    elementType BpmnElementType,
    handler func(*BpmnElement, *BpmnExecutionContext) error,
) {
    engine.Handlers[elementType] = handler
}

// 注册默认处理器
func (engine *BpmnExecutionEngine) RegisterDefaultHandlers() {
    // 开始事件处理器
    engine.RegisterHandler(ElementStartEvent, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行开始事件: %s\n", element.Name)
        return nil
    })
    
    // 结束事件处理器
    engine.RegisterHandler(ElementEndEvent, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行结束事件: %s\n", element.Name)
        return nil
    })
    
    // 任务处理器
    engine.RegisterHandler(ElementTask, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行任务: %s\n", element.Name)
        return nil
    })
    
    // 服务任务处理器
    engine.RegisterHandler(ElementServiceTask, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行服务任务: %s\n", element.Name)
        
        // 从属性中获取服务信息
        if serviceName, ok := element.Properties["serviceName"]; ok {
            fmt.Printf("调用服务: %s\n", serviceName)
            
            // 模拟服务调用
            switch serviceName {
            case "paymentService":
                fmt.Println("处理支付...")
                time.Sleep(100 * time.Millisecond)
                ctx.Variables["paymentStatus"] = "SUCCESS"
                return nil
                
            case "inventoryService":
                fmt.Println("检查库存...")
                time.Sleep(50 * time.Millisecond)
                ctx.Variables["inventoryStatus"] = "AVAILABLE"
                return nil
                
            case "shippingService":
                fmt.Println("创建物流订单...")
                time.Sleep(150 * time.Millisecond)
                ctx.Variables["shippingStatus"] = "CREATED"
                ctx.Variables["trackingNumber"] = "TRK12345"
                return nil
                
            default:
                return fmt.Errorf("未知服务: %s", serviceName)
            }
        } else {
            return fmt.Errorf("服务任务没有指定serviceName属性")
        }
    })
    
    // 用户任务处理器
    engine.RegisterHandler(ElementUserTask, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行用户任务: %s\n", element.Name)
        
        if assignee, ok := element.Properties["assignee"]; ok {
            fmt.Printf("分配给用户: %s\n", assignee)
            ctx.Variables["userTaskStatus"] = "ASSIGNED"
            
            // 模拟用户处理
            fmt.Println("等待用户处理...")
            // 在实际应用中，这里应该暂停流程执行，直到用户完成任务
            
            // 假设用户已完成任务
            ctx.Variables["userTaskStatus"] = "COMPLETED"
            return nil
        } else {
            return fmt.Errorf("用户任务没有指定assignee属性")
        }
    })
    
    // 排他网关处理器
    engine.RegisterHandler(ElementExclusiveGateway, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行排他网关: %s\n", element.Name)
        return nil
    })
    
    // 并行网关处理器
    engine.RegisterHandler(ElementParallelGateway, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行并行网关: %s\n", element.Name)
        return nil
    })
    
    // 包容网关处理器
    engine.RegisterHandler(ElementInclusiveGateway, func(element *BpmnElement, ctx *BpmnExecutionContext) error {
        fmt.Printf("执行包容网关: %s\n", element.Name)
        return nil
    })
}

// 执行流程
func (engine *BpmnExecutionEngine) Execute() (*BpmnExecutionContext, error) {
    // 验证流程
    if valid, errors := engine.Process.Validate(); !valid {
        return nil, fmt.Errorf("流程验证失败: %v", errors)
    }
    
    // 创建执行上下文
    ctx := &BpmnExecutionContext{
        ProcessID:        engine.Process.ID,
        Tokens:           make(map[string]bool),
        Variables:        make(map[string]interface{}),
        CompletedElements: make(map[string]bool),
    }
    
    // 在所有开始事件上放置令牌
    startEvents := engine.Process.GetStartEvents()
    for _, event := range startEvents {
        ctx.Tokens[event.ID] = true
    }
    
    // 执行流程直到没有活动令牌
    for len(ctx.Tokens) > 0 {
        // 获取当前活动令牌
        var activeTokens []string
        for tokenID := range ctx.Tokens {
            activeTokens = append(activeTokens, tokenID)
        }
        
        // 执行每个令牌
        for _, tokenID := range activeTokens {
            if err := engine.ExecuteToken(tokenID, ctx); err != nil {
                return ctx, err
            }
        }
    }
    
    // 检查是否所有结束事件都被执行
    endEvents := engine.Process.GetEndEvents()
    atLeastOneEndReached := false
    
    for _, event := range endEvents {
        if ctx.CompletedElements[event.ID] {
            atLeastOneEndReached = true
            break
        }
    }
    
    if !atLeastOneEndReached {
        return ctx, fmt.Errorf("流程未完全执行：没有到达任何结束事件")
    }
    
    return ctx, nil
}

// 执行单个令牌
func (engine *BpmnExecutionEngine) ExecuteToken(tokenID string, ctx *BpmnExecutionContext) error {
    // 获取令牌所在的元素
    element, ok := engine.Process.Elements[tokenID]
    if !ok {
        return fmt.Errorf("找不到令牌所在的元素: %s", tokenID)
    }
    
    // 如果元素已经完成，则跳过
    if ctx.CompletedElements[element.ID] {
        delete(ctx.Tokens, element.ID)
        return nil
    }
    
    // 执行元素
    if handler, ok := engine.Handlers[element.ElementType]; ok {
        if err := handler(element, ctx); err != nil {
            return fmt.Errorf("执行元素 %s 失败: %w", element.Name, err)
        }
    } else {
        return fmt.Errorf("未找到元素类型的处理器: %s", element.ElementType)
    }
    
    // 标记元素为已完成
    ctx.CompletedElements[element.ID] = true
    
    // 移除当前令牌
    delete(ctx.Tokens, element.ID)
    
    // 根据元素类型判断如何处理后续流
    switch element.ElementType {
    case ElementExclusiveGateway:
        // 排他网关：评估所有出边的条件，选择第一个满足条件的
        outgoingFlows := engine.Process.GetOutgoingFlows(element.ID)
        
        var selectedFlow *BpmnFlowElement
        for _, flow := range outgoingFlows {
            if flow.ConditionExpression != "" {
                // 评估条件
                conditionMet := engine.EvaluateCondition(flow.ConditionExpression, ctx)
                if conditionMet {
                    selectedFlow = flow
                    break
                }
            } else {
                // 没有条件的流被视为默认路径
                if selectedFlow == nil {
                    selectedFlow = flow
                }
            }
        }
        
        if selectedFlow != nil {
            // 在目标元素上放置令牌
            ctx.Tokens[selectedFlow.TargetRef] = true
        } else if len(outgoingFlows) > 0 {
            // 如果所有条件都不满足，选择最后一个作为默认路径
            ctx.Tokens[outgoingFlows[len(outgoingFlows)-1].TargetRef] = true
        }
        
    case ElementParallelGateway:
        // 检查是否为汇聚网关
        incomingFlows := engine.Process.GetIncomingFlows(element.ID)
        if len(incomingFlows) > 1 {
            // 汇聚网关：检查是否所有入边的源元素都已完成
            allSourcesCompleted := true
            for _, flow := range incomingFlows {
                if !ctx.CompletedElements[flow.SourceRef] {
                    allSourcesCompleted = false
                    break
                }
            }
            
            if allSourcesCompleted {
                // 在所有出边的目标元素上放置令牌
                outgoingFlows := engine.Process.GetOutgoingFlows(element.ID)
                for _, flow := range outgoingFlows {
                    ctx.Tokens[flow.TargetRef] = true
                }
            }
        } else {
            // 分叉网关：在所有出边的目标元素上放置令牌
            outgoingFlows := engine.Process.GetOutgoingFlows(element.ID)
            for _, flow := range outgoingFlows {
                ctx.Tokens[flow.TargetRef] = true
            }
        }
        
    case ElementInclusiveGateway:
        // 包容网关：评估所有出边的条件，对所有满足条件的出边放置令牌
        outgoingFlows := engine.Process.GetOutgoingFlows(element.ID)
        
        var selectedFlows []*BpmnFlowElement
        for _, flow := range outgoingFlows {
            if flow.ConditionExpression != "" {
                // 评估条件
                conditionMet := engine.EvaluateCondition(flow.ConditionExpression, ctx)
                if conditionMet {
                    selectedFlows = append(selectedFlows, flow)
                }
            } else {
                // 没有条件的流被视为默认路径
                selectedFlows = append(selectedFlows, flow)
            }
        }
        
        if len(selectedFlows) > 0 {
            // 在所有选中的目标元素上放置令牌
            for _, flow := range selectedFlows {
                ctx.Tokens[flow.TargetRef] = true
            }
        } else if len(outgoingFlows) > 0 {
            // 如果所有条件都不满足，选择最后一个作为默认路径
            ctx.Tokens[outgoingFlows[len(outgoingFlows)-1].TargetRef] = true
        }
        
    default:
        // 对于其他元素类型，简单地将令牌放在所有出边的目标元素上
        outgoingFlows := engine.Process.GetOutgoingFlows(element.ID)
        for _, flow := range outgoingFlows {
            ctx.Tokens[flow.TargetRef] = true
        }
    }
    
    return nil
}

// 评估条件表达式
func (engine *BpmnExecutionEngine) EvaluateCondition(condition string, ctx *BpmnExecutionContext) bool {
    // 简化实现，实际应用应使用完整的表达式引擎
    switch condition {
    case "paymentStatus == 'SUCCESS'":
        status, ok := ctx.Variables["paymentStatus"]
        return ok && status == "SUCCESS"
        
    case "inventoryStatus == 'AVAILABLE'":
        status, ok := ctx.Variables["inventoryStatus"]
        return ok && status == "AVAILABLE"
        
    case "amount > 1000":
        amountVal, ok := ctx.Variables["amount"]
        if !ok {
            return false
        }
        
        amount, ok := amountVal.(float64)
        if !ok {
            return false
        }
        
        return amount > 1000
        
    default:
        fmt.Printf("未知条件表达式: %s\n", condition)
        return false
    }
}

// 构建并执行订单处理BPMN流程
func CreateAndExecuteOrderProcess() {
    process := NewBpmnProcess("order_process", "订单处理流程")
    
    // 添加节点
    process.AddElement("start", "开始", ElementStartEvent)
    process.AddElement("validate_order", "验证订单", ElementTask)
    
    paymentTask := process.AddElement("process_payment", "处理支付", ElementServiceTask)
    paymentTask.Properties["serviceName"] = "paymentService"
    
    inventoryTask := process.AddElement("check_inventory", "检查库存", ElementServiceTask)
    inventoryTask.Properties["serviceName"] = "inventoryService"
    
    process.AddElement("payment_gateway", "支付网关", ElementExclusiveGateway)
    process.AddElement("inventory_gateway", "库存网关", ElementExclusiveGateway)
    
    shippingTask := process.AddElement("create_shipment", "创建物流订单", ElementServiceTask)
    shippingTask.Properties["serviceName"] = "shippingService"
    
    process.AddElement("notify_customer", "通知客户", ElementTask)
    process.AddElement("cancel_order", "取消订单", ElementTask)
    process.AddElement("end_success", "成功结束", ElementEndEvent)
    process.AddElement("end_cancelled", "取消结束", ElementEndEvent)
    
    // 添加流
    process.AddFlowElement("flow1", "", ElementSequenceFlow, "start", "validate_order", "")
    process.AddFlowElement("flow2", "", ElementSequenceFlow, "validate_order", "process_payment", "")
    process.AddFlowElement("flow3", "", ElementSequenceFlow, "process_payment", "payment_gateway", "")
    
    process.AddFlowElement("flow4", "支付成功", ElementSequenceFlow, 
                         "payment_gateway", "check_inventory", "paymentStatus == 'SUCCESS'")
    
    process.AddFlowElement("flow5", "支付失败", ElementSequenceFlow, 
                         "payment_gateway", "cancel_order", "")
    
    process.AddFlowElement("flow6", "", ElementSequenceFlow, "check_inventory", "inventory_gateway", "")
    
    process.AddFlowElement("flow7", "库存可用", ElementSequenceFlow, 
                         "inventory_gateway", "create_shipment", "inventoryStatus == 'AVAILABLE'")
    
    process.AddFlowElement("flow8", "库存不可用", ElementSequenceFlow, 
                         "inventory_gateway", "cancel_order", "")
    
    process.AddFlowElement("flow9", "", ElementSequenceFlow, "create_shipment", "notify_customer", "")
    process.AddFlowElement("flow10", "", ElementSequenceFlow, "notify_customer", "end_success", "")
    process.AddFlowElement("flow11", "", ElementSequenceFlow, "cancel_order", "end_cancelled", "")
    
    // 创建执行引擎
    engine := NewBpmnExecutionEngine(process)
    
    // 执行流程
    ctx, err := engine.Execute()
    if err != nil {
        fmt.Printf("流程执行失败: %v\n", err)
        return
    }
    
    fmt.Println("流程执行成功!")
    fmt.Println("变量状态:")
    for key, value := range ctx.Variables {
        fmt.Printf("  %s: %v\n", key, value)
    }
}
```

### 4.4 工作流可视化与监控

```go
// 工作流可视化与监控组件
type WorkflowMonitor struct {
    ActiveWorkflows    map[string]*WorkflowExecutionStatus
    ExecutionHistory   []*WorkflowExecutionEvent
    PerformanceMetrics map[string]*WorkflowMetrics
    mu                 sync.RWMutex
}

type WorkflowExecutionStatus struct {
    WorkflowID     string
    WorkflowType   string
    StartTime      time.Time
    LastUpdated    time.Time
    CurrentState   string
    ActiveActivities []string
    Variables      map[string]interface{}
    IsCompleted    bool
    CompletionTime *time.Time
}

type WorkflowExecutionEvent struct {
    WorkflowID   string
    EventType    string
    ActivityID   string
    ActivityName string
    Timestamp    time.Time
    Details      map[string]string
}

type WorkflowMetrics struct {
    TotalExecutionTime     time.Duration
    ActivityExecutionTimes map[string]time.Duration
    ErrorCount             int
    Throughput             float64 // 每秒处理的活动数
}

// 创建新的工作流监控器
func NewWorkflowMonitor() *WorkflowMonitor {
    return &WorkflowMonitor{
        ActiveWorkflows:    make(map[string]*WorkflowExecutionStatus),
        ExecutionHistory:   make([]*WorkflowExecutionEvent, 0),
        PerformanceMetrics: make(map[string]*WorkflowMetrics),
    }
}

// 记录工作流开始
func (wm *WorkflowMonitor) RecordWorkflowStart(
    workflowID, workflowType, initialState string,
    variables map[string]interface{},
) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 创建工作流状态
    status := &WorkflowExecutionStatus{
        WorkflowID:       workflowID,
        WorkflowType:     workflowType,
        StartTime:        now,
        LastUpdated:      now,
        CurrentState:     initialState,
        ActiveActivities: make([]string, 0),
        Variables:        variables,
        IsCompleted:      false,
        CompletionTime:   nil,
    }
    
    // 保存工作流状态
    wm.ActiveWorkflows[workflowID] = status
    
    // 记录工作流开始事件
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "WorkflowStarted",
        ActivityID:   "",
        ActivityName: "",
        Timestamp:    now,
        Details:      make(map[string]string),
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
    
    // 初始化性能指标
    wm.PerformanceMetrics[workflowID] = &WorkflowMetrics{
        TotalExecutionTime:     0,
        ActivityExecutionTimes: make(map[string]time.Duration),
        ErrorCount:             0,
        Throughput:             0,
    }
}

// 记录活动开始
func (wm *WorkflowMonitor) RecordActivityStart(
    workflowID, activityID, activityName string,
) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 更新工作流状态
    if status, ok := wm.ActiveWorkflows[workflowID]; ok {
        status.LastUpdated = now
        status.CurrentState = fmt.Sprintf("执行活动: %s", activityName)
        status.ActiveActivities = append(status.ActiveActivities, activityID)
    }
    
    // 记录活动开始事件
    details := map[string]string{
        "activityName": activityName,
    }
    
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "ActivityStarted",
        ActivityID:   activityID,
        ActivityName: activityName,
        Timestamp:    now,
        Details:      details,
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
}

// 记录活动完成
func (wm *WorkflowMonitor) RecordActivityComplete(
    workflowID, activityID, activityName string,
    duration time.Duration,
) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 更新工作流状态
    if status, ok := wm.ActiveWorkflows[workflowID]; ok {
        status.LastUpdated = now
        
        // 移除已完成的活动
        var newActiveActivities []string
        for _, id := range status.ActiveActivities {
            if id != activityID {
                newActiveActivities = append(newActiveActivities, id)
            }
        }
        status.ActiveActivities = newActiveActivities
    }
    
    // 记录活动完成事件
    details := map[string]string{
        "activityName": activityName,
        "duration_ms":  fmt.Sprintf("%d", duration.Milliseconds()),
    }
    
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "ActivityCompleted",
        ActivityID:   activityID,
        ActivityName: activityName,
        Timestamp:    now,
        Details:      details,
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
    
    // 更新性能指标
    if metrics, ok := wm.PerformanceMetrics[workflowID]; ok {
        metrics.ActivityExecutionTimes[activityID] = duration
        
        // 重新计算吞吐量
        totalActivities := float64(len(metrics.ActivityExecutionTimes))
        totalTime := metrics.TotalExecutionTime.Seconds()
        if totalTime > 0 {
            metrics.Throughput = totalActivities / totalTime
        }
    }
}

// 记录活动失败
func (wm *WorkflowMonitor) RecordActivityFailure(
    workflowID, activityID, activityName, errorMessage string,
) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 更新工作流状态
    if status, ok := wm.ActiveWorkflows[workflowID]; ok {
        status.LastUpdated = now
        status.CurrentState = fmt.Sprintf("活动失败: %s", activityName)
        
        // 移除失败的活动
        var newActiveActivities []string
        for _, id := range status.ActiveActivities {
            if id != activityID {
                newActiveActivities = append(newActiveActivities, id)
            }
        }
        status.ActiveActivities = newActiveActivities
    }
    
    // 记录活动失败事件
    details := map[string]string{
        "activityName": activityName,
        "error":        errorMessage,
    }
    
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "ActivityFailed",
        ActivityID:   activityID,
        ActivityName: activityName,
        Timestamp:    now,
        Details:      details,
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
    
    // 更新性能指标
    if metrics, ok := wm.PerformanceMetrics[workflowID]; ok {
        metrics.ErrorCount++
    }
}

// 记录工作流完成
func (wm *WorkflowMonitor) RecordWorkflowComplete(workflowID string) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 更新工作流状态
    if status, ok := wm.ActiveWorkflows[workflowID]; ok {
        status.LastUpdated = now
        status.CurrentState = "已完成"
        status.IsCompleted = true
        status.CompletionTime = &now
        
        // 计算总执行时间
        totalTime := now.Sub(status.StartTime)
        
        // 更新性能指标
        if metrics, ok := wm.PerformanceMetrics[workflowID]; ok {
            metrics.TotalExecutionTime = totalTime
        }
    }
    
    // 记录工作流完成事件
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "WorkflowCompleted",
        ActivityID:   "",
        ActivityName: "",
        Timestamp:    now,
        Details:      make(map[string]string),
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
}

// 记录工作流失败
func (wm *WorkflowMonitor) RecordWorkflowFailure(workflowID, errorMessage string) {
    wm.mu.Lock()
    defer wm.mu.Unlock()
    
    now := time.Now()
    
    // 更新工作流状态
    if status, ok := wm.ActiveWorkflows[workflowID]; ok {
        status.LastUpdated = now
        status.CurrentState = fmt.Sprintf("失败: %s", errorMessage)
        status.IsCompleted = true
        status.CompletionTime = &now
        
        // 计算总执行时间
        totalTime := now.Sub(status.StartTime)
        
        // 更新性能指标
        if metrics, ok := wm.PerformanceMetrics[workflowID]; ok {
            metrics.TotalExecutionTime = totalTime
        }
    }
    
    // 记录工作流失败事件
    details := map[string]string{
        "error": errorMessage,
    }
    
    event := &WorkflowExecutionEvent{
        WorkflowID:   workflowID,
        EventType:    "WorkflowFailed",
        ActivityID:   "",
        ActivityName: "",
        Timestamp:    now,
        Details:      details,
    }
    
    wm.ExecutionHistory = append(wm.ExecutionHistory, event)
}

// 获取工作流状态
func (wm *WorkflowMonitor) GetWorkflowStatus(workflowID string) (*WorkflowExecutionStatus, bool) {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    status, ok := wm.ActiveWorkflows[workflowID]
    return status, ok
}

// 获取工作流执行历史
func (wm *WorkflowMonitor) GetWorkflowHistory(workflowID string) []*WorkflowExecutionEvent {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    var history []*WorkflowExecutionEvent
    for _, event := range wm.ExecutionHistory {
        if event.WorkflowID == workflowID {
            history = append(history, event)
        }
    }
    
    return history
}

// 获取工作流性能指标
func (wm *WorkflowMonitor) GetWorkflowMetrics(workflowID string) (*WorkflowMetrics, bool) {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    metrics, ok := wm.PerformanceMetrics[workflowID]
    return metrics, ok
}

// 生成工作流执行摘要
func (wm *WorkflowMonitor) GenerateWorkflowSummary(workflowID string) (string, bool) {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    status, statusOk := wm.ActiveWorkflows[workflowID]
    if !statusOk {
        return "", false
    }
    
    metrics, metricsOk := wm.PerformanceMetrics[workflowID]
    if !metricsOk {
        return "", false
    }
    
    var summary strings.Builder
    summary.WriteString(fmt.Sprintf("工作流执行摘要 - ID: %s\n", workflowID))
    summary.WriteString(fmt.Sprintf("类型: %s\n", status.WorkflowType))
    summary.WriteString(fmt.Sprintf("开始时间: %s\n", status.StartTime.Format(time.RFC3339)))
    
    if status.CompletionTime != nil {
        summary.WriteString(fmt.Sprintf("完成时间: %s\n", status.CompletionTime.Format(time.RFC3339)))
        
        duration := status.CompletionTime.Sub(status.StartTime)
        summary.WriteString(fmt.Sprintf("总执行时间: %s\n", duration))
    }
    
    summary.WriteString(fmt.Sprintf("当前状态: %s\n", status.CurrentState))
    summary.WriteString(fmt.Sprintf("完成状态: %s\n", func() string {
        if status.IsCompleted {
            return "已完成"
        }
        return "进行中"
    }()))
    
    summary.WriteString("\n性能指标:\n")
    summary.WriteString(fmt.Sprintf("错误数量: %d\n", metrics.ErrorCount))
    summary.WriteString(fmt.Sprintf("吞吐量: %.2f 活动/秒\n", metrics.Throughput))
    
    summary.WriteString("\n活动执行时间:\n")
    for activityID, duration := range metrics.ActivityExecutionTimes {
        summary.WriteString(fmt.Sprintf("  %s: %s\n", activityID, duration))
    }
    
    return summary.String(), true
}

// 生成工作流执行时间轴数据
func (wm *WorkflowMonitor) GenerateWorkflowTimeline(workflowID string) []map[string]interface{} {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    var timeline []map[string]interface{}
    history := wm.GetWorkflowHistory(workflowID)
    
    // 查找每个活动的开始和结束时间
    activityStarts := make(map[string]time.Time)
    
    for _, event := range history {
        switch event.EventType {
        case "ActivityStarted":
            activityStarts[event.ActivityID] = event.Timestamp
            
        case "ActivityCompleted", "ActivityFailed":
            if startTime, ok := activityStarts[event.ActivityID]; ok {
                timelineItem := map[string]interface{}{
                    "activity":   event.ActivityName,
                    "start_time": startTime,
                    "end_time":   event.Timestamp,
                    "duration":   event.Timestamp.Sub(startTime).Milliseconds(),
                    "status":     event.EventType,
                }
                timeline = append(timeline, timelineItem)
            }
        }
    }
    
    return timeline
}

// 导出工作流执行图可视化（DOT格式）
func (wm *WorkflowMonitor) ExportWorkflowGraph(workflowID string) (string, bool) {
    wm.mu.RLock()
    defer wm.mu.RUnlock()
    
    history := wm.GetWorkflowHistory(workflowID)
    if len(history) == 0 {
        return "", false
    }
    
    // 构建图形
    var dot strings.Builder
    dot.WriteString("digraph workflow {\n")
    dot.WriteString("  rankdir=TB;\n")
    dot.WriteString("  node [shape=box, style=filled, fillcolor=lightblue];\n")
    
    // 添加节点
    nodes := make(map[string]bool)
    edges := make(map[string]bool)
    
    for _, event := range history {
        if event.ActivityID == "" {
            continue
        }
        
        // 为节点添加颜色标记
        nodeColor := "lightblue"
        switch event.EventType {
        case "ActivityStarted":
            nodeColor = "lightblue"
        case "ActivityCompleted":
            nodeColor = "lightgreen"
        case "ActivityFailed":
            nodeColor = "lightcoral"
        }
        
        nodeDef := fmt.Sprintf("  \"%s\" [label=\"%s\", fillcolor=%s];\n", 
                             event.ActivityID, event.ActivityName, nodeColor)
        nodes[nodeDef] = true
    }
    
    // 添加边
    var prevActivity string
    for _, event := range history {
        if event.EventType == "ActivityStarted" && event.ActivityID != "" {
            if prevActivity != "" {
                edgeDef := fmt.Sprintf("  \"%s\" -> \"%s\";\n", prevActivity, event.ActivityID)
                edges[edgeDef] = true
            }
            prevActivity = event.ActivityID
        }
    }
    
    // 写入节点和边
    for node := range nodes {
        dot.WriteString(node)
    }
    
    for edge := range edges {
        dot.WriteString(edge)
    }
    
    dot.WriteString("}\n")
    
    return dot.String(), true
}

// 工作流执行跟踪器（集成到工作流引擎中）
type WorkflowTracker struct {
    Monitor       *WorkflowMonitor
    ActivityTimers map[string]time.Time
}

// 创建新的工作流跟踪器
func NewWorkflowTracker() *WorkflowTracker {
    return &WorkflowTracker{
        Monitor:       NewWorkflowMonitor(),
        ActivityTimers: make(map[string]time.Time),
    }
}

// 跟踪工作流引擎中的事件
func (wt *WorkflowTracker) TrackWorkflowEvent(
    eventType, workflowID string,
    activityID, activityName string,
    details map[string]string,
) {
    switch eventType {
    case "WorkflowStarted":
        variables := make(map[string]interface{})
        wt.Monitor.RecordWorkflowStart(workflowID, "Unknown", "初始化", variables)
        
    case "WorkflowCompleted":
        wt.Monitor.RecordWorkflowComplete(workflowID)
        
    case "WorkflowFailed":
        errorMsg := "未知错误"
        if details != nil {
            if err, ok := details["error"]; ok {
                errorMsg = err
            }
        }
        wt.Monitor.RecordWorkflowFailure(workflowID, errorMsg)
        
    case "ActivityStarted":
        if activityID != "" && activityName != "" {
            wt.Monitor.RecordActivityStart(workflowID, activityID, activityName)
            
            // 开始计时
            timerKey := fmt.Sprintf("%s_%s", workflowID, activityID)
            wt.ActivityTimers[timerKey] = time.Now()
        }
        
    case "ActivityCompleted":
        if activityID != "" && activityName != "" {
            // 停止计时
            timerKey := fmt.Sprintf("%s_%s", workflowID, activityID)
            if startTime, ok := wt.ActivityTimers[timerKey]; ok {
                duration := time.Since(startTime)
                wt.Monitor.RecordActivityComplete(workflowID, activityID, activityName, duration)
                delete(wt.ActivityTimers, timerKey)
            }
        }
        
    case "ActivityFailed":
        if activityID != "" && activityName != "" {
            errorMsg := "未知错误"
            if details != nil {
                if err, ok := details["error"]; ok {
                    errorMsg = err
                }
            }
            wt.Monitor.RecordActivityFailure(workflowID, activityID, activityName, errorMsg)
            
            // 停止计时
            timerKey := fmt.Sprintf("%s_%s", workflowID, activityID)
            delete(wt.ActivityTimers, timerKey)
        }
    }
}

// 获取监控器引用
func (wt *WorkflowTracker) GetMonitor() *WorkflowMonitor {
    return wt.Monitor
}

// 集成可视化与监控到工作流引擎
func IntegrateMonitoringWithEngine() {
    // 创建工作流追踪器
    tracker := NewWorkflowTracker()
    
    // 创建模拟工作流执行
    workflowID := "order-123"
    
    // 模拟工作流开始
    tracker.TrackWorkflowEvent("WorkflowStarted", workflowID, "", "", nil)
    
    // 模拟活动执行
    activities := []struct {
        ID   string
        Name string
        Duration time.Duration
    }{
        {"validate", "验证订单", 50 * time.Millisecond},
        {"payment", "处理支付", 200 * time.Millisecond},
        {"inventory", "检查库存", 50 * time.Millisecond},
        {"shipping", "创建物流订单", 150 * time.Millisecond},
        {"notify", "通知客户", 50 * time.Millisecond},
    }
    
    for _, activity := range activities {
        // 模拟活动开始
        tracker.TrackWorkflowEvent("ActivityStarted", workflowID, activity.ID, activity.Name, nil)
        
        // 模拟处理时间
        time.Sleep(activity.Duration)
        
        // 模拟活动完成
        tracker.TrackWorkflowEvent("ActivityCompleted", workflowID, activity.ID, activity.Name, nil)
    }
    
    // 模拟工作流完成
    tracker.TrackWorkflowEvent("WorkflowCompleted", workflowID, "", "", nil)
    
    // 获取并打印工作流摘要
    monitor := tracker.GetMonitor()
    summary, ok := monitor.GenerateWorkflowSummary(workflowID)
    if ok {
        fmt.Println(summary)
    }
    
    // 获取并导出工作流图
    graph, ok := monitor.ExportWorkflowGraph(workflowID)
    if ok {
        fmt.Println("工作流图 (DOT格式):")
        fmt.Println(graph)
        
        // 在实际应用中，可以将DOT格式保存到文件或转换为SVG/PNG
        // ioutil.WriteFile("workflow.dot", []byte(graph), 0644)
        // 然后使用命令：dot -Tpng workflow.dot -o workflow.png
    }
}
```

### 4.5 Golang工作流实现的总结与实践建议

通过上述实现，我们展示了使用Golang语言实现不同工作流模型的核心概念和实用技术。以下是关键总结和最佳实践建议：

1. **选择合适的工作流模型**：

```go
// 工作流模型选择指南
func SelectWorkflowModel(requirements WorkflowRequirements) WorkflowModelType {
    switch {
    // 对于简单的顺序流程
    case requirements.IsSequential && !requirements.HasParallelActivities:
        return ModelStateMachine
        
    // 对于需要形式化验证的流程
    case requirements.NeedsFormalVerification:
        return ModelPetriNet
        
    // 对于具有复杂业务规则和分支的流程
    case requirements.HasComplexBusinessRules:
        return ModelBPMN
        
    // 对于需要动态创建和修改的流程
    case requirements.IsHighlyDynamic:
        return ModelDynamic
        
    // 默认使用状态机
    default:
        return ModelStateMachine
    }
}

type WorkflowModelType int

const (
    ModelStateMachine WorkflowModelType = iota
    ModelPetriNet
    ModelBPMN
    ModelDynamic
)

type WorkflowRequirements struct {
    IsSequential            bool
    HasParallelActivities   bool
    NeedsFormalVerification bool
    HasComplexBusinessRules bool
    IsHighlyDynamic         bool
}
```

1. **错误处理与补偿策略**：

```go
// 工作流错误处理策略
type ErrorHandlingStrategy struct {
    StrategyType string // "retry", "compensate", "alternative", "manual", "terminate"
    
    // 重试配置
    MaxAttempts  int
    DelayMs      int
    
    // 补偿配置
    CompensationActivities []string
    
    // 替代路径配置
    FallbackActivity string
    
    // 手动干预配置
    NotificationEndpoint string
}

// 工作流错误处理示例
func HandleWorkflowError(
    err error,
    context *WorkflowContext,
    strategy *ErrorHandlingStrategy,
) error {
    switch strategy.StrategyType {
    case "retry":
        if context.AttemptCount < strategy.MaxAttempts {
            fmt.Printf("尝试重试活动，尝试次数: %d/%d\n", 
                     context.AttemptCount+1, strategy.MaxAttempts)
            time.Sleep(time.Duration(strategy.DelayMs) * time.Millisecond)
            context.AttemptCount++
            return nil
        }
        return fmt.Errorf("已达到最大重试次数: %d", strategy.MaxAttempts)
        
    case "compensate":
        fmt.Println("执行补偿活动")
        // 反向执行补偿活动
        for i := len(strategy.CompensationActivities) - 1; i >= 0; i-- {
            activity := strategy.CompensationActivities[i]
            fmt.Printf("执行补偿活动: %s\n", activity)
            // 执行补偿活动
        }
        return nil
        
    case "alternative":
        fmt.Printf("切换到替代路径: %s\n", strategy.FallbackActivity)
        // 激活替代活动
        return nil
        
    case "manual":
        fmt.Printf("需要手动干预，发送通知到: %s\n", strategy.NotificationEndpoint)
        // 发送通知并暂停工作流
        return nil
        
    case "terminate":
        fmt.Println("终止工作流")
        return fmt.Errorf("工作流被手动终止")
        
    default:
        return fmt.Errorf("未知的错误处理策略: %s", strategy.StrategyType)
    }
}

type WorkflowContext struct {
    WorkflowID   string
    AttemptCount int
    Variables    map[string]interface{}
    // 其他上下文信息
}
```

1. **工作流持久化策略**：

```go
// 工作流持久化接口
type WorkflowPersistence interface {
    SaveWorkflowState(workflowID string, state *WorkflowState) error
    LoadWorkflowState(workflowID string) (*WorkflowState, error)
    SaveExecutionEvent(event *WorkflowExecutionEvent) error
    LoadExecutionHistory(workflowID string) ([]*WorkflowExecutionEvent, error)
}

// 数据库持久化实现
type DatabaseWorkflowPersistence struct {
    ConnectionString string
    DB               *sql.DB
}

func NewDatabaseWorkflowPersistence(connectionString string) (*DatabaseWorkflowPersistence, error) {
    db, err := sql.Open("postgres", connectionString)
    if err != nil {
        return nil, err
    }
    
    return &DatabaseWorkflowPersistence{
        ConnectionString: connectionString,
        DB:               db,
    }, nil
}

func (p *DatabaseWorkflowPersistence) SaveWorkflowState(workflowID string, state *WorkflowState) error {
    // 序列化状态
    stateJSON, err := json.Marshal(state)
    if err != nil {
        return err
    }
    
    // 保存到数据库
    query := `
        INSERT INTO workflow_states (workflow_id, state_data, updated_at)
        VALUES ($1, $2, $3)
        ON CONFLICT (workflow_id) DO UPDATE 
        SET state_data = $2, updated_at = $3
    `
    
    _, err = p.DB.Exec(query, workflowID, stateJSON, time.Now())
    return err
}

func (p *DatabaseWorkflowPersistence) LoadWorkflowState(workflowID string) (*WorkflowState, error) {
    query := `SELECT state_data FROM workflow_states WHERE workflow_id = $1`
    
    var stateJSON []byte
    err := p.DB.QueryRow(query, workflowID).Scan(&stateJSON)
    if err != nil {
        return nil, err
    }
    
    var state WorkflowState
    err = json.Unmarshal(stateJSON, &state)
    if err != nil {
        return nil, err
    }
    
    return &state, nil
}

func (p *DatabaseWorkflowPersistence) SaveExecutionEvent(event *WorkflowExecutionEvent) error {
    // 序列化事件详情
    detailsJSON, err := json.Marshal(event.Details)
    if err != nil {
        return err
    }
    
    query := `
        INSERT INTO workflow_events (
            workflow_id, event_type, activity_id, activity_name, 
            timestamp, details
        ) VALUES ($1, $2, $3, $4, $5, $6)
    `
    
    _, err = p.DB.Exec(
        query, 
        event.WorkflowID, event.EventType, event.ActivityID, 
        event.ActivityName, event.Timestamp, detailsJSON,
    )
    
    return err
}

func (p *DatabaseWorkflowPersistence) LoadExecutionHistory(workflowID string) ([]*WorkflowExecutionEvent, error) {
    query := `
        SELECT event_type, activity_id, activity_name, timestamp, details
        FROM workflow_events
        WHERE workflow_id = $1
        ORDER BY timestamp
    `
    
    rows, err := p.DB.Query(query, workflowID)
    if err != nil {
        return nil, err
    }
    defer rows.Close()
    
    var events []*WorkflowExecutionEvent
    for rows.Next() {
        var event WorkflowExecutionEvent
        var detailsJSON []byte
        
        err := rows.Scan(
            &event.EventType, &event.ActivityID, &event.ActivityName, 
            &event.Timestamp, &detailsJSON,
        )
        if err != nil {
            return nil, err
        }
        
        // 解析详情
        if err := json.Unmarshal(detailsJSON, &event.Details); err != nil {
            return nil, err
        }
        
        event.WorkflowID = workflowID
        events = append(events, &event)
    }
    
    return events, nil
}

// 文件系统持久化实现
type FileSystemWorkflowPersistence struct {
    BasePath string
}

func NewFileSystemWorkflowPersistence(basePath string) (*FileSystemWorkflowPersistence, error) {
    // 确保目录存在
    if err := os.MkdirAll(basePath, 0755); err != nil {
        return nil, err
    }
    
    return &FileSystemWorkflowPersistence{
        BasePath: basePath,
    }, nil
}

func (p *FileSystemWorkflowPersistence) SaveWorkflowState(workflowID string, state *WorkflowState) error {
    filePath := filepath.Join(p.BasePath, fmt.Sprintf("%s_state.json", workflowID))
    
    // 序列化状态
    stateJSON, err := json.MarshalIndent(state, "", "  ")
    if err != nil {
        return err
    }
    
    // 写入文件
    return ioutil.WriteFile(filePath, stateJSON, 0644)
}

func (p *FileSystemWorkflowPersistence) LoadWorkflowState(workflowID string) (*WorkflowState, error) {
    filePath := filepath.Join(p.BasePath, fmt.Sprintf("%s_state.json", workflowID))
    
    // 读取文件
    stateJSON, err := ioutil.ReadFile(filePath)
    if err != nil {
        return nil, err
    }
    
    var state WorkflowState
    err = json.Unmarshal(stateJSON, &state)
    if err != nil {
        return nil, err
    }
    
    return &state, nil
}

func (p *FileSystemWorkflowPersistence) SaveExecutionEvent(event *WorkflowExecutionEvent) error {
    filePath := filepath.Join(p.BasePath, fmt.Sprintf("%s_history.jsonl", event.WorkflowID))
    
    // 序列化事件
    eventJSON, err := json.Marshal(event)
    if err != nil {
        return err
    }
    
    // 追加到文件
    file, err := os.OpenFile(filePath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
    if err != nil {
        return err
    }
    defer file.Close()
    
    _, err = file.Write(append(eventJSON, '\n'))
    return err
}

func (p *FileSystemWorkflowPersistence) LoadExecutionHistory(workflowID string) ([]*WorkflowExecutionEvent, error) {
    filePath := filepath.Join(p.BasePath, fmt.Sprintf("%s_history.jsonl", workflowID))
    
    // 检查文件是否存在
    if _, err := os.Stat(filePath); os.IsNotExist(err) {
        return []*WorkflowExecutionEvent{}, nil
    }
    
    // 读取文件
    file, err := os.Open(filePath)
    if err != nil {
        return nil, err
    }
    defer file.Close()
    
    scanner := bufio.NewScanner(file)
    var events []*WorkflowExecutionEvent
    
    for scanner.Scan() {
        line := scanner.Text()
        var event WorkflowExecutionEvent
        
        if err := json.Unmarshal([]byte(line), &event); err != nil {
            return nil, err
        }
        
        events = append(events, &event)
    }
    
    if err := scanner.Err(); err != nil {
        return nil, err
    }
    
    return events, nil
}

type WorkflowState struct {
    CurrentState    string
    Variables       map[string]interface{}
    ActiveActivities []string
    // 其他状态信息
}
```

1. **实践建议总结**：

以下是使用Golang实现工作流系统的关键实践建议：

1. **接口设计优先**：
   - 使用Go的接口系统定义工作流组件的抽象行为
   - 为不同的工作流元素（活动、网关、事件等）定义清晰的接口
   - 遵循组合优于继承的原则设计可扩展的工作流组件

2. **错误处理策略**：
   - 利用Go的错误处理模式返回有意义的错误信息
   - 实现错误包装（`fmt.Errorf("...: %w", err)`）以保留错误上下文
   - 定义不同级别的错误处理策略：重试、补偿、替代路径

3. **并发控制**：
   - 使用goroutines和channels实现并行活动执行
   - 利用`context`包实现超时控制和取消操作
   - 在共享资源访问时正确使用互斥锁

4. **持久化与恢复**：
   - 实现事件日志机制，记录所有工作流状态变更
   - 使用事务确保状态更新的原子性
   - 设计可恢复的工作流执行模型，支持从中断点恢复

5. **测试策略**：
   - 编写单元测试验证每个工作流组件
   - 实现集成测试验证完整的工作流执行
   - 使用模拟对象（mock）测试外部系统交互

6. **性能优化**：
   - 避免不必要的内存分配，特别是在热路径上
   - 使用对象池减少垃圾回收压力
   - 批量处理数据库操作提高吞吐量

7. **可视化与监控**：
   - 实现标准化的日志记录格式，便于分析
   - 导出工作流执行指标以监控性能
   - 提供可视化工具辅助工作流设计和调试

8. **安全考虑**：
   - 实现适当的访问控制机制
   - 对敏感数据进行加密存储
   - 防止恶意输入导致的工作流异常行为

这些工作流实现方法和最佳实践，结合Go的简洁性、高效的并发模型以及强大的标准库，
为构建复杂且可靠的工作流系统提供了坚实基础。
Go语言特别适合构建工作流引擎，因为它的并发模型与工作流的并行执行需求非常匹配，
同时其简单直观的错误处理方式也便于实现复杂的工作流错误恢复逻辑。
