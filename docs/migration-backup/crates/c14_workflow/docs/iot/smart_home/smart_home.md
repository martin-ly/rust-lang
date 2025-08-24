# 智能家居场景自动化系统实现指南

## 目录

- [智能家居场景自动化系统实现指南](#智能家居场景自动化系统实现指南)
  - [目录](#目录)
  - [一、系统架构概述](#一系统架构概述)
    - [1.1 物理架构](#11-物理架构)
    - [1.2 逻辑架构](#12-逻辑架构)
  - [二、设备兼容性与协议适配](#二设备兼容性与协议适配)
    - [2.1 主流协议支持策略](#21-主流协议支持策略)
    - [2.2 设备抽象与能力模型](#22-设备抽象与能力模型)
    - [2.3 动态协议发现与设备接入](#23-动态协议发现与设备接入)
  - [三、工作流引擎性能优化](#三工作流引擎性能优化)
    - [3.1 轻量级工作流定义](#31-轻量级工作流定义)
    - [3.2 优化的工作流执行引擎](#32-优化的工作流执行引擎)
    - [3.3 工作流状态持久化与恢复](#33-工作流状态持久化与恢复)
    - [3.4 资源监控与自适应调度](#34-资源监控与自适应调度)
  - [四、用户体验简化](#四用户体验简化)
    - [4.1 场景模板与向导](#41-场景模板与向导)
    - [4.2 自然语言场景创建](#42-自然语言场景创建)
    - [4.3 可视化场景编辑器](#43-可视化场景编辑器)
    - [4.4 场景执行可视化与故障排查](#44-场景执行可视化与故障排查)
  - [五、安全与隐私保护](#五安全与隐私保护)
    - [5.1 设备层安全](#51-设备层安全)
    - [5.2 数据隐私与访问控制](#52-数据隐私与访问控制)
    - [5.3 通信加密与安全通道](#53-通信加密与安全通道)
    - [5.4 异常行为检测](#54-异常行为检测)
  - [总结](#总结)
    - [1. 设备兼容性与协议适配](#1-设备兼容性与协议适配)
    - [2. 工作流引擎性能优化](#2-工作流引擎性能优化)
    - [3. 用户体验简化](#3-用户体验简化)
    - [4. 安全与隐私保护](#4-安全与隐私保护)
    - [5. 系统可靠性保障](#5-系统可靠性保障)

## 一、系统架构概述

智能家居场景自动化系统采用分层架构，从设备层到云平台层，实现了完整的自动化工作流管理。
系统核心是多层次工作流引擎，能够协调设备控制、场景执行和智能决策。

### 1.1 物理架构

- **设备层**：各类智能设备
- **网关层**：本地协议转换与初步处理
- **边缘层**：本地工作流执行与数据处理
- **云平台层**：高级分析与全局协调

### 1.2 逻辑架构

- **设备抽象层**：统一设备访问接口
- **工作流引擎层**：场景定义与执行
- **数据处理层**：数据存储与分析
- **应用服务层**：用户界面与API

## 二、设备兼容性与协议适配

设备兼容性是智能家居系统面临的首要挑战，需要解决多样化的设备类型和通信协议问题。

### 2.1 主流协议支持策略

```go
// protocol/adapter.go
package protocol

// ProtocolAdapter 定义协议适配器接口
type ProtocolAdapter interface {
    Initialize() error
    Discover() ([]DeviceInfo, error)
    Connect(deviceID string) error
    Disconnect(deviceID string) error
    SendCommand(deviceID string, command Command) (Response, error)
    SubscribeEvents(deviceID string, callback EventCallback) error
}

// 支持的协议类型
const (
    ProtocolZigbee = "zigbee"
    ProtocolZWave = "zwave"
    ProtocolWiFi = "wifi"
    ProtocolBLE = "bluetooth"
    ProtocolMatter = "matter"
    // 更多协议...
)

// 创建特定协议适配器的工厂函数
func NewProtocolAdapter(protocolType string, config map[string]interface{}) (ProtocolAdapter, error) {
    switch protocolType {
    case ProtocolZigbee:
        return newZigbeeAdapter(config)
    case ProtocolZWave:
        return newZWaveAdapter(config)
    case ProtocolWiFi:
        return newWiFiAdapter(config)
    case ProtocolBLE:
        return newBLEAdapter(config)
    case ProtocolMatter:
        return newMatterAdapter(config)
    default:
        return nil, fmt.Errorf("unsupported protocol: %s", protocolType)
    }
}

// ... existing code ...
```

### 2.2 设备抽象与能力模型

为解决设备异构性问题，引入基于能力(Capability)的设备抽象：

```go
// device/capability.go
package device

// Capability 定义设备能力接口
type Capability interface {
    GetType() string
    GetAttributes() map[string]interface{}
    GetCommands() []string
    ExecuteCommand(command string, args map[string]interface{}) (interface{}, error)
}

// 常见设备能力类型
const (
    CapabilitySwitchable = "switchable"  // 开关控制
    CapabilityDimmable = "dimmable"      // 亮度调节
    CapabilityColorable = "colorable"    // 颜色控制
    CapabilityThermostat = "thermostat"  // 温控
    CapabilitySensor = "sensor"          // 传感器
    // 更多能力类型...
)

// 抽象设备实现
type AbstractDevice struct {
    ID            string
    Name          string
    Manufacturer  string
    Model         string
    FirmwareVersion string
    Protocol      string
    Capabilities  map[string]Capability
    Online        bool
    LastSeen      time.Time
    Properties    map[string]interface{}
}

// 检查设备是否拥有特定能力
func (d *AbstractDevice) HasCapability(capabilityType string) bool {
    _, exists := d.Capabilities[capabilityType]
    return exists
}

// 执行设备命令
func (d *AbstractDevice) ExecuteCommand(capabilityType, command string, args map[string]interface{}) (interface{}, error) {
    capability, exists := d.Capabilities[capabilityType]
    if !exists {
        return nil, fmt.Errorf("device %s does not have capability %s", d.ID, capabilityType)
    }
    return capability.ExecuteCommand(command, args)
}

// ... existing code ...
```

### 2.3 动态协议发现与设备接入

```rust
// src/discovery/discovery_manager.rs
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;

pub struct DiscoveryManager {
    protocol_adapters: HashMap<String, Arc<dyn ProtocolAdapter>>,
    device_registry: Arc<DeviceRegistry>,
    discovery_channel: mpsc::Sender<DiscoveryEvent>,
}

impl DiscoveryManager {
    pub fn new(device_registry: Arc<DeviceRegistry>) -> (Self, mpsc::Receiver<DiscoveryEvent>) {
        let (tx, rx) = mpsc::channel(100);
        
        (Self {
            protocol_adapters: HashMap::new(),
            device_registry,
            discovery_channel: tx,
        }, rx)
    }
    
    pub fn register_protocol_adapter(&mut self, protocol: String, adapter: Arc<dyn ProtocolAdapter>) {
        self.protocol_adapters.insert(protocol, adapter);
    }
    
    pub async fn start_discovery(&self) -> Result<(), Error> {
        for (protocol, adapter) in &self.protocol_adapters {
            let adapter_clone = adapter.clone();
            let tx = self.discovery_channel.clone();
            let protocol = protocol.clone();
            
            tokio::spawn(async move {
                match adapter_clone.discover().await {
                    Ok(devices) => {
                        for device in devices {
                            let _ = tx.send(DiscoveryEvent::DeviceFound {
                                protocol: protocol.clone(),
                                device_info: device,
                            }).await;
                        }
                    }
                    Err(e) => {
                        log::error!("Discovery failed for protocol {}: {}", protocol, e);
                    }
                }
            });
        }
        
        Ok(())
    }
    
    pub async fn process_discovery_events(&self, mut rx: mpsc::Receiver<DiscoveryEvent>) {
        while let Some(event) = rx.recv().await {
            match event {
                DiscoveryEvent::DeviceFound { protocol, device_info } => {
                    if let Err(e) = self.device_registry.register_device(protocol, device_info).await {
                        log::error!("Failed to register device: {}", e);
                    }
                }
            }
        }
    }
}

// ... existing code ...
```

## 三、工作流引擎性能优化

工作流引擎是系统的核心组件，需要在资源受限环境中高效运行，同时保证执行可靠性。

### 3.1 轻量级工作流定义

```go
// workflow/definition.go
package workflow

// 工作流节点类型
const (
    NodeTypeStart = "start"
    NodeTypeEnd = "end"
    NodeTypeAction = "action"
    NodeTypeCondition = "condition"
    NodeTypeParallel = "parallel"
    NodeTypeWait = "wait"
    NodeTypeEvent = "event"
)

// WorkflowNode 工作流节点定义
type WorkflowNode struct {
    ID          string                 `json:"id"`
    Type        string                 `json:"type"`
    Name        string                 `json:"name"`
    NextNodes   []string               `json:"nextNodes,omitempty"`  // 普通节点的下一节点
    Branches    map[string][]string    `json:"branches,omitempty"`   // 条件节点的分支
    Properties  map[string]interface{} `json:"properties,omitempty"` // 节点特定属性
    Timeout     *int                   `json:"timeout,omitempty"`    // 节点超时秒数
    RetryPolicy *RetryPolicy           `json:"retryPolicy,omitempty"`// 重试策略
}

// WorkflowDefinition 工作流定义
type WorkflowDefinition struct {
    ID          string                 `json:"id"`
    Name        string                 `json:"name"`
    Version     int                    `json:"version"`
    Nodes       map[string]WorkflowNode`json:"nodes"`
    StartNodeID string                 `json:"startNodeID"`
    Metadata    map[string]interface{} `json:"metadata,omitempty"`
    CreatedAt   time.Time              `json:"createdAt"`
    UpdatedAt   time.Time              `json:"updatedAt"`
}

// RetryPolicy 重试策略
type RetryPolicy struct {
    MaxRetries  int     `json:"maxRetries"`
    Delay       int     `json:"delay"`       // 初始延迟(毫秒)
    MaxDelay    int     `json:"maxDelay"`    // 最大延迟(毫秒)
    Multiplier  float64 `json:"multiplier"`  // 延迟倍数
}

// ... existing code ...
```

### 3.2 优化的工作流执行引擎

```rust
// src/workflow/engine.rs
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use tokio::sync::{mpsc, RwLock};
use tokio::time::{self, Duration};

pub struct WorkflowEngine {
    workflow_registry: Arc<WorkflowRegistry>,
    workflow_executor: Arc<WorkflowExecutor>,
    state_manager: Arc<StateManager>,
    active_workflows: Arc<RwLock<HashMap<String, ActiveWorkflow>>>,
    compiled_workflows: Arc<RwLock<HashMap<String, CompiledWorkflow>>>,
}

impl WorkflowEngine {
    pub fn new(
        workflow_registry: Arc<WorkflowRegistry>,
        state_manager: Arc<StateManager>,
    ) -> Self {
        let workflow_executor = Arc::new(WorkflowExecutor::new());
        
        Self {
            workflow_registry,
            workflow_executor,
            state_manager,
            active_workflows: Arc::new(RwLock::new(HashMap::new())),
            compiled_workflows: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 预编译工作流优化执行性能
    pub async fn precompile_workflow(&self, workflow_id: &str) -> Result<(), Error> {
        let definition = self.workflow_registry.get_workflow(workflow_id).await?;
        
        // 创建优化的执行计划
        let compiled = self.create_execution_plan(&definition)?;
        
        // 缓存编译后的工作流
        let mut workflows = self.compiled_workflows.write().await;
        workflows.insert(workflow_id.to_string(), compiled);
        
        Ok(())
    }
    
    // 执行工作流
    pub async fn execute_workflow(
        &self,
        workflow_id: &str,
        input: HashMap<String, serde_json::Value>,
    ) -> Result<String, Error> {
        // 检查是否有预编译版本
        let compiled = {
            let workflows = self.compiled_workflows.read().await;
            workflows.get(workflow_id).cloned()
        };
        
        let execution_id = generate_uuid();
        
        // 如果有预编译版本，直接使用
        if let Some(compiled) = compiled {
            self.execute_compiled_workflow(execution_id.clone(), compiled, input).await?;
            return Ok(execution_id);
        }
        
        // 否则，获取定义并执行
        let definition = self.workflow_registry.get_workflow(workflow_id).await?;
        self.start_workflow_execution(execution_id.clone(), definition, input).await?;
        
        Ok(execution_id)
    }
    
    // 为热点工作流预热缓存
    pub async fn prewarm_hot_workflows(&self) -> Result<(), Error> {
        let hot_workflows = self.workflow_registry.get_hot_workflows().await?;
        
        for workflow_id in hot_workflows {
            if let Err(e) = self.precompile_workflow(&workflow_id).await {
                log::warn!("Failed to precompile hot workflow {}: {}", workflow_id, e);
                continue;
            }
        }
        
        Ok(())
    }
    
    // 快照工作流执行状态，用于故障恢复
    async fn snapshot_workflow_state(&self, execution_id: &str) -> Result<(), Error> {
        let active = {
            let workflows = self.active_workflows.read().await;
            workflows.get(execution_id).cloned()
        };
        
        if let Some(active) = active {
            self.state_manager.save_workflow_state(execution_id, active).await?;
        }
        
        Ok(())
    }
    
    // ... existing code ...
}

// ... existing code ...
```

### 3.3 工作流状态持久化与恢复

```go
// workflow/state.go
package workflow

import (
    "context"
    "encoding/json"
    "fmt"
    "time"
)

// WorkflowState 工作流状态
type WorkflowState struct {
    ExecutionID  string                 `json:"executionID"`
    WorkflowID   string                 `json:"workflowID"`
    CurrentNodes []string               `json:"currentNodes"`
    Variables    map[string]interface{} `json:"variables"`
    History      []NodeExecution        `json:"history"`
    Status       string                 `json:"status"`
    StartedAt    time.Time              `json:"startedAt"`
    UpdatedAt    time.Time              `json:"updatedAt"`
    CompletedAt  *time.Time             `json:"completedAt,omitempty"`
    Error        *WorkflowError         `json:"error,omitempty"`
}

// NodeExecution 节点执行记录
type NodeExecution struct {
    NodeID     string    `json:"nodeID"`
    StartedAt  time.Time `json:"startedAt"`
    CompletedAt *time.Time `json:"completedAt,omitempty"`
    Status     string    `json:"status"`
    Output     interface{} `json:"output,omitempty"`
    Error      *string   `json:"error,omitempty"`
}

// StateManager 状态管理接口
type StateManager interface {
    SaveState(ctx context.Context, state *WorkflowState) error
    GetState(ctx context.Context, executionID string) (*WorkflowState, error)
    ListActiveExecutions(ctx context.Context) ([]string, error)
    CleanupCompletedExecutions(ctx context.Context, olderThan time.Duration) error
}

// 多层次状态存储实现
type MultiLevelStateManager struct {
    memoryCache     *MemoryStateStore     // 内存缓存
    localStorage    *LocalFileStateStore  // 本地文件存储
    remoteStorage   *RemoteStateStore     // 远程存储(可选)
    stateCompress   bool                  // 是否压缩状态
    localMaxAge     time.Duration         // 本地存储保留时间
}

// SaveState 保存工作流状态，采用多层次策略
func (m *MultiLevelStateManager) SaveState(ctx context.Context, state *WorkflowState) error {
    // 始终更新内存缓存
    if err := m.memoryCache.SaveState(ctx, state); err != nil {
        return fmt.Errorf("memory cache save error: %w", err)
    }
    
    // 根据状态大小决定是否压缩
    stateData, err := json.Marshal(state)
    if err != nil {
        return fmt.Errorf("state serialization error: %w", err)
    }
    
    compressedState := state
    if m.stateCompress && len(stateData) > 4096 {
        // 对大状态进行压缩处理
        compressedState = m.compressState(state)
    }
    
    // 保存到本地存储
    if err := m.localStorage.SaveState(ctx, compressedState); err != nil {
        log.Warnf("Failed to save state to local storage: %v", err)
        // 继续执行，不让本地存储失败中断流程
    }
    
    // 特定条件下保存到远程存储
    if m.shouldSaveToRemote(state) && m.remoteStorage != nil {
        if err := m.remoteStorage.SaveState(ctx, compressedState); err != nil {
            log.Warnf("Failed to save state to remote storage: %v", err)
            // 继续执行，不让远程存储失败中断流程
        }
    }
    
    return nil
}

// GetState 获取工作流状态，采用层次查找策略
func (m *MultiLevelStateManager) GetState(ctx context.Context, executionID string) (*WorkflowState, error) {
    // 首先尝试从内存缓存获取
    state, err := m.memoryCache.GetState(ctx, executionID)
    if err == nil && state != nil {
        return state, nil
    }
    
    // 其次尝试从本地存储获取
    state, err = m.localStorage.GetState(ctx, executionID)
    if err == nil && state != nil {
        // 恢复到内存缓存
        _ = m.memoryCache.SaveState(ctx, state)
        return state, nil
    }
    
    // 最后尝试从远程存储获取
    if m.remoteStorage != nil {
        state, err = m.remoteStorage.GetState(ctx, executionID)
        if err == nil && state != nil {
            // 恢复到内存缓存和本地存储
            _ = m.memoryCache.SaveState(ctx, state)
            _ = m.localStorage.SaveState(ctx, state)
            return state, nil
        }
    }
    
    return nil, fmt.Errorf("workflow state not found: %s", executionID)
}

// ... existing code ...
```

### 3.4 资源监控与自适应调度

```rust
// src/engine/resource_monitor.rs
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::time;

pub struct ResourceMonitor {
    cpu_usage: Arc<Mutex<f32>>,
    memory_usage: Arc<Mutex<f32>>,
    disk_io: Arc<Mutex<f32>>,
    network_io: Arc<Mutex<f32>>,
    last_update: Arc<Mutex<Instant>>,
}

impl ResourceMonitor {
    pub fn new() -> Self {
        Self {
            cpu_usage: Arc::new(Mutex::new(0.0)),
            memory_usage: Arc::new(Mutex::new(0.0)),
            disk_io: Arc::new(Mutex::new(0.0)),
            network_io: Arc::new(Mutex::new(0.0)),
            last_update: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    pub async fn start_monitoring(&self) {
        let cpu_usage = self.cpu_usage.clone();
        let memory_usage = self.memory_usage.clone();
        let disk_io = self.disk_io.clone();
        let network_io = self.network_io.clone();
        let last_update = self.last_update.clone();
        
        tokio::spawn(async move {
            let mut interval = time::interval(Duration::from_secs(5));
            
            loop {
                interval.tick().await;
                
                // 获取系统资源使用情况
                let sys_info = get_system_info().await;
                
                // 更新监控数据
                {
                    let mut cpu = cpu_usage.lock().unwrap();
                    *cpu = sys_info.cpu_usage;
                    
                    let mut mem = memory_usage.lock().unwrap();
                    *mem = sys_info.memory_usage;
                    
                    let mut disk = disk_io.lock().unwrap();
                    *disk = sys_info.disk_io;
                    
                    let mut net = network_io.lock().unwrap();
                    *net = sys_info.network_io;
                    
                    let mut last = last_update.lock().unwrap();
                    *last = Instant::now();
                }
            }
        });
    }
    
    pub fn get_resource_usage(&self) -> ResourceUsage {
        let cpu = *self.cpu_usage.lock().unwrap();
        let memory = *self.memory_usage.lock().unwrap();
        let disk = *self.disk_io.lock().unwrap();
        let network = *self.network_io.lock().unwrap();
        
        ResourceUsage {
            cpu_usage: cpu,
            memory_usage: memory,
            disk_io: disk,
            network_io: network,
        }
    }
    
    pub fn should_throttle(&self) -> bool {
        let cpu = *self.cpu_usage.lock().unwrap();
        let memory = *self.memory_usage.lock().unwrap();
        
        // 简单策略：当CPU或内存使用率超过80%时限流
        cpu > 80.0 || memory > 80.0
    }
    
    pub fn get_recommended_concurrency(&self) -> usize {
        let cpu = *self.cpu_usage.lock().unwrap();
        let memory = *self.memory_usage.lock().unwrap();
        
        // 资源使用率越高，推荐的并发度越低
        let base_concurrency = 10;
        let cpu_factor = (100.0 - cpu) / 100.0;
        let mem_factor = (100.0 - memory) / 100.0;
        
        // 取两个因子的较小值
        let factor = if cpu_factor < mem_factor { cpu_factor } else { mem_factor };
        
        // 计算推荐并发度，最小为1
        let concurrency = (base_concurrency as f32 * factor).ceil() as usize;
        if concurrency < 1 { 1 } else { concurrency }
    }
}

// 自适应工作流调度器
pub struct AdaptiveScheduler {
    resource_monitor: Arc<ResourceMonitor>,
    max_concurrency: usize,
    execution_queue: Arc<Mutex<Vec<PendingExecution>>>,
}

impl AdaptiveScheduler {
    pub fn new(resource_monitor: Arc<ResourceMonitor>, max_concurrency: usize) -> Self {
        Self {
            resource_monitor,
            max_concurrency,
            execution_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub async fn schedule_workflow(
        &self,
        engine: Arc<WorkflowEngine>,
        workflow_id: String,
        input: HashMap<String, serde_json::Value>,
        priority: u8,
    ) -> Result<String, Error> {
        let execution_id = generate_uuid();
        
        // 高优先级工作流直接执行
        if priority >= 8 {
            return engine.execute_workflow(&workflow_id, input).await;
        }
        
        // 检查当前资源情况
        let current_concurrency = engine.get_active_executions_count().await;
        let recommended_concurrency = self.resource_monitor.get_recommended_concurrency();
        
        // 如果当前并发度低于推荐值，直接执行
        if current_concurrency < recommended_concurrency {
            return engine.execute_workflow(&workflow_id, input).await;
        }
        
        // 否则，加入调度队列
        {
            let mut queue = self.execution_queue.lock().unwrap();
            queue.push(PendingExecution {
                execution_id: execution_id.clone(),
                workflow_id,
                input,
                priority,
                enqueued_at: Instant::now(),
            });
            
            // 按优先级排序
            queue.sort_by(|a, b| b.priority.cmp(&a.priority));
        }
        
        Ok(execution_id)
    }
    
    pub async fn start_scheduler(&self, engine: Arc<WorkflowEngine>) {
        let execution_queue = self.execution_queue.clone();
        let resource_monitor = self.resource_monitor.clone();
        
        tokio::spawn(async move {
            let mut interval = time::interval(Duration::from_millis(100));
            
            loop {
                interval.tick().await;
                
                // 获取当前资源情况
                let current_concurrency = engine.get_active_executions_count().await;
                let recommended_concurrency = resource_monitor.get_recommended_concurrency();
                
                // 如果有富余资源，执行等待中的工作流
                if current_concurrency < recommended_concurrency {
                    let to_execute = {
                        let mut queue = execution_queue.lock().unwrap();
                        if queue.is_empty() {
                            None
                        } else {
                            Some(queue.remove(0))
                        }
                    };
                    
                    if let Some(pending) = to_execute {
                        // 执行工作流
                        if let Err(e) = engine.execute_workflow(&pending.workflow_id, pending.input).await {
                            log::error!("Failed to execute scheduled workflow: {}", e);
                        }
                    }
                }
            }
        });
    }
}

// ... existing code ...
```

## 四、用户体验简化

智能家居系统的复杂性需要通过良好的用户体验设计来简化，确保不给用户增加额外的学习成本。

### 4.1 场景模板与向导

```go
// template/scene_template.go
package template

// SceneTemplate 场景模板定义
type SceneTemplate struct {
    ID          string                 `json:"id"`
    Name        string                 `json:"name"`
    Description string                 `json:"description"`
    Category    string                 `json:"category"`
    Complexity  int                    `json:"complexity"`  // 1-5的复杂度等级
    Workflow    WorkflowDefinition     `json:"workflow"`
    Parameters  []TemplateParameter    `json:"parameters"`
    CompatibleDevices []DeviceRequirement `json:"compatibleDevices"`
    PreviewImage string                `json:"previewImage,omitempty"`
    PopularityScore float64            `json:"popularityScore"`
    Tags        []string               `json:"tags,omitempty"`
}

// TemplateParameter 模板参数
type TemplateParameter struct {
    ID          string      `json:"id"`
    Name        string      `json:"name"`
    Description string      `json:"description"`
    Type        string      `json:"type"`  // string, number, boolean, device, etc.
    Required    bool        `json:"required"`
    Default     interface{} `json:"default,omitempty"`
    Constraints interface{} `json:"constraints,omitempty"` // 参数约束
}

// DeviceRequirement 设备要求
type DeviceRequirement struct {
    Type        string   `json:"type"`           // 设备类型
    Capabilities []string `json:"capabilities"`  // 所需能力
    Count       int      `json:"count"`          // 所需数量
    Optional    bool     `json:"optional"`       // 是否可选
}

// SceneTemplateService 场景模板服务
type SceneTemplateService struct {
    repository  TemplateRepository
    deviceManager DeviceManager
}

// 根据用户家庭设备推荐合适的模板
func (s *SceneTemplateService) RecommendTemplates(userID string, limit int) ([]SceneTemplate, error) {
    // 获取用户设备列表
    devices, err := s.deviceManager.GetUserDevices(userID)
    if err != nil {
        return nil, fmt.Errorf("failed to get user devices: %w", err)
    }
    
    // 构建用户设备能力映射
    capabilityMap := make(map[string]int)
    deviceTypeMap := make(map[string]int)
    
    for _, device := range devices {
        deviceTypeMap[device.Type]++
        for cap := range device.Capabilities {
            capabilityMap[cap]++
        }
    }
    
    // 获取所有模板
    templates, err := s.repository.GetAllTemplates()
    if err != nil {
        return nil, fmt.Errorf("failed to get templates: %w", err)
    }
    
    // 计算每个模板的匹配度
    type templateScore struct {
        template SceneTemplate
        score    float64
    }
    
    var scores []templateScore
    
    for _, tmpl := range templates {
        score := calculateTemplateMatchScore(tmpl, deviceTypeMap, capabilityMap)
        scores = append(scores, templateScore{
            template: tmpl,
            score:    score,
        })
    }
    
    // 按匹配度排序
    sort.Slice(scores, func(i, j int) bool {
        return scores[i].score > scores[j].score
    })
    
    // 返回前N个推荐
    result := make([]SceneTemplate, 0, limit)
    for i := 0; i < len(scores) && i < limit; i++ {
        if scores[i].score > 0 {
            result = append(result, scores[i].template)
        }
    }
    
    return result, nil
}

// 计算模板与用户设备的匹配度
func calculateTemplateMatchScore(template SceneTemplate, deviceTypes map[string]int, capabilities map[string]int) float64 {
    // 基础分数
    score := 1.0
    
    // 检查必要设备需求是否满足
    for _, req := range template.CompatibleDevices {
        if req.Optional {
            continue
        }
        
        if deviceTypes[req.Type] < req.Count {
            return 0.0 // 必要设备不满足，直接返回0分
        }
        
        // 所有必须能力都要满足
        for _, cap := range req.Capabilities {
            if capabilities[cap] < req.Count {
                return 0.0 // 必要能力不满足，直接返回0分
            }
        }
    }
    
    // 增加匹配的可选设备的得分
    for _, req := range template.CompatibleDevices {
        if !req.Optional {
            continue
        }
        
        devCount := deviceTypes[req.Type]
        if devCount > 0 {
            matchRatio := float64(min(devCount, req.Count)) / float64(req.Count)
            score += 0.2 * matchRatio
        }
    }
    
    // 考虑模板的受欢迎程度
    score *= (1.0 + 0.3*min(template.PopularityScore/100.0, 1.0))
    
    return score
}

// ... existing code ...
```

### 4.2 自然语言场景创建

```go
// nlp/scene_creator.go
package nlp

import (
    "context"
    "fmt"
)

// NLSceneCreator 自然语言场景创建器
type NLSceneCreator struct {
    nlpService     NLPService
    deviceManager  DeviceManager
    sceneManager   SceneManager
    templateService TemplateService
}

// 通过自然语言创建场景
func (c *NLSceneCreator) CreateSceneFromText(ctx context.Context, userID, text string) (*Scene, error) {
    // 1. 使用NLP服务解析用户意图
    intent, err := c.nlpService.ParseSceneIntent(ctx, text)
    if err != nil {
        return nil, fmt.Errorf("failed to parse intent: %w", err)
    }
    
    // 2. 根据意图类型选择不同处理路径
    switch intent.Type {
    case IntentCreateBasicScene:
        return c.handleBasicSceneCreation(ctx, userID, intent)
    case IntentCreateScheduledScene:
        return c.handleScheduledSceneCreation(ctx, userID, intent)
    case IntentCreateConditionalScene:
        return c.handleConditionalSceneCreation(ctx, userID, intent)
    default:
        return nil, fmt.Errorf("unsupported intent type: %s", intent.Type)
    }
}

// 处理基本场景创建
func (c *NLSceneCreator) handleBasicSceneCreation(ctx context.Context, userID string, intent SceneIntent) (*Scene, error) {
    // 提取场景名称
    sceneName := intent.SceneName
    if sceneName == "" {
        sceneName = "我的场景"
    }
    
    // 创建场景
    scene := &Scene{
        Name:        sceneName,
        Description: intent.Description,
        Owner:       userID,
        Actions:     []Action{},
    }
    
    // 解析设备动作
    for _, actionIntent := range intent.DeviceActions {
        // 查找匹配的设备
        devices, err := c.findMatchingDevices(ctx, userID, actionIntent.DeviceQuery)
        if err != nil || len(devices) == 0 {
            return nil, fmt.Errorf("no matching devices found for: %s", actionIntent.DeviceQuery)
        }
        
        // 对每个匹配的设备创建动作
        for _, device := range devices {
            action, err := c.createDeviceAction(device, actionIntent)
            if err != nil {
                return nil, err
            }
            scene.Actions = append(scene.Actions, *action)
        }
    }
    
    // 保存场景
    savedScene, err := c.sceneManager.CreateScene(ctx, scene)
    if err != nil {
        return nil, fmt.Errorf("failed to save scene: %w", err)
    }
    
    return savedScene, nil
}

// 查找匹配设备
func (c *NLSceneCreator) findMatchingDevices(ctx context.Context, userID, query string) ([]Device, error) {
    // 首先尝试直接通过名称匹配
    devices, err := c.deviceManager.FindDevicesByName(ctx, userID, query)
    if err == nil && len(devices) > 0 {
        return devices, nil
    }
    
    // 然后尝试通过房间和类型匹配
    roomResult, err := c.nlpService.ExtractRoomAndDeviceType(ctx, query)
    if err != nil {
        return nil, err
    }
    
    var result []Device
    
    // 如果有房间信息，先根据房间筛选
    if roomResult.Room != "" {
        roomDevices, err := c.deviceManager.GetDevicesByRoom(ctx, userID, roomResult.Room)
        if err != nil {
            return nil, err
        }
        
        // 如果有设备类型，继续筛选
        if roomResult.DeviceType != "" {
            for _, device := range roomDevices {
                if device.Type == roomResult.DeviceType {
                    result = append(result, device)
                }
            }
        } else {
            result = roomDevices
        }
    } else if roomResult.DeviceType != "" {
        // 只有设备类型，根据类型查找
        typeDevices, err := c.deviceManager.GetDevicesByType(ctx, userID, roomResult.DeviceType)
        if err != nil {
            return nil, err
        }
        result = typeDevices
    }
    
    return result, nil
}

// 创建设备动作
func (c *NLSceneCreator) createDeviceAction(device Device, actionIntent ActionIntent) (*Action, error) {
    // 确定设备支持的能力
    capability := ""
    for _, cap := range actionIntent.PossibleCapabilities {
        if device.HasCapability(cap) {
            capability = cap
            break
        }
    }
    
    if capability == "" {
        return nil, fmt.Errorf("device %s does not support required capabilities", device.Name)
    }
    
    // 根据能力创建适当的命令参数
    command := actionIntent.Command
    params := map[string]interface{}{}
    
    switch capability {
    case CapabilitySwitchable:
        if actionIntent.State == "on" || actionIntent.State == "开" {
            command = "turnOn"
        } else {
            command = "turnOff"
        }
    case CapabilityDimmable:
        command = "setLevel"
        if actionIntent.Level > 0 {
            params["level"] = actionIntent.Level
        } else {
            params["level"] = 100 // 默认全亮
        }
    case CapabilityColorable:
        command = "setColor"
        if actionIntent.Color != "" {
            params["color"] = actionIntent.Color
        } else {
            params["color"] = "white" // 默认白色
        }
    case CapabilityThermostat:
        command = "setTemperature"
        if actionIntent.Temperature > 0 {
            params["temperature"] = actionIntent.Temperature
        } else {
            params["temperature"] = 24 // 默认24度
        }
    }
    
    // 创建动作
    action := &Action{
        DeviceID:    device.ID,
        Capability:  capability,
        Command:     command,
        Parameters:  params,
    }
    
    return action, nil
}

// ... existing code ...
```

### 4.3 可视化场景编辑器

```typescript
// src/components/SceneEditor.tsx
import React, { useState, useEffect, useRef } from 'react';
import { 
  Device, Action, Condition, Trigger, 
  WorkflowNode, WorkflowDefinition, SceneTemplate 
} from '../types';
import { 
  Canvas, NodeEditor, Toolbar, PropertyPanel,
  DeviceSelector, TriggerConfigurator
} from './editor';
import { sceneService, deviceService, templateService } from '../services';

interface SceneEditorProps {
  sceneId?: string; // 如果提供，则编辑现有场景
  templateId?: string; // 如果提供，则从模板创建
  onSave: (sceneId: string) => void;
  onCancel: () => void;
}

const SceneEditor: React.FC<SceneEditorProps> = ({ 
  sceneId, templateId, onSave, onCancel 
}) => {
  const [workflow, setWorkflow] = useState<WorkflowDefinition | null>(null);
  const [devices, setDevices] = useState<Device[]>([]);
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [modified, setModified] = useState(false);
  const [saving, setSaving] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [suggestedActions, setSuggestedActions] = useState<Action[]>([]);
  
  const canvasRef = useRef<any>(null);
  
  // 初始化编辑器
  useEffect(() => {
    const init = async () => {
      try {
        // 加载用户设备
        const userDevices = await deviceService.getUserDevices();
        setDevices(userDevices);
        
        // 加载初始工作流
        let initialWorkflow: WorkflowDefinition | null = null;
        
        if (sceneId) {
          // 编辑现有场景
          const scene = await sceneService.getScene(sceneId);
          initialWorkflow = scene.workflow;
        } else if (templateId) {
          // 从模板创建
          const template = await templateService.getTemplate(templateId);
          initialWorkflow = template.workflow;
        } else {
          // 创建新场景
          initialWorkflow = createEmptyWorkflow();
        }
        
        setWorkflow(initialWorkflow);
      } catch (err) {
        setError(`初始化编辑器失败: ${err.message}`);
      }
    };
    
    init();
  }, [sceneId, templateId]);
  
  // 当工作流变化时生成建议
  useEffect(() => {
    if (workflow && devices.length > 0) {
      generateSuggestions();
    }
  }, [workflow, devices]);
  
  // 生成智能建议
  const generateSuggestions = async () => {
    try {
      // 基于当前工作流和设备分析可能的建议
      const suggestions = await sceneService.getSuggestions(workflow, devices);
      setSuggestedActions(suggestions);
    } catch (err) {
      console.error("生成建议失败:", err);
    }
  };
  
  // 保存场景
  const handleSave = async () => {
    if (!workflow) return;
    
    try {
      setSaving(true);
      setError(null);
      
      // 验证工作流
      const validationResult = await sceneService.validateWorkflow(workflow);
      if (!validationResult.valid) {
        setError(`场景验证失败: ${validationResult.errors.join(', ')}`);
        setSaving(false);
        return;
      }
      
      // 保存场景
      let savedSceneId: string;
      if (sceneId) {
        await sceneService.updateScene(sceneId, {
          name: workflow.name,
          workflow: workflow
        });
        savedSceneId = sceneId;
      } else {
        const newScene = await sceneService.createScene({
          name: workflow.name,
          workflow: workflow
        });
        savedSceneId = newScene.id;
      }
      
      setSaving(false);
      setModified(false);
      onSave(savedSceneId);
    } catch (err) {
      setError(`保存场景失败: ${err.message}`);
      setSaving(false);
    }
  };
  
  // 添加节点到工作流
  const handleAddNode = (nodeType: string) => {
    if (!workflow) return;
    
    const newNode: WorkflowNode = {
      id: `node-${Date.now()}`,
      type: nodeType,
      name: `New ${nodeType}`,
      nextNodes: [],
      properties: {}
    };
    
    const updatedWorkflow = {
      ...workflow,
      nodes: {
        ...workflow.nodes,
        [newNode.id]: newNode
      }
    };
    
    setWorkflow(updatedWorkflow);
    setSelectedNode(newNode.id);
    setModified(true);
  };
  
  // 更新节点属性
  const handleUpdateNodeProperties = (nodeId: string, properties: any) => {
    if (!workflow || !workflow.nodes[nodeId]) return;
    
    const updatedNode = {
      ...workflow.nodes[nodeId],
      properties: {
        ...workflow.nodes[nodeId].properties,
        ...properties
      }
    };
    
    const updatedWorkflow = {
      ...workflow,
      nodes: {
        ...workflow.nodes,
        [nodeId]: updatedNode
      }
    };
    
    setWorkflow(updatedWorkflow);
    setModified(true);
  };
  
  // 连接节点
  const handleConnectNodes = (sourceId: string, targetId: string) => {
    if (!workflow || !workflow.nodes[sourceId] || !workflow.nodes[targetId]) return;
    
    const sourceNode = workflow.nodes[sourceId];
    
    // 确保不会创建循环
    if (isNodeInPath(targetId, sourceId, workflow)) {
      setError("无法创建循环路径");
      return;
    }
    
    // 更新连接
    const updatedSourceNode = {
      ...sourceNode,
      nextNodes: [...sourceNode.nextNodes.filter(id => id !== targetId), targetId]
    };
    
    const updatedWorkflow = {
      ...workflow,
      nodes: {
        ...workflow.nodes,
        [sourceId]: updatedSourceNode
      }
    };
    
    setWorkflow(updatedWorkflow);
    setModified(true);
  };
  
  // 应用建议的动作
  const handleApplySuggestion = (action: Action) => {
    if (!workflow) return;
    
    // 创建一个新的动作节点
    const actionNode: WorkflowNode = {
      id: `action-${Date.now()}`,
      type: 'action',
      name: `${action.deviceName} - ${action.command}`,
      nextNodes: [],
      properties: {
        deviceId: action.deviceId,
        capability: action.capability,
        command: action.command,
        parameters: action.parameters
      }
    };
    
    // 找到当前最后一个节点
    let lastNodeId = workflow.startNodeID;
    const nodesWithoutNext = Object.keys(workflow.nodes).filter(id => 
      workflow.nodes[id].nextNodes.length === 0 && id !== actionNode.id
    );
    
    if (nodesWithoutNext.length > 0) {
      lastNodeId = nodesWithoutNext[0];
    }
    
    // 将新节点加入工作流
    const updatedWorkflow = {
      ...workflow,
      nodes: {
        ...workflow.nodes,
        [actionNode.id]: actionNode
      }
    };
    
    // 更新连接
    if (lastNodeId) {
      updatedWorkflow.nodes[lastNodeId] = {
        ...updatedWorkflow.nodes[lastNodeId],
        nextNodes: [...updatedWorkflow.nodes[lastNodeId].nextNodes, actionNode.id]
      };
    }
    
    setWorkflow(updatedWorkflow);
    setSelectedNode(actionNode.id);
    setModified(true);
  };
  
  // 检查是否会创建循环路径
  const isNodeInPath = (startId: string, targetId: string, workflow: WorkflowDefinition): boolean => {
    const visited = new Set<string>();
    const stack = [startId];
    
    while (stack.length > 0) {
      const nodeId = stack.pop()!;
      
      if (nodeId === targetId) {
        return true;
      }
      
      if (!visited.has(nodeId)) {
        visited.add(nodeId);
        const node = workflow.nodes[nodeId];
        if (node && node.nextNodes) {
          stack.push(...node.nextNodes);
        }
      }
    }
    
    return false;
  };
  
  // 创建空工作流
  const createEmptyWorkflow = (): WorkflowDefinition => {
    const startNodeId = `start-${Date.now()}`;
    
    return {
      id: `workflow-${Date.now()}`,
      name: "新场景",
      version: 1,
      nodes: {
        [startNodeId]: {
          id: startNodeId,
          type: 'start',
          name: '开始',
          nextNodes: [],
          properties: {}
        }
      },
      startNodeID: startNodeId,
      metadata: {},
      createdAt: new Date(),
      updatedAt: new Date()
    };
  };
  
  if (!workflow) {
    return <div className="loading">加载编辑器...</div>;
  }
  
  return (
    <div className="scene-editor">
      <div className="editor-header">
        <h2>{sceneId ? "编辑场景" : "创建场景"}</h2>
        <input
          type="text"
          value={workflow.name}
          onChange={(e) => {
            setWorkflow({...workflow, name: e.target.value});
            setModified(true);
          }}
          placeholder="场景名称"
        />
        <div className="editor-actions">
          <button onClick={onCancel} disabled={saving}>取消</button>
          <button 
            onClick={handleSave} 
            disabled={saving || !modified}
            className="primary"
          >
            {saving ? "保存中..." : "保存场景"}
          </button>
        </div>
      </div>
      
      {error && <div className="error-message">{error}</div>}
      
      <div className="editor-main">
        <Toolbar onAddNode={handleAddNode} />
        
        <div className="canvas-container">
          <Canvas
            ref={canvasRef}
            workflow={workflow}
            onNodeSelect={setSelectedNode}
            onConnect={handleConnectNodes}
          />
        </div>
        
        <div className="editor-sidebar">
          {selectedNode && (
            <PropertyPanel
              node={workflow.nodes[selectedNode]}
              devices={devices}
              onUpdate={(props) => handleUpdateNodeProperties(selectedNode, props)}
            />
          )}
          
          <div className="suggestions-panel">
            <h3>智能建议</h3>
            {suggestedActions.length > 0 ? (
              <ul className="suggestions-list">
                {suggestedActions.map((action, index) => (
                  <li key={index} className="suggestion-item">
                    <div className="suggestion-content">
                      <span className="device-name">{action.deviceName}</span>
                      <span className="command">{action.command}</span>
                    </div>
                    <button onClick={() => handleApplySuggestion(action)}>
                      应用
                    </button>
                  </li>
                ))}
              </ul>
            ) : (
              <p className="no-suggestions">暂无建议</p>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

export default SceneEditor;
```

### 4.4 场景执行可视化与故障排查

```rust
// src/ui/execution_monitor.rs
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{self, Duration};

pub struct ExecutionMonitor {
    workflow_engine: Arc<WorkflowEngine>,
    active_executions: Arc<RwLock<HashMap<String, ExecutionStatus>>>,
    execution_history: Arc<RwLock<VecDeque<ExecutionRecord>>>,
    event_channel: mpsc::Sender<ExecutionEvent>,
}

impl ExecutionMonitor {
    pub fn new(workflow_engine: Arc<WorkflowEngine>) -> (Self, mpsc::Receiver<ExecutionEvent>) {
        let (tx, rx) = mpsc::channel(100);
        
        (Self {
            workflow_engine,
            active_executions: Arc::new(RwLock::new(HashMap::new())),
            execution_history: Arc::new(RwLock::new(VecDeque::with_capacity(100))),
            event_channel: tx,
        }, rx)
    }
    
    pub async fn start_monitoring(&self) {
        let engine = self.workflow_engine.clone();
        let active_executions = self.active_executions.clone();
        let execution_history = self.execution_history.clone();
        let event_channel = self.event_channel.clone();
        
        // 订阅工作流引擎事件
        let mut event_receiver = engine.subscribe_events().await;
        
        tokio::spawn(async move {
            while let Some(event) = event_receiver.recv().await {
                match event {
                    WorkflowEvent::ExecutionStarted { execution_id, workflow_id, .. } => {
                        let status = ExecutionStatus {
                            execution_id: execution_id.clone(),
                            workflow_id,
                            started_at: chrono::Utc::now(),
                            current_step: "初始化".to_string(),
                            status: "运行中".to_string(),
                            progress: 0,
                            current_nodes: vec![],
                            error: None,
                        };
                        
                        // 更新活动执行
                        {
                            let mut executions = active_executions.write().await;
                            executions.insert(execution_id.clone(), status.clone());
                        }
                        
                        // 发送UI事件
                        let _ = event_channel.send(ExecutionEvent::Started(status)).await;
                    },
                    WorkflowEvent::NodeStarted { execution_id, node_id, node_type, node_name, .. } => {
                        // 更新活动执行
                        {
                            let mut executions = active_executions.write().await;
                            if let Some(status) = executions.get_mut(&execution_id) {
                                status.current_step = format!("执行: {}", node_name);
                                status.current_nodes.push(node_id.clone());
                                
                                // 发送UI事件
                                let _ = event_channel.send(ExecutionEvent::StepStarted {
                                    execution_id: execution_id.clone(),
                                    node_id,
                                    node_type,
                                    node_name,
                                })).await;
                            }
                        }
                    },
                    WorkflowEvent::NodeCompleted { execution_id, node_id, output, .. } => {
                        // 更新活动执行
                        {
                            let mut executions = active_executions.write().await;
                            if let Some(status) = executions.get_mut(&execution_id) {
                                // 更新进度
                                let definition = engine.get_workflow_definition(&status.workflow_id).await.ok();
                                if let Some(def) = definition {
                                    let total_nodes = def.nodes.len();
                                    let completed_nodes = status.current_nodes.len();
                                    status.progress = (completed_nodes as f32 / total_nodes as f32 * 100.0) as i32;
                                }
                                
                                // 发送UI事件
                                let _ = event_channel.send(ExecutionEvent::StepCompleted {
                                    execution_id: execution_id.clone(),
                                    node_id,
                                    output,
                                })).await;
                            }
                        }
                    },
                    WorkflowEvent::ExecutionCompleted { execution_id, result, .. } => {
                        // 更新活动执行和历史记录
                        {
                            let mut executions = active_executions.write().await;
                            if let Some(mut status) = executions.remove(&execution_id) {
                                status.status = "已完成".to_string();
                                status.progress = 100;
                                status.completed_at = Some(chrono::Utc::now());
                                
                                // 添加到历史记录
                                let mut history = execution_history.write().await;
                                history.push_front(ExecutionRecord::from_status(status.clone(), None));
                                if history.len() > 100 {
                                    history.pop_back();
                                }
                                
                                // 发送UI事件
                                let _ = event_channel.send(ExecutionEvent::Completed {
                                    execution_id,
                                    result,
                                })).await;
                            }
                        }
                    },
                    WorkflowEvent::ExecutionFailed { execution_id, error, .. } => {
                        // 更新活动执行和历史记录
                        {
                            let mut executions = active_executions.write().await;
                            if let Some(mut status) = executions.remove(&execution_id) {
                                status.status = "失败".to_string();
                                status.error = Some(error.clone());
                                status.completed_at = Some(chrono::Utc::now());
                                
                                // 添加到历史记录
                                let mut history = execution_history.write().await;
                                history.push_front(ExecutionRecord::from_status(status.clone(), Some(error.clone())));
                                if history.len() > 100 {
                                    history.pop_back();
                                }
                                
                                // 发送UI事件
                                let _ = event_channel.send(ExecutionEvent::Failed {
                                    execution_id,
                                    error,
                                })).await;
                            }
                        }
                    },
                }
            }
        });
        
        // 启动定时清理任务
        let active_executions = self.active_executions.clone();
        tokio::spawn(async move {
            let mut interval = time::interval(Duration::from_secs(60));
            
            loop {
                interval.tick().await;
                
                // 检查长时间未更新的执行
                let now = chrono::Utc::now();
                let mut expired_executions = vec![];
                
                {
                    let executions = active_executions.read().await;
                    for (id, status) in executions.iter() {
                        // 超过30分钟未完成的执行视为卡住
                        if status.started_at + chrono::Duration::minutes(30) < now {
                            expired_executions.push(id.clone());
                        }
                    }
                }
                
                // 处理卡住的执行
                for execution_id in expired_executions {
                    // 尝试取消执行
                    if let Err(e) = engine.cancel_execution(&execution_id).await {
                        log::error!("Failed to cancel stuck execution {}: {}", execution_id, e);
                    }
                }
            }
        });
    }
    
    // 获取执行详情
    pub async fn get_execution_details(&self, execution_id: &str) -> Option<ExecutionDetails> {
        // 首先检查活动执行
        {
            let executions = self.active_executions.read().await;
            if let Some(status) = executions.get(execution_id) {
                let definition = self.workflow_engine.get_workflow_definition(&status.workflow_id).await.ok();
                return Some(ExecutionDetails {
                    status: status.clone(),
                    workflow_definition: definition,
                    node_history: vec![],
                });
            }
        }
        
        // 然后检查历史记录
        {
            let history = self.execution_history.read().await;
            for record in history.iter() {
                if record.execution_id == execution_id {
                    let definition = self.workflow_engine.get_workflow_definition(&record.workflow_id).await.ok();
                    
                    // 获取节点执行历史
                    let node_history = self.workflow_engine.get_execution_node_history(execution_id).await
                        .unwrap_or_else(|_| vec![]);
                    
                    return Some(ExecutionDetails {
                        status: ExecutionStatus::from_record(record),
                        workflow_definition: definition,
                        node_history,
                    });
                }
            }
        }
        
        None
    }
    
    // 重试失败的执行
    pub async fn retry_execution(&self, execution_id: &str) -> Result<String, Error> {
        // 先检查历史记录
        let record = {
            let history = self.execution_history.read().await;
            history.iter()
                .find(|r| r.execution_id == execution_id && r.status == "失败")
                .cloned()
        };
        
        if let Some(record) = record {
            // 创建新的执行
            let new_execution_id = self.workflow_engine.execute_workflow(
                &record.workflow_id, 
                record.input.clone()
            ).await?;
            
            return Ok(new_execution_id);
        }
        
        Err
```rust
        Err(Error::NotFound(format!("找不到失败的执行记录: {}", execution_id)))
    }
    
    // 获取执行历史
    pub async fn get_execution_history(&self, limit: usize) -> Vec<ExecutionRecord> {
        let history = self.execution_history.read().await;
        let mut result = Vec::new();
        
        for (i, record) in history.iter().enumerate() {
            if i >= limit {
                break;
            }
            result.push(record.clone());
        }
        
        result
    }
    
    // 分析执行故障模式
    pub async fn analyze_failure_patterns(&self) -> HashMap<String, FailurePattern> {
        let mut patterns = HashMap::new();
        
        // 获取历史记录
        let history = self.execution_history.read().await;
        
        // 分析失败的执行
        for record in history.iter() {
            if record.status != "失败" || record.error.is_none() {
                continue;
            }
            
            let error = record.error.as_ref().unwrap();
            let pattern_key = if error.contains("device connection") {
                "device_connection".to_string()
            } else if error.contains("timeout") {
                "timeout".to_string()
            } else if error.contains("permission") {
                "permission".to_string()
            } else {
                "other".to_string()
            };
            
            let entry = patterns.entry(pattern_key.clone()).or_insert_with(|| FailurePattern {
                pattern_type: pattern_key,
                count: 0,
                workflow_ids: HashMap::new(),
                error_messages: HashMap::new(),
                first_seen: chrono::Utc::now(),
                last_seen: chrono::UNIX_EPOCH.into(),
            });
            
            entry.count += 1;
            
            // 更新工作流统计
            *entry.workflow_ids.entry(record.workflow_id.clone()).or_insert(0) += 1;
            
            // 更新错误消息统计
            *entry.error_messages.entry(error.clone()).or_insert(0) += 1;
            
            // 更新时间范围
            if record.completed_at.unwrap_or(record.started_at) < entry.first_seen {
                entry.first_seen = record.completed_at.unwrap_or(record.started_at);
            }
            
            if record.completed_at.unwrap_or(record.started_at) > entry.last_seen {
                entry.last_seen = record.completed_at.unwrap_or(record.started_at);
            }
        }
        
        patterns
    }
}

// ... existing code ...
```

## 五、安全与隐私保护

智能家居系统处理敏感数据和控制关键设备，必须具备全面的安全与隐私保护机制。

### 5.1 设备层安全

```rust
// src/security/device_security.rs
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use ring::aead::{self, BoundKey, NonceSequence, Aad, UnboundKey, SealingKey, OpeningKey};
use ring::rand::{SecureRandom, SystemRandom};

pub struct DeviceSecurityManager {
    device_keys: Arc<RwLock<HashMap<String, DeviceSecurityContext>>>,
    random: SystemRandom,
    key_rotation_interval: chrono::Duration,
}

struct DeviceSecurityContext {
    device_id: String,
    encryption_key: Vec<u8>,
    signing_key: Vec<u8>,
    last_rotation: chrono::DateTime<chrono::Utc>,
    key_version: u32,
}

impl DeviceSecurityManager {
    pub fn new(key_rotation_days: u32) -> Self {
        Self {
            device_keys: Arc::new(RwLock::new(HashMap::new())),
            random: SystemRandom::new(),
            key_rotation_interval: chrono::Duration::days(key_rotation_days as i64),
        }
    }
    
    // 设备认证
    pub async fn authenticate_device(&self, device_id: &str, auth_data: &DeviceAuthData) -> Result<bool, SecurityError> {
        // 获取设备安全上下文
        let context = {
            let keys = self.device_keys.read().await;
            keys.get(device_id).cloned()
        };
        
        let context = match context {
            Some(ctx) => ctx,
            None => return Err(SecurityError::DeviceNotRegistered(device_id.to_string())),
        };
        
        // 验证时间戳，防止重放攻击
        let now = chrono::Utc::now();
        let auth_time = chrono::DateTime::from_timestamp(auth_data.timestamp as i64, 0)
            .ok_or(SecurityError::InvalidTimestamp)?;
            
        if (now - auth_time).num_seconds().abs() > 300 {
            return Err(SecurityError::TimestampOutOfRange);
        }
        
        // 验证签名
        let message = format!("{}:{}", device_id, auth_data.timestamp);
        let verified = self.verify_signature(&context.signing_key, message.as_bytes(), &auth_data.signature)?;
        
        if !verified {
            return Err(SecurityError::SignatureVerificationFailed);
        }
        
        // 检查是否需要轮换密钥
        if now - context.last_rotation > self.key_rotation_interval {
            let device_keys = self.device_keys.clone();
            let device_id = device_id.to_string();
            let manager = self.clone();
            
            // 异步轮换密钥，不阻塞当前认证流程
            tokio::spawn(async move {
                if let Err(e) = manager.rotate_device_keys(&device_id).await {
                    log::error!("Failed to rotate keys for device {}: {}", device_id, e);
                }
            });
        }
        
        Ok(true)
    }
    
    // 设备通信加密
    pub async fn encrypt_message(&self, device_id: &str, message: &[u8]) -> Result<EncryptedMessage, SecurityError> {
        // 获取设备安全上下文
        let context = {
            let keys = self.device_keys.read().await;
            keys.get(device_id).cloned()
        };
        
        let context = match context {
            Some(ctx) => ctx,
            None => return Err(SecurityError::DeviceNotRegistered(device_id.to_string())),
        };
        
        // 创建随机nonce
        let mut nonce = [0u8; 12];
        self.random.fill(&mut nonce).map_err(|_| SecurityError::RandomGenerationFailed)?;
        
        // 加密消息
        let unbound_key = UnboundKey::new(&aead::CHACHA20_POLY1305, &context.encryption_key)
            .map_err(|_| SecurityError::KeyCreationFailed)?;
            
        let mut sealing_key = SealingKey::new(unbound_key, CounterNonce::new(nonce));
        
        let mut in_out = message.to_vec();
        let aad = Aad::empty();
        
        sealing_key.seal_in_place_append_tag(aad, &mut in_out)
            .map_err(|_| SecurityError::EncryptionFailed)?;
        
        Ok(EncryptedMessage {
            ciphertext: in_out,
            nonce: nonce.to_vec(),
            key_version: context.key_version,
        })
    }
    
    // 设备通信解密
    pub async fn decrypt_message(&self, device_id: &str, encrypted: &EncryptedMessage) -> Result<Vec<u8>, SecurityError> {
        // 获取设备安全上下文
        let context = {
            let keys = self.device_keys.read().await;
            keys.get(device_id).cloned()
        };
        
        let context = match context {
            Some(ctx) => ctx,
            None => return Err(SecurityError::DeviceNotRegistered(device_id.to_string())),
        };
        
        // 验证密钥版本
        if encrypted.key_version != context.key_version {
            return Err(SecurityError::KeyVersionMismatch);
        }
        
        // 解密消息
        let unbound_key = UnboundKey::new(&aead::CHACHA20_POLY1305, &context.encryption_key)
            .map_err(|_| SecurityError::KeyCreationFailed)?;
            
        let nonce = match encrypted.nonce.try_into() {
            Ok(n) => n,
            Err(_) => return Err(SecurityError::InvalidNonce),
        };
        
        let mut opening_key = OpeningKey::new(unbound_key, CounterNonce::new(nonce));
        
        let mut in_out = encrypted.ciphertext.clone();
        let aad = Aad::empty();
        
        let decrypted_len = opening_key.open_in_place(aad, &mut in_out)
            .map_err(|_| SecurityError::DecryptionFailed)?
            .len();
            
        in_out.truncate(decrypted_len);
        
        Ok(in_out)
    }
    
    // 密钥轮换
    async fn rotate_device_keys(&self, device_id: &str) -> Result<(), SecurityError> {
        // 获取当前安全上下文
        let mut context = {
            let keys = self.device_keys.read().await;
            keys.get(device_id).cloned()
        };
        
        let mut context = match context {
            Some(ctx) => ctx,
            None => return Err(SecurityError::DeviceNotRegistered(device_id.to_string())),
        };
        
        // 生成新密钥
        let mut new_encryption_key = vec![0u8; 32];
        self.random.fill(&mut new_encryption_key).map_err(|_| SecurityError::RandomGenerationFailed)?;
        
        let mut new_signing_key = vec![0u8; 32];
        self.random.fill(&mut new_signing_key).map_err(|_| SecurityError::RandomGenerationFailed)?;
        
        // 更新安全上下文
        context.encryption_key = new_encryption_key;
        context.signing_key = new_signing_key;
        context.last_rotation = chrono::Utc::now();
        context.key_version += 1;
        
        // 保存更新后的上下文
        {
            let mut keys = self.device_keys.write().await;
            keys.insert(device_id.to_string(), context);
        }
        
        // 通知设备更新密钥
        self.notify_device_key_rotation(device_id).await?;
        
        Ok(())
    }
    
    // 验证签名
    fn verify_signature(&self, key: &[u8], message: &[u8], signature: &[u8]) -> Result<bool, SecurityError> {
        // 使用HMAC-SHA256验证签名
        use ring::hmac;
        
        let key = hmac::Key::new(hmac::HMAC_SHA256, key);
        let tag = hmac::sign(&key, message);
        
        let expected_signature = tag.as_ref();
        
        if signature.len() != expected_signature.len() {
            return Ok(false);
        }
        
        // 恒定时间比较防止计时攻击
        let mut result = 0;
        for (a, b) in signature.iter().zip(expected_signature.iter()) {
            result |= a ^ b;
        }
        
        Ok(result == 0)
    }
    
    // 通知设备更新密钥
    async fn notify_device_key_rotation(&self, device_id: &str) -> Result<(), SecurityError> {
        // 实际实现中，这里会通过安全通道通知设备进行密钥更新
        // 此处为示例，实际实现需要根据具体通信协议
        Ok(())
    }
}

// Nonce生成器
struct CounterNonce {
    nonce: [u8; 12],
}

impl CounterNonce {
    fn new(nonce: [u8; 12]) -> Self {
        Self { nonce }
    }
}

impl NonceSequence for CounterNonce {
    fn advance(&mut self) -> Result<Nonce, ring::error::Unspecified> {
        Ok(*GenericArray::from_slice(&self.nonce))
    }
}

// ... existing code ...
```

### 5.2 数据隐私与访问控制

```go
// privacy/data_manager.go
package privacy

import (
    "context"
    "fmt"
    "time"
)

// 数据敏感级别
const (
    DataSensitivityLow    = 1
    DataSensitivityMedium = 2
    DataSensitivityHigh   = 3
    DataSensitivityCritical = 4
)

// 数据类型
const (
    DataTypeDeviceStatus = "device_status"
    DataTypeUserActivity = "user_activity"
    DataTypeLocation     = "location"
    DataTypeAudio        = "audio"
    DataTypeVideo        = "video"
    DataTypeHealthData   = "health_data"
)

// 数据处理目的
const (
    PurposeDeviceControl  = "device_control"
    PurposeAutomation     = "automation"
    PurposeAnalytics      = "analytics"
    PurposeUserProfile    = "user_profile"
    PurposeThirdParty     = "third_party"
)

// 数据位置
const (
    StorageLocalOnly       = "local_only"
    StorageLocalAndCloud   = "local_and_cloud"
    StorageCloudOnly       = "cloud_only"
)

// DataPolicy 数据隐私策略
type DataPolicy struct {
    DataType        string
    Sensitivity     int
    RetentionPeriod time.Duration
    StorageLocation string
    AllowedPurposes map[string]bool
    Anonymize       bool
    Encrypt         bool
}

// DataPrivacyManager 数据隐私管理器
type DataPrivacyManager struct {
    policies        map[string]DataPolicy
    userPreferences map[string]map[string]UserPrivacyPreference
    accessControl   AccessController
}

// UserPrivacyPreference 用户隐私偏好
type UserPrivacyPreference struct {
    DataType        string
    ConsentedPurposes map[string]bool
    StorageOption   string
    RetentionOverride *time.Duration
}

// NewDataPrivacyManager 创建数据隐私管理器
func NewDataPrivacyManager(accessControl AccessController) *DataPrivacyManager {
    // 初始化默认数据策略
    defaultPolicies := map[string]DataPolicy{
        DataTypeDeviceStatus: {
            DataType:        DataTypeDeviceStatus,
            Sensitivity:     DataSensitivityLow,
            RetentionPeriod: 30 * 24 * time.Hour, // 30天
            StorageLocation: StorageLocalAndCloud,
            AllowedPurposes: map[string]bool{
                PurposeDeviceControl: true,
                PurposeAutomation:    true,
                PurposeAnalytics:     true,
            },
            Anonymize: false,
            Encrypt:   true,
        },
        DataTypeUserActivity: {
            DataType:        DataTypeUserActivity,
            Sensitivity:     DataSensitivityMedium,
            RetentionPeriod: 90 * 24 * time.Hour, // 90天
            StorageLocation: StorageLocalAndCloud,
            AllowedPurposes: map[string]bool{
                PurposeAutomation: true,
                PurposeAnalytics:  true,
                PurposeUserProfile: true,
            },
            Anonymize: false,
            Encrypt:   true,
        },
        DataTypeLocation: {
            DataType:        DataTypeLocation,
            Sensitivity:     DataSensitivityHigh,
            RetentionPeriod: 7 * 24 * time.Hour, // 7天
            StorageLocation: StorageLocalOnly,
            AllowedPurposes: map[string]bool{
                PurposeAutomation: true,
            },
            Anonymize: true,
            Encrypt:   true,
        },
        DataTypeAudio: {
            DataType:        DataTypeAudio,
            Sensitivity:     DataSensitivityHigh,
            RetentionPeriod: 24 * time.Hour, // 1天
            StorageLocation: StorageLocalOnly,
            AllowedPurposes: map[string]bool{
                PurposeDeviceControl: true,
            },
            Anonymize: true,
            Encrypt:   true,
        },
        DataTypeVideo: {
            DataType:        DataTypeVideo,
            Sensitivity:     DataSensitivityCritical,
            RetentionPeriod: 48 * time.Hour, // 2天
            StorageLocation: StorageLocalOnly,
            AllowedPurposes: map[string]bool{},
            Anonymize: false,
            Encrypt:   true,
        },
        DataTypeHealthData: {
            DataType:        DataTypeHealthData,
            Sensitivity:     DataSensitivityCritical,
            RetentionPeriod: 365 * 24 * time.Hour, // 1年
            StorageLocation: StorageLocalOnly,
            AllowedPurposes: map[string]bool{
                PurposeUserProfile: true,
            },
            Anonymize: true,
            Encrypt:   true,
        },
    }
    
    return &DataPrivacyManager{
        policies:        defaultPolicies,
        userPreferences: make(map[string]map[string]UserPrivacyPreference),
        accessControl:   accessControl,
    }
}

// 检查数据处理权限
func (m *DataPrivacyManager) CheckDataProcessingPermission(
    ctx context.Context,
    userID string,
    dataType string,
    purpose string,
) (bool, error) {
    // 获取数据策略
    policy, exists := m.policies[dataType]
    if !exists {
        return false, fmt.Errorf("无效的数据类型: %s", dataType)
    }
    
    // 检查策略是否允许该目的
    if !policy.AllowedPurposes[purpose] {
        return false, nil
    }
    
    // 检查用户偏好
    userPrefs, exists := m.userPreferences[userID]
    if exists {
        if pref, hasPref := userPrefs[dataType]; hasPref {
            if !pref.ConsentedPurposes[purpose] {
                return false, nil
            }
        }
    }
    
    // 检查访问控制
    caller := GetCallerFromContext(ctx)
    if caller == nil {
        return false, fmt.Errorf("无法识别调用者")
    }
    
    allowed, err := m.accessControl.CheckAccess(caller, dataType, ActionProcess)
    if err != nil {
        return false, fmt.Errorf("访问控制检查失败: %w", err)
    }
    
    return allowed, nil
}

// 确定数据存储位置
func (m *DataPrivacyManager) DetermineStorageLocation(
    userID string,
    dataType string,
) (string, error) {
    // 获取数据策略
    policy, exists := m.policies[dataType]
    if !exists {
        return "", fmt.Errorf("无效的数据类型: %s", dataType)
    }
    
    // 检查用户偏好
    userPrefs, exists := m.userPreferences[userID]
    if exists {
        if pref, hasPref := userPrefs[dataType]; hasPref && pref.StorageOption != "" {
            return pref.StorageOption, nil
        }
    }
    
    return policy.StorageLocation, nil
}

// 应用数据处理规则
func (m *DataPrivacyManager) ApplyDataProcessingRules(
    ctx context.Context,
    userID string,
    data *DataItem,
) (*ProcessedDataItem, error) {
    // 获取数据策略
    policy, exists := m.policies[data.Type]
    if !exists {
        return nil, fmt.Errorf("无效的数据类型: %s", data.Type)
    }
    
    // 检查处理权限
    permitted, err := m.CheckDataProcessingPermission(ctx, userID, data.Type, data.Purpose)
    if err != nil {
        return nil, err
    }
    
    if !permitted {
        return nil, fmt.Errorf("没有处理该数据的权限")
    }
    
    // 创建处理后的数据副本
    processed := &ProcessedDataItem{
        ID:        data.ID,
        Type:      data.Type,
        Timestamp: data.Timestamp,
        UserID:    userID,
        Purpose:   data.Purpose,
        Content:   data.Content,
    }
    
    // 应用数据处理规则
    if policy.Anonymize {
        processed.Content = m.anonymizeData(data.Type, data.Content)
        processed.Anonymized = true
    }
    
    // 确定存储位置
    storageLocation, err := m.DetermineStorageLocation(userID, data.Type)
    if err != nil {
        return nil, err
    }
    processed.StorageLocation = storageLocation
    
    // 设置数据保留期限
    retentionPeriod := policy.RetentionPeriod
    
    // 检查用户偏好中的保留期覆盖
    userPrefs, exists := m.userPreferences[userID]
    if exists {
        if pref, hasPref := userPrefs[data.Type]; hasPref && pref.RetentionOverride != nil {
            retentionPeriod = *pref.RetentionOverride
        }
    }
    
    processed.ExpiryTime = time.Now().Add(retentionPeriod)
    
    return processed, nil
}

// 匿名化数据
func (m *DataPrivacyManager) anonymizeData(dataType string, content interface{}) interface{} {
    // 根据数据类型应用不同的匿名化策略
    switch dataType {
    case DataTypeLocation:
        return m.anonymizeLocationData(content)
    case DataTypeUserActivity:
        return m.anonymizeActivityData(content)
    case DataTypeAudio:
        return m.anonymizeAudioData(content)
    case DataTypeHealthData:
        return m.anonymizeHealthData(content)
    default:
        return content
    }
}

// ... existing code ...
```

### 5.3 通信加密与安全通道

```rust
// src/security/secure_comm.rs
use std::sync::Arc;
use tokio::io::{AsyncRead, AsyncWrite};
use tokio_rustls::rustls::{self, ClientConfig, ServerConfig};
use tokio_rustls::{TlsAcceptor, TlsConnector};
use std::fs::File;
use std::io::BufReader;

pub struct SecureCommManager {
    client_config: Arc<ClientConfig>,
    server_config: Arc<ServerConfig>,
    certificate_manager: Arc<CertificateManager>,
}

impl SecureCommManager {
    pub fn new(
        cert_path: &str, 
        key_path: &str,
        trusted_certs_path: &str,
    ) -> Result<Self, SecurityError> {
        // 加载服务器证书和私钥
        let cert_file = File::open(cert_path)
            .map_err(|e| SecurityError::CertificateLoadError(e.to_string()))?;
        let mut cert_reader = BufReader::new(cert_file);
        
        let key_file = File::open(key_path)
            .map_err(|e| SecurityError::KeyLoadError(e.to_string()))?;
        let mut key_reader = BufReader::new(key_file);
        
        // 加载证书链
        let cert_chain = rustls_pemfile::certs(&mut cert_reader)
            .filter_map(Result::ok)
            .map(rustls::Certificate)
            .collect::<Vec<_>>();
        
        if cert_chain.is_empty() {
            return Err(SecurityError::CertificateParseError("Empty certificate chain".to_string()));
        }
        
        // 加载私钥
        let mut keys = rustls_pemfile::pkcs8_private_keys(&mut key_reader)
            .filter_map(Result::ok)
            .collect::<Vec<_>>();
            
        if keys.is_empty() {
            return Err(SecurityError::KeyParseError("No private keys found".to_string()));
        }
        
        let key = rustls::PrivateKey(keys.remove(0));
        
        // 加载可信证书
        let mut root_store = rustls::RootCertStore::empty();
        let trusted_cert_file = File::open(trusted_certs_path)
            .map_err(|e| SecurityError::CertificateLoadError(e.to_string()))?;
        let mut trusted_cert_reader = BufReader::new(trusted_cert_file);
        
        let trusted_certs = rustls_pemfile::certs(&mut trusted_cert_reader)
            .filter_map(Result::ok)
            .map(rustls::Certificate)
            .collect::<Vec<_>>();
            
        for cert in trusted_certs {
            root_store.add(&cert).map_err(|e| {
                SecurityError::CertificateParseError(format!("Failed to add trusted cert: {}", e))
            })?;
        }
        
        // 创建服务器配置
        let server_config = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(cert_chain.clone(), key.clone())
            .map_err(|e| SecurityError::ConfigurationError(e.to_string()))?;
            
        // 创建客户端配置
        let client_config = ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(root_store)
            .with_single_cert(cert_chain, key)
            .map_err(|e| SecurityError::ConfigurationError(e.to_string()))?;
            
        // 创建证书管理器
        let certificate_manager = Arc::new(CertificateManager::new(
            cert_path, key_path, trusted_certs_path
        )?);
        
        Ok(Self {
            client_config: Arc::new(client_config),
            server_config: Arc::new(server_config),
            certificate_manager,
        })
    }
    
    // 创建安全客户端连接
    pub async fn connect_to_server<S>(&self, stream: S, server_name: &str) 
        -> Result<SecureStream<tokio_rustls::client::TlsStream<S>>, SecurityError>
    where
        S: AsyncRead + AsyncWrite + Unpin,
    {
        let connector = TlsConnector::from(self.client_config.clone());
        let server_name = rustls::ServerName::try_from(server_name)
            .map_err(|e| SecurityError::ConfigurationError(e.to_string()))?;
            
        let stream = connector.connect(server_name, stream).await
            .map_err(|e| SecurityError::ConnectionError(e.to_string()))?;
            
        Ok(SecureStream { stream })
    }
    
    // 接受安全客户端连接
    pub async fn accept_client<S>(&self, stream: S) 
        -> Result<SecureStream<tokio_rustls::server::TlsStream<S>>, SecurityError>
    where
        S: AsyncRead + AsyncWrite + Unpin,
    {
        let acceptor = TlsAcceptor::from(self.server_config.clone());
        
        let stream = acceptor.accept(stream).await
            .map_err(|e| SecurityError::ConnectionError(e.to_string()))?;
            
        Ok(SecureStream { stream })
    }
    
    // 轮换证书
    pub async fn rotate_certificates(&self) -> Result<(), SecurityError> {
        self.certificate_manager.rotate_certificates().await
    }
    
    // 撤销证书
    pub async fn revoke_certificate(&self, serial: &str) -> Result<(), SecurityError> {
        self.certificate_manager.revoke_certificate(serial).await
    }
}

// 安全流包装器
pub struct SecureStream<S> {
    stream: S,
}

impl<S> SecureStream<S> 
where
    S: AsyncRead + AsyncWrite + Unpin,
{
    // 发送加密消息
    pub async fn send_message(&mut self, message: &[u8]) -> Result<(), SecurityError> {
        use tokio::io::AsyncWriteExt;
        
        // 写入消息长度
        let len = message.len() as u32;
        let len_bytes = len.to_be_bytes();
        
        self.stream.write_all(&len_bytes).await
            .map_err(|e| SecurityError::CommunicationError(e.to_string()))?;
            
        // 写入消息内容
        self.stream.write_all(message).await
            .map_err(|e| SecurityError::CommunicationError(e.to_string()))?;
            
        self.stream.flush().await
            .map_err(|e| SecurityError::CommunicationError(e.to_string()))?;
            
        Ok(())
    }
    
    // 接收加密消息
```rust
    // 接收加密消息
    pub async fn receive_message(&mut self) -> Result<Vec<u8>, SecurityError> {
        use tokio::io::AsyncReadExt;
        
        // 读取消息长度
        let mut len_bytes = [0u8; 4];
        self.stream.read_exact(&mut len_bytes).await
            .map_err(|e| SecurityError::CommunicationError(e.to_string()))?;
            
        let len = u32::from_be_bytes(len_bytes) as usize;
        
        // 检查长度是否合理，防止恶意长消息
        if len > 1024 * 1024 {  // 限制为1MB
            return Err(SecurityError::MessageTooLarge(len));
        }
        
        // 读取消息内容
        let mut message = vec![0u8; len];
        self.stream.read_exact(&mut message).await
            .map_err(|e| SecurityError::CommunicationError(e.to_string()))?;
            
        Ok(message)
    }
    
    // 获取底层流
    pub fn into_inner(self) -> S {
        self.stream
    }
}

// 证书管理器
pub struct CertificateManager {
    cert_path: String,
    key_path: String,
    trusted_certs_path: String,
    cert_db: Arc<RwLock<CertificateDatabase>>,
}

impl CertificateManager {
    pub fn new(
        cert_path: &str,
        key_path: &str,
        trusted_certs_path: &str,
    ) -> Result<Self, SecurityError> {
        let cert_db = CertificateDatabase::load()
            .map_err(|e| SecurityError::DatabaseError(e.to_string()))?;
            
        Ok(Self {
            cert_path: cert_path.to_string(),
            key_path: key_path.to_string(),
            trusted_certs_path: trusted_certs_path.to_string(),
            cert_db: Arc::new(RwLock::new(cert_db)),
        })
    }
    
    // 轮换证书
    pub async fn rotate_certificates(&self) -> Result<(), SecurityError> {
        // 生成新的证书和密钥对
        let (new_cert, new_key) = self.generate_new_certificate()?;
        
        // 保存新证书和密钥
        std::fs::write(&self.cert_path, &new_cert)
            .map_err(|e| SecurityError::CertificateWriteError(e.to_string()))?;
            
        std::fs::write(&self.key_path, &new_key)
            .map_err(|e| SecurityError::KeyWriteError(e.to_string()))?;
            
        // 更新证书数据库
        let cert_info = self.parse_certificate_info(&new_cert)?;
        
        {
            let mut db = self.cert_db.write().await;
            db.add_certificate(cert_info.clone()).await?;
        }
        
        // 通知连接的设备和客户端证书已更新
        self.notify_certificate_update(cert_info).await?;
        
        Ok(())
    }
    
    // 撤销证书
    pub async fn revoke_certificate(&self, serial: &str) -> Result<(), SecurityError> {
        {
            let mut db = self.cert_db.write().await;
            db.revoke_certificate(serial).await?;
        }
        
        // 生成新的CRL
        self.generate_crl().await?;
        
        // 通知连接的设备和客户端CRL已更新
        self.notify_crl_update().await?;
        
        Ok(())
    }
    
    // 验证证书是否有效
    pub async fn validate_certificate(&self, cert_data: &[u8]) -> Result<bool, SecurityError> {
        let cert_info = self.parse_certificate_info(cert_data)?;
        
        // 检查证书是否已撤销
        {
            let db = self.cert_db.read().await;
            if db.is_revoked(&cert_info.serial).await? {
                return Ok(false);
            }
        }
        
        // 验证证书有效期
        let now = chrono::Utc::now();
        if now < cert_info.not_before || now > cert_info.not_after {
            return Ok(false);
        }
        
        // TODO: 验证证书链和签名
        
        Ok(true)
    }
    
    // 生成新证书
    fn generate_new_certificate(&self) -> Result<(Vec<u8>, Vec<u8>), SecurityError> {
        // 实际实现中，这里会使用如rcgen库生成新证书
        // 此处为简化示例
        Err(SecurityError::NotImplemented("Certificate generation not implemented".to_string()))
    }
    
    // 解析证书信息
    fn parse_certificate_info(&self, cert_data: &[u8]) -> Result<CertificateInfo, SecurityError> {
        // 实际实现中，这里会解析X.509证书
        // 此处为简化示例
        Err(SecurityError::NotImplemented("Certificate parsing not implemented".to_string()))
    }
    
    // 生成证书吊销列表
    async fn generate_crl(&self) -> Result<(), SecurityError> {
        // 实际实现中，这里会生成CRL
        // 此处为简化示例
        Ok(())
    }
    
    // 通知证书更新
    async fn notify_certificate_update(&self, cert_info: CertificateInfo) -> Result<(), SecurityError> {
        // 实际实现中，这里会通知已连接的设备和客户端
        // 此处为简化示例
        Ok(())
    }
    
    // 通知CRL更新
    async fn notify_crl_update(&self) -> Result<(), SecurityError> {
        // 实际实现中，这里会通知已连接的设备和客户端
        // 此处为简化示例
        Ok(())
    }
}

// 证书数据库
struct CertificateDatabase {
    certificates: HashMap<String, CertificateInfo>,
    revoked_certificates: HashMap<String, RevokedCertInfo>,
}

impl CertificateDatabase {
    fn load() -> Result<Self, Error> {
        // 实际实现中，这里会从持久化存储加载证书数据库
        // 此处为简化示例
        Ok(Self {
            certificates: HashMap::new(),
            revoked_certificates: HashMap::new(),
        })
    }
    
    async fn add_certificate(&mut self, cert_info: CertificateInfo) -> Result<(), Error> {
        self.certificates.insert(cert_info.serial.clone(), cert_info);
        self.save().await
    }
    
    async fn revoke_certificate(&mut self, serial: &str) -> Result<(), Error> {
        if let Some(cert_info) = self.certificates.remove(serial) {
            let revoked_info = RevokedCertInfo {
                serial: serial.to_string(),
                revocation_date: chrono::Utc::now(),
                reason: Some("Administrative".to_string()),
            };
            
            self.revoked_certificates.insert(serial.to_string(), revoked_info);
        }
        
        self.save().await
    }
    
    async fn is_revoked(&self, serial: &str) -> Result<bool, Error> {
        Ok(self.revoked_certificates.contains_key(serial))
    }
    
    async fn save(&self) -> Result<(), Error> {
        // 实际实现中，这里会将数据库保存到持久化存储
        // 此处为简化示例
        Ok(())
    }
}

// ... existing code ...
```

### 5.4 异常行为检测

```go
// security/anomaly_detection.go
package security

import (
    "context"
    "fmt"
    "math"
    "sync"
    "time"
)

// AnomalyDetector 异常行为检测器
type AnomalyDetector struct {
    baselines      map[string]Baseline
    activeProfiles map[string]UserActivityProfile
    deviceProfiles map[string]DeviceActivityProfile
    detectionRules []DetectionRule
    alertService   AlertService
    
    mu             sync.RWMutex
    baselineMu     sync.RWMutex
}

// Baseline 基线配置
type Baseline struct {
    UserID         string
    HomeID         string
    DeviceUsage    map[string]DeviceUsagePattern
    AccessPatterns []AccessPattern
    LocationPatterns []LocationPattern
    UpdatedAt      time.Time
}

// DeviceUsagePattern 设备使用模式
type DeviceUsagePattern struct {
    DeviceID       string
    DeviceType     string
    DailyActiveHours []int // 0-23小时，值为使用频率
    WeekdayActiveHours [][]int // 7天x24小时
    CommandFrequency map[string]float64 // 命令->每日频率
    AverageUsageDuration float64 // 平均每次使用时长(分钟)
}

// AccessPattern 访问模式
type AccessPattern struct {
    ActorType      string // user, guest, remote, etc.
    ActorID        string
    AccessTime     [][]int // 7天x24小时的访问频率
    AccessLocations []string // 常见访问位置
    DeviceAccessed map[string]float64 // 设备->访问频率
}

// LocationPattern 位置模式
type LocationPattern struct {
    RoomID         string
    OccupancyHours [][]int // 7天x24小时的房间占用情况
    AverageDuration float64 // 平均停留时间(分钟)
}

// UserActivityProfile 用户活动剖面
type UserActivityProfile struct {
    UserID         string
    CurrentActivity map[string]time.Time // 活动->最后活动时间
    AccessedDevices map[string]time.Time // 设备->最后访问时间
    CurrentLocation string
    LocationHistory []LocationRecord
    HashedIPAddresses []string
    LastSeen       time.Time
}

// LocationRecord 位置记录
type LocationRecord struct {
    RoomID         string
    EnteredAt      time.Time
    ExitedAt       *time.Time
}

// DeviceActivityProfile 设备活动剖面
type DeviceActivityProfile struct {
    DeviceID       string
    LastCommands   []CommandRecord
    CurrentState   map[string]interface{}
    LastActiveTime time.Time
    RunningTime    int64 // 累计运行时间(秒)
    AnomalyScore   float64 // 异常分数，0-1
}

// CommandRecord 命令记录
type CommandRecord struct {
    Command        string
    Parameters     map[string]interface{}
    Timestamp      time.Time
    ActorID        string
    ActorType      string
    Source         string // ui, automation, voice, etc.
}

// DetectionRule 检测规则
type DetectionRule struct {
    ID             string
    Name           string
    Type           string // user, device, access, location
    Conditions     []RuleCondition
    Severity       int // 1-5
    Action         string
    Enabled        bool
}

// RuleCondition 规则条件
type RuleCondition struct {
    Field          string
    Operator       string // eq, ne, gt, lt, in, etc.
    Value          interface{}
}

// AnomalyDetectionResult 异常检测结果
type AnomalyDetectionResult struct {
    Detected       bool
    Score          float64 // 0-1
    Rule           *DetectionRule
    Details        string
    Timestamp      time.Time
}

// NewAnomalyDetector 创建异常检测器
func NewAnomalyDetector(alertService AlertService) *AnomalyDetector {
    detector := &AnomalyDetector{
        baselines:      make(map[string]Baseline),
        activeProfiles: make(map[string]UserActivityProfile),
        deviceProfiles: make(map[string]DeviceActivityProfile),
        alertService:   alertService,
    }
    
    // 加载默认检测规则
    detector.loadDefaultRules()
    
    return detector
}

// 加载默认检测规则
func (d *AnomalyDetector) loadDefaultRules() {
    d.detectionRules = []DetectionRule{
        {
            ID:       "rule_1",
            Name:     "非常规时间访问",
            Type:     "access",
            Severity: 3,
            Action:   "alert",
            Enabled:  true,
            Conditions: []RuleCondition{
                {
                    Field:    "access_time_deviation",
                    Operator: "gt",
                    Value:    0.8,
                },
            },
        },
        {
            ID:       "rule_2",
            Name:     "异常位置访问",
            Type:     "access",
            Severity: 4,
            Action:   "block_and_alert",
            Enabled:  true,
            Conditions: []RuleCondition{
                {
                    Field:    "location",
                    Operator: "not_in",
                    Value:    []string{"baseline_locations"},
                },
            },
        },
        {
            ID:       "rule_3",
            Name:     "设备异常使用频率",
            Type:     "device",
            Severity: 2,
            Action:   "alert",
            Enabled:  true,
            Conditions: []RuleCondition{
                {
                    Field:    "command_frequency_deviation",
                    Operator: "gt",
                    Value:    0.7,
                },
                {
                    Field:    "command_count",
                    Operator: "gt",
                    Value:    5,
                },
            },
        },
        {
            ID:       "rule_4",
            Name:     "快速连续设备切换",
            Type:     "user",
            Severity: 3,
            Action:   "alert",
            Enabled:  true,
            Conditions: []RuleCondition{
                {
                    Field:    "device_switch_rate",
                    Operator: "gt",
                    Value:    0.5, // 每秒超过0.5个设备
                },
                {
                    Field:    "unique_device_count",
                    Operator: "gt",
                    Value:    3,
                },
            },
        },
        {
            ID:       "rule_5",
            Name:     "无人在家设备活动",
            Type:     "home",
            Severity: 4,
            Action:   "alert",
            Enabled:  true,
            Conditions: []RuleCondition{
                {
                    Field:    "home_occupied",
                    Operator: "eq",
                    Value:    false,
                },
                {
                    Field:    "non_scheduled_activity",
                    Operator: "eq",
                    Value:    true,
                },
            },
        },
    }
}

// 处理设备命令
func (d *AnomalyDetector) ProcessDeviceCommand(
    ctx context.Context,
    command CommandRecord,
) (*AnomalyDetectionResult, error) {
    d.mu.Lock()
    defer d.mu.Unlock()
    
    // 更新设备活动剖面
    deviceProfile, exists := d.deviceProfiles[command.DeviceID]
    if !exists {
        deviceProfile = DeviceActivityProfile{
            DeviceID:      command.DeviceID,
            LastCommands:  []CommandRecord{},
            CurrentState:  make(map[string]interface{}),
            LastActiveTime: time.Now(),
            RunningTime:   0,
            AnomalyScore:  0,
        }
    }
    
    // 添加命令记录
    deviceProfile.LastCommands = append(deviceProfile.LastCommands, command)
    if len(deviceProfile.LastCommands) > 20 {
        deviceProfile.LastCommands = deviceProfile.LastCommands[1:]
    }
    deviceProfile.LastActiveTime = time.Now()
    
    // 更新用户活动剖面
    if command.ActorType == "user" && command.ActorID != "" {
        userProfile, exists := d.activeProfiles[command.ActorID]
        if !exists {
            userProfile = UserActivityProfile{
                UserID:         command.ActorID,
                CurrentActivity: make(map[string]time.Time),
                AccessedDevices: make(map[string]time.Time),
                LocationHistory: []LocationRecord{},
                LastSeen:       time.Now(),
            }
        }
        
        userProfile.AccessedDevices[command.DeviceID] = time.Now()
        userProfile.CurrentActivity["device_control"] = time.Now()
        userProfile.LastSeen = time.Now()
        
        d.activeProfiles[command.ActorID] = userProfile
    }
    
    // 保存更新的设备剖面
    d.deviceProfiles[command.DeviceID] = deviceProfile
    
    // 检测异常
    return d.detectDeviceCommandAnomaly(ctx, command, deviceProfile)
}

// 检测设备命令异常
func (d *AnomalyDetector) detectDeviceCommandAnomaly(
    ctx context.Context,
    command CommandRecord,
    profile DeviceActivityProfile,
) (*AnomalyDetectionResult, error) {
    // 获取基线
    homeID := GetHomeIDFromContext(ctx)
    if homeID == "" {
        return nil, fmt.Errorf("无法从上下文获取家庭ID")
    }
    
    d.baselineMu.RLock()
    baseline, exists := d.baselines[homeID]
    d.baselineMu.RUnlock()
    
    if !exists {
        // 无基线，无法比较
        return &AnomalyDetectionResult{
            Detected:  false,
            Score:     0,
            Timestamp: time.Now(),
        }, nil
    }
    
    // 计算时间异常分数
    timeScore := d.calculateTimeAnomalyScore(command, baseline)
    
    // 计算命令频率异常分数
    frequencyScore := d.calculateFrequencyAnomalyScore(command, profile, baseline)
    
    // 计算访问模式异常分数
    accessScore := d.calculateAccessAnomalyScore(command, baseline)
    
    // 组合分数
    combinedScore := math.Max(timeScore, math.Max(frequencyScore, accessScore))
    
    // 更新设备异常分数
    profile.AnomalyScore = combinedScore
    d.deviceProfiles[command.DeviceID] = profile
    
    // 应用检测规则
    for _, rule := range d.detectionRules {
        if !rule.Enabled || rule.Type != "device" {
            continue
        }
        
        // 检查规则条件
        matched := true
        details := ""
        
        for _, condition := range rule.Conditions {
            switch condition.Field {
            case "command_frequency_deviation":
                if condition.Operator == "gt" {
                    threshold, ok := condition.Value.(float64)
                    if !ok || frequencyScore <= threshold {
                        matched = false
                    } else {
                        details += fmt.Sprintf("命令频率异常: %.2f > %.2f; ", frequencyScore, threshold)
                    }
                }
            case "time_deviation":
                if condition.Operator == "gt" {
                    threshold, ok := condition.Value.(float64)
                    if !ok || timeScore <= threshold {
                        matched = false
                    } else {
                        details += fmt.Sprintf("时间异常: %.2f > %.2f; ", timeScore, threshold)
                    }
                }
            case "access_pattern_deviation":
                if condition.Operator == "gt" {
                    threshold, ok := condition.Value.(float64)
                    if !ok || accessScore <= threshold {
                        matched = false
                    } else {
                        details += fmt.Sprintf("访问模式异常: %.2f > %.2f; ", accessScore, threshold)
                    }
                }
            }
            
            if !matched {
                break
            }
        }
        
        if matched {
            result := &AnomalyDetectionResult{
                Detected:  true,
                Score:     combinedScore,
                Rule:      &rule,
                Details:   details,
                Timestamp: time.Now(),
            }
            
            // 执行规则动作
            if rule.Action == "alert" || rule.Action == "block_and_alert" {
                d.alertService.SendAlert(ctx, Alert{
                    Type:     "anomaly_detection",
                    Severity: rule.Severity,
                    Message:  fmt.Sprintf("检测到设备异常活动: %s - %s", command.DeviceID, details),
                    Details:  map[string]interface{}{
                        "device_id":   command.DeviceID,
                        "command":     command.Command,
                        "actor_id":    command.ActorID,
                        "actor_type":  command.ActorType,
                        "score":       combinedScore,
                        "timestamp":   time.Now(),
                        "rule_name":   rule.Name,
                    },
                })
            }
            
            return result, nil
        }
    }
    
    // 没有匹配的规则
    return &AnomalyDetectionResult{
        Detected:  false,
        Score:     combinedScore,
        Timestamp: time.Now(),
    }, nil
}

// ... existing code ...
```

## 总结

以上代码实现了智能家居场景自动化系统的核心组件，主要关注五个重点方面：

### 1. 设备兼容性与协议适配

- 实现了统一的协议适配器接口，支持ZigBee、Z-Wave、WiFi等多种协议
- 设计了基于能力(Capability)的设备抽象模型，解决设备异构性
- 提供了动态设备发现与接入机制，实现即插即用

### 2. 工作流引擎性能优化

- 轻量级工作流定义，支持条件分支、并行执行等复杂逻辑
- 工作流预编译与热路径优化，显著提升执行性能
- 多层次状态持久化策略，确保断电或重启后仍能恢复工作流
- 基于资源监控的自适应调度，平衡系统负载

### 3. 用户体验简化

- 场景模板与智能推荐，降低用户创建场景的难度
- 自然语言场景创建，支持口语化指令创建自动化
- 直观的可视化编辑器，结合智能建议简化复杂场景设计
- 执行可视化与故障排查工具，帮助用户理解系统行为

### 4. 安全与隐私保护

- 设备层安全机制，包括认证、加密通信和密钥轮换
- 细粒度数据隐私管理，支持不同数据类型的策略设置
- TLS加密通信通道，保护所有网络传输
- 异常行为检测系统，及时发现潜在安全威胁

### 5. 系统可靠性保障

- 多层次容错设计，应对网络中断和设备故障
- 优先本地执行策略，减少对云端依赖
- 分层存储与同步机制，确保数据一致性
- 全面的监控与报警系统，快速响应异常

通过这些实现，智能家居场景自动化系统能够提供稳定、安全、易用的智能家居体验，同时兼顾性能和资源效率。系统的模块化设计也使其具备良好的扩展性，可以适应不断发展的智能家居生态。
