# 通用智能家居系统架构设计深度指南

## 目录

- [通用智能家居系统架构设计深度指南](#通用智能家居系统架构设计深度指南)
  - [目录](#目录)
  - [1. API设计深度建议](#1-api设计深度建议)
    - [1.1 RESTful API设计最佳实践](#11-restful-api设计最佳实践)
    - [1.2 GraphQL API设计](#12-graphql-api设计)
    - [1.3 API批量操作与事务](#13-api批量操作与事务)
    - [1.4 API 版本升级与兼容性](#14-api-版本升级与兼容性)
  - [2. 前后端分离深度实践](#2-前后端分离深度实践)
    - [2.1 前后端接口契约](#21-前后端接口契约)
    - [2.2 领域驱动设计(DDD)应用架构](#22-领域驱动设计ddd应用架构)
    - [2.3 前端应用层设计](#23-前端应用层设计)
    - [2.4 模块边界与依赖管理](#24-模块边界与依赖管理)
  - [3. 状态同步机制深度实现](#3-状态同步机制深度实现)
    - [3.1 WebSocket实时状态同步](#31-websocket实时状态同步)
    - [3.2 离线状态同步与冲突解决](#32-离线状态同步与冲突解决)
    - [3.3 事件驱动架构](#33-事件驱动架构)
    - [3.4 分布式状态一致性](#34-分布式状态一致性)
  - [4. 前端架构深度设计](#4-前端架构深度设计)
    - [4.1 组件设计系统](#41-组件设计系统)
    - [4.2 设备控制组件](#42-设备控制组件)
    - [4.3 状态管理架构](#43-状态管理架构)
    - [4.4 离线模式与数据持久化](#44-离线模式与数据持久化)
  - [5. 权限与用户体验优化](#5-权限与用户体验优化)
    - [5.1 基于角色的访问控制（RBAC）](#51-基于角色的访问控制rbac)
    - [5.2 渐进式用户引导与提示](#52-渐进式用户引导与提示)
    - [5.3 个性化推荐系统](#53-个性化推荐系统)
    - [5.4 学习与适应能力](#54-学习与适应能力)

## 1. API设计深度建议

### 1.1 RESTful API设计最佳实践

```go
// api/router.go
func SetupAPIRoutes(r *gin.Engine, middleware ...gin.HandlerFunc) {
    // API版本管理
    v1 := r.Group("/api/v1", middleware...)
    {
        // 设备管理
        devices := v1.Group("/devices")
        {
            devices.GET("", controller.ListDevices)
            devices.GET("/:id", controller.GetDevice)
            devices.POST("", controller.AddDevice)
            devices.PUT("/:id", controller.UpdateDevice)
            devices.DELETE("/:id", controller.DeleteDevice)
            devices.POST("/:id/commands", controller.ExecuteDeviceCommand)
            devices.GET("/:id/capabilities", controller.GetDeviceCapabilities)
            devices.GET("/:id/state", controller.GetDeviceState)
        }
        
        // 场景管理
        scenes := v1.Group("/scenes")
        {
            scenes.GET("", controller.ListScenes)
            scenes.GET("/:id", controller.GetScene)
            scenes.POST("", controller.CreateScene)
            scenes.PUT("/:id", controller.UpdateScene)
            scenes.DELETE("/:id", controller.DeleteScene)
            scenes.POST("/:id/execute", controller.ExecuteScene)
            scenes.GET("/:id/history", controller.GetSceneExecutionHistory)
        }
        
        // 工作流管理
        workflows := v1.Group("/workflows")
        {
            workflows.GET("", controller.ListWorkflows)
            workflows.GET("/:id", controller.GetWorkflow)
            workflows.POST("", controller.CreateWorkflow)
            workflows.PUT("/:id", controller.UpdateWorkflow)
            workflows.GET("/:id/executions", controller.ListWorkflowExecutions)
            workflows.POST("/:id/executions", controller.ExecuteWorkflow)
            workflows.GET("/executions/:id", controller.GetExecutionDetails)
        }
        
        // 用户偏好与设置
        settings := v1.Group("/settings")
        {
            settings.GET("", controller.GetUserSettings)
            settings.PUT("", controller.UpdateUserSettings)
            settings.GET("/privacy", controller.GetPrivacySettings)
            settings.PUT("/privacy", controller.UpdatePrivacySettings)
        }
    }
}
```

### 1.2 GraphQL API设计

```go
// api/graphql/schema.go
var Schema = `
type Query {
    # 设备查询
    devices(filter: DeviceFilter): [Device!]!
    device(id: ID!): Device
    
    # 场景查询
    scenes(filter: SceneFilter): [Scene!]!
    scene(id: ID!): Scene
    
    # 工作流查询
    workflows(filter: WorkflowFilter): [Workflow!]!
    workflow(id: ID!): Workflow
    workflowExecution(id: ID!): WorkflowExecution
    
    # 用户数据
    userSettings: UserSettings!
    analytics(period: AnalyticsPeriod!): Analytics!
}

type Mutation {
    # 设备操作
    executeDeviceCommand(input: DeviceCommandInput!): CommandResult!
    updateDeviceSettings(input: DeviceSettingsInput!): Device!
    
    # 场景操作
    createScene(input: SceneInput!): Scene!
    updateScene(id: ID!, input: SceneInput!): Scene!
    executeScene(id: ID!): SceneExecutionResult!
    
    # 工作流操作
    createWorkflow(input: WorkflowInput!): Workflow!
    executeWorkflow(id: ID!, input: WorkflowExecutionInput): WorkflowExecution!
    cancelExecution(id: ID!): Boolean!
}

type Subscription {
    # 实时订阅
    deviceStateChanged(deviceId: ID): DeviceState!
    sceneExecutionUpdated(sceneId: ID): SceneExecutionUpdate!
    workflowExecutionUpdated(executionId: ID!): WorkflowExecutionUpdate!
    homeStateChanged: HomeState!
}

# 设备类型定义
type Device {
    id: ID!
    name: String!
    type: String!
    room: Room
    manufacturer: String
    model: String
    firmwareVersion: String
    capabilities: [Capability!]!
    state: DeviceState!
    online: Boolean!
    lastSeen: DateTime
    statistics: DeviceStatistics
}

# 更多类型定义...
`

// api/graphql/resolvers.go
type Resolver struct {
    DeviceService    service.DeviceService
    SceneService     service.SceneService
    WorkflowService  service.WorkflowService
    AnalyticsService service.AnalyticsService
    UserService      service.UserService
}

func (r *Resolver) Query() QueryResolver {
    return &queryResolver{r}
}

func (r *Resolver) Mutation() MutationResolver {
    return &mutationResolver{r}
}

func (r *Resolver) Subscription() SubscriptionResolver {
    return &subscriptionResolver{r}
}

type queryResolver struct{ *Resolver }

func (r *queryResolver) Devices(ctx context.Context, filter *DeviceFilter) ([]*Device, error) {
    // 实现设备查询逻辑
    devices, err := r.DeviceService.ListDevices(ctx, filter.ToServiceFilter())
    if err != nil {
        return nil, err
    }
    
    // 转换为GraphQL类型
    result := make([]*Device, len(devices))
    for i, d := range devices {
        result[i] = DeviceToGraphQL(d)
    }
    
    return result, nil
}

// 更多解析器实现...
```

### 1.3 API批量操作与事务

```go
// api/controller/device_controller.go
func (c *DeviceController) BatchExecuteCommands(ctx *gin.Context) {
    var request BatchCommandRequest
    if err := ctx.ShouldBindJSON(&request); err != nil {
        ctx.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }
    
    results := make([]CommandResult, len(request.Commands))
    successful := 0
    
    // 批量执行设备命令
    for i, cmd := range request.Commands {
        result, err := c.deviceService.ExecuteCommand(ctx, cmd.DeviceID, cmd.Capability, cmd.Command, cmd.Parameters)
        if err != nil {
            results[i] = CommandResult{
                Success: false,
                Error:   err.Error(),
            }
        } else {
            results[i] = CommandResult{
                Success: true,
                Data:    result,
            }
            successful++
        }
    }
    
    ctx.JSON(http.StatusOK, gin.H{
        "results": results,
        "summary": BatchSummary{
            Total:      len(request.Commands),
            Successful: successful,
            Failed:     len(request.Commands) - successful,
        },
    })
}
```

### 1.4 API 版本升级与兼容性

```go
// api/middleware/versioning.go
func APIVersioning() gin.HandlerFunc {
    return func(c *gin.Context) {
        // 获取客户端请求的API版本
        requestedVersion := c.GetHeader("X-API-Version")
        if requestedVersion == "" {
            // 默认使用最新版本
            requestedVersion = "v1"
        }
        
        // 版本兼容性映射
        versionMap := map[string]string{
            "v1": "v1",
            "v1.1": "v1",
            "v1.2": "v1",
            "v2": "v2",
        }
        
        // 版本升级提示
        deprecatedVersions := map[string]string{
            "v1": "API v1将在2023年12月31日弃用，请升级到v2",
        }
        
        // 检查版本并设置路由
        mappedVersion, exists := versionMap[requestedVersion]
        if !exists {
            c.JSON(http.StatusBadRequest, gin.H{
                "error": "不支持的API版本",
                "supported_versions": []string{"v1", "v2"},
            })
            c.Abort()
            return
        }
        
        // 设置内部版本
        c.Set("api_version", mappedVersion)
        
        // 检查是否有弃用警告
        if warning, deprecated := deprecatedVersions[requestedVersion]; deprecated {
            c.Header("X-API-Deprecated", warning)
        }
        
        c.Next()
    }
}
```

## 2. 前后端分离深度实践

### 2.1 前后端接口契约

```typescript
// frontend/src/api/types.ts
export interface DeviceDTO {
    id: string;
    name: string;
    type: string;
    roomId?: string;
    manufacturer?: string;
    model?: string;
    firmwareVersion?: string;
    capabilities: string[];
    online: boolean;
    lastSeen?: string;
    state: Record<string, any>;
}

export interface CommandRequest {
    capability: string;
    command: string;
    parameters?: Record<string, any>;
}

export interface CommandResponse {
    success: boolean;
    data?: any;
    error?: string;
    timestamp: string;
}

// API客户端接口
export interface DeviceAPI {
    getDevices(): Promise<DeviceDTO[]>;
    getDevice(id: string): Promise<DeviceDTO>;
    executeCommand(id: string, request: CommandRequest): Promise<CommandResponse>;
    getDeviceState(id: string): Promise<Record<string, any>>;
}

// 相应的后端接口
// backend/interfaces/api.go
type DeviceDTO struct {
    ID              string                 `json:"id"`
    Name            string                 `json:"name"`
    Type            string                 `json:"type"`
    RoomID          *string                `json:"roomId,omitempty"`
    Manufacturer    *string                `json:"manufacturer,omitempty"`
    Model           *string                `json:"model,omitempty"`
    FirmwareVersion *string                `json:"firmwareVersion,omitempty"`
    Capabilities    []string               `json:"capabilities"`
    Online          bool                   `json:"online"`
    LastSeen        *time.Time             `json:"lastSeen,omitempty"`
    State           map[string]interface{} `json:"state"`
}

type CommandRequest struct {
    Capability string                 `json:"capability" binding:"required"`
    Command    string                 `json:"command" binding:"required"`
    Parameters map[string]interface{} `json:"parameters,omitempty"`
}

type CommandResponse struct {
    Success   bool        `json:"success"`
    Data      interface{} `json:"data,omitempty"`
    Error     string      `json:"error,omitempty"`
    Timestamp time.Time   `json:"timestamp"`
}
```

### 2.2 领域驱动设计(DDD)应用架构

```go
// backend/domain/device/device.go
package device

// Device 设备领域模型
type Device struct {
    ID              string
    Name            string
    Type            string
    RoomID          string
    Manufacturer    string
    Model           string
    FirmwareVersion string
    Capabilities    map[string]Capability
    State           State
    Online          bool
    LastSeen        time.Time
}

// State 设备状态
type State struct {
    Values     map[string]interface{}
    UpdatedAt  time.Time
}

// ExecuteCommand 执行设备命令
func (d *Device) ExecuteCommand(capability string, command string, parameters map[string]interface{}) (*CommandResult, error) {
    // 检查设备是否在线
    if !d.Online {
        return nil, ErrDeviceOffline
    }
    
    // 检查设备是否支持该能力
    cap, exists := d.Capabilities[capability]
    if !exists {
        return nil, ErrCapabilityNotSupported
    }
    
    // 检查命令是否有效
    if !cap.SupportsCommand(command) {
        return nil, ErrCommandNotSupported
    }
    
    // 执行命令
    result, err := cap.ExecuteCommand(command, parameters)
    if err != nil {
        return nil, err
    }
    
    // 更新设备状态
    for k, v := range result.StateChanges {
        d.State.Values[k] = v
    }
    d.State.UpdatedAt = time.Now()
    
    return result, nil
}

// backend/application/device/service.go
package device

// DeviceService 设备应用服务
type DeviceService struct {
    repo            DeviceRepository
    eventPublisher  EventPublisher
    capabilityFactory CapabilityFactory
}

// ExecuteDeviceCommand 执行设备命令
func (s *DeviceService) ExecuteDeviceCommand(
    ctx context.Context,
    deviceID string,
    capability string,
    command string,
    parameters map[string]interface{},
) (*dto.CommandResponse, error) {
    // 获取设备
    device, err := s.repo.GetDevice(ctx, deviceID)
    if err != nil {
        return nil, err
    }
    
    // 执行命令
    result, err := device.ExecuteCommand(capability, command, parameters)
    if err != nil {
        return nil, err
    }
    
    // 保存设备状态
    if err := s.repo.UpdateDevice(ctx, device); err != nil {
        return nil, err
    }
    
    // 发布设备状态变更事件
    s.eventPublisher.PublishEvent(ctx, DeviceStateChangedEvent{
        DeviceID: deviceID,
        Changes:  result.StateChanges,
        Time:     time.Now(),
    })
    
    // 构建响应
    response := &dto.CommandResponse{
        Success:   true,
        Data:      result.Data,
        Timestamp: time.Now(),
    }
    
    return response, nil
}
```

### 2.3 前端应用层设计

```typescript
// frontend/src/services/device.service.ts
import { inject, injectable } from 'inversify';
import { DeviceAPI, DeviceDTO, CommandRequest, CommandResponse } from '../api/types';
import { Device, DeviceCapability, DeviceState } from '../models/device.model';
import { DeviceMapper } from '../mappers/device.mapper';
import { EventBus } from '../core/event-bus';

@injectable()
export class DeviceService {
    constructor(
        @inject('DeviceAPI') private deviceAPI: DeviceAPI,
        private eventBus: EventBus,
        private mapper: DeviceMapper
    ) {}
    
    // 获取所有设备
    async getAllDevices(): Promise<Device[]> {
        const deviceDTOs = await this.deviceAPI.getDevices();
        return deviceDTOs.map(dto => this.mapper.toDevice(dto));
    }
    
    // 执行设备命令
    async executeCommand(
        deviceId: string, 
        capability: string, 
        command: string, 
        parameters?: Record<string, any>
    ): Promise<boolean> {
        try {
            const request: CommandRequest = {
                capability,
                command,
                parameters
            };
            
            const response = await this.deviceAPI.executeCommand(deviceId, request);
            
            if (response.success) {
                // 发布设备状态变更事件
                this.eventBus.publish('device.state.changed', {
                    deviceId,
                    capability,
                    command,
                    parameters,
                    result: response.data
                });
                return true;
            } else {
                throw new Error(response.error || '命令执行失败');
            }
        } catch (error) {
            console.error(`执行设备命令失败: ${error.message}`);
            throw error;
        }
    }
    
    // 订阅设备状态变更
    subscribeToStateChanges(
        deviceId: string | null, 
        callback: (state: DeviceState) => void
    ): () => void {
        const handler = (event: any) => {
            if (deviceId === null || event.deviceId === deviceId) {
                // 获取最新状态
                this.deviceAPI.getDeviceState(event.deviceId).then(state => {
                    callback(this.mapper.toDeviceState(state));
                });
            }
        };
        
        // 订阅WebSocket或其他实时状态更新
        this.eventBus.subscribe('device.state.changed', handler);
        
        // 返回取消订阅函数
        return () => {
            this.eventBus.unsubscribe('device.state.changed', handler);
        };
    }
}
```

### 2.4 模块边界与依赖管理

```typescript
// frontend/src/core/di-container.ts
import { Container } from 'inversify';
import { DeviceAPI, SceneAPI, WorkflowAPI } from '../api';
import { 
    DeviceService, 
    SceneService, 
    WorkflowService,
    AnalyticsService,
    NotificationService 
} from '../services';
import { DeviceMapper, SceneMapper, WorkflowMapper } from '../mappers';
import { EventBus } from './event-bus';

export const container = new Container();

// 核心服务
container.bind<EventBus>(EventBus).toSelf().inSingletonScope();

// API层注册
container.bind<DeviceAPI>('DeviceAPI').to(DeviceAPIImpl).inSingletonScope();
container.bind<SceneAPI>('SceneAPI').to(SceneAPIImpl).inSingletonScope();
container.bind<WorkflowAPI>('WorkflowAPI').to(WorkflowAPIImpl).inSingletonScope();

// 映射器注册
container.bind<DeviceMapper>(DeviceMapper).toSelf().inSingletonScope();
container.bind<SceneMapper>(SceneMapper).toSelf().inSingletonScope();
container.bind<WorkflowMapper>(WorkflowMapper).toSelf().inSingletonScope();

// 服务层注册
container.bind<DeviceService>(DeviceService).toSelf().inSingletonScope();
container.bind<SceneService>(SceneService).toSelf().inSingletonScope();
container.bind<WorkflowService>(WorkflowService).toSelf().inSingletonScope();
container.bind<AnalyticsService>(AnalyticsService).toSelf().inSingletonScope();
container.bind<NotificationService>(NotificationService).toSelf().inSingletonScope();

export function getService<T>(serviceIdentifier: interfaces.ServiceIdentifier<T>): T {
    return container.get<T>(serviceIdentifier);
}
```

## 3. 状态同步机制深度实现

### 3.1 WebSocket实时状态同步

```go
// backend/api/websocket/hub.go
type Hub struct {
    clients    map[*Client]bool
    broadcast  chan *Message
    register   chan *Client
    unregister chan *Client
    rooms      map[string]map[*Client]bool
}

func NewHub() *Hub {
    return &Hub{
        clients:    make(map[*Client]bool),
        broadcast:  make(chan *Message),
        register:   make(chan *Client),
        unregister: make(chan *Client),
        rooms:      make(map[string]map[*Client]bool),
    }
}

func (h *Hub) Run() {
    for {
        select {
        case client := <-h.register:
            h.clients[client] = true
            // 加入房间
            if client.homeID != "" {
                if _, ok := h.rooms[client.homeID]; !ok {
                    h.rooms[client.homeID] = make(map[*Client]bool)
                }
                h.rooms[client.homeID][client] = true
            }
        case client := <-h.unregister:
            if _, ok := h.clients[client]; ok {
                delete(h.clients, client)
                close(client.send)
                
                // 离开房间
                if client.homeID != "" {
                    if room, ok := h.rooms[client.homeID]; ok {
                        delete(room, client)
                        if len(room) == 0 {
                            delete(h.rooms, client.homeID)
                        }
                    }
                }
            }
        case message := <-h.broadcast:
            // 广播到特定房间
            if message.Room != "" {
                if room, ok := h.rooms[message.Room]; ok {
                    for client := range room {
                        select {
                        case client.send <- message.Data:
                        default:
                            close(client.send)
                            delete(h.clients, client)
                            delete(room, client)
                            if len(room) == 0 {
                                delete(h.rooms, message.Room)
                            }
                        }
                    }
                }
                continue
            }
            
            // 全局广播
            for client := range h.clients {
                select {
                case client.send <- message.Data:
                default:
                    close(client.send)
                    delete(h.clients, client)
                }
            }
        }
    }
}

// backend/api/websocket/client.go
type Client struct {
    hub     *Hub
    conn    *websocket.Conn
    send    chan []byte
    userID  string
    homeID  string
}

func (c *Client) readPump() {
    defer func() {
        c.hub.unregister <- c
        c.conn.Close()
    }()
    
    c.conn.SetReadLimit(maxMessageSize)
    c.conn.SetReadDeadline(time.Now().Add(pongWait))
    c.conn.SetPongHandler(func(string) error { 
        c.conn.SetReadDeadline(time.Now().Add(pongWait))
        return nil 
    })
    
    for {
        _, message, err := c.conn.ReadMessage()
        if err != nil {
            if websocket.IsUnexpectedCloseError(err, websocket.CloseGoingAway, websocket.CloseAbnormalClosure) {
                log.Printf("WebSocket error: %v", err)
            }
            break
        }
        
        // 处理客户端发来的消息
        var request map[string]interface{}
        if err := json.Unmarshal(message, &request); err != nil {
            log.Printf("WebSocket JSON解析错误: %v", err)
            continue
        }
        
        // 处理订阅请求
        if typ, ok := request["type"].(string); ok && typ == "subscribe" {
            if topic, ok := request["topic"].(string); ok {
                // 处理订阅
                log.Printf("客户端 %s 订阅 %s", c.userID, topic)
            }
        }
    }
}

func (c *Client) writePump() {
    ticker := time.NewTicker(pingPeriod)
    defer func() {
        ticker.Stop()
        c.conn.Close()
    }()
    
    for {
        select {
        case message, ok := <-c.send:
            c.conn.SetWriteDeadline(time.Now().Add(writeWait))
            if !ok {
                // Hub关闭了通道
                c.conn.WriteMessage(websocket.CloseMessage, []byte{})
                return
            }
            
            w, err := c.conn.NextWriter(websocket.TextMessage)
            if err != nil {
                return
            }
            w.Write(message)
            
            // 添加队列中的所有消息到当前消息
            n := len(c.send)
            for i := 0; i < n; i++ {
                w.Write([]byte{'\n'})
                w.Write(<-c.send)
            }
            
            if err := w.Close(); err != nil {
                return
            }
        case <-ticker.C:
            c.conn.SetWriteDeadline(time.Now().Add(writeWait))
            if err := c.conn.WriteMessage(websocket.PingMessage, nil); err != nil {
                return
            }
        }
    }
}

// backend/events/device_events.go
// 设备状态变更事件处理
func (s *EventService) HandleDeviceStateChanged(event DeviceStateChangedEvent) {
    // 构建事件消息
    message := WebSocketMessage{
        Type: "device.state.changed",
        Data: map[string]interface{}{
            "deviceId": event.DeviceID,
            "changes":  event.Changes,
            "timestamp": event.Time,
        },
    }
    
    // 序列化为JSON
    data, err := json.Marshal(message)
    if err != nil {
        log.Printf("事件序列化错误: %v", err)
        return
    }
    
    // 发送到WebSocket hub
    s.webSocketHub.broadcast <- &Message{
        Room: event.HomeID,
        Data: data,
    }
    
    // 同时发送到Redis Pub/Sub用于分布式部署
    s.redisClient.Publish(ctx, "device-events", data).Err()
}
```

### 3.2 离线状态同步与冲突解决

```go
// backend/sync/offline_sync.go
type OfflineSyncManager struct {
    deviceRepo      DeviceRepository
    sceneRepo       SceneRepository
    syncStateRepo   SyncStateRepository
    conflictResolver ConflictResolver
}

// SyncState 同步状态
type SyncState struct {
    EntityType    string
    EntityID      string
    Version       int64
    LastUpdated   time.Time
    LastSyncedAt  time.Time
    ClientID      string
}

// SyncRequest 同步请求
type SyncRequest struct {
    ClientID      string
    ClientVersion map[string]map[string]int64 // 类型->ID->版本
    LastSyncTime  time.Time
}

// SyncResponse 同步响应
type SyncResponse struct {
    Updates       map[string][]interface{} // 类型->实体列表
    Conflicts     []Conflict
    ServerTime    time.Time
}

// 处理客户端同步请求
func (m *OfflineSyncManager) HandleSyncRequest(ctx context.Context, req SyncRequest) (*SyncResponse, error) {
    response := &SyncResponse{
        Updates:    make(map[string][]interface{}),
        Conflicts:  []Conflict{},
        ServerTime: time.Now(),
    }
    
    // 处理设备同步
    deviceUpdates, deviceConflicts, err := m.syncDevices(ctx, req)
    if err != nil {
        return nil, err
    }
    
    if len(deviceUpdates) > 0 {
        response.Updates["devices"] = deviceUpdates
    }
    
    response.Conflicts = append(response.Conflicts, deviceConflicts...)
    
    // 处理场景同步
    sceneUpdates, sceneConflicts, err := m.syncScenes(ctx, req)
    if err != nil {
        return nil, err
    }
    
    if len(sceneUpdates) > 0 {
        response.Updates["scenes"] = sceneUpdates
    }
    
    response.Conflicts = append(response.Conflicts, sceneConflicts...)
    
    return response, nil
}

// 同步设备数据
func (m *OfflineSyncManager) syncDevices(ctx context.Context, req SyncRequest) ([]interface{}, []Conflict, error) {
    var updates []interface{}
    var conflicts []Conflict
    
    // 获取客户端的设备版本信息
    clientDeviceVersions := req.ClientVersion["devices"]
    
    // 获取自上次同步以来的服务器设备更新
    serverUpdates, err := m.deviceRepo.GetUpdatedSince(ctx, req.LastSyncTime)
    if err != nil {
        return nil, nil, err
    }
    
    // 比较版本并解决冲突
    for _, device := range serverUpdates {
        clientVersion, hasClientVersion := clientDeviceVersions[device.ID]
        
        // 获取当前服务器版本
        syncState, err := m.syncStateRepo.GetSyncState(ctx, "device", device.ID)
        if err != nil && !errors.Is(err, ErrNotFound) {
            return nil, nil, err
        }
        
        serverVersion := int64(0)
        if syncState != nil {
            serverVersion = syncState.Version
        }
        
        // 如果客户端没有这个设备的版本信息，直接发送更新
        if !hasClientVersion {
            updates = append(updates, device)
            continue
        }
        
        // 如果客户端版本低于服务器版本，发送更新
        if clientVersion < serverVersion {
            updates = append(updates, device)
            continue
        }
        
        // 如果客户端版本高于服务器版本，可能有冲突
        if clientVersion > serverVersion {
            conflict := Conflict{
                EntityType: "device",
                EntityID:   device.ID,
                ClientVersion: clientVersion,
                ServerVersion: serverVersion,
                Resolution: "server_wins", // 默认服务器优先
            }
            
            // 解决冲突
            resolved, err := m.conflictResolver.ResolveDeviceConflict(ctx, device, clientVersion)
            if err != nil {
                return nil, nil, err
            }
            
            if resolved {
                conflict.Resolution = "merged"
                conflict.ResolvedEntity = device
            }
            
            conflicts = append(conflicts, conflict)
        }
    }
    
    return updates, conflicts, nil
}

// 解决设备冲突
func (r *ConflictResolver) ResolveDeviceConflict(ctx context.Context, serverDevice *Device, clientVersion int64) (bool, error) {
    // 获取客户端版本的设备数据
    clientDevice, err := r.offlineDataRepo.GetDeviceVersion(ctx, serverDevice.ID, clientVersion)
    if err != nil {
        return false, err
    }
    
    // 没有客户端数据，无法解决
    if clientDevice == nil {
        return false, nil
    }
    
    // 基于设备类型的字段级合并策略
    result := &Device{
        ID:              serverDevice.ID,
        Name:            serverDevice.Name,  // 服务器优先
        Type:            serverDevice.Type,  // 类型不应更改，服务器优先
        RoomID:          serverDevice.RoomID, // 服务器优先
        Manufacturer:    serverDevice.Manufacturer,
        Model:           serverDevice.Model,
        FirmwareVersion: serverDevice.FirmwareVersion, // 服务器优先
        Capabilities:    serverDevice.Capabilities,     // 服务器优先
        Online:          serverDevice.Online,           // 服务器优先
        LastSeen:        serverDevice.LastSeen,         // 服务器优先
    }
    
    // 对设备状态进行智能合并
    mergedState := make(map[string]interface{})
    
    // 首先拷贝服务器状态作为基础
    for k, v := range serverDevice.State.Values {
        mergedState[k] = v
    }
    
    // 合并客户端的状态变更，但只接受静态设置，不接受传感器数据
    for k, v := range clientDevice.State.Values {
        capability, exists := serverDevice.Capabilities[getCapabilityTypeForAttribute(k)]
        if !exists {
            continue
        }
        
        // 如果是用户可配置的设置，接受客户端值
        if capability.IsUserConfigurable() && !capability.IsSensorData() {
            mergedState[k] = v
        }
    }
    
    result.State = State{
        Values:    mergedState,
        UpdatedAt: time.Now(),
    }
    
    // 保存合并结果
    if err := r.deviceRepo.UpdateDevice(ctx, result); err != nil {
        return false, err
    }
    
    // 更新同步状态
    newVersion := clientVersion + 1
    if err := r.syncStateRepo.UpdateSyncState(ctx, &SyncState{
        EntityType:   "device",
        EntityID:     serverDevice.ID,
        Version:      newVersion,
        LastUpdated:  time.Now(),
        LastSyncedAt: time.Now(),
    }); err != nil {
        return false, err
    }
    
    return true, nil
}

// backend/sync/offline_data_service.go
type OfflineChangeHandler struct {
    deviceService   DeviceService
    sceneService    SceneService
    workflowService WorkflowService
    syncStateRepo   SyncStateRepository
}

// 处理离线创建的设备命令
func (h *OfflineChangeHandler) HandleOfflineDeviceCommands(
    ctx context.Context, 
    userID string, 
    commands []OfflineDeviceCommand,
) ([]CommandResult, error) {
    results := make([]CommandResult, len(commands))
    
    for i, cmd := range commands {
        // 检查命令时间戳是否过旧
        if time.Since(cmd.Timestamp) > maxCommandAge {
            results[i] = CommandResult{
                Success: false,
                Error:   "命令过期",
            }
            continue
        }
        
        // 获取设备当前状态
        device, err := h.deviceService.GetDevice(ctx, cmd.DeviceID)
        if err != nil {
            results[i] = CommandResult{
                Success: false,
                Error:   fmt.Sprintf("获取设备失败: %v", err),
            }
            continue
        }
        
        // 检查命令是否已经执行过（幂等性检查）
        if h.isCommandAlreadyExecuted(ctx, cmd.CommandID) {
            // 获取原始结果
            originalResult, err := h.getCommandResult(ctx, cmd.CommandID)
            if err == nil && originalResult != nil {
                results[i] = *originalResult
                continue
            }
            
            // 如果找不到原始结果，创建一个成功的结果
            results[i] = CommandResult{
                Success: true,
                Data:    "命令已执行",
            }
            continue
        }
        
        // 检查命令是否仍然有效
        if !h.isCommandStillValid(ctx, cmd, device) {
            results[i] = CommandResult{
                Success: false,
                Error:   "设备状态已变更，命令无效",
            }
            continue
        }
        
        // 执行命令
        result, err := h.deviceService.ExecuteDeviceCommand(
            ctx, 
            cmd.DeviceID, 
            cmd.Capability, 
            cmd.Command, 
            cmd.Parameters,
        )
        
        // 记录命令执行结果
        h.recordCommandExecution(ctx, cmd.CommandID, result)
        
        results[i] = CommandResult{
            Success:   result.Success,
            Data:      result.Data,
            Error:     result.Error,
            Timestamp: time.Now(),
        }
    }
    
    return results, nil
}

// 检查命令是否仍然有效
func (h *OfflineChangeHandler) isCommandStillValid(
    ctx context.Context, 
    cmd OfflineDeviceCommand, 
    device *Device,
) bool {
    // 对于幂等命令，总是有效
    if isIdempotentCommand(cmd.Command) {
        return true
    }
    
    // 检查命令的前置条件
    if cmd.Preconditions == nil {
        return true
    }
    
    // 验证设备当前状态是否满足前置条件
    for attr, expectedValue := range cmd.Preconditions {
        currentValue, exists := device.State.Values[attr]
        if !exists || !reflect.DeepEqual(currentValue, expectedValue) {
            return false
        }
    }
    
    return true
}
```

### 3.3 事件驱动架构

```go
// backend/events/event_manager.go
package events

import (
    "context"
    "encoding/json"
    "fmt"
    "time"
    
    "github.com/go-redis/redis/v8"
    "github.com/nats-io/nats.go"
)

// Event 事件接口
type Event interface {
    GetType() string
    GetPayload() interface{}
    GetTimestamp() time.Time
    GetSource() string
}

// BaseEvent 基础事件实现
type BaseEvent struct {
    Type      string
    Payload   interface{}
    Timestamp time.Time
    Source    string
}

func (e BaseEvent) GetType() string {
    return e.Type
}

func (e BaseEvent) GetPayload() interface{} {
    return e.Payload
}

func (e BaseEvent) GetTimestamp() time.Time {
    return e.Timestamp
}

func (e BaseEvent) GetSource() string {
    return e.Source
}

// EventHandler 事件处理器接口
type EventHandler interface {
    HandleEvent(ctx context.Context, event Event) error
}

// EventPublisher 事件发布器接口
type EventPublisher interface {
    PublishEvent(ctx context.Context, event Event) error
}

// EventManager 事件管理器
type EventManager struct {
    handlers    map[string][]EventHandler
    natsConn    *nats.Conn
    redisClient *redis.Client
    serviceName string
}

// NewEventManager 创建事件管理器
func NewEventManager(natsConn *nats.Conn, redisClient *redis.Client, serviceName string) *EventManager {
    return &EventManager{
        handlers:    make(map[string][]EventHandler),
        natsConn:    natsConn,
        redisClient: redisClient,
        serviceName: serviceName,
    }
}

// RegisterHandler 注册事件处理器
func (m *EventManager) RegisterHandler(eventType string, handler EventHandler) {
    m.handlers[eventType] = append(m.handlers[eventType], handler)
}

// PublishEvent 发布事件
func (m *EventManager) PublishEvent(ctx context.Context, event Event) error {
    // 添加源服务信息
    if e, ok := event.(BaseEvent); ok && e.Source == "" {
        e.Source = m.serviceName
        event = e
    }
    
    // 序列化事件
    data, err := json.Marshal(event)
    if err != nil {
        return fmt.Errorf("序列化事件失败: %w", err)
    }
    
    // 通过NATS发布
    subject := fmt.Sprintf("events.%s", event.GetType())
    if err := m.natsConn.Publish(subject, data); err != nil {
        return fmt.Errorf("NATS发布失败: %w", err)
    }
    
    // 通过Redis发布
    channel := fmt.Sprintf("events:%s", event.GetType())
    if err := m.redisClient.Publish(ctx, channel, data).Err(); err != nil {
        return fmt.Errorf("Redis发布失败: %w", err)
    }
    
    // 本地处理
    m.processEvent(ctx, event)
    
    return nil
}

// StartEventProcessor 启动事件处理器
func (m *EventManager) StartEventProcessor(ctx context.Context) error {
    // 订阅NATS事件
    for eventType := range m.handlers {
        subject := fmt.Sprintf("events.%s", eventType)
        
        if _, err := m.natsConn.Subscribe(subject, func(msg *nats.Msg) {
            var event BaseEvent
            if err := json.Unmarshal(msg.Data, &event); err != nil {
                log.Printf("解析事件失败: %v", err)
                return
            }
            
            m.processEvent(ctx, event)
        }); err != nil {
            return fmt.Errorf("NATS订阅失败: %w", err)
        }
    }
    
    // 订阅Redis事件
    pubsub := m.redisClient.PSubscribe(ctx, "events:*")
    defer pubsub.Close()
    
    go func() {
        for {
            select {
            case <-ctx.Done():
                return
            case msg := <-pubsub.Channel():
                var event BaseEvent
                if err := json.Unmarshal([]byte(msg.Payload), &event); err != nil {
                    log.Printf("解析Redis事件失败: %v", err)
                    continue
                }
                
                // 忽略本服务发出的事件，避免重复处理
                if event.Source == m.serviceName {
                    continue
                }
                
                m.processEvent(ctx, event)
            }
        }
    }()
    
    return nil
}

// 处理事件
func (m *EventManager) processEvent(ctx context.Context, event Event) {
    handlers, exists := m.handlers[event.GetType()]
    if !exists {
        return
    }
    
    for _, handler := range handlers {
        go func(h EventHandler) {
            if err := h.HandleEvent(ctx, event); err != nil {
                log.Printf("处理事件失败 [%s]: %v", event.GetType(), err)
            }
        }(handler)
    }
}

// 特定类型事件定义
// DeviceStateChangedEvent 设备状态变更事件
type DeviceStateChangedEvent struct {
    BaseEvent
    DeviceID    string
    HomeID      string
    Changes     map[string]interface{}
}

// SceneExecutedEvent 场景执行事件
type SceneExecutedEvent struct {
    BaseEvent
    SceneID     string
    HomeID      string
    Success     bool
    ExecutionID string
    Duration    time.Duration
}

// backend/events/handlers/device_event_handler.go
type DeviceEventHandler struct {
    deviceService    DeviceService
    notifyService    NotificationService
    automationEngine AutomationEngine
}

func (h *DeviceEventHandler) HandleEvent(ctx context.Context, event Event) error {
    switch e := event.GetPayload().(type) {
    case DeviceStateChangedEvent:
        return h.handleDeviceStateChanged(ctx, e)
    default:
        return fmt.Errorf("未知事件类型: %T", e)
    }
}

func (h *DeviceEventHandler) handleDeviceStateChanged(ctx context.Context, event DeviceStateChangedEvent) error {
    // 更新设备缓存
    if err := h.deviceService.UpdateDeviceCache(ctx, event.DeviceID, event.Changes); err != nil {
        return err
    }
    
    // 检查是否需要触发自动化规则
    if err := h.automationEngine.CheckTriggers(ctx, DeviceTrigger{
        DeviceID: event.DeviceID,
        HomeID:   event.HomeID,
        Changes:  event.Changes,
        Time:     event.Timestamp,
    }); err != nil {
        log.Printf("检查触发器失败: %v", err)
    }
    
    // 检查是否需要发送通知
    if h.shouldNotifyUser(event.DeviceID, event.Changes) {
        h.notifyService.SendDeviceNotification(ctx, event.DeviceID, event.Changes)
    }
    
    return nil
}
```

### 3.4 分布式状态一致性

```go
// backend/consistency/distributed_state.go
package consistency

import (
    "context"
    "errors"
    "fmt"
    "sync"
    "time"
    
    "github.com/go-redis/redis/v8"
)

// StateEntry 状态条目
type StateEntry struct {
    Key       string
    Value     interface{}
    Version   int64
    UpdatedAt time.Time
    TTL       time.Duration
}

// DistributedStateManager 分布式状态管理器
type DistributedStateManager struct {
    redisClient  *redis.Client
    localCache   sync.Map
    lockTTL      time.Duration
    stateTTL     time.Duration
    nodeID       string
}

// NewDistributedStateManager 创建分布式状态管理器
func NewDistributedStateManager(
    redisClient *redis.Client,
    nodeID string,
    lockTTL time.Duration,
    stateTTL time.Duration,
) *DistributedStateManager {
    return &DistributedStateManager{
        redisClient: redisClient,
        localCache:  sync.Map{},
        lockTTL:     lockTTL,
        stateTTL:    stateTTL,
        nodeID:      nodeID,
    }
}

// GetState 获取状态
func (m *DistributedStateManager) GetState(ctx context.Context, key string) (*StateEntry, error) {
    // 先查本地缓存
    if entry, ok := m.localCache.Load(key); ok {
        return entry.(*StateEntry), nil
    }
    
    // 从Redis获取
    data, err := m.redisClient.Get(ctx, getRedisKey(key)).Result()
    if err != nil {
        if errors.Is(err, redis.Nil) {
            return nil, ErrStateNotFound
        }
        return nil, fmt.Errorf("获取状态失败: %w", err)
    }
    
    var entry StateEntry
    if err := json.Unmarshal([]byte(data), &entry); err != nil {
        return nil, fmt.Errorf("解析状态失败: %w", err)
    }
    
    // 更新本地缓存
    m.localCache.Store(key, &entry)
    
    return &entry, nil
}

// SetState 设置状态
func (m *DistributedStateManager) SetState(ctx context.Context, entry *StateEntry) error {
    // 获取分布式锁
    lock := m.redisClient.NewMutex(getLockKey(entry.Key), 
        redis.MutexOptions{
            TTL: m.lockTTL,
        },
    )
    
    if err := lock.Lock(ctx); err != nil {
        return fmt.Errorf("获取锁失败: %w", err)
    }
    defer lock.Unlock(ctx)
    
    // 获取当前状态版本
    currentEntry, err := m.GetState(ctx, entry.Key)
    if err != nil && !errors.Is(err, ErrStateNotFound) {
        return err
    }
    
    // 如果存在当前状态，检查版本
    if currentEntry != nil {
        // 乐观锁检查，确保没有版本冲突
        if entry.Version > 0 && entry.Version != currentEntry.Version {
            return ErrVersionConflict
        }
        
        // 更新版本号
        entry.Version = currentEntry.Version + 1
    } else {
        // 新建状态，版本从1开始
        entry.Version = 1
    }
    
    // 设置更新时间
    entry.UpdatedAt = time.Now()
    
    // 设置TTL
    if entry.TTL == 0 {
        entry.TTL = m.stateTTL
    }
    
    // 序列化状态
    data, err := json.Marshal(entry)
    if err != nil {
        return fmt.Errorf("序列化状态失败: %w", err)
    }
    
    // 写入Redis
    if err := m.redisClient.Set(ctx, getRedisKey(entry.Key), data, entry.TTL).Err(); err != nil {
        return fmt.Errorf("设置状态失败: %w", err)
    }
    
    // 更新本地缓存
    m.localCache.Store(entry.Key, entry)
    
    // 发布状态变更通知
    if err := m.publishStateChanged(ctx, entry); err != nil {
        log.Printf("发布状态变更通知失败: %v", err)
    }
    
    return nil
}

// DeleteState 删除状态
func (m *DistributedStateManager) DeleteState(ctx context.Context, key string) error {
    // 获取分布式锁
    lock := m.redisClient.NewMutex(getLockKey(key),
        redis.MutexOptions{
            TTL: m.lockTTL,
        },
    )
    
    if err := lock.Lock(ctx); err != nil {
        return fmt.Errorf("获取锁失败: %w", err)
    }
    defer lock.Unlock(ctx)
    
    // 从Redis删除
    if err := m.redisClient.Del(ctx, getRedisKey(key)).Err(); err != nil {
        return fmt.Errorf("删除状态失败: %w", err)
    }
    
    // 从本地缓存删除
    m.localCache.Delete(key)
    
    // 发布状态删除通知
    if err := m.publishStateDeleted(ctx, key); err != nil {
        log.Printf("发布状态删除通知失败: %v", err)
    }
    
    return nil
}

// 发布状态变更通知
func (m *DistributedStateManager) publishStateChanged(ctx context.Context, entry *StateEntry) error {
    notification := StateChangeNotification{
        Type:      "state_changed",
        Key:       entry.Key,
        Version:   entry.Version,
        UpdatedAt: entry.UpdatedAt,
        Source:    m.nodeID,
    }
    
    data, err := json.Marshal(notification)
    if err != nil {
        return err
    }
    
    return m.redisClient.Publish(ctx, "state_changes", data).Err()
}

// 发布状态删除通知
func (m *DistributedStateManager) publishStateDeleted(ctx context.Context, key string) error {
    notification := StateChangeNotification{
        Type:      "state_deleted",
        Key:       key,
        UpdatedAt: time.Now(),
        Source:    m.nodeID,
    }
    
    data, err := json.Marshal(notification)
    if err != nil {
        return err
    }
    
    return m.redisClient.Publish(ctx, "state_changes", data).Err()
}

// 启动状态变更监听
func (m *DistributedStateManager) StartStateChangeListener(ctx context.Context) error {
    pubsub := m.redisClient.Subscribe(ctx, "state_changes")
    defer pubsub.Close()
    
    // 处理状态变更消息
    go func() {
        for {
            select {
            case <-ctx.Done():
                return
            case msg := <-pubsub.Channel():
                var notification StateChangeNotification
                if err := json.Unmarshal([]byte(msg.Payload), &notification); err != nil {
                    log.Printf("解析状态变更通知失败: %v", err)
                    continue
                }
                
                // 忽略自己发出的通知
                if notification.Source == m.nodeID {
                    continue
                }
                
                // 处理状态变更
                switch notification.Type {
                case "state_changed":
                    // 使本地缓存失效，下次获取时会从Redis刷新
                    m.localCache.Delete(notification.Key)
                case "state_deleted":
                    // 从本地缓存删除
                    m.localCache.Delete(notification.Key)
                }
            }
        }
    }()
    
    return nil
}

// 辅助函数
func getRedisKey(key string) string {
    return fmt.Sprintf("state:%s", key)
}

func getLockKey(key string) string {
    return fmt.Sprintf("lock:state:%s", key)
}

// StateChangeNotification 状态变更通知
type StateChangeNotification struct {
    Type      string
    Key       string
    Version   int64
    UpdatedAt time.Time
    Source    string
}
```

## 4. 前端架构深度设计

### 4.1 组件设计系统

```typescript
// frontend/src/components/design-system/index.ts
export * from './Button';
export * from './Card';
export * from './Input';
export * from './Toggle';
export * from './Slider';
export * from './Select';
export * from './Modal';
export * from './Notification';
export * from './Layout';
export * from './Tabs';
export * from './Icons';
export * from './Theme';

// frontend/src/components/design-system/Button.tsx
import React from 'react';
import styled, { css } from 'styled-components';
import { Spinner } from './Spinner';

export type ButtonVariant = 'primary' | 'secondary' | 'tertiary' | 'danger' | 'ghost';
export type ButtonSize = 'small' | 'medium' | 'large';

export interface ButtonProps extends React.ButtonHTMLAttributes<HTMLButtonElement> {
    variant?: ButtonVariant;
    size?: ButtonSize;
    isLoading?: boolean;
    isFullWidth?: boolean;
    leftIcon?: React.ReactNode;
    rightIcon?: React.ReactNode;
}

const sizeStyles = {
    small: css`
        height: 32px;
        padding: 0 12px;
        font-size: 14px;
    `,
    medium: css`
        height: 40px;
        padding: 0 16px;
        font-size: 16px;
    `,
    large: css`
        height: 48px;
        padding: 0 24px;
        font-size: 18px;
    `,
};

const variantStyles = {
    primary: css`
        background-color: ${props => props.theme.colors.primary};
        color: white;
        
        &:hover:not(:disabled) {
            background-color: ${props => props.theme.colors.primaryHover};
        }
        
        &:active:not(:disabled) {
            background-color: ${props => props.theme.colors.primaryActive};
        }
    `,
    secondary: css`
        background-color: ${props => props.theme.colors.secondary};
        color: white;
        
        &:hover:not(:disabled) {
            background-color: ${props => props.theme.colors.secondaryHover};
        }
        
        &:active:not(:disabled) {
            background-color: ${props => props.theme.colors.secondaryActive};
        }
    `,
    tertiary: css`
        background-color: transparent;
        color: ${props => props.theme.colors.primary};
        border: 1px solid ${props => props.theme.colors.primary};
        
        &:hover:not(:disabled) {
            background-color: ${props => props.theme.colors.primaryLight};
        }
        
        &:active:not(:disabled) {
            background-color: ${props => props.theme.colors.primaryLighter};
        }
    `,
    danger: css`
        background-color: ${props => props.theme.colors.danger};
        color: white;
        
        &:hover:not(:disabled) {
            background-color: ${props => props.theme.colors.dangerHover};
        }
        
        &:active:not(:disabled) {
            background-color: ${props => props.theme.colors.dangerActive};
        }
    `,
    ghost: css`
        background-color: transparent;
        color: ${props => props.theme.colors.text};
        
        &:hover:not(:disabled) {
            background-color: ${props => props.theme.colors.backgroundHover};
        }
        
        &:active:not(:disabled) {
            background-color: ${props => props.theme.colors.backgroundActive};
        }
    `,
};

const StyledButton = styled.button<ButtonProps>`
    display: inline-flex;
    align-items: center;
    justify-content: center;
    border-radius: ${props => props.theme.borderRadius};
    font-weight: 500;
    border: none;
    cursor: pointer;
    transition: all 0.2s ease;
    position: relative;
    
    ${props => sizeStyles[props.size || 'medium']}
    ${props => variantStyles[props.variant || 'primary']}
    
    width: ${props => props.isFullWidth ? '100%' : 'auto'};
    
    &:disabled {
        opacity: 0.6;
        cursor: not-allowed;
    }
    
    .button-content {
        display: flex;
        align-items: center;
        justify-content: center;
        visibility: ${props => props.isLoading ? 'hidden' : 'visible'};
    }
    
    .spinner-container {
        position: absolute;
        top: 50%;
        left: 50%;
        transform: translate(-50%, -50%);
    }
    
    .icon {
        display: flex;
        align-items: center;
    }
    
    .left-icon {
        margin-right: 8px;
    }
    
    .right-icon {
        margin-left: 8px;
    }
`;

export const Button: React.FC<ButtonProps> = ({
    children,
    variant = 'primary',
    size = 'medium',
    isLoading = false,
    isFullWidth = false,
    leftIcon,
    rightIcon,
    ...props
}) => {
    return (
        <StyledButton
            variant={variant}
            size={size}
            isLoading={isLoading}
            isFullWidth={isFullWidth}
            disabled={isLoading || props.disabled}
            {...props}
        >
            <div className="button-content">
                {leftIcon && <span className="icon left-icon">{leftIcon}</span>}
                {children}
                {rightIcon && <span className="icon right-icon">{rightIcon}</span>}
            </div>
            
            {isLoading && (
                <div className="spinner-container">
                    <Spinner size={size === 'small' ? 16 : size === 'medium' ? 20 : 24} color="currentColor" />
                </div>
            )}
        </StyledButton>
    );
};
```

### 4.2 设备控制组件

```typescript
// frontend/src/components/devices/DeviceCard.tsx
import React, { useState, useEffect } from 'react';
import styled from 'styled-components';
import { useDeviceState } from '../../hooks/useDeviceState';
import { useDeviceControl } from '../../hooks/useDeviceControl';
import { Device } from '../../models/device.model';
import { Card, Toggle, Slider, Button, Icon } from '../design-system';
import { DeviceIcon } from './DeviceIcon';
import { DeviceStatusIndicator } from './DeviceStatusIndicator';

interface DeviceCardProps {
    device: Device;
    onDetailsClick?: (device: Device) => void;
}

const StyledDeviceCard = styled(Card)`
    width: 100%;
    max-width: 300px;
    height: 180px;
    padding: 16px;
    position: relative;
    transition: transform 0.2s ease, box-shadow 0.2s ease;
    
    &:hover {
        transform: translateY(-4px);
        box-shadow: ${props => props.theme.shadows.medium};
    }
    
    .device-header {
        display: flex;
        align-items: center;
        margin-bottom: 16px;
        
        .device-icon {
            margin-right: 12px;
            color: ${props => props.theme.colors.primary};
        }
        
        .device-info {
            flex: 1;
            
            .device-name {
                
```typescript
                font-weight: 600;
                margin: 0 0 4px;
                color: ${props => props.theme.colors.textDark};
            }
            
            .device-room {
                font-size: 12px;
                color: ${props => props.theme.colors.textLight};
            }
        }
        
        .status-indicator {
            margin-left: 8px;
        }
    }
    
    .device-controls {
        margin-top: 20px;
    }
    
    .slider-container {
        margin-top: 16px;
    }
    
    .device-actions {
        position: absolute;
        bottom: 16px;
        right: 16px;
        display: flex;
        gap: 8px;
    }
`;

export const DeviceCard: React.FC<DeviceCardProps> = ({ device, onDetailsClick }) => {
    const { deviceState, isLoading: stateLoading } = useDeviceState(device.id);
    const { executeCommand, isLoading: commandLoading } = useDeviceControl();
    
    const isLoading = stateLoading || commandLoading;
    const isOn = deviceState?.power === 'on' || deviceState?.switch === 'on';
    
    const hasLightControl = device.hasCapability('dimmable') || device.hasCapability('colorable');
    const hasThermostatControl = device.hasCapability('thermostat');
    
    const handleToggleClick = () => {
        const command = isOn ? 'turnOff' : 'turnOn';
        const capability = device.hasCapability('switchable') ? 'switchable' : 'power';
        
        executeCommand(device.id, capability, command);
    };
    
    const handleBrightnessChange = (value: number) => {
        executeCommand(device.id, 'dimmable', 'setBrightness', { brightness: value });
    };
    
    const handleTemperatureChange = (value: number) => {
        executeCommand(device.id, 'thermostat', 'setTemperature', { temperature: value });
    };
    
    return (
        <StyledDeviceCard>
            <div className="device-header">
                <div className="device-icon">
                    <DeviceIcon type={device.type} size={32} />
                </div>
                <div className="device-info">
                    <h3 className="device-name">{device.name}</h3>
                    {device.room && <p className="device-room">{device.room.name}</p>}
                </div>
                <div className="status-indicator">
                    <DeviceStatusIndicator online={device.online} />
                </div>
            </div>
            
            <div className="device-controls">
                {device.hasCapability('switchable') && (
                    <Toggle 
                        isChecked={isOn}
                        onChange={handleToggleClick}
                        disabled={!device.online || isLoading}
                        label={isOn ? '开' : '关'}
                    />
                )}
                
                {hasLightControl && isOn && (
                    <div className="slider-container">
                        <Slider
                            min={1}
                            max={100}
                            value={deviceState?.brightness || 100}
                            onChange={handleBrightnessChange}
                            disabled={!device.online || isLoading}
                            label="亮度"
                            showValue
                        />
                    </div>
                )}
                
                {hasThermostatControl && (
                    <div className="slider-container">
                        <Slider
                            min={16}
                            max={32}
                            value={deviceState?.temperature || 24}
                            onChange={handleTemperatureChange}
                            disabled={!device.online || isLoading}
                            label="温度"
                            showValue
                            unit="°C"
                        />
                    </div>
                )}
            </div>
            
            <div className="device-actions">
                <Button
                    variant="ghost"
                    size="small"
                    onClick={() => onDetailsClick?.(device)}
                    aria-label="设备详情"
                >
                    <Icon name="settings" size={18} />
                </Button>
            </div>
        </StyledDeviceCard>
    );
};

// frontend/src/components/devices/DeviceControlPanel.tsx
import React, { useState, useEffect } from 'react';
import styled from 'styled-components';
import { 
    Tabs, TabList, Tab, TabPanel, 
    Card, Button, Slider, ColorPicker, Select, 
    Toggle, Input
} from '../design-system';
import { Device } from '../../models/device.model';
import { useDeviceState } from '../../hooks/useDeviceState';
import { useDeviceControl } from '../../hooks/useDeviceControl';
import { DeviceHistoryChart } from './DeviceHistoryChart';
import { DeviceIcon } from './DeviceIcon';

interface DeviceControlPanelProps {
    device: Device;
    onClose: () => void;
}

const StyledPanel = styled(Card)`
    width: 100%;
    max-width: 600px;
    margin: 0 auto;
    
    .panel-header {
        display: flex;
        align-items: center;
        margin-bottom: 24px;
        
        .device-icon {
            margin-right: 16px;
            color: ${props => props.theme.colors.primary};
        }
        
        .device-info {
            flex: 1;
            
            .device-name {
                font-size: 24px;
                font-weight: 600;
                margin: 0 0 4px;
            }
            
            .device-details {
                font-size: 14px;
                color: ${props => props.theme.colors.textLight};
            }
        }
    }
    
    .control-section {
        margin-bottom: 24px;
    }
    
    .control-row {
        display: flex;
        align-items: center;
        margin-bottom: 16px;
        
        .control-label {
            width: 120px;
            font-weight: 500;
        }
        
        .control-content {
            flex: 1;
        }
    }
    
    .panel-footer {
        display: flex;
        justify-content: flex-end;
        margin-top: 24px;
        gap: 12px;
    }
`;

export const DeviceControlPanel: React.FC<DeviceControlPanelProps> = ({ device, onClose }) => {
    const { deviceState, isLoading: stateLoading } = useDeviceState(device.id);
    const { executeCommand, isLoading: commandLoading } = useDeviceControl();
    
    const isLoading = stateLoading || commandLoading;
    const isOn = deviceState?.power === 'on' || deviceState?.switch === 'on';
    
    const handlePowerToggle = () => {
        const command = isOn ? 'turnOff' : 'turnOn';
        const capability = device.hasCapability('switchable') ? 'switchable' : 'power';
        
        executeCommand(device.id, capability, command);
    };
    
    // 渲染不同设备类型的控制面板
    const renderDeviceControls = () => {
        if (device.type === 'light') {
            return renderLightControls();
        } else if (device.type === 'thermostat') {
            return renderThermostatControls();
        } else if (device.type === 'lock') {
            return renderLockControls();
        } else if (device.type === 'camera') {
            return renderCameraControls();
        } else {
            return renderGenericControls();
        }
    };
    
    const renderLightControls = () => {
        return (
            <div className="control-section">
                <div className="control-row">
                    <div className="control-label">开关</div>
                    <div className="control-content">
                        <Toggle
                            isChecked={isOn}
                            onChange={handlePowerToggle}
                            disabled={!device.online || isLoading}
                            size="large"
                        />
                    </div>
                </div>
                
                {device.hasCapability('dimmable') && (
                    <div className="control-row">
                        <div className="control-label">亮度</div>
                        <div className="control-content">
                            <Slider
                                min={1}
                                max={100}
                                value={deviceState?.brightness || 100}
                                onChange={(value) => executeCommand(
                                    device.id, 'dimmable', 'setBrightness', { brightness: value }
                                )}
                                disabled={!device.online || !isOn || isLoading}
                                showValue
                                unit="%"
                            />
                        </div>
                    </div>
                )}
                
                {device.hasCapability('colorable') && (
                    <div className="control-row">
                        <div className="control-label">颜色</div>
                        <div className="control-content">
                            <ColorPicker
                                color={deviceState?.color || '#ffffff'}
                                onChange={(color) => executeCommand(
                                    device.id, 'colorable', 'setColor', { color }
                                )}
                                disabled={!device.online || !isOn || isLoading}
                            />
                        </div>
                    </div>
                )}
                
                {device.hasCapability('colorTemperature') && (
                    <div className="control-row">
                        <div className="control-label">色温</div>
                        <div className="control-content">
                            <Slider
                                min={2700}
                                max={6500}
                                value={deviceState?.colorTemperature || 4000}
                                onChange={(value) => executeCommand(
                                    device.id, 'colorTemperature', 'setColorTemperature', 
                                    { temperature: value }
                                )}
                                disabled={!device.online || !isOn || isLoading}
                                showValue
                                unit="K"
                            />
                        </div>
                    </div>
                )}
            </div>
        );
    };
    
    const renderThermostatControls = () => {
        // 温控器控制面板实现
        return (
            <div className="control-section">
                <div className="control-row">
                    <div className="control-label">模式</div>
                    <div className="control-content">
                        <Select
                            value={deviceState?.mode || 'heat'}
                            onChange={(value) => executeCommand(
                                device.id, 'thermostat', 'setMode', { mode: value }
                            )}
                            disabled={!device.online || isLoading}
                            options={[
                                { value: 'heat', label: '制热' },
                                { value: 'cool', label: '制冷' },
                                { value: 'auto', label: '自动' },
                                { value: 'off', label: '关闭' },
                            ]}
                        />
                    </div>
                </div>
                
                <div className="control-row">
                    <div className="control-label">温度设置</div>
                    <div className="control-content">
                        <Slider
                            min={16}
                            max={32}
                            value={deviceState?.targetTemperature || 24}
                            onChange={(value) => executeCommand(
                                device.id, 'thermostat', 'setTargetTemperature', 
                                { temperature: value }
                            )}
                            disabled={!device.online || deviceState?.mode === 'off' || isLoading}
                            showValue
                            unit="°C"
                        />
                    </div>
                </div>
                
                <div className="control-row">
                    <div className="control-label">当前温度</div>
                    <div className="control-content">
                        <span>{deviceState?.currentTemperature || '--'}°C</span>
                    </div>
                </div>
                
                <div className="control-row">
                    <div className="control-label">湿度</div>
                    <div className="control-content">
                        <span>{deviceState?.humidity || '--'}%</span>
                    </div>
                </div>
            </div>
        );
    };
    
    const renderLockControls = () => {
        // 门锁控制面板实现
        const isLocked = deviceState?.lockState === 'locked';
        
        return (
            <div className="control-section">
                <div className="control-row">
                    <div className="control-label">锁状态</div>
                    <div className="control-content">
                        <Button
                            variant={isLocked ? 'primary' : 'secondary'}
                            onClick={() => executeCommand(
                                device.id, 'lock', isLocked ? 'unlock' : 'lock'
                            )}
                            disabled={!device.online || isLoading}
                            leftIcon={<Icon name={isLocked ? 'lock' : 'unlock'} />}
                            isLoading={isLoading}
                        >
                            {isLocked ? '已锁定' : '已解锁'}
                        </Button>
                    </div>
                </div>
                
                {device.hasCapability('pinCodeLock') && (
                    <div className="control-row">
                        <div className="control-label">临时密码</div>
                        <div className="control-content">
                            <Button
                                variant="tertiary"
                                onClick={() => executeCommand(
                                    device.id, 'pinCodeLock', 'generateTemporaryPin'
                                )}
                                disabled={!device.online || isLoading}
                            >
                                生成临时密码
                            </Button>
                        </div>
                    </div>
                )}
                
                <div className="control-row">
                    <div className="control-label">最近操作</div>
                    <div className="control-content">
                        <p>
                            {deviceState?.lastAction ? (
                                `${deviceState.lastAction.type} - ${new Date(deviceState.lastAction.time).toLocaleString()}`
                            ) : '无记录'}
                        </p>
                    </div>
                </div>
            </div>
        );
    };
    
    const renderCameraControls = () => {
        // 摄像头控制面板实现
        return (
            <div className="control-section">
                <div className="camera-preview">
                    {deviceState?.streamUrl ? (
                        <img 
                            src={deviceState.streamUrl} 
                            alt="Camera Preview" 
                            style={{ width: '100%', borderRadius: '8px' }}
                        />
                    ) : (
                        <div className="no-preview">
                            <Icon name="camera-off" size={48} />
                            <p>摄像头离线或未开启流</p>
                        </div>
                    )}
                </div>
                
                <div className="control-row">
                    <div className="control-label">流状态</div>
                    <div className="control-content">
                        <Toggle
                            isChecked={!!deviceState?.streamActive}
                            onChange={() => executeCommand(
                                device.id, 'camera', 
                                deviceState?.streamActive ? 'stopStream' : 'startStream'
                            )}
                            disabled={!device.online || isLoading}
                            label={deviceState?.streamActive ? '流已开启' : '流已关闭'}
                        />
                    </div>
                </div>
                
                {device.hasCapability('ptz') && (
                    <div className="control-row">
                        <div className="control-label">控制</div>
                        <div className="control-content ptz-controls">
                            <Button
                                variant="ghost"
                                onClick={() => executeCommand(
                                    device.id, 'ptz', 'move', { direction: 'up' }
                                )}
                                disabled={!device.online || isLoading}
                            >
                                <Icon name="arrow-up" />
                            </Button>
                            
                            <div style={{ display: 'flex', gap: '8px' }}>
                                <Button
                                    variant="ghost"
                                    onClick={() => executeCommand(
                                        device.id, 'ptz', 'move', { direction: 'left' }
                                    )}
                                    disabled={!device.online || isLoading}
                                >
                                    <Icon name="arrow-left" />
                                </Button>
                                
                                <Button
                                    variant="ghost"
                                    onClick={() => executeCommand(
                                        device.id, 'ptz', 'move', { direction: 'right' }
                                    )}
                                    disabled={!device.online || isLoading}
                                >
                                    <Icon name="arrow-right" />
                                </Button>
                            </div>
                            
                            <Button
                                variant="ghost"
                                onClick={() => executeCommand(
                                    device.id, 'ptz', 'move', { direction: 'down' }
                                )}
                                disabled={!device.online || isLoading}
                            >
                                <Icon name="arrow-down" />
                            </Button>
                        </div>
                    </div>
                )}
            </div>
        );
    };
    
    const renderGenericControls = () => {
        // 通用设备控制面板实现
        return (
            <div className="control-section">
                {device.hasCapability('switchable') && (
                    <div className="control-row">
                        <div className="control-label">电源</div>
                        <div className="control-content">
                            <Toggle
                                isChecked={isOn}
                                onChange={handlePowerToggle}
                                disabled={!device.online || isLoading}
                                size="large"
                            />
                        </div>
                    </div>
                )}
                
                {Object.entries(deviceState || {}).map(([key, value]) => {
                    if (key === 'power' || key === 'switch') return null;
                    
                    return (
                        <div className="control-row" key={key}>
                            <div className="control-label">{formatPropertyName(key)}</div>
                            <div className="control-content">
                                {formatPropertyValue(key, value)}
                            </div>
                        </div>
                    );
                })}
            </div>
        );
    };
    
    // 辅助函数，格式化属性名
    const formatPropertyName = (name: string): string => {
        const nameMap: Record<string, string> = {
            'temperature': '温度',
            'humidity': '湿度',
            'battery': '电池',
            'online': '在线状态',
            'brightness': '亮度',
            'color': '颜色',
            'mode': '模式'
            // 更多映射...
        };
        
        return nameMap[name] || name.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase());
    };
    
    // 辅助函数，格式化属性值
    const formatPropertyValue = (key: string, value: any): React.ReactNode => {
        if (key === 'battery') {
            return `${value}%`;
        } else if (key === 'temperature') {
            return `${value}°C`;
        } else if (key === 'humidity') {
            return `${value}%`;
        } else if (key === 'online') {
            return value ? '在线' : '离线';
        } else if (key === 'color' && typeof value === 'string') {
            return (
                <div style={{ 
                    width: '24px', 
                    height: '24px', 
                    backgroundColor: value,
                    borderRadius: '4px',
                    border: '1px solid #ddd'
                }} />
            );
        } else if (key === 'lastSeen' && value) {
            return new Date(value).toLocaleString();
        }
        
        return String(value);
    };
    
    return (
        <StyledPanel>
            <div className="panel-header">
                <div className="device-icon">
                    <DeviceIcon type={device.type} size={48} />
                </div>
                <div className="device-info">
                    <h2 className="device-name">{device.name}</h2>
                    <p className="device-details">
                        {device.manufacturer} {device.model} • 
                        {device.online ? ' 在线' : ' 离线'} • 
                        {device.room ? ` ${device.room.name}` : ''}
                    </p>
                </div>
            </div>
            
            <Tabs>
                <TabList>
                    <Tab>控制</Tab>
                    <Tab>历史</Tab>
                    <Tab>设置</Tab>
                </TabList>
                
                <TabPanel>
                    {renderDeviceControls()}
                </TabPanel>
                
                <TabPanel>
                    <DeviceHistoryChart deviceId={device.id} />
                </TabPanel>
                
                <TabPanel>
                    <div className="control-section">
                        <div className="control-row">
                            <div className="control-label">设备名称</div>
                            <div className="control-content">
                                <Input 
                                    value={device.name}
                                    onChange={() => {/* 实现设备重命名 */}}
                                />
                            </div>
                        </div>
                        
                        <div className="control-row">
                            <div className="control-label">所在房间</div>
                            <div className="control-content">
                                {/* 房间选择器实现 */}
                            </div>
                        </div>
                        
                        <div className="control-row">
                            <div className="control-label">固件版本</div>
                            <div className="control-content">
                                <p>{device.firmwareVersion || '未知'}</p>
                                {device.firmwareUpdateAvailable && (
                                    <Button
                                        variant="secondary"
                                        size="small"
                                        onClick={() => executeCommand(
                                            device.id, 'firmware', 'updateFirmware'
                                        )}
                                    >
                                        更新固件
                                    </Button>
                                )}
                            </div>
                        </div>
                    </div>
                </TabPanel>
            </Tabs>
            
            <div className="panel-footer">
                <Button variant="tertiary" onClick={onClose}>
                    关闭
                </Button>
            </div>
        </StyledPanel>
    );
};
```

### 4.3 状态管理架构

```typescript
// frontend/src/store/index.ts
import { configureStore } from '@reduxjs/toolkit';
import { 
    deviceReducer,
    sceneReducer,
    automationReducer,
    userReducer,
    uiReducer,
    notificationReducer
} from './slices';
import { apiMiddleware } from './middleware/api';
import { webSocketMiddleware } from './middleware/websocket';
import { analyticsMiddleware } from './middleware/analytics';
import { persistanceMiddleware } from './middleware/persistance';

export const store = configureStore({
    reducer: {
        devices: deviceReducer,
        scenes: sceneReducer,
        automations: automationReducer,
        user: userReducer,
        ui: uiReducer,
        notifications: notificationReducer
    },
    middleware: (getDefaultMiddleware) => 
        getDefaultMiddleware({
            serializableCheck: {
                // 忽略非序列化状态的检查
                ignoredActions: ['devices/updateDeviceState/fulfilled'],
                ignoredPaths: ['devices.entities']
            }
        })
        .concat(apiMiddleware)
        .concat(webSocketMiddleware)
        .concat(analyticsMiddleware)
        .concat(persistanceMiddleware)
});

export type RootState = ReturnType<typeof store.getState>;
export type AppDispatch = typeof store.dispatch;

// frontend/src/store/slices/device.slice.ts
import { createSlice, createAsyncThunk, PayloadAction, createEntityAdapter } from '@reduxjs/toolkit';
import { Device, DeviceState } from '../../models/device.model';
import { deviceService } from '../../services';
import { RootState } from '../index';

// 设备适配器，用于标准化设备状态管理
const deviceAdapter = createEntityAdapter<Device>({
    selectId: (device) => device.id,
    sortComparer: (a, b) => a.name.localeCompare(b.name)
});

// 异步操作：获取所有设备
export const fetchDevices = createAsyncThunk(
    'devices/fetchDevices',
    async (_, { rejectWithValue }) => {
        try {
            const devices = await deviceService.getAllDevices();
            return devices;
        } catch (error) {
            return rejectWithValue(error.message);
        }
    }
);

// 异步操作：获取单个设备
export const fetchDevice = createAsyncThunk(
    'devices/fetchDevice',
    async (id: string, { rejectWithValue }) => {
        try {
            const device = await deviceService.getDevice(id);
            return device;
        } catch (error) {
            return rejectWithValue(error.message);
        }
    }
);

// 异步操作：执行设备命令
export const executeDeviceCommand = createAsyncThunk(
    'devices/executeCommand',
    async ({ 
        deviceId, 
        capability, 
        command, 
        parameters 
    }: {
        deviceId: string;
        capability: string;
        command: string;
        parameters?: Record<string, any>;
    }, { rejectWithValue }) => {
        try {
            const success = await deviceService.executeCommand(
                deviceId, capability, command, parameters
            );
            
            return {
                deviceId,
                success,
                capability,
                command,
                parameters
            };
        } catch (error) {
            return rejectWithValue(error.message);
        }
    }
);

// 异步操作：更新设备状态
export const updateDeviceState = createAsyncThunk(
    'devices/updateDeviceState',
    async ({ 
        deviceId, 
        state 
    }: {
        deviceId: string;
        state: Partial<DeviceState>;
    }, { getState, rejectWithValue }) => {
        try {
            // 这里可以选择是否需要调用API
            // 通常WebSocket已经推送了状态，只需更新本地状态
            return {
                deviceId,
                state
            };
        } catch (error) {
            return rejectWithValue(error.message);
        }
    }
);

// 设备状态接口
interface DevicesState {
    deviceStates: Record<string, DeviceState>;
    loading: boolean;
    error: string | null;
    lastUpdated: Record<string, Date>;
}

// 初始状态
const initialState = deviceAdapter.getInitialState<DevicesState>({
    deviceStates: {},
    loading: false,
    error: null,
    lastUpdated: {}
});

// 设备状态切片
const deviceSlice = createSlice({
    name: 'devices',
    initialState,
    reducers: {
        // 设备在线状态变更
        deviceOnlineStatusChanged(state, action: PayloadAction<{
            deviceId: string;
            online: boolean;
        }>) {
            const { deviceId, online } = action.payload;
            const device = state.entities[deviceId];
            if (device) {
                device.online = online;
            }
        },
        
        // 清除错误
        clearError(state) {
            state.error = null;
        },
        
        // WebSocket接收到设备状态更新
        deviceStateReceived(state, action: PayloadAction<{
            deviceId: string;
            state: Partial<DeviceState>;
        }>) {
            const { deviceId, state: newState } = action.payload;
            
            // 更新设备状态
            if (!state.deviceStates[deviceId]) {
                state.deviceStates[deviceId] = {} as DeviceState;
            }
            
            state.deviceStates[deviceId] = {
                ...state.deviceStates[deviceId],
                ...newState
            };
            
            // 更新最后更新时间
            state.lastUpdated[deviceId] = new Date();
        },
        
        // 批量更新设备状态
        batchUpdateDeviceStates(state, action: PayloadAction<Record<string, Partial<DeviceState>>>) {
            const updates = action.payload;
            
            for (const [deviceId, newState] of Object.entries(updates)) {
                if (!state.deviceStates[deviceId]) {
                    state.deviceStates[deviceId] = {} as DeviceState;
                }
                
                state.deviceStates[deviceId] = {
                    ...state.deviceStates[deviceId],
                    ...newState
                };
                
                state.lastUpdated[deviceId] = new Date();
            }
        }
    },
    extraReducers: (builder) => {
        builder
            // 获取所有设备
            .addCase(fetchDevices.pending, (state) => {
                state.loading = true;
                state.error = null;
            })
            .addCase(fetchDevices.fulfilled, (state, action) => {
                state.loading = false;
                deviceAdapter.setAll(state, action.payload);
            })
            .addCase(fetchDevices.rejected, (state, action) => {
                state.loading = false;
                state.error = action.payload as string;
            })
            
            // 获取单个设备
            .addCase(fetchDevice.fulfilled, (state, action) => {
                deviceAdapter.upsertOne(state, action.payload);
            })
            
            // 执行设备命令
            .addCase(executeDeviceCommand.pending, (state) => {
                state.loading = true;
                state.
```typescript
                state.error = null;
            })
            .addCase(executeDeviceCommand.fulfilled, (state, action) => {
                state.loading = false;
                
                // 为了响应性，我们可以在这里乐观地更新设备状态
                // 后续WebSocket会提供准确状态
                const { deviceId, command, capability, parameters } = action.payload;
                
                if (!state.deviceStates[deviceId]) {
                    state.deviceStates[deviceId] = {} as DeviceState;
                }
                
                // 基于命令类型更新状态
                if (command === 'turnOn') {
                    state.deviceStates[deviceId].power = 'on';
                } else if (command === 'turnOff') {
                    state.deviceStates[deviceId].power = 'off';
                } else if (command === 'setBrightness' && parameters?.brightness) {
                    state.deviceStates[deviceId].brightness = parameters.brightness;
                } else if (command === 'setColor' && parameters?.color) {
                    state.deviceStates[deviceId].color = parameters.color;
                }
                
                state.lastUpdated[deviceId] = new Date();
            })
            .addCase(executeDeviceCommand.rejected, (state, action) => {
                state.loading = false;
                state.error = action.payload as string;
            })
            
            // 更新设备状态
            .addCase(updateDeviceState.fulfilled, (state, action) => {
                const { deviceId, state: newState } = action.payload;
                
                if (!state.deviceStates[deviceId]) {
                    state.deviceStates[deviceId] = {} as DeviceState;
                }
                
                state.deviceStates[deviceId] = {
                    ...state.deviceStates[deviceId],
                    ...newState
                };
                
                state.lastUpdated[deviceId] = new Date();
            });
    }
});

// 导出操作
export const { 
    deviceOnlineStatusChanged, 
    clearError, 
    deviceStateReceived,
    batchUpdateDeviceStates
} = deviceSlice.actions;

// 导出选择器
export const selectDeviceState = (state: RootState, deviceId: string) => 
    state.devices.deviceStates[deviceId];

export const selectDeviceById = (state: RootState, deviceId: string) =>
    state.devices.entities[deviceId];

export const selectAllDevices = (state: RootState) =>
    Object.values(state.devices.entities).filter(device => device !== undefined) as Device[];

export const selectDevicesByRoom = (state: RootState, roomId: string) =>
    selectAllDevices(state).filter(device => device.roomId === roomId);

export const selectDevicesByType = (state: RootState, type: string) =>
    selectAllDevices(state).filter(device => device.type === type);

export const selectDevicesLoading = (state: RootState) => state.devices.loading;

export const selectDevicesError = (state: RootState) => state.devices.error;

// 导出reducer
export const deviceReducer = deviceSlice.reducer;

// frontend/src/store/middleware/websocket.ts
import { Middleware } from 'redux';
import { deviceStateReceived, deviceOnlineStatusChanged } from '../slices/device.slice';
import { sceneExecutionUpdated } from '../slices/scene.slice';
import { notificationReceived } from '../slices/notification.slice';
import { RootState } from '../index';

export const webSocketMiddleware: Middleware<{}, RootState> = store => {
    let socket: WebSocket | null = null;
    let reconnectInterval: number | null = null;
    let reconnectTimeout = 1000; // 初始重连延迟1秒
    const maxReconnectTimeout = 30000; // 最大重连延迟30秒

    const connect = () => {
        // 获取认证Token
        const token = store.getState().user.token;
        if (!token) return;

        // 创建WebSocket连接
        socket = new WebSocket(`${process.env.REACT_APP_WS_URL}/ws?token=${token}`);

        socket.onopen = () => {
            console.log('WebSocket连接已建立');
            // 重置重连计时器
            reconnectTimeout = 1000;
            if (reconnectInterval) {
                clearInterval(reconnectInterval);
                reconnectInterval = null;
            }
        };

        socket.onclose = (event) => {
            console.log('WebSocket连接已关闭', event);
            socket = null;

            // 设置重连
            if (!reconnectInterval) {
                reconnectInterval = window.setInterval(() => {
                    connect();
                    // 指数退避重连
                    reconnectTimeout = Math.min(reconnectTimeout * 1.5, maxReconnectTimeout);
                }, reconnectTimeout);
            }
        };

        socket.onerror = (error) => {
            console.error('WebSocket错误', error);
        };

        socket.onmessage = (event) => {
            try {
                const data = JSON.parse(event.data);
                handleMessage(data);
            } catch (error) {
                console.error('WebSocket消息解析错误', error);
            }
        };
    };

    const handleMessage = (message: any) => {
        switch (message.type) {
            case 'device.state.changed':
                store.dispatch(deviceStateReceived({
                    deviceId: message.data.deviceId,
                    state: message.data.changes
                }));
                break;
            case 'device.online.changed':
                store.dispatch(deviceOnlineStatusChanged({
                    deviceId: message.data.deviceId,
                    online: message.data.online
                }));
                break;
            case 'scene.execution.updated':
                store.dispatch(sceneExecutionUpdated(message.data));
                break;
            case 'notification':
                store.dispatch(notificationReceived(message.data));
                break;
            default:
                console.log('未处理的WebSocket消息类型', message.type);
        }
    };

    return next => action => {
        // 用户登录成功时连接WebSocket
        if (action.type === 'user/login/fulfilled') {
            connect();
        }
        
        // 用户登出时断开WebSocket
        if (action.type === 'user/logout') {
            if (socket) {
                socket.close();
                socket = null;
            }
            
            if (reconnectInterval) {
                clearInterval(reconnectInterval);
                reconnectInterval = null;
            }
        }
        
        // 发送消息到WebSocket
        if (action.type === 'websocket/send' && socket) {
            socket.send(JSON.stringify(action.payload));
        }
        
        return next(action);
    };
};
```

### 4.4 离线模式与数据持久化

```typescript
// frontend/src/store/middleware/persistance.ts
import { Middleware } from 'redux';
import { RootState } from '../index';
import localforage from 'localforage';
import { throttle } from 'lodash';

// 配置持久化存储
localforage.config({
    name: 'smarthome',
    storeName: 'app_state'
});

// 需要持久化的状态键
const PERSISTED_KEYS = [
    'devices.entities',
    'devices.deviceStates',
    'scenes.entities',
    'automations.entities',
    'user.preferences',
    'ui.layout'
];

// 从存储加载状态
export const loadState = async (): Promise<Partial<RootState>> => {
    try {
        const serializedState = await localforage.getItem<string>('appState');
        if (serializedState === null) {
            return {};
        }
        return JSON.parse(serializedState);
    } catch (err) {
        console.error('加载持久化状态失败', err);
        return {};
    }
};

// 将状态保存到存储
const saveState = async (state: RootState) => {
    try {
        // 筛选需要持久化的状态
        const persistedState: any = {};
        
        for (const key of PERSISTED_KEYS) {
            const parts = key.split('.');
            let value = state;
            
            for (const part of parts) {
                if (!value[part]) break;
                value = value[part];
            }
            
            if (value !== state) {
                if (!persistedState[parts[0]]) {
                    persistedState[parts[0]] = {};
                }
                persistedState[parts[0]][parts[1]] = value;
            }
        }
        
        // 为大型对象添加序列化安全检查
        const serializedState = JSON.stringify(persistedState);
        await localforage.setItem('appState', serializedState);
    } catch (err) {
        console.error('保存状态失败', err);
    }
};

// 节流版本的保存状态函数，避免频繁写入
const throttledSaveState = throttle(saveState, 1000);

// 持久化中间件
export const persistanceMiddleware: Middleware<{}, RootState> = store => next => action => {
    const result = next(action);
    throttledSaveState(store.getState());
    return result;
};

// frontend/src/offline/sync-manager.ts
import { deviceService, sceneService } from '../services';
import localforage from 'localforage';
import { v4 as uuidv4 } from 'uuid';
import { store } from '../store';
import { executeDeviceCommand } from '../store/slices/device.slice';

// 离线命令队列
interface OfflineCommand {
    id: string;
    type: 'device' | 'scene';
    action: string;
    params: any;
    timestamp: number;
    retryCount: number;
}

// 离线同步管理器
class SyncManager {
    private commandQueue: OfflineCommand[] = [];
    private isOnline: boolean = navigator.onLine;
    private isSyncing: boolean = false;
    
    constructor() {
        // 监听在线状态变化
        window.addEventListener('online', this.handleOnline);
        window.addEventListener('offline', this.handleOffline);
        
        // 初始化
        this.init();
    }
    
    private async init() {
        // 加载未同步的命令
        try {
            const savedCommands = await localforage.getItem<OfflineCommand[]>('offlineCommands');
            if (savedCommands) {
                this.commandQueue = savedCommands;
                console.log(`加载了 ${savedCommands.length} 条离线命令`);
            }
        } catch (error) {
            console.error('加载离线命令失败', error);
        }
        
        // 如果在线，尝试立即同步
        if (this.isOnline) {
            this.syncCommands();
        }
    }
    
    private handleOnline = () => {
        console.log('网络连接已恢复');
        this.isOnline = true;
        this.syncCommands();
    }
    
    private handleOffline = () => {
        console.log('网络连接已断开');
        this.isOnline = false;
    }
    
    // 添加离线命令
    public addCommand(command: Omit<OfflineCommand, 'id' | 'timestamp' | 'retryCount'>) {
        const fullCommand: OfflineCommand = {
            ...command,
            id: uuidv4(),
            timestamp: Date.now(),
            retryCount: 0
        };
        
        this.commandQueue.push(fullCommand);
        this.saveQueue();
        
        // 如果在线，尝试立即同步
        if (this.isOnline) {
            this.syncCommands();
        }
    }
    
    // 同步命令队列
    private async syncCommands() {
        if (this.isSyncing || this.commandQueue.length === 0 || !this.isOnline) {
            return;
        }
        
        this.isSyncing = true;
        console.log(`开始同步 ${this.commandQueue.length} 条命令`);
        
        // 复制队列进行处理，防止同步过程中添加新命令
        const commands = [...this.commandQueue];
        const failedCommands: OfflineCommand[] = [];
        
        for (const command of commands) {
            try {
                await this.executeCommand(command);
                // 从队列中移除成功执行的命令
                this.commandQueue = this.commandQueue.filter(cmd => cmd.id !== command.id);
            } catch (error) {
                console.error(`执行命令失败: ${command.id}`, error);
                
                // 更新重试计数
                const updatedCommand = {
                    ...command,
                    retryCount: command.retryCount + 1
                };
                
                // 如果重试次数过多，放弃该命令
                if (updatedCommand.retryCount >= 5) {
                    console.warn(`命令 ${command.id} 已达到最大重试次数，放弃执行`);
                    this.commandQueue = this.commandQueue.filter(cmd => cmd.id !== command.id);
                } else {
                    failedCommands.push(updatedCommand);
                    // 更新队列中的命令
                    this.commandQueue = this.commandQueue.map(cmd => 
                        cmd.id === command.id ? updatedCommand : cmd
                    );
                }
            }
        }
        
        // 保存更新后的队列
        await this.saveQueue();
        
        this.isSyncing = false;
        console.log(`同步完成，剩余 ${this.commandQueue.length} 条命令未同步`);
    }
    
    // 执行单个命令
    private async executeCommand(command: OfflineCommand) {
        if (command.type === 'device') {
            switch (command.action) {
                case 'executeCommand':
                    const { deviceId, capability, command: cmd, parameters } = command.params;
                    await deviceService.executeCommand(deviceId, capability, cmd, parameters);
                    break;
                default:
                    throw new Error(`未知的设备命令类型: ${command.action}`);
            }
        } else if (command.type === 'scene') {
            switch (command.action) {
                case 'executeScene':
                    await sceneService.executeScene(command.params.sceneId);
                    break;
                default:
                    throw new Error(`未知的场景命令类型: ${command.action}`);
            }
        }
    }
    
    // 保存队列到本地存储
    private async saveQueue() {
        try {
            await localforage.setItem('offlineCommands', this.commandQueue);
        } catch (error) {
            console.error('保存命令队列失败', error);
        }
    }
    
    // 获取队列长度
    public getQueueLength(): number {
        return this.commandQueue.length;
    }
    
    // 清空队列
    public async clearQueue() {
        this.commandQueue = [];
        await this.saveQueue();
    }
}

// 创建单例实例
export const syncManager = new SyncManager();

// 离线模式的动作中间件
export const offlineActionMiddleware = store => next => action => {
    // 检查是否是设备命令执行动作
    if (action.type === 'devices/executeCommand/pending') {
        const { deviceId, capability, command, parameters } = action.meta.arg;
        
        // 如果离线，添加到离线队列
        if (!navigator.onLine) {
            syncManager.addCommand({
                type: 'device',
                action: 'executeCommand',
                params: { deviceId, capability, command, parameters }
            });
            
            // 返回一个本地模拟的成功响应，以保持UI响应性
            return next({
                type: 'devices/executeCommand/fulfilled',
                payload: {
                    deviceId,
                    success: true,
                    capability,
                    command,
                    parameters,
                    offlineQueued: true
                },
                meta: action.meta
            });
        }
    }
    
    // 其他情况正常处理
    return next(action);
};

// frontend/src/hooks/useOfflineStatus.ts
import { useState, useEffect } from 'react';
import { syncManager } from '../offline/sync-manager';

export function useOfflineStatus() {
    const [isOnline, setIsOnline] = useState(navigator.onLine);
    const [pendingActions, setPendingActions] = useState(syncManager.getQueueLength());
    
    useEffect(() => {
        // 监听在线状态变化
        const handleOnline = () => setIsOnline(true);
        const handleOffline = () => setIsOnline(false);
        
        window.addEventListener('online', handleOnline);
        window.addEventListener('offline', handleOffline);
        
        // 定期检查队列长度
        const intervalId = setInterval(() => {
            setPendingActions(syncManager.getQueueLength());
        }, 1000);
        
        return () => {
            window.removeEventListener('online', handleOnline);
            window.removeEventListener('offline', handleOffline);
            clearInterval(intervalId);
        };
    }, []);
    
    return { isOnline, pendingActions };
}
```

## 5. 权限与用户体验优化

### 5.1 基于角色的访问控制（RBAC）

```go
// backend/security/rbac.go
package security

import (
    "context"
    "errors"
    "fmt"
    "time"
)

// 权限常量
const (
    // 设备权限
    PermDeviceView        = "device:view"
    PermDeviceControl     = "device:control"
    PermDeviceManage      = "device:manage"
    
    // 场景权限
    PermSceneView         = "scene:view"
    PermSceneExecute      = "scene:execute"
    PermSceneManage       = "scene:manage"
    
    // 自动化权限
    PermAutomationView    = "automation:view"
    PermAutomationManage  = "automation:manage"
    
    // 家庭权限
    PermHomeView          = "home:view"
    PermHomeManage        = "home:manage"
    PermHomeAdmin         = "home:admin"
    
    // 用户权限
    PermUserView          = "user:view"
    PermUserManage        = "user:manage"
)

// 预定义角色
const (
    RoleHomeOwner      = "home_owner"
    RoleHomeAdmin      = "home_admin"
    RoleHomeMember     = "home_member"
    RoleHomeGuest      = "home_guest"
    RoleTemporaryAccess = "temporary_access"
)

// 凭据
type Credential struct {
    UserID      string
    HomeID      string
    Roles       []string
    TokenID     string
    Expires     time.Time
    Permissions map[string]bool
}

// 权限服务
type PermissionService struct {
    roleRepository      RoleRepository
    permissionRepository PermissionRepository
    credentialCache     CredentialCache
}

// 创建权限服务
func NewPermissionService(
    roleRepo RoleRepository,
    permRepo PermissionRepository,
    cache CredentialCache,
) *PermissionService {
    return &PermissionService{
        roleRepository:      roleRepo,
        permissionRepository: permRepo,
        credentialCache:     cache,
    }
}

// 获取用户凭据
func (s *PermissionService) GetUserCredential(
    ctx context.Context,
    userID string,
    homeID string,
) (*Credential, error) {
    // 先查缓存
    cacheKey := fmt.Sprintf("cred:%s:%s", userID, homeID)
    if cached, found := s.credentialCache.Get(cacheKey); found {
        return cached.(*Credential), nil
    }
    
    // 获取用户角色
    roles, err := s.roleRepository.GetUserRoles(ctx, userID, homeID)
    if err != nil {
        return nil, fmt.Errorf("获取用户角色失败: %w", err)
    }
    
    // 构建权限映射
    permissions := make(map[string]bool)
    
    for _, role := range roles {
        // 获取角色权限
        rolePerms, err := s.permissionRepository.GetRolePermissions(ctx, role)
        if err != nil {
            return nil, fmt.Errorf("获取角色权限失败: %w", err)
        }
        
        // 合并权限
        for _, perm := range rolePerms {
            permissions[perm] = true
        }
    }
    
    // 创建凭据
    credential := &Credential{
        UserID:      userID,
        HomeID:      homeID,
        Roles:       roles,
        Permissions: permissions,
        Expires:     time.Now().Add(24 * time.Hour),
    }
    
    // 缓存凭据
    s.credentialCache.Set(cacheKey, credential, 1*time.Hour)
    
    return credential, nil
}

// 检查权限
func (s *PermissionService) CheckPermission(
    ctx context.Context,
    credential *Credential,
    requiredPermission string,
) bool {
    if credential == nil {
        return false
    }
    
    // 检查凭据是否过期
    if credential.Expires.Before(time.Now()) {
        return false
    }
    
    // 检查是否有超级管理员角色
    for _, role := range credential.Roles {
        if role == RoleHomeOwner {
            return true
        }
    }
    
    // 检查特定权限
    return credential.Permissions[requiredPermission]
}

// 验证访问
func (s *PermissionService) VerifyAccess(
    ctx context.Context,
    userID string,
    homeID string,
    resource string,
    action string,
) (bool, error) {
    // 获取用户凭据
    credential, err := s.GetUserCredential(ctx, userID, homeID)
    if err != nil {
        return false, err
    }
    
    // 构建权限字符串
    requiredPermission := fmt.Sprintf("%s:%s", resource, action)
    
    // 检查权限
    hasPermission := s.CheckPermission(ctx, credential, requiredPermission)
    
    return hasPermission, nil
}

// 为用户分配角色
func (s *PermissionService) AssignRoleToUser(
    ctx context.Context,
    userID string,
    homeID string,
    role string,
) error {
    // 检查操作者是否有权限管理角色
    operatorID, ok := GetUserIDFromContext(ctx)
    if !ok {
        return errors.New("未找到操作者ID")
    }
    
    if operatorID != userID {
        canManage, err := s.VerifyAccess(ctx, operatorID, homeID, "user", "manage")
        if err != nil {
            return err
        }
        
        if !canManage {
            return errors.New("没有管理用户角色的权限")
        }
    }
    
    // 检查是否是有效角色
    validRoles := []string{
        RoleHomeOwner,
        RoleHomeAdmin,
        RoleHomeMember,
        RoleHomeGuest,
        RoleTemporaryAccess,
    }
    
    isValidRole := false
    for _, validRole := range validRoles {
        if role == validRole {
            isValidRole = true
            break
        }
    }
    
    if !isValidRole {
        return fmt.Errorf("无效的角色: %s", role)
    }
    
    // 分配角色
    if err := s.roleRepository.AssignRole(ctx, userID, homeID, role); err != nil {
        return fmt.Errorf("分配角色失败: %w", err)
    }
    
    // 清除缓存
    cacheKey := fmt.Sprintf("cred:%s:%s", userID, homeID)
    s.credentialCache.Delete(cacheKey)
    
    return nil
}

// 移除用户角色
func (s *PermissionService) RemoveRoleFromUser(
    ctx context.Context,
    userID string,
    homeID string,
    role string,
) error {
    // 检查操作者是否有权限管理角色
    operatorID, ok := GetUserIDFromContext(ctx)
    if !ok {
        return errors.New("未找到操作者ID")
    }
    
    canManage, err := s.VerifyAccess(ctx, operatorID, homeID, "user", "manage")
    if err != nil {
        return err
    }
    
    if !canManage {
        return errors.New("没有管理用户角色的权限")
    }
    
    // 不允许移除自己的所有者角色
    if userID == operatorID && role == RoleHomeOwner {
        return errors.New("不能移除自己的家庭所有者角色")
    }
    
    // 移除角色
    if err := s.roleRepository.RemoveRole(ctx, userID, homeID, role); err != nil {
        return fmt.Errorf("移除角色失败: %w", err)
    }
    
    // 清除缓存
    cacheKey := fmt.Sprintf("cred:%s:%s", userID, homeID)
    s.credentialCache.Delete(cacheKey)
    
    return nil
}

// 创建自定义角色
func (s *PermissionService) CreateCustomRole(
    ctx context.Context,
    homeID string,
    roleName string,
    permissions []string,
) error {
    // 检查操作者是否有权限管理角色
    operatorID, ok := GetUserIDFromContext(ctx)
    if !ok {
        return errors.New("未找到操作者ID")
    }
    
    canManage, err := s.VerifyAccess(ctx, operatorID, homeID, "home", "admin")
    if err != nil {
        return err
    }
    
    if !canManage {
        return errors.New("没有管理家庭角色的权限")
    }
    
    // 验证权限是否有效
    for _, perm := range permissions {
        if !s.isValidPermission(perm) {
            return fmt.Errorf("无效的权限: %s", perm)
        }
    }
    
    // 创建角色
    customRoleName := fmt.Sprintf("custom:%s:%s", homeID, roleName)
    if err := s.roleRepository.CreateRole(ctx, customRoleName, permissions); err != nil {
        return fmt.Errorf("创建角色失败: %w", err)
    }
    
    return nil
}

// 检查权限是否有效
func (s *PermissionService) isValidPermission(permission string) bool {
    validPermissions := []string{
        PermDeviceView, PermDeviceControl, PermDeviceManage,
        PermSceneView, PermSceneExecute, PermSceneManage,
        PermAutomationView, PermAutomationManage,
        PermHomeView, PermHomeManage, PermHomeAdmin,
        PermUserView, PermUserManage,
    }
    
    for _, validPerm := range validPermissions {
        if permission == validPerm {
            return true
        }
    }
    
    return false
}
```

### 5.2 渐进式用户引导与提示

```typescript
// frontend/src/components/onboarding/OnboardingManager.tsx
import React, { useState, useEffect } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { RootState } from '../../store';
import { 
    completeOnboardingStep, 
    dismissOnboarding,
    resetOnboarding 
} from '../../store/slices/user.slice';
import { OnboardingStep } from './OnboardingStep';
import { OnboardingWelcome } from './OnboardingWelcome';
import { OnboardingProgress } from './OnboardingProgress';
import { useLocalStorage } from '../../hooks/useLocalStorage';

// 引导步骤定义
export interface OnboardingStepDef {
    id: string;
    title: string;
    description: string;
    target: string; // CSS选择器或组件ID
    position: 'top' | 'right' | 'bottom' | 'left';
    route?: string; // 如果步骤要求特定路由
    condition?: () => boolean; // 条件函数，决定是否显示该步骤
}

const onboardingSteps: OnboardingStepDef[] = [
    {
        id: 'welcome',
        title: '欢迎使用智能家居',
        description: '让我们快速了解如何使用这个应用',
        target: 'body',
        position: 'top',
    },
    {
        id: 'dashboard',
        title: '主控面板',
        description: '这里显示您的设备和场景的概览',
        target: '.dashboard-container',
        position: 'bottom',
        route: '/dashboard',
    },
    {
        id: 'add-device',
        title: '添加设备',
        description: '点击这里添加新的智能设备',
        target: '.add-device-button',
        position: 'bottom',
        route: '/dashboard',
    },
    {
        id: 'create-scene',
        title:
```typescript
    {
        id: 'create-scene',
        title: '创建场景',
        description: '场景可以同时控制多个设备，让您一键完成复杂操作',
        target: '.create-scene-button',
        position: 'left',
        route: '/scenes',
    },
    {
        id: 'device-control',
        title: '设备控制',
        description: '点击设备卡片可以控制设备',
        target: '.device-card:first-child',
        position: 'top',
        route: '/devices',
        condition: () => document.querySelectorAll('.device-card').length > 0,
    },
    {
        id: 'automation',
        title: '自动化',
        description: '设置自动化规则，让您的家更智能',
        target: '.automation-tab',
        position: 'right',
        route: '/automation',
    },
    {
        id: 'profile',
        title: '个人设置',
        description: '在这里可以管理您的账户和偏好设置',
        target: '.profile-button',
        position: 'left',
    },
    {
        id: 'complete',
        title: '完成！',
        description: '您已经了解了基本功能，现在开始享受智能家居的便利吧',
        target: 'body',
        position: 'top',
    }
];

// 引导管理器组件
export const OnboardingManager: React.FC = () => {
    const dispatch = useDispatch();
    const { currentStep, completed } = useSelector((state: RootState) => state.user.onboarding);
    const [isVisible, setIsVisible] = useState(false);
    const [activeStep, setActiveStep] = useState<OnboardingStepDef | null>(null);
    const [hasLocalStorage] = useLocalStorage('onboarding-completed', false);
    
    // 初始化引导
    useEffect(() => {
        // 如果已经在本地存储中标记为完成，则不显示
        if (hasLocalStorage || completed) {
            return;
        }
        
        const timer = setTimeout(() => {
            setIsVisible(true);
        }, 1000); // 延迟启动，让页面先加载完成
        
        return () => clearTimeout(timer);
    }, [hasLocalStorage, completed]);
    
    // 监听步骤变化
    useEffect(() => {
        if (!isVisible) return;
        
        const currentStepDef = onboardingSteps.find(step => step.id === currentStep);
        if (!currentStepDef) {
            setActiveStep(null);
            return;
        }
        
        // 检查条件
        if (currentStepDef.condition && !currentStepDef.condition()) {
            // 如果条件不满足，跳过此步骤
            handleNext();
            return;
        }
        
        // 如果步骤需要特定路由，导航到该路由
        if (currentStepDef.route && window.location.pathname !== currentStepDef.route) {
            // 使用history API或路由库导航
            window.history.pushState({}, '', currentStepDef.route);
        }
        
        // 等待DOM更新后再显示提示
        setTimeout(() => {
            const targetElement = document.querySelector(currentStepDef.target);
            if (!targetElement && currentStepDef.target !== 'body') {
                // 如果目标元素不存在且不是body，跳过此步骤
                handleNext();
                return;
            }
            
            setActiveStep(currentStepDef);
        }, 300);
    }, [currentStep, isVisible]);
    
    const handleNext = () => {
        const currentIndex = onboardingSteps.findIndex(step => step.id === currentStep);
        
        if (currentIndex >= onboardingSteps.length - 1) {
            // 已完成所有步骤
            handleComplete();
            return;
        }
        
        // 下一步
        const nextStep = onboardingSteps[currentIndex + 1];
        dispatch(completeOnboardingStep(nextStep.id));
    };
    
    const handlePrevious = () => {
        const currentIndex = onboardingSteps.findIndex(step => step.id === currentStep);
        
        if (currentIndex <= 0) {
            return;
        }
        
        // 前一步
        const prevStep = onboardingSteps[currentIndex - 1];
        dispatch(completeOnboardingStep(prevStep.id));
    };
    
    const handleComplete = () => {
        setIsVisible(false);
        dispatch(dismissOnboarding());
        localStorage.setItem('onboarding-completed', 'true');
    };
    
    const handleReset = () => {
        dispatch(resetOnboarding());
        setIsVisible(true);
    };
    
    // 如果没有激活的步骤或已完成，不渲染任何内容
    if (!isVisible || !activeStep) {
        return null;
    }
    
    // 如果是欢迎步骤，显示欢迎界面
    if (activeStep.id === 'welcome') {
        return (
            <OnboardingWelcome
                onStart={handleNext}
                onSkip={handleComplete}
            />
        );
    }
    
    // 如果是完成步骤，显示完成界面
    if (activeStep.id === 'complete') {
        return (
            <OnboardingStep
                step={activeStep}
                onNext={handleComplete}
                onPrevious={handlePrevious}
                isLastStep={true}
                totalSteps={onboardingSteps.length - 2} // 减去欢迎和完成步骤
                currentStepIndex={onboardingSteps.length - 2}
            />
        );
    }
    
    // 普通步骤
    const stepIndex = onboardingSteps.findIndex(step => step.id === activeStep.id) - 1; // 减去欢迎步骤
    const isLastStep = stepIndex === onboardingSteps.length - 3; // 减去欢迎和完成步骤
    
    return (
        <>
            <OnboardingStep
                step={activeStep}
                onNext={handleNext}
                onPrevious={handlePrevious}
                onSkip={handleComplete}
                isLastStep={isLastStep}
                totalSteps={onboardingSteps.length - 2} // 减去欢迎和完成步骤
                currentStepIndex={stepIndex}
            />
            <OnboardingProgress
                current={stepIndex}
                total={onboardingSteps.length - 2} // 减去欢迎和完成步骤
            />
        </>
    );
};

// frontend/src/components/onboarding/OnboardingStep.tsx
import React, { useEffect, useRef, useState } from 'react';
import styled from 'styled-components';
import { createPortal } from 'react-dom';
import { OnboardingStepDef } from './OnboardingManager';
import { Button } from '../design-system';

// 引导步骤组件属性
interface OnboardingStepProps {
    step: OnboardingStepDef;
    onNext: () => void;
    onPrevious: () => void;
    onSkip?: () => void;
    isLastStep: boolean;
    totalSteps: number;
    currentStepIndex: number;
}

// 计算提示框位置
interface Position {
    top: number;
    left: number;
    arrowPosition: 'top' | 'right' | 'bottom' | 'left';
}

const StyledTooltip = styled.div<{ position: Position }>`
    position: fixed;
    z-index: 1000;
    top: ${props => props.position.top}px;
    left: ${props => props.position.left}px;
    width: 300px;
    background-color: ${props => props.theme.colors.background};
    border-radius: 8px;
    box-shadow: ${props => props.theme.shadows.large};
    padding: 20px;
    transform: translate(-50%, -50%);
    
    &::before {
        content: '';
        position: absolute;
        width: 0;
        height: 0;
        border: 10px solid transparent;
        
        ${props => props.position.arrowPosition === 'top' && `
            border-bottom-color: ${props.theme.colors.background};
            top: -20px;
            left: 50%;
            transform: translateX(-50%);
        `}
        
        ${props => props.position.arrowPosition === 'right' && `
            border-left-color: ${props.theme.colors.background};
            right: -20px;
            top: 50%;
            transform: translateY(-50%);
        `}
        
        ${props => props.position.arrowPosition === 'bottom' && `
            border-top-color: ${props.theme.colors.background};
            bottom: -20px;
            left: 50%;
            transform: translateX(-50%);
        `}
        
        ${props => props.position.arrowPosition === 'left' && `
            border-right-color: ${props.theme.colors.background};
            left: -20px;
            top: 50%;
            transform: translateY(-50%);
        `}
    }
    
    .tooltip-title {
        font-size: 18px;
        font-weight: 600;
        margin-bottom: 8px;
        color: ${props => props.theme.colors.textDark};
    }
    
    .tooltip-description {
        margin-bottom: 16px;
        color: ${props => props.theme.colors.text};
    }
    
    .tooltip-progress {
        margin-bottom: 12px;
        font-size: 14px;
        color: ${props => props.theme.colors.textLight};
    }
    
    .tooltip-buttons {
        display: flex;
        justify-content: space-between;
    }
`;

const Overlay = styled.div`
    position: fixed;
    top: 0;
    left: 0;
    right: 0;
    bottom: 0;
    background-color: rgba(0, 0, 0, 0.5);
    z-index: 999;
`;

const TargetHighlight = styled.div`
    position: absolute;
    z-index: 1000;
    box-shadow: 0 0 0 9999px rgba(0, 0, 0, 0.5);
    border-radius: 4px;
    pointer-events: none;
`;

export const OnboardingStep: React.FC<OnboardingStepProps> = ({
    step,
    onNext,
    onPrevious,
    onSkip,
    isLastStep,
    totalSteps,
    currentStepIndex
}) => {
    const [position, setPosition] = useState<Position>({
        top: 0,
        left: 0,
        arrowPosition: 'top'
    });
    const [highlight, setHighlight] = useState({
        top: 0,
        left: 0,
        width: 0,
        height: 0,
        visible: false
    });
    const tooltipRef = useRef<HTMLDivElement>(null);
    
    // 计算位置
    useEffect(() => {
        const calculatePosition = () => {
            if (step.target === 'body') {
                // 居中显示
                setPosition({
                    top: window.innerHeight / 2,
                    left: window.innerWidth / 2,
                    arrowPosition: 'top'
                });
                setHighlight({ top: 0, left: 0, width: 0, height: 0, visible: false });
                return;
            }
            
            const targetElement = document.querySelector(step.target);
            if (!targetElement) return;
            
            const targetRect = targetElement.getBoundingClientRect();
            let tooltipTop = 0;
            let tooltipLeft = 0;
            
            // 设置高亮
            setHighlight({
                top: targetRect.top,
                left: targetRect.left,
                width: targetRect.width,
                height: targetRect.height,
                visible: true
            });
            
            // 根据位置计算提示框位置
            switch (step.position) {
                case 'top':
                    tooltipTop = targetRect.top - 20;
                    tooltipLeft = targetRect.left + targetRect.width / 2;
                    break;
                case 'right':
                    tooltipTop = targetRect.top + targetRect.height / 2;
                    tooltipLeft = targetRect.right + 20;
                    break;
                case 'bottom':
                    tooltipTop = targetRect.bottom + 20;
                    tooltipLeft = targetRect.left + targetRect.width / 2;
                    break;
                case 'left':
                    tooltipTop = targetRect.top + targetRect.height / 2;
                    tooltipLeft = targetRect.left - 20;
                    break;
            }
            
            // 确保提示框在视口内
            if (tooltipRef.current) {
                const tooltipRect = tooltipRef.current.getBoundingClientRect();
                
                if (tooltipTop - tooltipRect.height / 2 < 0) {
                    tooltipTop = tooltipRect.height / 2 + 20;
                } else if (tooltipTop + tooltipRect.height / 2 > window.innerHeight) {
                    tooltipTop = window.innerHeight - tooltipRect.height / 2 - 20;
                }
                
                if (tooltipLeft - tooltipRect.width / 2 < 0) {
                    tooltipLeft = tooltipRect.width / 2 + 20;
                } else if (tooltipLeft + tooltipRect.width / 2 > window.innerWidth) {
                    tooltipLeft = window.innerWidth - tooltipRect.width / 2 - 20;
                }
            }
            
            setPosition({
                top: tooltipTop,
                left: tooltipLeft,
                arrowPosition: step.position
            });
        };
        
        calculatePosition();
        
        // 监听窗口大小变化
        window.addEventListener('resize', calculatePosition);
        
        return () => {
            window.removeEventListener('resize', calculatePosition);
        };
    }, [step]);
    
    // 创建Portal以确保提示框在DOM顶层
    return createPortal(
        <>
            <Overlay onClick={onSkip} />
            
            {highlight.visible && (
                <TargetHighlight
                    style={{
                        top: `${highlight.top}px`,
                        left: `${highlight.left}px`,
                        width: `${highlight.width}px`,
                        height: `${highlight.height}px`,
                    }}
                />
            )}
            
            <StyledTooltip ref={tooltipRef} position={position}>
                <h3 className="tooltip-title">{step.title}</h3>
                <p className="tooltip-description">{step.description}</p>
                <div className="tooltip-progress">
                    步骤 {currentStepIndex + 1} / {totalSteps}
                </div>
                <div className="tooltip-buttons">
                    <div>
                        {currentStepIndex > 0 && (
                            <Button
                                variant="ghost"
                                size="small"
                                onClick={onPrevious}
                            >
                                上一步
                            </Button>
                        )}
                    </div>
                    <div>
                        {onSkip && (
                            <Button
                                variant="ghost"
                                size="small"
                                onClick={onSkip}
                            >
                                跳过
                            </Button>
                        )}
                        <Button
                            variant="primary"
                            size="small"
                            onClick={onNext}
                        >
                            {isLastStep ? '完成' : '下一步'}
                        </Button>
                    </div>
                </div>
            </StyledTooltip>
        </>,
        document.body
    );
};
```

### 5.3 个性化推荐系统

```go
// backend/recommendation/recommendation_service.go
package recommendation

import (
    "context"
    "fmt"
    "sort"
    "time"
)

// 推荐类型
const (
    RecommendationTypeScene       = "scene"
    RecommendationTypeDevice      = "device"
    RecommendationTypeAutomation  = "automation"
    RecommendationTypeOptimization = "optimization"
)

// 推荐项
type Recommendation struct {
    ID             string                 `json:"id"`
    Type           string                 `json:"type"`
    Title          string                 `json:"title"`
    Description    string                 `json:"description"`
    Score          float64                `json:"score"`
    CreatedAt      time.Time              `json:"createdAt"`
    ExpiresAt      time.Time              `json:"expiresAt"`
    Metadata       map[string]interface{} `json:"metadata"`
    Acknowledged   bool                   `json:"acknowledged"`
    Implemented    bool                   `json:"implemented"`
    Dismissed      bool                   `json:"dismissed"`
}

// 推荐服务
type RecommendationService struct {
    repo                  RecommendationRepository
    deviceService         DeviceService
    sceneService          SceneService
    automationService     AutomationService
    usageAnalyzer         UsageAnalyzer
    patternDetector       PatternDetector
    userPreferenceService UserPreferenceService
}

// 创建推荐服务
func NewRecommendationService(
    repo RecommendationRepository,
    deviceService DeviceService,
    sceneService SceneService,
    automationService AutomationService,
    usageAnalyzer UsageAnalyzer,
    patternDetector PatternDetector,
    userPreferenceService UserPreferenceService,
) *RecommendationService {
    return &RecommendationService{
        repo:                  repo,
        deviceService:         deviceService,
        sceneService:          sceneService,
        automationService:     automationService,
        usageAnalyzer:         usageAnalyzer,
        patternDetector:       patternDetector,
        userPreferenceService: userPreferenceService,
    }
}

// 获取用户推荐
func (s *RecommendationService) GetRecommendationsForUser(
    ctx context.Context,
    userID string,
    homeID string,
    limit int,
) ([]Recommendation, error) {
    // 获取现有推荐
    existingRecs, err := s.repo.GetActiveRecommendations(ctx, userID, homeID)
    if err != nil {
        return nil, fmt.Errorf("获取现有推荐失败: %w", err)
    }
    
    // 检查是否需要生成新推荐
    needsNewRecs := len(existingRecs) < limit
    
    // 如果用户没有足够的推荐，生成新的
    if needsNewRecs {
        if err := s.generateRecommendations(ctx, userID, homeID); err != nil {
            return nil, fmt.Errorf("生成推荐失败: %w", err)
        }
        
        // 重新获取推荐列表
        existingRecs, err = s.repo.GetActiveRecommendations(ctx, userID, homeID)
        if err != nil {
            return nil, fmt.Errorf("获取推荐失败: %w", err)
        }
    }
    
    // 应用用户偏好过滤
    filteredRecs := s.applyUserPreferences(ctx, userID, existingRecs)
    
    // 按分数排序
    sort.Slice(filteredRecs, func(i, j int) bool {
        return filteredRecs[i].Score > filteredRecs[j].Score
    })
    
    // 限制数量
    if len(filteredRecs) > limit {
        filteredRecs = filteredRecs[:limit]
    }
    
    return filteredRecs, nil
}

// 根据用户偏好过滤推荐
func (s *RecommendationService) applyUserPreferences(
    ctx context.Context,
    userID string,
    recommendations []Recommendation,
) []Recommendation {
    prefs, err := s.userPreferenceService.GetUserPreferences(ctx, userID)
    if err != nil {
        // 如果获取偏好失败，返回原始推荐列表
        return recommendations
    }
    
    // 过滤已禁用的推荐类型
    filteredRecs := make([]Recommendation, 0, len(recommendations))
    
    for _, rec := range recommendations {
        // 检查该类型的推荐是否已禁用
        if disabled, exists := prefs.DisabledRecommendationTypes[rec.Type]; exists && disabled {
            continue
        }
        
        // 根据用户偏好调整分数
        if weights, exists := prefs.RecommendationTypeWeights; exists {
            if weight, hasWeight := weights[rec.Type]; hasWeight {
                rec.Score *= weight
            }
        }
        
        filteredRecs = append(filteredRecs, rec)
    }
    
    return filteredRecs
}

// 生成推荐
func (s *RecommendationService) generateRecommendations(
    ctx context.Context,
    userID string,
    homeID string,
) error {
    // 并行生成不同类型的推荐
    errCh := make(chan error, 4)
    
    go func() {
        if err := s.generateSceneRecommendations(ctx, userID, homeID); err != nil {
            errCh <- fmt.Errorf("生成场景推荐失败: %w", err)
        } else {
            errCh <- nil
        }
    }()
    
    go func() {
        if err := s.generateDeviceRecommendations(ctx, userID, homeID); err != nil {
            errCh <- fmt.Errorf("生成设备推荐失败: %w", err)
        } else {
            errCh <- nil
        }
    }()
    
    go func() {
        if err := s.generateAutomationRecommendations(ctx, userID, homeID); err != nil {
            errCh <- fmt.Errorf("生成自动化推荐失败: %w", err)
        } else {
            errCh <- nil
        }
    }()
    
    go func() {
        if err := s.generateOptimizationRecommendations(ctx, userID, homeID); err != nil {
            errCh <- fmt.Errorf("生成优化推荐失败: %w", err)
        } else {
            errCh <- nil
        }
    }()
    
    // 收集错误
    var errors []error
    for i := 0; i < 4; i++ {
        if err := <-errCh; err != nil {
            errors = append(errors, err)
        }
    }
    
    // 如果有错误，返回第一个错误
    if len(errors) > 0 {
        return errors[0]
    }
    
    return nil
}

// 生成场景推荐
func (s *RecommendationService) generateSceneRecommendations(
    ctx context.Context,
    userID string,
    homeID string,
) error {
    // 分析用户设备使用模式
    patterns, err := s.patternDetector.DetectDeviceUsagePatterns(ctx, userID, homeID)
    if err != nil {
        return fmt.Errorf("检测设备使用模式失败: %w", err)
    }
    
    // 获取现有场景
    existingScenes, err := s.sceneService.GetAllScenes(ctx, homeID)
    if err != nil {
        return fmt.Errorf("获取现有场景失败: %w", err)
    }
    
    // 将现有场景转换为模式特征向量，用于相似度比较
    existingPatterns := make(map[string][]float64)
    for _, scene := range existingScenes {
        existingPatterns[scene.ID] = s.patternDetector.ExtractSceneFeatures(scene)
    }
    
    // 对每个检测到的模式创建场景推荐
    recommendations := make([]Recommendation, 0)
    
    for _, pattern := range patterns {
        // 检查模式是否与现有场景相似
        isSimilarToExisting := false
        
        for _, featureVector := range existingPatterns {
            similarity := s.patternDetector.CalculatePatternSimilarity(pattern.Features, featureVector)
            if similarity > 0.7 {  // 相似度阈值
                isSimilarToExisting = true
                break
            }
        }
        
        // 如果与现有场景相似，跳过
        if isSimilarToExisting {
            continue
        }
        
        // 创建场景推荐
        devicesStr := ""
        for i, device := range pattern.Devices {
            if i > 0 {
                devicesStr += ", "
            }
            devicesStr += device.Name
        }
        
        recommendation := Recommendation{
            ID:          generateUUID(),
            Type:        RecommendationTypeScene,
            Title:       fmt.Sprintf("创建"%s"场景", pattern.Name),
            Description: fmt.Sprintf("基于您的使用习惯，我们发现您经常同时操作这些设备: %s", devicesStr),
            Score:       pattern.Confidence,
            CreatedAt:   time.Now(),
            ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),  // 30天后过期
            Metadata: map[string]interface{}{
                "pattern":  pattern,
                "devices":  pattern.Devices,
                "actions":  pattern.Actions,
                "timeInfo": pattern.TimeInfo,
            },
        }
        
        recommendations = append(recommendations, recommendation)
    }
    
    // 保存推荐
    if len(recommendations) > 0 {
        if err := s.repo.SaveRecommendations(ctx, userID, homeID, recommendations); err != nil {
            return fmt.Errorf("保存场景推荐失败: %w", err)
        }
    }
    
    return nil
}

// 生成设备推荐
func (s *RecommendationService) generateDeviceRecommendations(
    ctx context.Context,
    userID string,
    homeID string,
) error {
    // 获取现有设备
    existingDevices, err := s.deviceService.GetUserDevices(ctx, userID, homeID)
    if err != nil {
        return fmt.Errorf("获取现有设备失败: %w", err)
    }
    
    // 分析设备使用和房间覆盖情况
    coverage, err := s.usageAnalyzer.AnalyzeHomeCoverage(ctx, homeID)
    if err != nil {
        return fmt.Errorf("分析家庭覆盖率失败: %w", err)
    }
    
    // 基于现有设备和使用模式推荐新设备
    recommendations := make([]Recommendation, 0)
    
    // 检查是否缺少某些类型的设备
    deviceTypeMap := make(map[string]bool)
    for _, device := range existingDevices {
        deviceTypeMap[device.Type] = true
    }
    
    // 基本设备类型检查
    essentialDeviceTypes := map[string]string{
        "motion_sensor": "动作传感器可以自动检测您的存在，并触发相应的自动化",
        "light":         "智能灯泡可以提供更好的照明控制和氛围",
        "thermostat":    "智能恒温器可以优化温度控制，提高舒适度并节省能源",
        "lock":          "智能锁可以提高安全性并提供便捷的访问控制",
    }
    
    for deviceType, description := range essentialDeviceTypes {
        if !deviceTypeMap[deviceType] {
            recommendation := Recommendation{
                ID:          generateUUID(),
                Type:        RecommendationTypeDevice,
                Title:       fmt.Sprintf("添加%s", getDeviceTypeName(deviceType)),
                Description: description,
                Score:       0.8,
                CreatedAt:   time.Now(),
                ExpiresAt:   time.Now().Add(90 * 24 * time.Hour),  // 90天后过期
                Metadata: map[string]interface{}{
                    "deviceType": deviceType,
                },
            }
            
            recommendations = append(recommendations, recommendation)
        }
    }
    
    // 检查房间覆盖情况
    for roomID, roomCoverage := range coverage.RoomCoverage {
        room, err := s.deviceService.GetRoom(ctx, homeID, roomID)
        if err != nil {
            continue
        }
        
        // 对覆盖率低的房间推荐设备
        if roomCoverage.CoverageScore < 0.5 {
            // 根据房间类型推荐不同设备
            recommendedDevices := getRecommendedDevicesForRoom(room.Type, roomCoverage.MissingDeviceTypes)
            
            for _, deviceType := range recommendedDevices {
                recommendation := Recommendation{
                    ID:          generateUUID(),
                    Type:        RecommendationTypeDevice,
                    Title:       fmt.Sprintf("为%s添加%s", room.Name, getDeviceTypeName(deviceType)),
                    Description: fmt.Sprintf("您的%s缺少智能%s，添加它可以增强您的智能家居体验", room.Name, getDeviceTypeName(deviceType)),
                    Score:       0.7 * (1 - roomCoverage.CoverageScore),
                    CreatedAt:   time.Now(),
                    ExpiresAt:   time.Now().Add(60 * 24 * time.Hour),  // 60天后过期
                    Metadata: map[string]interface{}{
                        "deviceType": deviceType,
                        "roomId":     roomID,
                        "roomName":   room.Name,
                    },
                }
                
                recommendations = append(recommendations, recommendation)
            }
        }
    }
    
    // 保存推荐
    if len(recommendations) > 0 {
        if err := s.repo.SaveRecommendations(ctx, userID, homeID, recommendations); err != nil {
            return fmt.Errorf("保存设备推荐失败: %w", err)
        }
    }
    
    return nil
}

// 生成自动化推荐
func (s *RecommendationService) generateAutomationRecommendations(
    ctx context.Context,
    userID string,
    homeID string,
) error {
    // 获取现有自动化
    existingAutomations, err := s.automationService.GetAllAutomations(ctx, homeID)
    if err != nil {
        return fmt.Errorf("获取现有自动化失败: %w", err)
    }
    
    // 获取设备列表
    devices, err := s.deviceService.GetUserDevices(ctx, userID, homeID)
    if err != nil {
        return fmt.Errorf("获取设备列表失败: %w", err)
    }
    
    // 分析行为模式
    behaviors, err := s.patternDetector.DetectUserBehaviors(ctx, userID, homeID)
    if err != nil {
        return fmt.Errorf("检测用户行为失败: %w", err)
    }
    
    // 基于设备种类和行为模式生成自动化推荐
    recommendations := make([]Recommendation, 0)
    
    // 创建设备类型映射
    devicesByType := make(map[string][]Device)
    for _, device := range devices {
        devicesByType[device.Type] = append(devicesByType[device.Type], device)
    }
    
    // 检查是否可以创建基本自动化
    if len(devicesByType["motion_sensor"]) > 0 && len(devicesByType["light"]) > 0 {
        hasMotionLightAutomation := false
        
        // 检查是否已存在类似自动化
        for _, automation := range existingAutomations {
            if automation.Type == "motion_light" {
                hasMotionLightAutomation = true
                break
            }
        }
        
        if !hasMotionLightAutomation {
            // 为每个没有关联自动化的动作传感器推荐
            for _, sensor := range devicesByType["motion_sensor"] {
                nearby := findNearbyDevices(sensor, devicesByType["light"], 5.0) // 5米内的灯
                
                if len(nearby) > 0 {
                    deviceNames := ""
                    for i, device := range nearby {
                        if i > 0 {
                            deviceNames += ", "
                        }
                        deviceNames += device.Name
                    }
                    
                    recommendation := Recommendation{
                        ID:          generateUUID(),
                        Type:        RecommendationTypeAutomation,
                        Title:       "创建动作感应照明自动化",
                        Description: fmt.Sprintf("当%s检测到动作时，自动打开%s", sensor.Name, deviceNames),
                        Score:       0.9,
                        CreatedAt:   time.Now(),
                        ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
                        Metadata: map[string]interface{}{
                            "automationType": "motion_light",
                            "triggerDevice":  sensor,
                            "actionDevices":  nearby,
                        },
                    }
                    
                    recommendations = append(recommendations, recommendation)
                }
            }
        }
    }
    
    // 基于用户作息时间创建自动化推荐
    if len(behaviors.SleepPatterns) > 0 && len(devicesByType["light"]) > 0 {
        hasSleepAutomation := false
        
        // 检查是否已存在类似自动化
        for _, automation := range existingAutomations {
            if automation.Type == "sleep_routine" {
                hasSleepAutomation = true
                break
            }
        }
        
        if !hasSleepAutomation {
            // 计算平均睡眠时间
            var totalBedtime, totalWakeup time.Duration
            for _, pattern := range behaviors.SleepPatterns {
                totalBedtime += pattern.BedTime.Sub(time.Date(0, 1, 1, 0, 0, 0, 0, time.UTC))
                totalWakeup += pattern.WakeupTime.Sub(time.Date(0, 1, 1, 0, 0, 0, 0, time.UTC))
            }
            
            avgBedtime := time.Date(0, 1, 1, 0, 0, 0, 0, time.UTC).Add(totalBedtime / time.Duration(len(behaviors.SleepPatterns)))
            avgWakeup := time.Date(0, 1, 1, 0, 0, 0, 0, time.UTC).Add(totalWakeup / time.Duration(len(behaviors.SleepPatterns)))
            
            recommendation := Recommendation{
                ID:          generateUUID(),
                Type:        RecommendationTypeAutomation,
                Title:       "创建睡眠例程自动化",
                Description: fmt.Sprintf("每天晚上%s关闭灯光，早上%s自动开灯", avgBedtime.Format("15:04"), avgWakeup.Format("15:04")),
                Score:       0.85,
                CreatedAt:   time.Now(),
                ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
                Metadata: map[string]interface{}{
                    "automationType": "sleep_routine",
                    "bedTime":        avgBedtime.Format("15:04"),
                    "wakeupTime":     avgWakeup.Format("15:04"),
                    "actionDevices":  devicesByType["light"],
                },
            }
            
            recommendations = append(recommendations, recommendation)
        }
    }
    
    // 基于离家/回家模式创建自动化推荐
    if behaviors.HasAwayPattern && (len(devicesByType["light"]) > 0 || len(devicesByType["thermostat"]) > 0) {
        hasAwayAutomation := false
        
        // 检查是否已存在类似自动化
        for _, automation := range existingAutomations {
            if automation.Type == "away_mode" {
                hasAwayAutomation = true
                break
            }
        }
        
        if !hasAwayAutomation {
            description := "当所有人离开家时，自动"
            actionItems := []string{}
            
            if len(devicesByType["light"]) > 0 {
                actionItems = append(actionItems, "关闭所有灯")
            }
            
            if len(devicesByType["thermostat"]) > 0 {
                actionItems = append(actionItems, "调整温度到节能模式")
            }
            
            for i, item := range actionItems {
                if i > 0 {
                    if i == len(actionItems)-1 {
                        description += "并"
                    } else {
                        description += "、"
                    }
                }
                description += item
            }
            
            recommendation := Recommendation{
                ID:          generateUUID(),
                Type:        RecommendationTypeAutomation,
                Title:       "创建离家模式自动化",
                Description: description,
                Score:       0.8,
                CreatedAt:   time.Now(),
                ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
                Metadata: map[string]interface{}{
                    "automationType": "away_mode",
                    "lightDevices":   devicesByType["light"],
                    "thermostats":    devicesByType["thermostat"],
                },
            }
            
            recommendations = append(recommendations, recommendation)
        }
    }
    
    // 保存推荐
    if len(recommendations) > 0 {
        if err := s.repo.SaveRecommendations(ctx, userID, homeID, recommendations); err != nil {
            return fmt.Errorf("保存自动化推荐失败: %w", err)
        }
    }
    
    return nil
}

// 生成优化推荐
func (s *RecommendationService) generateOptimizationRecommendations(
    ctx context.Context,
    userID string,
    homeID string,
) error {
    // 分析能源使用情况
    energyAnalysis, err := s.usageAnalyzer.AnalyzeEnergyUsage(ctx, homeID)
    if err != nil {
        return fmt.Errorf("分析能源使用失败: %w", err)
    }
    
    // 分析设备使用情况
    deviceUsage, err := s.usageAnalyzer.AnalyzeDeviceUsage(ctx, homeID)
    if err != nil {
        return fmt.Errorf("分析设备使用失败: %w", err)
    }
    
    // 基于分析生成优化推荐
    recommendations := make([]Recommendation, 0)
    
    // 能源浪费优化
    for _, waste := range energyAnalysis.WastePoints {
        recommendation := Recommendation{
            ID:          generateUUID(),
            Type:        RecommendationTypeOptimization,
            Title:       fmt.Sprintf("优化%s的能源使用", waste.DeviceName),
            Description: waste.Description,
            Score:       waste.WasteScore,
            CreatedAt:   time.Now(),
            ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
            Metadata: map[string]interface{}{
                "optimizationType": "energy",
                "deviceId":         waste.DeviceID,
                "deviceName":       waste.DeviceName,
                "wasteDetails":     waste,
            },
        }
        
        recommendations = append(recommendations, recommendation)
    }
    
    // 低使用率设备优化
    for _, usage := range deviceUsage.LowUsageDevices {
        if usage.UsageRate < 0.1 { // 使用率低于10%
            recommendation := Recommendation{
                ID:          generateUUID(),
                Type:        RecommendationTypeOptimization,
                Title:       fmt.Sprintf("优化%s的使用", usage.DeviceName),
                Description: fmt.Sprintf("您的%s使用率很低(%.1f%%)，考虑将其移动到更有用的位置或创建自动化来增加其使用价值", usage.DeviceName, usage.UsageRate*100),
                Score:       0.7,
                CreatedAt:   time.Now(),
                ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
                Metadata: map[string]interface{}{
                    "optimizationType": "usage",
                    "deviceId":         usage.DeviceID,
                    "deviceName":       usage.DeviceName,
                    "usageDetails":     usage,
                },
            }
            
            recommendations = append(recommendations, recommendation)
        }
    }
    
    // 闲置场景优化
    scenes, err := s.sceneService.GetAllScenes(ctx, homeID)
    if err == nil {
        for _, scene := range scenes {
            usageData, err := s.usageAnalyzer.GetSceneUsageStatistics(ctx, scene.ID)
            if err != nil {
                continue
            }
            
            // 如果场景创建超过30天且使用次数少于3次
            if time.Since(scene.CreatedAt) > 30*24*time.Hour && usageData.ExecutionCount < 3 {
                recommendation := Recommendation{
                    ID:          generateUUID(),
                    Type:        RecommendationTypeOptimization,
                    Title:       fmt.Sprintf("移除或优化闲置场景: %s", scene.Name),
                    Description: fmt.Sprintf("您的场景"%s"创建于%s，但仅使用了%d次。考虑更新它或移除以保持整洁的界面。", scene.Name, scene.CreatedAt.Format("2006-01-02"), usageData.ExecutionCount),
                    Score:       0.6,
                    CreatedAt:   time.Now(),
                    ExpiresAt:   time.Now().Add(30 * 24 * time.Hour),
                    Metadata: map[string]interface{}{
                        "optimizationType": "scene",
                        "sceneId":          scene.ID,
                        "sceneName":        scene.Name,
                        "usageDetails":     usageData,
                    },
                }
                
                recommendations = append(recommendations, recommendation)
            }
        }
    }
    
    // 保存推荐
    if len(recommendations) > 0 {
        if err := s.repo.SaveRecommendations(ctx, userID, homeID, recommendations); err != nil {
            return fmt.Errorf("保存优化推荐失败: %w", err)
        }
    }
    
    return nil
}

// 标记推荐为已处理
func (s *RecommendationService) MarkRecommendationAsImplemented(
    ctx context.Context,
    userID string,
    recommendationID string,
) error {
    return s.repo.UpdateRecommendationStatus(ctx, userID, recommendationID, true, false)
}

// 标记推荐为已拒绝
func (s *RecommendationService) DismissRecommendation(
    ctx context.Context,
    userID string,
    recommendationID string,
) error {
    return s.repo.UpdateRecommendationStatus(ctx, userID, recommendationID, false, true)
}

// 标记推荐为已看到
func (s *RecommendationService) AcknowledgeRecommendation(
    ctx context.Context,
    userID string,
    recommendationID string,
) error {
    return s.repo.UpdateRecommendationStatus(ctx, userID, recommendationID, false, false)
}

// Helper functions

// 获取设备类型名称
func getDeviceTypeName(deviceType string) string {
    typeNames := map[string]string{
        "light":         "智能灯",
        "switch":        "智能开关",
        "outlet":        "智能插座",
        "motion_sensor": "动作传感器",
        "contact_sensor": "门窗传感器",
        "thermostat":    "恒温器",
        "lock":          "智能锁",
        "camera":        "摄像头",
        "speaker":       "智能音箱",
        "vacuum":        "扫地机器人",
    }
    
    if name, exists := typeNames[deviceType]; exists {
        return name
    }
    
    return deviceType
}

// 根据房间类型获取推荐设备
func getRecommendedDevicesForRoom(roomType string, missingTypes []string) []string {
    // 创建缺失设备类型映射，便于查找
    missingMap := make(map[string]bool)
    for _, t := range missingTypes {
        missingMap[t] = true
    }
    
    // 根据房间类型的推荐设备
    recommendedForType := map[string][]string{
        "living_room": {"light", "motion_sensor", "tv_controller", "speaker"},
        "bedroom":     {"light", "motion_sensor", "thermostat"},
        "kitchen":     {"light", "motion_sensor", "contact_sensor", "smoke_detector"},
        "bathroom":    {"light", "motion_sensor", "humidity_sensor"},
        "entrance":    {"light", "motion_sensor", "contact_sensor", "camera", "lock"},
        "office":      {"light", "motion_sensor", "outlet"},
    }
    
    // 如果房间类型没有特定推荐，使用通用推荐
    recommended, exists := recommendedForType[roomType]
    if !exists {
        recommended = []string{"light", "motion_sensor"}
    }
    
    // 过滤只包含缺失的设备类型
    result := make([]string, 0)
    for _, t := range recommended {
        if missingMap[t] {
            result = append(result, t)
        }
    }
    
    return result
}

// 查找附近设备
func findNearbyDevices(sourceDevice Device, candidates []Device, maxDistance float64) []Device {
    result := make([]Device, 0)
    
    for _, candidate := range candidates {
        // 只有在同一房间或有位置信息的设备才能计算距离
        if sourceDevice.RoomID == candidate.RoomID || 
          (sourceDevice.Location != nil && candidate.Location != nil) {
            
            var distance float64
            
            if sourceDevice.Location != nil && candidate.Location != nil {
                // 计算两点之间的欧几里得距离
                dx := sourceDevice.Location.X - candidate.Location.X
                dy := sourceDevice.Location.Y - candidate.Location.Y
                dz := sourceDevice.Location.Z - candidate.Location.Z
                distance = math.Sqrt(dx*dx + dy*dy + dz*dz)
            } else {
                // 如果在同一房间但没有位置信息，假设距离为1
                distance = 1.0
            }
            
            if distance <= maxDistance {
                result = append(result, candidate)
            }
        }
    }
    
    return result
}

// frontend/src/components/recommendations/RecommendationCard.tsx
import React from 'react';
import styled from 'styled-components';
import { Card, Button, Icon } from '../design-system';
import { useDispatch } from 'react-redux';
import { 
    implementRecommendation, 
    dismissRecommendation 
} from '../../store/slices/recommendation.slice';
import { Recommendation } from '../../models/recommendation.model';

interface RecommendationCardProps {
    recommendation: Recommendation;
    onSelect: (recommendation: Recommendation) => void;
}

const StyledCard = styled(Card)`
    padding: 20px;
    margin-bottom: 16px;
    transition: transform 0.2s ease, box-shadow 0.2s ease;
    
    &:hover {
        transform: translateY(-2px);
        box-shadow: ${props => props.theme.shadows.medium};
    }
    
    .recommendation-header {
        display: flex;
        align-items: center;
        margin-bottom: 12px;
        
        .recommendation-icon {
            margin-right: 12px;
            color: ${props => props.theme.colors.primary};
        }
        
        .recommendation-title {
            font-size: 18px;
            font-weight: 600;
            margin: 0;
            flex: 1;
        }
        
        .recommendation-score {
            background-color: ${props => props.theme.colors.primaryLight};
            color: ${props => props.theme.colors.primary};
            padding: 4px 8px;
            border-radius: 12px;
            font-size: 14px;
            font-weight: 500;
        }
    }
    
    .recommendation-description {
        margin-bottom: 16px;
        color: ${props => props.theme.colors.text};
    }
    
    .recommendation-actions {
        display: flex;
        justify-content: space-between;
    }
    
    .recommendation-create-date {
        font-size: 12px;
        color: ${props => props.theme.colors.textLight};
        margin-top: 12px;
    }
`;

export const RecommendationCard: React.FC<RecommendationCardProps> = ({
    recommendation,
    onSelect,
}) => {
    const dispatch = useDispatch();
    
    const handleImplement = (e: React.MouseEvent) => {
        e.stopPropagation();
        dispatch(implementRecommendation(recommendation.id));
        onSelect(recommendation);
    };
    
    const handleDismiss = (e: React.MouseEvent) => {
        e.stopPropagation();
        dispatch(dismissRecommendation(recommendation.id));
    };
    
    // 根据推荐类型选择图标
    const getIcon = () => {
        switch (recommendation.type) {
            case 'scene':
                return <Icon name="zap" size={24} />;
            case 'device':
                return <Icon name="smartphone" size={24} />;
            case 'automation':
                return <Icon name="activity" size={24} />;
            case 'optimization':
                return <Icon name="trending-up" size={24} />;
            default:
                return <Icon name="star" size={24} />;
        }
    };
    
    return (
        <StyledCard onClick={() => onSelect(recommendation)}>
            <div className="recommendation-header">
                <div className="recommendation-icon">
                    {getIcon()}
                </div>
                <h3 className="recommendation-title">{recommendation.title}</h3>
                <div className="recommendation-score">
                    {Math.round(recommendation.score * 100)}% 匹配
                </div>
            </div>
            
            <p className="recommendation-description">{recommendation.description}</p>
            
            <div className="recommendation-actions">
                <Button
                    variant="primary"
                    size="small"
                    onClick={handleImplement}
                >
                    应用
                </Button>
                
                <Button
                    variant="ghost"
                    size="small"
                    onClick={handleDismiss}
                >
                    忽略
                </Button>
            </div>
            
            <div className="recommendation-create-date">
                推荐于 {new Date(recommendation.createdAt).toLocaleDateString()}
            </div>
        </StyledCard>
    );
};
```

### 5.4 学习与适应能力

```typescript
// frontend/src/services/learning.service.ts
import { inject, injectable } from 'inversify';
import { BehaviorSubject, Observable } from 'rxjs';
import { debounceTime, distinctUntilChanged } from 'rxjs/operators';
import { LocalStorageService } from './local-storage.service';
import { AnalyticsService } from './analytics.service';

// 用户交互记录
export interface UserInteraction {
    type: string;        // 交互类型
    target: string;      // 目标对象
    timestamp: number;   // 时间戳
    context?: any;       // 上下文信息
}

// 学习模型
export interface LearningModel {
    preferences: Record<string, any>;  // 用户偏好
    patterns: Record<string, any>;     // 使用模式
    lastUpdated: number;               // 最后更新时间
}

@injectable()
export class LearningService {
    private model: LearningModel;
    private interactions: UserInteraction[] = [];
    private modelSubject = new BehaviorSubject<LearningModel | null>(null);
    private updateDebounceMs = 5000; // 5秒内的变化一起处理
    
    constructor(
        @inject('LocalStorageService') private storage: LocalStorageService,
        @inject('AnalyticsService') private analytics: AnalyticsService
    ) {
        this.initializeModel();
    }
    
    // 初始化学习模型
    private async initializeModel(): Promise<void> {
        try {
            const savedModel = await this.storage.getItem<LearningModel>('learning_model');
            if (savedModel) {
                this.model = savedModel;
            } else {
                this.model = this.createDefaultModel();
            }
            
            this.modelSubject.next(this.model);
        } catch (error) {
            console.error('初始化学习模型失败', error);
            this.model = this.createDefaultModel();
        }
    }
    
    // 创建默认模型
    private createDefaultModel(): LearningModel {
        return {
            preferences: {
                theme: 'system',
                dashboardLayout: 'grid',
                moreDetailsByDefault: false,
                favoriteFeatures: []
            },
            patterns: {
                frequentUsage: {},
                deviceUsageTimes: {},
                navigationFlows: [],
                deviceGroups: []
            },
            lastUpdated: Date.now()
        };
    }
    
    // 记录用户交互
    public recordInteraction(interaction: Omit<UserInteraction, 'timestamp'>): void {
        const fullInteraction: UserInteraction = {
            ...interaction,
            timestamp: Date.now()
        };
        
        this.interactions.push(fullInteraction);
        
        // 记录到分析服务
        this.analytics.trackEvent('user_interaction', {
            interaction_type: interaction.type,
            target: interaction.target
        });
        
        // 超过一定数量的交互触发更新
        if (this.interactions.length >= 10) {
            this.updateModel();
        }
    }
    
    // 更新学习模型
    public updateModel(): void {
        if (this.interactions.length === 0) return;
        
        const currentInteractions = [...this.interactions];
        this.interactions = [];
        
        // 分析交互并更新模型
        this.analyzeInteractions(currentInteractions);
        
        // 保存模型
        this.model.lastUpdated = Date.now();
        this.storage.setItem('learning_model', this.model);
        
        // 通知订阅者
        this.modelSubject.next(this.model);
    }
    
    // 分析用户交互
    private analyzeInteractions(interactions: UserInteraction[]): void {
        // 提取设备使用时间模式
        this.analyzeDeviceUsageTimes(interactions);
        
        // 分析导航流
        this.analyzeNavigationFlows(interactions);
        
        // 分析设备分组
        this.analyzeDeviceGroups(interactions);
        
        // 分析偏好
        this.analyzePreferences(interactions);
    }
    
    // 分析设备使用时间
    private analyzeDeviceUsageTimes(interactions: UserInteraction[]): void {
        const deviceControls = interactions.filter(i => i.type === 'device_control');
        
        deviceControls.forEach(interaction => {
            const { target: deviceId, context } = interaction;
            const hour = new Date(interaction.timestamp).getHours();
            
            if (!this.model.patterns.deviceUsageTimes[deviceId]) {
                this.model.patterns.deviceUsageTimes[deviceId] = {
                    hourly: Array(24).fill(0),
                    commands: {}
                };
            }
            
            // 更新小时使用计数
            this.model.patterns.deviceUsageTimes[deviceId].hourly[hour]++;
            
            // 记录命令使用情况
            if (context?.command) {
                const { command } = context;
                if (!this.model.patterns.deviceUsageTimes[deviceId].commands[command]) {
                    this.model.patterns.deviceUsageTimes[deviceId].commands[command] = 0;
                }
                this.model.patterns.deviceUsageTimes[deviceId].commands[command]++;
            }
        });
    }
    
    // 分析导航流
    private analyzeNavigationFlows(interactions: UserInteraction[]): void {
        const navigations = interactions.filter(i => i.type === 'navigation');
        
        if (navigations.length < 2) return;
        
        // 按时间排序
        navigations.sort((a, b) => a.timestamp - b.timestamp);
        
        // 分析导航路径
        for (let i = 0; i < navigations.length - 1; i++) {
            const from = navigations[i].target;
            const to = navigations[i + 1].target;
            const flow = `${from}>${to}`;
            
            // 查找是否已有此流
            const existingFlow = this.model.patterns.navigationFlows.find(f => f.path === flow);
            
            if (existingFlow) {
                existingFlow.count++;
            } else {
                this.model.patterns.navigationFlows.push({
                    path: flow,
                    count: 1,
                    firstSeen: navigations[i].timestamp
                });
            }
        }
        
        // 限制保存的流数量
        if (this.model.patterns.navigationFlows.length > 20) {
            this.model.patterns.navigationFlows.sort((a, b) => b.count - a.count);
            this.model.patterns.navigationFlows = this.model.patterns.navigationFlows.slice(0, 20);
        }
    }
    
    // 分析设备分组
    private analyzeDeviceGroups(interactions: UserInteraction[]): void {
        const deviceControls = interactions.filter(i => i.type === 'device_control');
        
        if (deviceControls.length < 2) return;
        
        // 按用户ID和会话分组
        const sessionDevices: Record<string, string[]> = {};
        
        deviceControls.forEach(interaction => {
            const { context, target: deviceId } = interaction;
            const sessionId = context?.sessionId || 'default';
            
            if (!sessionDevices[sessionId]) {
                sessionDevices[sessionId] = [];
            }
            
            if (!sessionDevices[sessionId].includes(deviceId)) {
                sessionDevices[sessionId].push(deviceId);
            }
        });
        
        // 分析设备共现关系
        const devicePairs: Record<string, number> = {};
        
        Object.values(sessionDevices).forEach(devices => {
            // 只考虑有多个设备的会话
            if (devices.length < 2) return;
            
            // 计算设备对的共现次数
            for (let i = 0; i < devices.length; i++) {
                for (let j = i + 1; j < devices.length; j++) {
                    // 确保设备对的顺序一致性
                    const pair = [devices[i], devices[j]].sort().join('|');
                    
                    if (!devicePairs[pair]) {
                        devicePairs[pair] = 0;
                    }
                    
                    devicePairs[pair]++;
                }
            }
        });
        
        // 更新设备分组
        Object.entries(devicePairs).forEach(([pair, count]) => {
            const [deviceA, deviceB] = pair.split('|');
            
            // 查找现有的设备组
            let foundGroup = false;
            
            for (const group of this.model.patterns.deviceGroups) {
                // 如果设备对中的任一设备在组中，考虑将另一个也加入
                if (group.devices.includes(deviceA) || group.devices.includes(deviceB)) {
                    // 只有当共现次数足够高时才合并
                    if (count >= 3) {
                        if (!group.devices.includes(deviceA)) {
                            group.devices.push(deviceA);
                        }
                        if (!group.devices.includes(deviceB)) {
                            group.devices.push(deviceB);
                        }
                        foundGroup = true;
                        break;
                    }
                }
            }
            
            // 如果没有找到匹配的组且共现次数足够高，创建新组
            if (!foundGroup && count >= 5) {
                this.model.patterns.deviceGroups.push({
                    id: `group_${Date.now()}`,
                    name: '自动发现的设备组',
                    devices: [deviceA, deviceB],
                    confidence: Math.min(1.0, count / 10) // 最高为1.0
                });
            }
        });
        
        // 合并高度重叠的组
        this.mergeOverlappingGroups();
    }
    
    // 合并重叠的设备组
    private mergeOverlappingGroups(): void {
        const { deviceGroups } = this.model.patterns;
        let merged = true;
        
        while (merged) {
            merged = false;
            
            for (let i = 0; i < deviceGroups.length; i++) {
                for (let j = i + 1; j < deviceGroups.length; j++) {
                    const groupA = deviceGroups[i];
                    const groupB = deviceGroups[j];
                    
                    // 计算重叠度
                    const overlap = groupA.devices.filter(d => groupB.devices.includes(d)).length;
                    const overlapRatio = overlap / Math.min(groupA.devices.length, groupB.devices.length);
                    
                    // 如果重叠度超过70%，合并这两个组
                    if (overlapRatio > 0.7) {
                        // 合并设备列表
                        const mergedDevices = [...new Set([...groupA.devices, ...groupB.devices])];
                        
                        // 计算新的置信度
                        const newConfidence = (groupA.confidence + groupB.confidence) / 2;
                        
                        // 更新组A
                        groupA.devices = mergedDevices;
                        groupA.confidence = newConfidence;
                        
                        // 移除组B
                        deviceGroups.splice(j, 1);
                        
                        merged = true;
                        break;
                    }
                }
                
                if (merged) break;
            }
        }
    }
    
    // 分析用户偏好
    private analyzePreferences(interactions: UserInteraction[]): void {
        // 分析主题偏好
        const themeToggles = interactions.filter(i => i.type === 'theme_toggle');
        if (themeToggles.length > 0) {
            // 使用最后一次设置的主题
            const lastToggle = themeToggles[themeToggles.length - 1];
            this.model.preferences.theme = lastToggle.context?.theme || this.model.preferences.theme;
        }
        
        // 分析布局偏好
        const layoutChanges = interactions.filter(i => i.type === 'layout_change');
        if (layoutChanges.length > 0) {
            // 使用最后一次设置的布局
            const lastChange = layoutChanges[layoutChanges.length - 1];
            this.model.preferences.dashboardLayout = lastChange.context?.layout || this.model.preferences.dashboardLayout;
        }
        
        // 分析详情显示偏好
        const detailsToggles = interactions.filter(i => i.type === 'details_toggle');
        if (detailsToggles.length >= 3) {
            // 计算用户倾向
            const showDetails = detailsToggles.filter(i => i.context?.show === true).length;
            const hideDetails = detailsToggles.length - showDetails;
            
            // 如果明显倾向一方，更新偏好
            if (Math.abs(showDetails - hideDetails) >= 3) {
                this.model.preferences.moreDetailsByDefault = showDetails > hideDetails;
            }
        }
        
        // 分析常用功能
        const featureUsage: Record<string, number> = {};
        
        interactions.forEach(interaction => {
            if (interaction.type === 'feature_use') {
                const feature = interaction.target;
                if (!featureUsage[feature]) {
                    featureUsage[feature] = 0;
                }
                featureUsage[feature]++;
            }
        });
        
        // 更新常用功能列表
        const sortedFeatures = Object.entries(featureUsage)
            .sort((a, b) => b[1] - a[1])
            .map(([feature]) => feature);
            
        // 只保留前5个常用功能
        this.model.preferences.favoriteFeatures = sortedFeatures.slice(0, 5);
    }
    
    // 获取学习模型
    public getModel(): LearningModel {
        return this.model;
    }
    
    // 观察模型变化
    public observeModel(): Observable<LearningModel | null> {
        return this.modelSubject.asObservable().pipe(
            debounceTime(300),
            distinctUntilChanged()
        );
    }
    
    // 获取设备使用时间建议
    public getDeviceUsageTimeSuggestion(deviceId: string): number | null {
        const deviceUsage = this.model.patterns.deviceUsageTimes[deviceId];
        if (!deviceUsage) return null;
        
        // 找出使用频率最高的小时
        let maxHour = 0;
        let maxCount = 0;
        
        deviceUsage.hourly.forEach((count, hour) => {
            if (count > maxCount) {
                maxCount = count;
                maxHour = hour;
            }
        });
        
        // 只有当使用次数足够时才返回建议
        return maxCount >= 5 ? maxHour : null;
    }
    
    // 获取设备命令建议
    public getDeviceCommandSuggestion(deviceId: string): string | null {
        const deviceUsage = this.model.patterns.deviceUsageTimes[deviceId];
        if (!deviceUsage || !deviceUsage.commands) return null;
        
        // 找出使用频率最高的命令
        let maxCommand = '';
        let maxCount = 0;
        
        Object.entries(deviceUsage.commands).forEach(([command, count]) => {
            if (count > maxCount) {
                maxCount = count;
                maxCommand = command;
            }
        });
        
        // 只有当使用次数足够时才返回建议
        return maxCount >= 3 ? maxCommand : null;
    }
    
    // 获取导航建议
    public getNavigationSuggestion(currentPage: string): string | null {
        // 找出从当前页面出发最常去的下一页
        const relevantFlows = this.model.patterns.navigationFlows
            .filter(flow => flow.path.startsWith(`${currentPage}>`));
            
        if (relevantFlows.length === 0) return null;
        
        // 按频率排序
        relevantFlows.sort((a, b) => b.count - a.count);
        
        // 提取建议的下一页
        const suggestedPage = relevantFlows[0].path.split('>')[1];
        
        // 只有当导航次数足够时才返回建议
        return relevantFlows[0].count >= 5 ? suggestedPage : null;
    }
    
    // 获取设备组建议
    public getDeviceGroupSuggestions(): Array<{id: string, name: string, devices: string[], confidence: number}> {
        // 只返回置信度较高的组
        return this.model.patterns.deviceGroups
            .filter(group => group.confidence >= 0.5)
            .sort((a, b) => b.confidence - a.confidence);
    }
    
    // 重置学习模型
    public resetModel(): void {
        this.model = this.createDefaultModel();
        this.storage.setItem('learning_model', this.model);
        this.modelSubject.next(this.model);
    }
}

// frontend/src/hooks/useAdaptiveUI.ts
import { useState, useEffect } from 'react';
import { useSelector } from 'react-redux';
import { RootState } from '../store';
import { useInjection } from '../core/di-hooks';
import { LearningService } from '../services/learning.service';

export function useAdaptiveUI() {
    const learningService = useInjection<LearningService>('LearningService');
    const [model, setModel] = useState(learningService.getModel());
    const user = useSelector((state: RootState) => state.user);
    const [adaptations, setAdaptations] = useState({
        suggestedLayout: '',
        favoriteFeatures: [] as string[],
        quickAccessDevices: [] as string[],
        useDetailView: false
    });
    
    // 监听模型变化
    useEffect(() => {
        const subscription = learningService.observeModel().subscribe(updatedModel => {
            if (updatedModel) {
                setModel(updatedModel);
            }
        });
        
        return () => {
            subscription.unsubscribe();
        };
    }, [learningService]);
    
    // 计算UI适应
    useEffect(() => {
        // 如果用户明确设置了偏好，使用用户设置
        const suggestedLayout = user.preferences.layout || model.preferences.dashboardLayout;
        
        // 从学习模型中获取常用功能
        const favoriteFeatures = [...model.preferences.favoriteFeatures];
        
        // 计算常用设备
        const quickAccessDevices = calculateQuickAccessDevices();
        
        // 详情视图偏好
        const useDetailView = user.preferences.detailedView !== undefined 
            ? user.preferences.detailedView 
            : model.preferences.moreDetailsByDefault;
            
        setAdaptations({
            suggestedLayout,
            favoriteFeatures,
            quickAccessDevices,
            useDetailView
        });
    }, [model, user]);
    
    // 计算快速访问设备
    const calculateQuickAccessDevices = () => {
        // 从设备使用时间中提取最常用的设备
        const deviceUsage = model.patterns.deviceUsageTimes;
        
        // 计算每个设备的总使用次数
        const deviceTotalUsage = Object.entries(deviceUsage).map(([deviceId, usage]) => {
            const total = usage.hourly.reduce((sum, count) => sum + count, 0);
            return { deviceId, total };
        });
        
        // 按使用次数排序并返回前5个
        deviceTotalUsage.sort((a, b) => b.total - a.total);
        return deviceTotalUsage.slice(0, 5).map(d => d.deviceId);
    };
    
    // 记录交互
    const recordInteraction = (type: string, target: string, context?: any) => {
        learningService.recordInteraction({ type, target, context });
    };
    
    return { adaptations, recordInteraction, model };
}

// frontend/src/components/adaptive/AdaptiveLayout.tsx
import React, { useEffect } from 'react';
import { useLocation } from 'react-router-dom';
import { useAdaptiveUI } from '../../hooks/useAdaptiveUI';
import { useSelector, useDispatch } from 'react-redux';
import { RootState } from '../../store';
import { setLayout } from '../../store/slices/ui.slice';
import { GridLayout, ListLayout } from '../layouts';

interface AdaptiveLayoutProps {
    children: React.ReactNode;
}

export const AdaptiveLayout: React.FC<AdaptiveLayoutProps> = ({ children }) => {
    const location = useLocation();
    const { adaptations, recordInteraction } = useAdaptiveUI();
    const dispatch = useDispatch();
    const currentLayout = useSelector((state: RootState) => state.ui.layout);
    
    // 应用自适应布局
    useEffect(() => {
        if (adaptations.suggestedLayout && adaptations.suggestedLayout !== currentLayout) {
            dispatch(setLayout(adaptations.suggestedLayout));
        }
    }, [adaptations.suggestedLayout, currentLayout, dispatch]);
    
    // 记录页面导航
    useEffect(() => {
        recordInteraction('navigation', location.pathname);
    }, [location.pathname, recordInteraction]);
    
    // 根据当前布局渲染
    const renderLayout = () => {
        switch (currentLayout) {
            case 'grid':
                return <GridLayout>{children}</GridLayout>;
            case 'list':
                return <ListLayout>{children}</ListLayout>;
            default:
                return <div>{children}</div>;
        }
    };
    
    return renderLayout();
};
```

通过以上代码，我全面阐述了智能家居系统实现中的关键五个方面的深度解决方案：

1. **API设计**: 提供了完善的RESTful与GraphQL API设计，包括版本管理、批量操作、请求优化和CRUD标准化接口，为前后端交互提供稳定的基础架构。

2. **前后端分离**: 采用领域驱动设计和分层架构，建立清晰的模块边界和依赖关系，实现前后端关注点分离，提高代码可维护性和扩展性。

3. **状态同步机制**: 实现了基于WebSocket的实时状态更新、离线状态同步与冲突解决、事件驱动架构和分布式状态一致性保障，确保多设备环境下系统状态的一致性和可靠性。

4. **前端架构**: 创建了灵活可复用的组件设计系统、设备控制组件、状态管理架构和离线模式数据持久化方案，提供流畅的用户界面和稳定的功能体验。

5. **权限与用户体验**: 设计了RBAC权限模型、渐进式用户引导、个性化推荐系统和学习适应能力，实现智能化的用户界面和推荐，提升用户体验。

这些代码模块共同构成了一个强大、可靠且用户友好的智能家居系统架构，既满足功能需求，又保证了良好的用户体验和系统性能。
