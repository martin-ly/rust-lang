# 智能家居工作流模型映射与实现指南

## 目录

- [智能家居工作流模型映射与实现指南](#智能家居工作流模型映射与实现指南)
  - [目录](#目录)
  - [一、场景到工作流的映射模型](#一场景到工作流的映射模型)
    - [1. 基本流程类型与对应的工作流表达](#1-基本流程类型与对应的工作流表达)
    - [2. 工作流组合模式映射](#2-工作流组合模式映射)
  - [二、实际场景映射示例](#二实际场景映射示例)
    - [场景一：离家模式（涉及多设备控制和顺序执行）](#场景一离家模式涉及多设备控制和顺序执行)
    - [场景二：温度异常处理（涉及条件分支与异步补偿）](#场景二温度异常处理涉及条件分支与异步补偿)
  - [三、工作流组合与嵌套模式](#三工作流组合与嵌套模式)
    - [1. 工作流组合模式示例](#1-工作流组合模式示例)
    - [2. 子工作流示例](#2-子工作流示例)
  - [四、异常场景与工作流解决方案](#四异常场景与工作流解决方案)
    - [1. 设备离线或不可用的容错模式](#1-设备离线或不可用的容错模式)
    - [2. 网络不稳定环境下的数据一致性保障](#2-网络不稳定环境下的数据一致性保障)
    - [3. 场景执行的事务性保障（Saga模式）](#3-场景执行的事务性保障saga模式)
  - [五、复杂现实问题到工作流模型的映射](#五复杂现实问题到工作流模型的映射)
    - [1. 能源管理系统在智能家居中的实现](#1-能源管理系统在智能家居中的实现)
    - [2. 分布式场景协调 - 多房间、多设备复杂场景](#2-分布式场景协调---多房间多设备复杂场景)
  - [六、工作流中需要解决的一致性问题](#六工作流中需要解决的一致性问题)
    - [1. 数据流与一致性保障模式](#1-数据流与一致性保障模式)
      - [场景故障恢复一致性管理工作流](#场景故障恢复一致性管理工作流)
    - [2. 冲突解决模式：优先级、版本与空间锁定](#2-冲突解决模式优先级版本与空间锁定)
  - [七、工作流设计中的关键挑战与解决方案](#七工作流设计中的关键挑战与解决方案)
    - [1. 长时间运行工作流与心跳机制](#1-长时间运行工作流与心跳机制)
    - [2. 动态工作流与运行时决策](#2-动态工作流与运行时决策)
    - [3. 工作流版本管理与向后兼容性](#3-工作流版本管理与向后兼容性)
  - [八、系统集成与协同工作](#八系统集成与协同工作)
    - [1. 智能家居系统的工作流层次结构](#1-智能家居系统的工作流层次结构)
    - [2. Temporal集成API层设计](#2-temporal集成api层设计)
  - [九、最佳实践与模式总结](#九最佳实践与模式总结)
    - [1. 智能家居工作流的最佳实践](#1-智能家居工作流的最佳实践)
    - [2. 实现Temporal工作流的关键点](#2-实现temporal工作流的关键点)
    - [3. 智能家居常见工作流模式汇总](#3-智能家居常见工作流模式汇总)
    - [4. 实际项目的集成路径](#4-实际项目的集成路径)
      - [渐进式集成Temporal的步骤](#渐进式集成temporal的步骤)
      - [Temporal与现有系统的集成模式](#temporal与现有系统的集成模式)
  - [十、工作流与AI集成](#十工作流与ai集成)
    - [1. 基于AI的场景推荐工作流](#1-基于ai的场景推荐工作流)
    - [2. AI自动场景生成工作流](#2-ai自动场景生成工作流)
  - [总结：工作流如何解决智能家居系统难题](#总结工作流如何解决智能家居系统难题)

## 一、场景到工作流的映射模型

### 1. 基本流程类型与对应的工作流表达

| 现实场景流程 | Temporal工作流表达 | 实现方式 |
|------------|------------------|---------|
| **数据流** | 活动(Activity)链与数据传递 | 活动间参数传递，关联上下文(Context) |
| **控制流** | 工作流编排逻辑 | 顺序执行、条件分支、并行执行 |
| **执行流** | 工作流调度与活动执行 | 工作流启动、活动分发、任务队列 |
| **容错机制** | 重试策略与补偿逻辑 | 活动重试、幂等设计、超时处理 |
| **一致性保障** | 事务与异步补偿 | Saga模式、检查点(Checkpoint) |

### 2. 工作流组合模式映射

```text
基本场景 -> 单一工作流
复合场景 -> 工作流组合（父子工作流）
多场景协调 -> 工作流编排（工作流间通信）
自适应场景 -> 动态工作流（运行时决策）
```

## 二、实际场景映射示例

### 场景一：离家模式（涉及多设备控制和顺序执行）

```go
// 离家模式工作流定义
func LeaveHomeModeWorkflow(ctx workflow.Context, params LeaveHomeParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("执行离家模式工作流", "用户", params.UserID)
    
    // 1. 数据流：通过参数和上下文在活动间传递数据
    opts := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
            InitialInterval: 1 * time.Second,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, opts)
    
    // 2. 控制流：按顺序执行设备控制
    // 2.1 检查家庭状态
    var homeStatus HomeStatusResult
    err := workflow.ExecuteActivity(ctx, activities.CheckHomeStatus, params.HomeID).Get(ctx, &homeStatus)
    if err != nil {
        return fmt.Errorf("检查家庭状态失败: %w", err)
    }
    
    // 2.2 如果有人在家，不执行离家模式
    if homeStatus.PeoplePresent {
        logger.Info("检测到有人在家，取消离家模式")
        return nil
    }
    
    // 2.3 顺序关闭设备（控制流-顺序执行）
    var deviceResult DeviceActionResult
    // 关灯
    err = workflow.ExecuteActivity(ctx, activities.TurnOffAllLights, params.HomeID).Get(ctx, &deviceResult)
    if err != nil {
        // 3. 容错：记录错误但继续执行其他设备
        logger.Error("关灯失败，继续执行其他设备操作", "error", err)
    }
    
    // 关空调
    err = workflow.ExecuteActivity(ctx, activities.SetHVACMode, SetHVACParams{
        HomeID: params.HomeID,
        Mode: "energy_saving",
        TargetTemp: 26.0,
    }).Get(ctx, &deviceResult)
    if err != nil {
        logger.Error("设置空调失败", "error", err)
    }
    
    // 2.4 并行执行其余设备操作（控制流-并行执行）
    futures := []workflow.Future{
        workflow.ExecuteActivity(ctx, activities.LockAllDoors, params.HomeID),
        workflow.ExecuteActivity(ctx, activities.CloseAllWindows, params.HomeID),
        workflow.ExecuteActivity(ctx, activities.EnableSecuritySystem, params.HomeID),
    }
    
    // 等待所有设备操作完成
    errs := []error{}
    for i, future := range futures {
        var result DeviceActionResult
        err := future.Get(ctx, &result)
        if err != nil {
            // 记录错误，但不中断流程
            errs = append(errs, fmt.Errorf("设备操作 %d 失败: %w", i, err))
        }
    }
    
    // 4. 一致性：发送最终状态确认通知
    if len(errs) > 0 {
        // 4.1 部分失败，执行补偿操作
        ctx = workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
            StartToCloseTimeout: 30 * time.Second,
        })
        var notificationResult NotificationResult
        _ = workflow.ExecuteActivity(ctx, activities.SendNotification, NotificationParams{
            UserID: params.UserID,
            Type: "leave_home_partial_success",
            Details: fmt.Sprintf("离家模式部分成功：%d个操作失败", len(errs)),
        }).Get(ctx, &notificationResult)
        
        return fmt.Errorf("离家模式部分失败：%v", errs)
    }
    
    // 全部成功
    var notificationResult NotificationResult
    _ = workflow.ExecuteActivity(ctx, activities.SendNotification, NotificationParams{
        UserID: params.UserID,
        Type: "leave_home_success",
        Details: "离家模式已成功启用",
    }).Get(ctx, &notificationResult)
    
    return nil
}
```

### 场景二：温度异常处理（涉及条件分支与异步补偿）

```go
// 温度异常处理工作流
func AbnormalTemperatureWorkflow(ctx workflow.Context, params TempMonitorParams) error {
    logger := workflow.GetLogger(ctx)
    
    // 设置活动选项，处理设备离线等异常
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 5,
            InitialInterval: 2 * time.Second,
            MaximumInterval: 10 * time.Second,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取当前温度数据
    var tempData TemperatureData
    err := workflow.ExecuteActivity(ctx, activities.GetRoomTemperature, 
        params.RoomID).Get(ctx, &tempData)
    if err != nil {
        // 容错：设备可能离线，使用备用传感器
        logger.Info("主传感器读取失败，尝试备用传感器", "error", err)
        backupOptions := workflow.ActivityOptions{
            StartToCloseTimeout: 5 * time.Second,
            RetryPolicy: &temporal.RetryPolicy{
                MaximumAttempts: 3,
            },
        }
        backupCtx := workflow.WithActivityOptions(ctx, backupOptions)
        err = workflow.ExecuteActivity(backupCtx, activities.GetBackupRoomTemperature, 
            params.RoomID).Get(backupCtx, &tempData)
        if err != nil {
            return fmt.Errorf("温度数据获取失败: %w", err)
        }
    }
    
    // 2. 基于条件分支的控制流执行不同逻辑
    if tempData.Temperature > params.MaxThreshold {
        // 2.1 温度过高分支
        logger.Info("检测到温度过高", "temp", tempData.Temperature, "threshold", params.MaxThreshold)
        
        // 检查空调状态
        var acStatus ACStatus
        err = workflow.ExecuteActivity(ctx, activities.GetACStatus, params.RoomID).Get(ctx, &acStatus)
        if err != nil {
            logger.Error("获取空调状态失败", "error", err)
            // 继续处理，假设空调可能不可用
        }
        
        // 控制流：条件分支
        if !acStatus.IsOn || acStatus.Mode != "cooling" || acStatus.TargetTemp > (params.MaxThreshold - 2) {
            // 启动降温逻辑
            err = workflow.ExecuteActivity(ctx, activities.SetACParams, ACParams{
                RoomID: params.RoomID,
                Power: true,
                Mode: "cooling",
                Temperature: params.MaxThreshold - 3, // 目标温度设为阈值低3度
                FanSpeed: "high",
            }).Get(ctx, nil)
            
            if err != nil {
                // 启动异步补偿 - 通知用户手动处理
                compensationCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
                    StartToCloseTimeout: 30 * time.Second,
                })
                _ = workflow.ExecuteActivity(compensationCtx, activities.SendHighPriorityNotification, NotificationParams{
                    UserID: params.UserID,
                    Title: "温度异常警告",
                    Message: fmt.Sprintf("房间温度异常（%.1f°C），自动控制失败，请手动处理", tempData.Temperature),
                    Priority: "high",
                }).Get(compensationCtx, nil)
                
                // 记录失败但不终止工作流
                logger.Error("空调调节失败", "error", err)
            }
        }
        
        // 启动子工作流：持续监控直到温度恢复正常
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("temp-monitor-%s-%s", params.RoomID, workflow.Now(ctx).Format("20060102-150405")),
        }
        childCtx := workflow.WithChildOptions(ctx, cwo)
        
        return workflow.ExecuteChildWorkflow(childCtx, TemperatureMonitoringWorkflow, TemperatureMonitoringParams{
            RoomID: params.RoomID,
            TargetTemp: params.MaxThreshold - 2,
            MonitorDuration: 30 * time.Minute,
            CheckInterval: 2 * time.Minute,
        }).Get(childCtx, nil)
        
    } else if tempData.Temperature < params.MinThreshold {
        // 2.2 温度过低分支 - 类似逻辑，这里简化
        logger.Info("检测到温度过低", "temp", tempData.Temperature, "threshold", params.MinThreshold)
        // ... 温度过低处理逻辑
    } else {
        // 2.3 温度正常分支
        logger.Info("温度在正常范围内", "temp", tempData.Temperature)
        // 正常情况可以终止监控或降低监控频率
    }
    
    return nil
}
```

## 三、工作流组合与嵌套模式

### 1. 工作流组合模式示例

```go
// 主工作流：协调多个子工作流的执行
func SmartHomeRoutineWorkflow(ctx workflow.Context, params DailyRoutineParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("开始执行智能家居日常例程", "user", params.UserID)
    
    // 1. 嵌套模式：使用子工作流
    // 早晨唤醒场景
    if params.IncludeMorningRoutine {
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("morning-routine-%s-%s", 
                params.UserID, workflow.Now(ctx).Format("20060102")),
        }
        morningCtx := workflow.WithChildOptions(ctx, cwo)
        
        var morningResult MorningRoutineResult
        err := workflow.ExecuteChildWorkflow(morningCtx, MorningRoutineWorkflow, MorningRoutineParams{
            UserID: params.UserID,
            WakeupTime: params.WakeupTime,
            Gradual: params.GradualWakeup,
        }).Get(morningCtx, &morningResult)
        
        if err != nil {
            logger.Error("早晨例程执行失败", "error", err)
            // 早晨例程失败不影响其他例程执行
        }
    }
    
    // 2. 工作流编排：使用信号在工作流之间协调
    // 设置夜间预热家庭信号
    signalName := "evening_preparation_signal"
    signalChan := workflow.GetSignalChannel(ctx, signalName)
    
    // 创建并启动晚间例程
    if params.IncludeEveningRoutine {
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("evening-routine-%s-%s", 
                params.UserID, workflow.Now(ctx).Format("20060102")),
        }
        eveningCtx := workflow.WithChildOptions(ctx, cwo)
        
        // 异步启动晚间例程
        eveningFuture := workflow.ExecuteChildWorkflow(eveningCtx, EveningRoutineWorkflow, EveningRoutineParams{
            UserID: params.UserID,
            ArrivalTime: params.ExpectedHomeTime,
        })
        
        // 在将来的某个时间点发送信号控制晚间例程的预热逻辑
        // 这里用一个定时器模拟用户出发回家的信号
        workflow.NewTimer(ctx, params.ExpectedHomeTime.Add(-30*time.Minute)).Future.Get(ctx, nil)
        
        // 发送信号，触发晚间例程中的家庭预热步骤
        err := eveningFuture.SignalChildWorkflow(ctx, signalName, HomePreparationSignal{
            UserLocation: "正在回家途中",
            EstimatedArrival: params.ExpectedHomeTime,
        }).Get(ctx, nil)
        
        if err != nil {
            logger.Error("发送晚间预热信号失败", "error", err)
        }
        
        // 等待晚间例程完成
        var eveningResult EveningRoutineResult
        if err := eveningFuture.Get(ctx, &eveningResult); err != nil {
            logger.Error("晚间例程执行失败", "error", err)
        }
    }
    
    // 3. 工作流聚合：同时监控多个不同的子工作流执行结果
    if params.EnableHomeSecurity {
        // 启动24小时安全监控工作流，但不等待其完成（长时间运行的后台工作流）
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("security-monitoring-%s-%s", 
                params.UserID, workflow.Now(ctx).Format("20060102")),
        }
        securityCtx := workflow.WithChildOptions(ctx, cwo)
        
        _ = workflow.ExecuteChildWorkflow(securityCtx, SecurityMonitoringWorkflow, SecurityParams{
            HomeID: params.HomeID,
            NotificationUserIDs: params.NotificationUserIDs,
            MonitorDuration: 24 * time.Hour,
        })
    }
    
    logger.Info("全部日常例程工作流启动完成")
    return nil
}
```

### 2. 子工作流示例

```go
// 晚间回家例程工作流 - 演示如何接收和处理信号
func EveningRoutineWorkflow(ctx workflow.Context, params EveningRoutineParams) (EveningRoutineResult, error) {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动晚间回家例程", "user", params.UserID)
    
    result := EveningRoutineResult{
        Status: "pending",
    }
    
    // 1. 接收信号的选择器
    var homePreparationSignal HomePreparationSignal
    signalName := "evening_preparation_signal"
    signalReceived := false
    
    // 创建选择器来处理信号或超时
    selector := workflow.NewSelector(ctx)
    
    // 添加信号通道处理
    signalChan := workflow.GetSignalChannel(ctx, signalName)
    selector.AddReceive(signalChan, func(c workflow.ReceiveChannel, more bool) {
        c.Receive(ctx, &homePreparationSignal)
        signalReceived = true
        logger.Info("收到家庭预热信号", "estimatedArrival", homePreparationSignal.EstimatedArrival)
    })
    
    // 添加超时处理 - 如果超过预计到达时间1小时仍没收到信号，自动开始预热
    arrivalTimeout := workflow.NewTimer(ctx, params.ArrivalTime.Add(1*time.Hour))
    selector.AddFuture(arrivalTimeout.Future, func(f workflow.Future) {
        _ = f.Get(ctx, nil)
        logger.Info("超时未收到信号，自动开始家庭预热")
        homePreparationSignal = HomePreparationSignal{
            UserLocation: "未知",
            EstimatedArrival: workflow.Now(ctx).Add(15*time.Minute),
        }
        signalReceived = true
    })
    
    // 等待信号或超时
    for !signalReceived {
        selector.Select(ctx)
    }
    
    // 2. 活动编排：基于信号数据准备家庭环境
    ctx = workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    })
    
    // 2.1 计算预热时间
    preheatingDuration := homePreparationSignal.EstimatedArrival.Sub(workflow.Now(ctx))
    if preheatingDuration < 0 {
        preheatingDuration = 5 * time.Minute // 如果已经过了预计到达时间，设置一个最小值
    }
    
    // 并行执行家庭预热任务
    futures := []workflow.Future{
        workflow.ExecuteActivity(ctx, activities.PreHeatHome, PreHeatParams{
            HomeID: params.HomeID,
            TargetTemp: params.TargetTemperature,
            Duration: preheatingDuration,
        }),
        workflow.ExecuteActivity(ctx, activities.PrepareAmbientLighting, LightingParams{
            HomeID: params.HomeID,
            Mode: "welcome",
            Brightness: 70,
        }),
        workflow.ExecuteActivity(ctx, activities.PrepareEntryway, EntryParams{
            HomeID: params.HomeID,
            UnlockDoor: params.AutoUnlock,
        }),
    }
    
    // 3. 容错与一致性处理
    errorCount := 0
    for i, future := range futures {
        err := future.Get(ctx, nil)
        if err != nil {
            errorCount++
            logger.Error("预热任务失败", "task", i, "error", err)
        }
    }
    
    // 4. 完成状态更新
    if errorCount == 0 {
        result.Status = "success"
        result.Message = "家庭成功预热，欢迎回家"
    } else if errorCount < len(futures) {
        result.Status = "partial_success"
        result.Message = fmt.Sprintf("家庭部分预热完成，%d个任务失败", errorCount)
    } else {
        result.Status = "failed"
        result.Message = "家庭预热失败，所有任务均未完成"
    }
    
    // 发送完成通知
    _ = workflow.ExecuteActivity(ctx, activities.SendNotification, NotificationParams{
        UserID: params.UserID,
        Title: "晚间回家例程",
        Message: result.Message,
    }).Get(ctx, nil)
    
    return result, nil
}
```

## 四、异常场景与工作流解决方案

### 1. 设备离线或不可用的容错模式

```go
// 温度控制容错工作流 - 处理设备离线情况
func RobustTemperatureControlWorkflow(ctx workflow.Context, params RobustTempParams) error {
    logger := workflow.GetLogger(ctx)
    
    // 设置活动选项
    options := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
            InitialInterval: 2 * time.Second,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, options)
    
    // 1. 活动降级策略：先尝试主设备，失败后降级到备用设备
    var result DeviceActionResult
    err := workflow.ExecuteActivity(ctx, activities.SetPrimaryHVACTemperature, ACParams{
        RoomID: params.RoomID,
        Temperature: params.TargetTemp,
    }).Get(ctx, &result)
    
    if err != nil {
        logger.Info("主空调控制失败，尝试备用设备", "error", err)
        
        // 尝试备用空调
        err = workflow.ExecuteActivity(ctx, activities.SetBackupHVACTemperature, ACParams{
            RoomID: params.RoomID,
            Temperature: params.TargetTemp,
        }).Get(ctx, &result)
        
        if err != nil {
            logger.Error("备用空调控制也失败", "error", err)
            
            // 2. 最终备用方案：尝试窗户控制通风
            if params.UseAlternatives {
                logger.Info("尝试替代方案：窗户控制")
                
                // 检查室外温度是否适合开窗
                var outdoorTemp TemperatureData
                errOutdoor := workflow.ExecuteActivity(ctx, activities.GetOutdoorTemperature, 
                    params.HomeID).Get(ctx, &outdoorTemp)
                
                if errOutdoor == nil && isTemperatureSuitable(outdoorTemp.Temperature, params.TargetTemp) {
                    // 室外温度适宜，开窗通风
                    _ = workflow.ExecuteActivity(ctx, activities.ControlWindows, WindowParams{
                        RoomID: params.RoomID,
                        Action: "open",
                        OpeningPercentage: 50,
                    }).Get(ctx, nil)
                }
            }
            
            // 3. 不管替代方案是否成功，都通知用户
            notifyCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
                StartToCloseTimeout: 30 * time.Second,
            })
            
            _ = workflow.ExecuteActivity(notifyCtx, activities.SendPriorityNotification, NotificationParams{
                UserID: params.UserID,
                Title: "温度控制失败",
                Message: fmt.Sprintf("无法设置房间 %s 的温度为 %.1f°C，请手动检查设备", 
                    params.RoomID, params.TargetTemp),
                Priority: "high",
            }).Get(notifyCtx, nil)
            
            return errors.New("所有温度控制方法都失败")
        }
    }
    
    // 4. 验证控制效果
    // 启动子工作流进行持续监控和验证
    cwo := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("temp-verify-%s-%s", 
            params.RoomID, workflow.Now(ctx).Format("20060102-150405")),
    }
    monitorCtx := workflow.WithChildOptions(ctx, cwo)
    
    return workflow.ExecuteChildWorkflow(monitorCtx, VerifyTemperatureWorkflow, VerifyTempParams{
        RoomID: params.RoomID,
        TargetTemp: params.TargetTemp,
        Tolerance: 1.0, // 允许1度的误差
        VerificationDuration: 15 * time.Minute,
    }).Get(monitorCtx, nil)
}

// 辅助函数：判断室外温度是否适合用来调节室内温度
func isTemperatureSuitable(outdoorTemp, targetTemp float64) bool {
    // 如果目标是制冷，室外温度应该低于目标温度
    if targetTemp < 24 {
        return outdoorTemp < targetTemp
    }
    // 如果目标是制热，室外温度应该高于目标温度
    return outdoorTemp > targetTemp
}
```

### 2. 网络不稳定环境下的数据一致性保障

```go
// 状态同步工作流 - 保证云端和本地数据的最终一致性
func DeviceStateSyncWorkflow(ctx workflow.Context, params StateSyncParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动设备状态同步工作流", "devices", len(params.DeviceIDs))
    
    // 设置活动选项
    options := workflow.ActivityOptions{
        StartToCloseTimeout: 15 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 5,
            InitialInterval: 1 * time.Second,
            MaximumInterval: 10 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, options)
    
    // 1. 处理离线状态和重连逻辑
    isConnected := true
    connectionCheckTimer := workflow.NewTimer(ctx, workflow.Now(ctx))
    
    for {
        // 等待定时器触发
        _ = connectionCheckTimer.Future.Get(ctx, nil)
        
        // 检查网络连接状态
        var networkStatus NetworkStatus
        err := workflow.ExecuteActivity(ctx, activities.CheckNetworkStatus, params.HomeID).Get(ctx, &networkStatus)
        
        // 网络状态变化处理
        if err != nil || !networkStatus.IsConnected {
            if isConnected {
                logger.Info("检测到网络断开，切换到离线模式")
                isConnected = false
                
                // 通知本地系统切换到离线模式
                _ = workflow.ExecuteActivity(ctx, activities.NotifySystemOfflineMode, 
                    params.HomeID).Get(ctx, nil)
            }
        } else {
            if !isConnected {
                logger.Info("网络已恢复，开始同步数据")
                isConnected = true
                
                // 执行数据同步流程
                err = syncDeviceStates(ctx, params.DeviceIDs, params.HomeID)
                if err != nil {
                    logger.Error("数据同步部分失败", "error", err)
                }
            }
            
            // 网络正常时也可以定期同步
            if params.SyncInterval > 0 && workflow.Now(ctx).Sub(params.LastSyncTime) >= params.SyncInterval {
                logger.Info("执行定期数据同步")
                _ = syncDeviceStates(ctx, params.DeviceIDs, params.HomeID)
                params.LastSyncTime = workflow.Now(ctx)
            }
        }
        
        // 设置下次检查时间
        nextCheckTime := workflow.Now(ctx).Add(30 * time.Second)
        connectionCheckTimer = workflow.NewTimer(ctx, nextCheckTime)
        
        // 如果是一次性同步，则完成工作流
        if params.SingleSync {
            return nil
        }
    }
}

// 辅助函数：同步设备状态 - 处理冲突和合并策略
func syncDeviceStates(ctx workflow.Context, deviceIDs []string, homeID string) error {
    logger := workflow.GetLogger(ctx)
    var syncErrors []error
    
    // 1. 获取本地缓存的设备状态变更
    var localChanges LocalDeviceChanges
    err := workflow.ExecuteActivity(ctx, activities.GetLocalDeviceChanges, 
        homeID).Get(ctx, &localChanges)
    if err != nil {
        return fmt.Errorf("获取本地变更失败: %w", err)
    }
    
    // 2. 获取云端的最新状态
    var cloudStates CloudDeviceStates
    err = workflow.ExecuteActivity(ctx, activities.GetCloudDeviceStates, 
        CloudStateRequest{HomeID: homeID, DeviceIDs: deviceIDs}).Get(ctx, &cloudStates)
    if err != nil {
        return fmt.Errorf("获取云端状态失败: %w", err)
    }
    
    // 3. 处理每个设备的状态同步
    for _, deviceID := range deviceIDs {
        logger.Info("同步设备状态", "device", deviceID)
        
        localState := localChanges.Changes[deviceID]
        cloudState := cloudStates.States[deviceID]
        
        // 3.1 检测冲突 - 基于时间戳和版本号
        if hasConflict(localState, cloudState) {
            // 解决冲突 - 这里使用合并策略
            logger.Info("检测到设备状态冲突，应用合并策略", "device", deviceID)
            
            // 3.2 应用合并策略
            mergedState, err := workflow.ExecuteActivity(ctx, activities.MergeDeviceStates, MergeParams{
                DeviceID: deviceID,
                LocalState: localState,
                CloudState: cloudState,
                MergeStrategy: params.MergeStrategy, // 可以是"cloud_priority", "local_priority", "timestamp_priority"
            }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("状态合并失败", "device", deviceID, "error", err)
                syncErrors = append(syncErrors, fmt.Errorf("设备 %s 状态合并失败: %w", deviceID, err))
                continue
            }
            
            // 3.3 同步合并后的状态到云端和本地
            err = workflow.ExecuteActivity(ctx, activities.UpdateDeviceState, UpdateStateParams{
                DeviceID: deviceID,
                NewState: mergedState,
                Target: "both", // 同时更新本地和云端
            }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("状态更新失败", "device", deviceID, "error", err)
                syncErrors = append(syncErrors, fmt.Errorf("设备 %s 状态更新失败: %w", deviceID, err))
            }
        } else if localState.LastUpdateTime.After(cloudState.LastUpdateTime) {
            // 3.4 本地状态较新，更新云端
            logger.Info("本地状态较新，同步到云端", "device", deviceID)
            
            err = workflow.ExecuteActivity(ctx, activities.UpdateDeviceState, UpdateStateParams{
                DeviceID: deviceID,
                NewState: localState,
                Target: "cloud",
            }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("更新云端状态失败", "device", deviceID, "error", err)
                syncErrors = append(syncErrors, fmt.Errorf("设备 %s 云端更新失败: %w", deviceID, err))
            }
        } else if cloudState.LastUpdateTime.After(localState.LastUpdateTime) {
            // 3.5 云端状态较新，更新本地
            logger.Info("云端状态较新，同步到本地", "device", deviceID)
            
            err = workflow.ExecuteActivity(ctx, activities.UpdateDeviceState, UpdateStateParams{
                DeviceID: deviceID,
                NewState: cloudState,
                Target: "local",
            }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("更新本地状态失败", "device", deviceID, "error", err)
                syncErrors = append(syncErrors, fmt.Errorf("设备 %s 本地更新失败: %w", deviceID, err))
            }
        } else {
            // 状态一致，无需操作
            logger.Info("设备状态已同步", "device", deviceID)
        }
    }
    
    // 4. 清理已同步的本地变更记录
    if len(syncErrors) == 0 {
        _ = workflow.ExecuteActivity(ctx, activities.CleanupLocalChanges, 
            homeID).Get(ctx, nil)
    }
    
    // 如果有错误，返回复合错误
    if len(syncErrors) > 0 {
        return fmt.Errorf("部分设备同步失败: %v", syncErrors)
    }
    
    return nil
}

// 辅助函数：检测状态冲突
func hasConflict(localState, cloudState DeviceState) bool {
    // 如果本地和云端在同一基础版本上有不同的修改，则视为冲突
    return localState.BaseVersion == cloudState.BaseVersion && 
           localState.StateHash != cloudState.StateHash
}
```

### 3. 场景执行的事务性保障（Saga模式）

```go
// 使用Saga模式实现事务性场景执行
func ComplexSceneExecutionWorkflow(ctx workflow.Context, params ComplexSceneParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("开始复杂场景执行", "sceneID", params.SceneID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 20 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
            InitialInterval: 2 * time.Second,
            MaximumInterval: 10 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取场景定义
    var sceneDefinition SceneDefinition
    err := workflow.ExecuteActivity(ctx, activities.GetSceneDefinition, 
        params.SceneID).Get(ctx, &sceneDefinition)
    if err != nil {
        return fmt.Errorf("获取场景定义失败: %w", err)
    }
    
    // 2. 验证场景条件
    var conditionResult ConditionEvaluationResult
    err = workflow.ExecuteActivity(ctx, activities.EvaluateSceneConditions, 
        sceneDefinition.Conditions).Get(ctx, &conditionResult)
    if err != nil {
        return fmt.Errorf("场景条件评估失败: %w", err)
    }
    
    if !conditionResult.IsSatisfied {
        logger.Info("场景条件不满足，不执行操作", 
            "failedConditions", conditionResult.FailedConditions)
        return nil
    }
    
    // 3. Saga模式实现 - 记录已执行的操作，以便在失败时进行补偿
    var executedActions []ExecutedAction
    var compensationNeeded bool = false
    var finalError error = nil
    
    // 3.1 按顺序执行设备操作
    for i, action := range sceneDefinition.Actions {
        // 跳过可选操作标记为非关键的操作
        if compensationNeeded && !action.IsCritical {
            logger.Info("跳过非关键操作", "action", i)
            continue
        }
        
        logger.Info("执行设备操作", "action", i, "device", action.DeviceID)
        
        var actionResult ActionResult
        err = workflow.ExecuteActivity(ctx, activities.ExecuteDeviceAction, 
            action).Get(ctx, &actionResult)
        
        if err != nil {
            logger.Error("设备操作失败", "action", i, "error", err)
            
            // 如果是关键操作失败，标记需要补偿
            if action.IsCritical {
                compensationNeeded = true
                finalError = fmt.Errorf("关键操作失败: %w", err)
            }
            
            continue
        }
        
        // 记录成功执行的操作，以便需要时进行补偿
        executedActions = append(executedActions, ExecutedAction{
            ActionDef: action,
            Result: actionResult,
            ExecutionTime: workflow.Now(ctx),
        })
    }
    
    // 4. 如果需要补偿，逆序执行补偿操作
    if compensationNeeded {
        logger.Info("开始执行补偿操作", "actionsToCompensate", len(executedActions))
        
        compensationOptions := workflow.ActivityOptions{
            StartToCloseTimeout: 30 * time.Second, // 补偿操作给予更长的超时时间
            RetryPolicy: &temporal.RetryPolicy{
                MaximumAttempts: 5, // 补偿操作给予更多重试次数
            },
        }
        compensationCtx := workflow.WithActivityOptions(ctx, compensationOptions)
        
        // 逆序执行补偿操作
        for i := len(executedActions) - 1; i >= 0; i-- {
            action := executedActions[i]
            
            // 跳过不需要补偿的操作
            if !action.ActionDef.NeedsCompensation {
                continue
            }
            
            logger.Info("执行补偿操作", "action", i, "device", action.ActionDef.DeviceID)
            
            compensationParams := CompensationParams{
                OriginalAction: action.ActionDef,
                OriginalResult: action.Result,
                ExecutionTime: action.ExecutionTime,
            }
            
            err = workflow.ExecuteActivity(compensationCtx, activities.ExecuteCompensatingAction, 
                compensationParams).Get(compensationCtx, nil)
            
            if err != nil {
                logger.Error("补偿操作失败", "action", i, "error", err)
                // 即使补偿操作失败，也继续尝试其他补偿
            }
        }
        
        // 添加失败记录
        _ = workflow.ExecuteActivity(ctx, activities.RecordSceneExecutionFailure, RecordFailureParams{
            SceneID: params.SceneID,
            Error: finalError.Error(),
            PartialExecution: executedActions,
            CompensationPerformed: true,
        }).Get(ctx, nil)
        
        return finalError
    }
    
    // 5. A事件触发更新成功
    logger.Info("场景执行成功", "actionsExecuted", len(executedActions))
    
    // 记录执行历史
    _ = workflow.ExecuteActivity(ctx, activities.RecordSceneExecutionSuccess, RecordSuccessParams{
        SceneID: params.SceneID,
        ActionsExecuted: executedActions,
        ExecutionDuration: workflow.Now(ctx).Sub(workflow.GetInfo(ctx).StartTime),
    }).Get(ctx, nil)
    
    return nil
}
```

## 五、复杂现实问题到工作流模型的映射

### 1. 能源管理系统在智能家居中的实现

```go
// 智能能源管理工作流
func SmartEnergyManagementWorkflow(ctx workflow.Context, params EnergyManagementParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动智能能源管理工作流", "homeID", params.HomeID)
    
    // 常量定义
    const (
        HIGH_ENERGY_PRICE_THRESHOLD = 0.15  // 每度电价格高于此值视为高峰
        BATTERY_HIGH_THRESHOLD = 0.8        // 电池充电80%以上视为高
        BATTERY_LOW_THRESHOLD = 0.2         // 电池低于20%视为低
    )
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 15 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 持续监控能源状态的周期性循环
    executionTimeout := workflow.Now(ctx).Add(params.Duration)
    checkInterval := 5 * time.Minute
    if params.CheckInterval > 0 {
        checkInterval = params.CheckInterval
    }
    
    // 初始化上次操作时间映射
    lastActionTime := make(map[string]time.Time)
    
    // 创建定时器
    timer := workflow.NewTimer(ctx, workflow.Now(ctx))
    
    for workflow.Now(ctx).Before(executionTimeout) {
        // 等待定时器触发
        _ = timer.Future.Get(ctx, nil)
        
        // 一次能源检查与优化的完整流程
        err := energyCheckAndOptimize(ctx, params.HomeID, lastActionTime)
        if err != nil {
            logger.Error("能源检查与优化失败", "error", err)
            // 失败不终止工作流，继续下一次检查
        }
        
        // 设置下一次检查时间
        timer = workflow.NewTimer(ctx, workflow.Now(ctx).Add(checkInterval))
    }
    
    logger.Info("能源管理工作流完成", "duration", params.Duration)
    return nil
}

// 单次能源检查与优化
func energyCheckAndOptimize(ctx workflow.Context, homeID string, lastActionTime map[string]time.Time) error {
    logger := workflow.GetLogger(ctx)
    
    // 1. 数据收集 - 获取当前能源状态
    var energyStatus EnergyStatus
    err := workflow.ExecuteActivity(ctx, activities.GetHomeEnergyStatus, 
        homeID).Get(ctx, &energyStatus)
    if err != nil {
        return fmt.Errorf("获取能源状态失败: %w", err)
    }
    
    // 2. 基于多条件的控制流决策树
    actions := []string{} // 要采取的操作列表
    
    // 2.1 光伏发电足够 且 电价低时充电
    if energyStatus.SolarProduction > energyStatus.CurrentConsumption*1.2 {
        if energyStatus.BatteryLevel < BATTERY_HIGH_THRESHOLD {
            // 有多余太阳能 且 电池未满
            actions = append(actions, "charge_battery_from_solar")
        }
        
        if energyStatus.GridElectricityPrice < 0.1 { // 电价低于0.1元/度
            // 有多余太阳能 且 可以卖电
            actions = append(actions, "sell_to_grid")
        }
    }
    
    // 2.2 峰电价时段使用电池供电
    if energyStatus.GridElectricityPrice > HIGH_ENERGY_PRICE_THRESHOLD &&
       energyStatus.BatteryLevel > BATTERY_LOW_THRESHOLD {
        actions = append(actions, "use_battery_power")
    }
    
    // 2.3 夜间低谷电价充电
    currentHour := workflow.Now(ctx).Hour()
    if (currentHour >= 22 || currentHour <= 6) && 
       energyStatus.GridElectricityPrice < 0.1 &&
       energyStatus.BatteryLevel < BATTERY_HIGH_THRESHOLD {
        actions = append(actions, "charge_battery_from_grid")
    }
    
    // 2.4 负载管理 - 高峰时段降低用电量
    if energyStatus.GridElectricityPrice > HIGH_ENERGY_PRICE_THRESHOLD &&
       energyStatus.CurrentConsumption > energyStatus.AvgConsumption*1.2 {
        
        // 查找可延迟的设备
        var deferrableDevices []DeferrableDevice
        err := workflow.ExecuteActivity(ctx, activities.GetDeferrableDevices, 
            homeID).Get(ctx, &deferrableDevices)
        
        if err == nil && len(deferrableDevices) > 0 {
            for _, device := range deferrableDevices {
                // 检查设备在最近30分钟内是否已经被延迟过
                lastTime, exists := lastActionTime["defer_"+device.ID]
                if !exists || workflow.Now(ctx).Sub(lastTime) > 30*time.Minute {
                    actions = append(actions, "defer_device_"+device.ID)
                    lastActionTime["defer_"+device.ID] = workflow.Now(ctx)
                }
            }
        }
    }
    
    // 3. 执行决策操作
    for _, action := range actions {
        var actionParams interface{}
        
        // 根据操作类型准备参数
        if strings.HasPrefix(action, "defer_device_") {
            deviceID := strings.TrimPrefix(action, "defer_device_")
            actionParams = DeferDeviceParams{
                HomeID: homeID,
                DeviceID: deviceID,
                DeferDuration: 2 * time.Hour,
            }
        } else if action == "use_battery_power" {
            actionParams = PowerSourceParams{
                HomeID: homeID,
                Source: "battery",
            }
        } else if action == "charge_battery_from_solar" {
            actionParams = BatteryChargeParams{
                HomeID: homeID,
                Source: "solar",
                ChargeRate: 0.8, // 80%的太阳能用来充电
            }
        } else if action == "charge_battery_from_grid" {
            actionParams = BatteryChargeParams{
                HomeID: homeID,
                Source: "grid",
                ChargeRate: 0.6, // 60%速率充电
            }
        } else if action == "sell_to_grid" {
            actionParams = SellToGridParams{
                HomeID: homeID,
                Percentage: 0.7, // 70%的多余电力卖回电网
            }
        }
        
        // 执行相应的活动
        err := workflow.ExecuteActivity(ctx, getActivityForAction(action), 
            actionParams).Get(ctx, nil)
        
        if err != nil {
            logger.Error("能源操作执行失败", "action", action, "error", err)
            // 单个操作失败不影响其他操作
        } else {
            logger.Info("能源操作执行成功", "action", action)
        }
    }
    
    // 4. 记录能源状态和决策
    _ = workflow.ExecuteActivity(ctx, activities.RecordEnergyDecision, EnergyDecisionRecord{
        HomeID: homeID,
        Timestamp: workflow.Now(ctx),
        EnergyStatus: energyStatus,
        ActionsPerformed: actions,
    }).Get(ctx, nil)
    
    return nil
}

// 辅助函数：根据操作名获取相应的活动函数
func getActivityForAction(action string) interface{} {
    if strings.HasPrefix(action, "defer_device_") {
        return activities.DeferDevice
    } else if action == "use_battery_power" {
        return activities.SetPowerSource
    } else if action == "charge_battery_from_solar" || action == "charge_battery_from_grid" {
        return activities.ChargeBattery
    } else if action == "sell_to_grid" {
        return activities.SellEnergyToGrid
    }
    return nil
}
```

### 2. 分布式场景协调 - 多房间、多设备复杂场景

```go
// 多房间协调工作流 - 例如"电影之夜"场景
func MovieNightWorkflow(ctx workflow.Context, params MovieNightParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动电影之夜工作流", "homeID", params.HomeID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 20 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 数据流 - 获取场景所需房间和设备信息
    var movieRooms MovieRoomConfig
    err := workflow.ExecuteActivity(ctx, activities.GetMovieNightRooms, 
        params.HomeID).Get(ctx, &movieRooms)
    if err != nil {
        return fmt.Errorf("获取电影房间配置失败: %w", err)
    }
    
    // 2. 控制流 - 按区域划分不同子工作流
    
    // 2.1 启动主娱乐区域准备子工作流（可能是客厅或媒体室）
    entertainmentCWO := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("movie-main-room-%s-%s", 
            params.HomeID, workflow.Now(ctx).Format("20060102-150405")),
    }
    entertainmentCtx := workflow.WithChildOptions(ctx, entertainmentCWO)
    
    entertainmentFuture := workflow.ExecuteChildWorkflow(entertainmentCtx, 
        PrepareEntertainmentRoomWorkflow, EntertainmentRoomParams{
            HomeID: params.HomeID,
            RoomID: movieRooms.MainRoomID,
            ContentSource: params.ContentSource,
            ContentID: params.ContentID,
            LightingScene: "movie",
            AudioLevel: params.Volume,
        })
    
    // 2.2 同时启动连接区域准备子工作流（例如走廊、楼梯）
    connectorCWO := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("movie-connector-rooms-%s-%s", 
            params.HomeID, workflow.Now(ctx).Format("20060102-150405")),
    }
    connectorCtx := workflow.WithChildOptions(ctx, connectorCWO)
    
    connectorFuture := workflow.ExecuteChildWorkflow(connectorCtx, 
        PrepareConnectorAreasWorkflow, ConnectorAreasParams{
            HomeID: params.HomeID,
            RoomIDs: movieRooms.ConnectorAreaIDs,
            LightingLevel: 30, // 低光照
        })
    
    // 2.3 为厨房准备零食区域子工作流
    kitchenCWO := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("movie-kitchen-prep-%s-%s", 
            params.HomeID, workflow.Now(ctx).Format("20060102-150405")),
    }
    kitchenCtx := workflow.WithChildOptions(ctx, kitchenCWO)
    
    kitchenFuture := workflow.ExecuteChildWorkflow(kitchenCtx, 
        PrepareKitchenWorkflow, KitchenParams{
            HomeID: params.HomeID,
            RoomID: movieRooms.KitchenID,
            PrepMode: "snacks",
            LightingScene: "cooking",
        })
    
    // 3. 执行流 - 等待所有区域准备就绪
    var errs []error
    
    // 等待主娱乐区域
    err = entertainmentFuture.Get(ctx, nil)
    if err != nil {
        errs = append(errs, fmt.Errorf("主娱乐区域准备失败: %w", err))
    }
    
    // 等待连接区域
    err = connectorFuture.Get(ctx, nil)
    if err != nil {
        errs = append(errs, fmt.Errorf("连接区域准备失败: %w", err))
    }
    
    // 等待厨房准备
    err = kitchenFuture.Get(ctx, nil)
    if err != nil {
        errs = append(errs, fmt.Errorf("厨房准备失败: %w", err))
    }
    
    // 4. 容错与一致性 - 处理部分失败情况
    if len(errs) > 0 {
        logger.Error("部分区域准备失败", "errors", errs)
        
        // 4.1 尝试继续执行关键步骤 - 至少让主娱乐区域工作
        if !entertainmentFuture.GetError(ctx, nil) {
            logger.Info("主娱乐区域已就绪，继续执行")
        } else {
            // 主区域失败，尝试紧急恢复
            emergencyCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
                StartToCloseTimeout: 30 * time.Second,
            })
            
            err = workflow.ExecuteActivity(emergencyCtx, activities.EmergencyPrepareMainRoom, 
                movieRooms.MainRoomID).Get(emergencyCtx, nil)
            
            if err != nil {
                // 如果紧急恢复也失败，通知用户并终止
                _ = workflow.ExecuteActivity(ctx, activities.SendPriorityNotification, NotificationParams{
                    UserID: params.UserID,
                    Title: "电影之夜准备失败",
                    Message: "无法准备主娱乐区域，请手动设置。",
                    Priority: "high",
                }).Get(ctx, nil)
                
                return fmt.Errorf("电影之夜场景执行失败: %v", errs)
            }
        }
    }
    
    // 5. 设置信号处理（响应用户反馈）
    // 创建用于接收音量调整信号的通道
    volumeSignalChan := workflow.GetSignalChannel(ctx, "adjust_volume_signal")
    
    // 创建用于接收暂停/继续信号的通道
    pauseSignalChan := workflow.GetSignalChannel(ctx, "pause_resume_signal")
    
    // 创建监控场景结束的选择器
    sel := workflow.NewSelector(ctx)
    
    // 电影持续时间定时器（假设电影2小时）
    movieDuration := 2 * time.Hour
    if params.Duration > 0 {
        movieDuration = params.Duration
    }
    
    movieEndTimer := workflow.NewTimer(ctx, workflow.Now(ctx).Add(movieDuration))
    
    // 添加音量调整信号处理
    sel.AddReceive(volumeSignalChan, func(c workflow.ReceiveChannel, more bool) {
        var volumeSignal VolumeAdjustSignal
        c.Receive(ctx, &volumeSignal)
        
        // 调整音量
        _ = workflow.ExecuteActivity(ctx, activities.AdjustEntertainmentVolume, AdjustVolumeParams{
            RoomID: movieRooms.MainRoomID,
            NewVolume: volumeSignal.Level,
        }).Get(ctx, nil)
    })
    
    // 添加暂停/继续信号处理
    sel.AddReceive(pauseSignalChan, func(c workflow.ReceiveChannel, more bool) {
        var pauseSignal PauseResumeSignal
        c.Receive(ctx, &pauseSignal)
        
        if pauseSignal.Action == "pause" {
            // 暂停媒体播放
            _ = workflow.ExecuteActivity(ctx, activities.ControlMediaPlayback, MediaControlParams{
                RoomID: movieRooms.MainRoomID,
                Action: "pause",
            }).Get(ctx, nil)
            
            // 提高照明亮度
            _ = workflow.ExecuteActivity(ctx, activities.AdjustRoomLighting, LightingParams{
                RoomID: movieRooms.MainRoomID,
                Scene: "pause",
                Brightness: 40,
            }).Get(ctx, nil)
        } else {
            // 继续媒体播放
            _ = workflow.ExecuteActivity(ctx, activities.ControlMediaPlayback, MediaControlParams{
                RoomID: movieRooms.MainRoomID,
                Action: "play",
            }).Get(ctx, nil)
            
            // 恢复电影照明
            _ = workflow.ExecuteActivity(ctx, activities.AdjustRoomLighting, LightingParams{
                RoomID: movieRooms.MainRoomID,
                Scene: "movie",
                Brightness: 10,
            }).Get(ctx, nil)
        }
    })
    
    // 添加定时器处理
    sel.AddFuture(movieEndTimer.Future, func(f workflow.Future) {
        _ = f.Get(ctx, nil)
        logger.Info("电影时间结束，开始清理流程")
    })
    
    // 无限循环，直到电影结束
    for {
        sel.Select(ctx)
        
        // 检查是否定时器已触发
        if movieEndTimer.Future.IsReady() {
            break
        }
    }
    
    // 6. 场景结束 - 恢复房间状态
    // 启动清理子工作流
    cleanupCWO := workflow.ChildWorkflowOptions{
        WorkflowID: fmt.Sprintf("movie-cleanup-%s-%s", 
            params.HomeID, workflow.Now(ctx).Format("20060102-150405")),
    }
    cleanupCtx := workflow.WithChildOptions(ctx, cleanupCWO)
    
    return workflow.ExecuteChildWorkflow(cleanupCtx, 
        MovieNightCleanupWorkflow, CleanupParams{
            HomeID: params.HomeID,
            RoomIDs: append([]string{movieRooms.MainRoomID, movieRooms.KitchenID}, 
                movieRooms.ConnectorAreaIDs...),
            RestoreToDefault: params.RestoreToDefault,
        }).Get(cleanupCtx, nil)
}
```

## 六、工作流中需要解决的一致性问题

### 1. 数据流与一致性保障模式

```text
+------------------------+          +------------------------+
| 云端数据层              |          | 边缘数据层             |
|                        |          |                        |
| - 全局场景定义          |<-------->| - 本地场景定义缓存      |
| - 历史执行记录          |          | - 最近执行历史         |
| - 用户配置              |          | - 设备状态缓存         |
| - 分析数据              |          | - 触发条件表达式       |
| - AI推理结果            |          |                        |
+--------^----------------+          +----------------^-------+
         |                                           |
         |                                           |
         |                                           |
+--------v----------------+          +----------------v-------+
| 工作流一致性模式         |          | 设备层数据             |
|                        |          |                        |
| - 具有状态版本的事件溯源 |          | - 设备当前状态         |
| - 优先级冲突解决        |          | - 设备阈值和限制       |
| - 空间锁定策略          |<-------->| - 设备操作缓冲区       |
| - 单调写确认            |          | - 设备固件版本         |
| - 幂等性操作设计        |          |                        |
+------------------------+          +------------------------+
```

#### 场景故障恢复一致性管理工作流

```go
// 智能家居场景一致性管理工作流
func SceneConsistencyManagerWorkflow(ctx workflow.Context, params ConsistencyManagerParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动场景一致性管理工作流", "homeID", params.HomeID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 15 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
            InitialInterval: 2 * time.Second,
            BackoffCoefficient: 1.5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 初始化 - 加载一致性配置
    var consistencyConfig ConsistencyConfig
    err := workflow.ExecuteActivity(ctx, activities.GetConsistencyConfig, 
        params.HomeID).Get(ctx, &consistencyConfig)
    if err != nil {
        return fmt.Errorf("获取一致性配置失败: %w", err)
    }
    
    // 2. 设置定期检查和监控
    checkInterval := 30 * time.Minute
    if consistencyConfig.CheckInterval > 0 {
        checkInterval = consistencyConfig.CheckInterval
    }
    
    timer := workflow.NewTimer(ctx, workflow.Now(ctx))
    
    // 设置接收紧急一致性检查信号的通道
    emergencyCheckChan := workflow.GetSignalChannel(ctx, "emergency_consistency_check")
    
    // 3. 循环检查与恢复
    for {
        // 使用选择器等待定时器或紧急检查信号
        selector := workflow.NewSelector(ctx)
        
        // 添加定时器处理
        selector.AddFuture(timer.Future, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            logger.Info("执行定期一致性检查")
        })
        
        // 添加紧急检查信号处理
        selector.AddReceive(emergencyCheckChan, func(c workflow.ReceiveChannel, more bool) {
            var signalData EmergencyCheckSignal
            c.Receive(ctx, &signalData)
            logger.Info("收到紧急一致性检查信号", "reason", signalData.Reason)
        })
        
        // 等待任一事件
        selector.Select(ctx)
        
        // 4. 执行一致性检查与修复流程
        err := performConsistencyCheck(ctx, params.HomeID, consistencyConfig)
        if err != nil {
            logger.Error("一致性检查失败，但继续监控", "error", err)
        }
        
        // 重置定时器
        timer = workflow.NewTimer(ctx, workflow.Now(ctx).Add(checkInterval))
    }
    
    // 注意：此工作流设计为长时间运行，实际上不会到达此处
    return nil
}

// 执行一致性检查与修复
func performConsistencyCheck(ctx workflow.Context, homeID string, config ConsistencyConfig) error {
    logger := workflow.GetLogger(ctx)
    
    // 1. 获取云端和边缘节点的场景定义状态
    var cloudScenes []SceneDefinitionStatus
    var edgeScenes []SceneDefinitionStatus
    
    errCloud := workflow.ExecuteActivity(ctx, activities.GetCloudSceneDefinitions, 
        homeID).Get(ctx, &cloudScenes)
    errEdge := workflow.ExecuteActivity(ctx, activities.GetEdgeSceneDefinitions, 
        homeID).Get(ctx, &edgeScenes)
    
    if errCloud != nil || errEdge != nil {
        return fmt.Errorf("获取场景定义失败: cloud=%v, edge=%v", errCloud, errEdge)
    }
    
    // 2. 识别并解决场景定义不一致
    var sceneUpdates []SceneDefinitionUpdate
    var sceneUpdatesNeeded bool
    
    for _, cloudScene := range cloudScenes {
        // 在边缘场景中查找对应场景
        edgeSceneFound := false
        for _, edgeScene := range edgeScenes {
            if cloudScene.ID == edgeScene.ID {
                edgeSceneFound = true
                
                // 检查版本是否匹配
                if cloudScene.Version > edgeScene.Version {
                    // 云端版本较新，需要更新边缘
                    sceneUpdates = append(sceneUpdates, SceneDefinitionUpdate{
                        SceneID: cloudScene.ID,
                        SourceVersion: edgeScene.Version,
                        TargetVersion: cloudScene.Version,
                        UpdateTarget: "edge",
                    })
                    sceneUpdatesNeeded = true
                } else if edgeScene.Version > cloudScene.Version && 
                          edgeScene.LastModified.After(cloudScene.LastModified) {
                    // 边缘版本较新且更晚修改，需要更新云端
                    sceneUpdates = append(sceneUpdates, SceneDefinitionUpdate{
                        SceneID: cloudScene.ID,
                        SourceVersion: cloudScene.Version,
                        TargetVersion: edgeScene.Version,
                        UpdateTarget: "cloud",
                    })
                    sceneUpdatesNeeded = true
                }
                break
            }
        }
        
        // 边缘节点没有此场景，需要添加
        if !edgeSceneFound {
            sceneUpdates = append(sceneUpdates, SceneDefinitionUpdate{
                SceneID: cloudScene.ID,
                SourceVersion: 0,
                TargetVersion: cloudScene.Version,
                UpdateTarget: "edge",
            })
            sceneUpdatesNeeded = true
        }
    }
    
    // 检查边缘场景中存在但云端不存在的场景
    for _, edgeScene := range edgeScenes {
        cloudSceneFound := false
        for _, cloudScene := range cloudScenes {
            if edgeScene.ID == cloudScene.ID {
                cloudSceneFound = true
                break
            }
        }
        
        if !cloudSceneFound && !edgeScene.IsLocalOnly {
            // 边缘有，云端没有，且不是仅本地场景，需要同步到云端
            sceneUpdates = append(sceneUpdates, SceneDefinitionUpdate{
                SceneID: edgeScene.ID,
                SourceVersion: 0,
                TargetVersion: edgeScene.Version,
                UpdateTarget: "cloud",
            })
            sceneUpdatesNeeded = true
        }
    }
    
    // 3. 执行场景定义同步
    if sceneUpdatesNeeded {
        logger.Info("发现场景定义不一致，执行同步", "updates", len(sceneUpdates))
        
        for _, update := range sceneUpdates {
            logger.Info("同步场景定义", "sceneID", update.SceneID, "target", update.UpdateTarget)
            
            err := workflow.ExecuteActivity(ctx, activities.SyncSceneDefinition, 
                update).Get(ctx, nil)
            
            if err != nil {
                logger.Error("同步场景失败", "sceneID", update.SceneID, "error", err)
                // 继续处理其他场景
            }
        }
    }
    
    // 4. 检查设备状态一致性
    var devicesNeedingSync []string
    err := workflow.ExecuteActivity(ctx, activities.IdentifyInconsistentDevices, 
        homeID).Get(ctx, &devicesNeedingSync)
    
    if err != nil {
        logger.Error("识别不一致设备失败", "error", err)
    } else if len(devicesNeedingSync) > 0 {
        logger.Info("发现设备状态不一致", "devices", len(devicesNeedingSync))
        
        // 启动子工作流处理设备状态同步
        cwo := workflow.ChildWorkflowOptions{
            WorkflowID: fmt.Sprintf("device-sync-%s-%s", 
                homeID, workflow.Now(ctx).Format("20060102-150405")),
        }
        syncCtx := workflow.WithChildOptions(ctx, cwo)
        
        _ = workflow.ExecuteChildWorkflow(syncCtx, DeviceStateSyncWorkflow, StateSyncParams{
            HomeID: homeID,
            DeviceIDs: devicesNeedingSync,
            SingleSync: true,
        }).Get(syncCtx, nil)
    }
    
    // 5. 验证执行中工作流状态的一致性
    var inconsistentWorkflows []WorkflowStateInfo
    err = workflow.ExecuteActivity(ctx, activities.CheckWorkflowStateConsistency, 
        homeID).Get(ctx, &inconsistentWorkflows)
    
    if err != nil {
        logger.Error("检查工作流状态一致性失败", "error", err)
    } else if len(inconsistentWorkflows) > 0 {
        logger.Info("发现工作流状态不一致", "workflows", len(inconsistentWorkflows))
        
        // 处理每个不一致的工作流
        for _, wf := range inconsistentWorkflows {
            logger.Info("处理不一致工作流", "workflowID", wf.WorkflowID)
            
            // 根据问题类型采取不同的修复策略
            switch wf.InconsistencyType {
            case "zombie": // 僵尸工作流 - 已完成但未清理
                err = workflow.ExecuteActivity(ctx, activities.TerminateZombieWorkflow, 
                    wf.WorkflowID).Get(ctx, nil)
                
            case "orphaned": // 孤儿工作流 - 父工作流丢失
                err = workflow.ExecuteActivity(ctx, activities.ReconcileOrphanedWorkflow, 
                    wf).Get(ctx, nil)
                
            case "duplicate": // 重复工作流 - 同一场景多个实例
                err = workflow.ExecuteActivity(ctx, activities.ResolveDuplicateWorkflows, 
                    wf).Get(ctx, nil)
                
            case "stalled": // 停滞工作流 - 长时间无进展
                err = workflow.ExecuteActivity(ctx, activities.RecoverStalledWorkflow, 
                    wf).Get(ctx, nil)
            }
            
            if err != nil {
                logger.Error("修复工作流状态失败", "workflowID", wf.WorkflowID, "error", err)
            }
        }
    }
    
    // 6. 清理过期的历史记录和临时数据
    if config.EnableHistoryCleanup {
        retention := 30 * 24 * time.Hour // 默认保留30天
        if config.HistoryRetention > 0 {
            retention = config.HistoryRetention
        }
        
        cutoffTime := workflow.Now(ctx).Add(-retention)
        
        err = workflow.ExecuteActivity(ctx, activities.CleanupExpiredHistory, CleanupParams{
            HomeID: homeID,
            CutoffTime: cutoffTime,
        }).Get(ctx, nil)
        
        if err != nil {
            logger.Error("清理历史记录失败", "error", err)
        }
    }
    
    return nil
}
```

### 2. 冲突解决模式：优先级、版本与空间锁定

```go
// 智能家居环境资源冲突解决工作流
func ResourceConflictResolutionWorkflow(ctx workflow.Context, params ConflictResolutionParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动资源冲突解决工作流", "roomID", params.RoomID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 10 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取当前房间的控制资源信息
    var roomResources RoomResourceInfo
    err := workflow.ExecuteActivity(ctx, activities.GetRoomResourceInfo, 
        params.RoomID).Get(ctx, &roomResources)
    if err != nil {
        return fmt.Errorf("获取房间资源信息失败: %w", err)
    }
    
    // 2. 获取当前活跃场景和工作流
    var activeFlows []ActiveWorkflowInfo
    err = workflow.ExecuteActivity(ctx, activities.GetActiveWorkflowsForRoom, 
        params.RoomID).Get(ctx, &activeFlows)
    if err != nil {
        return fmt.Errorf("获取活跃工作流失败: %w", err)
    }
    
    // 3. 识别资源冲突
    var conflicts []ResourceConflict
    for _, resource := range roomResources.Resources {
        // 查找对特定资源具有多个控制者的情况
        controllers := make(map[string][]string) // 资源ID -> 控制者工作流ID列表
        
        for _, flow := range activeFlows {
            for _, resourceID := range flow.ControlledResources {
                if resourceID == resource.ID {
                    controllers[resourceID] = append(controllers[resourceID], flow.WorkflowID)
                }
            }
        }
        
        // 如果有多个控制者，存在冲突
        for resourceID, flowIDs := range controllers {
            if len(flowIDs) > 1 {
                conflicts = append(conflicts, ResourceConflict{
                    ResourceID: resourceID,
                    ResourceType: resource.Type,
                    ContendingWorkflows: flowIDs,
                })
            }
        }
    }
    
    // 4. 解决每个资源冲突
    for _, conflict := range conflicts {
        logger.Info("解决资源冲突", "resource", conflict.ResourceID, "type", conflict.ResourceType)
        
        // 根据资源类型和冲突工作流确定解决策略
        strategy, err := determineConflictStrategy(ctx, conflict, activeFlows)
        if err != nil {
            logger.Error("确定冲突解决策略失败", "resource", conflict.ResourceID, "error", err)
            continue
        }
        
        // 4.1 基于优先级的资源分配 - 最高优先级场景胜出
        if strategy.Type == "priority_based" {
            logger.Info("使用优先级策略解决冲突", "winner", strategy.WinnerWorkflowID)
            
            // 向输家工作流发送信号，通知它们放弃资源控制
            for _, loserID := range strategy.LoserWorkflowIDs {
                err = workflow.SignalExternalWorkflow(ctx, loserID, "", "resource_yield", YieldResourceSignal{
                    ResourceID: conflict.ResourceID,
                    Reason: "higher_priority_workflow",
                    AlternativeResource: strategy.AlternativeResource,
                }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("发送让步信号失败", "workflow", loserID, "error", err)
                }
            }
        }
        
        // 4.2 基于共享协议的资源分配 - 资源可以共享，但需要协调设置
        else if strategy.Type == "shared_resource" {
            logger.Info("使用共享策略解决冲突", "resource", conflict.ResourceID)
            
            // 计算资源的共享参数
            err = workflow.ExecuteActivity(ctx, activities.CalculateSharedResourceParams, 
                SharedResourceRequest{
                    ResourceID: conflict.ResourceID,
                    WorkflowIDs: conflict.ContendingWorkflows,
                }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("计算共享资源参数失败", "error", err)
                continue
            }
            
            // 向所有相关工作流发送资源参数协商信号
            for _, workflowID := range conflict.ContendingWorkflows {
                err = workflow.SignalExternalWorkflow(ctx, workflowID, "", "resource_negotiate", 
                    ResourceNegotiateSignal{
                        ResourceID: conflict.ResourceID,
                        SharedParams: strategy.SharedParams,
                    }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("发送资源协商信号失败", "workflow", workflowID, "error", err)
                }
            }
        }
        
        // 4.3 基于时间片的资源分配 - 按时间顺序分配资源
        else if strategy.Type == "time_sliced" {
            logger.Info("使用时间片策略解决冲突", "resource", conflict.ResourceID)
            
            // 对于每个工作流，分配时间片
            timeSlices := strategy.TimeSlices
            for i, workflowID := range conflict.ContendingWorkflows {
                if i >= len(timeSlices) {
                    break
                }
                
                err = workflow.SignalExternalWorkflow(ctx, workflowID, "", "resource_time_slice", 
                    ResourceTimeSliceSignal{
                        ResourceID: conflict.ResourceID,
                        StartTime: timeSlices[i].StartTime,
                        EndTime: timeSlices[i].EndTime,
                    }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("发送时间片信号失败", "workflow", workflowID, "error", err)
                }
            }
        }
        
        // 4.4 基于版本的资源分配 - 最新版本的操作胜出
        else if strategy.Type == "version_based" {
            logger.Info("使用版本策略解决冲突", "winner", strategy.WinnerWorkflowID)
            
            // 记录版本冲突解决
            _ = workflow.ExecuteActivity(ctx, activities.RecordVersionResolution, VersionResolutionRecord{
                ResourceID: conflict.ResourceID,
                WinnerWorkflowID: strategy.WinnerWorkflowID,
                WinnerVersion: strategy.WinnerVersion,
                ResolvedAt: workflow.Now(ctx),
            }).Get(ctx, nil)
            
            // 向输家工作流发送信号
            for _, loserID := range strategy.LoserWorkflowIDs {
                err = workflow.SignalExternalWorkflow(ctx, loserID, "", "resource_yield", YieldResourceSignal{
                    ResourceID: conflict.ResourceID,
                    Reason: "newer_version_operation",
                }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("发送让步信号失败", "workflow", loserID, "error", err)
                }
            }
        }
        
        // 4.5 基于空间锁定的资源分配 - 明确定义资源划分边界
        else if strategy.Type == "spatial_locking" {
            logger.Info("使用空间锁定策略解决冲突", "resource", conflict.ResourceID)
            
            // 为每个工作流分配空间区域
            for i, workflowID := range conflict.ContendingWorkflows {
                if i >= len(strategy.SpatialAssignments) {
                    break
                }
                
                assignment := strategy.SpatialAssignments[i]
                err = workflow.SignalExternalWorkflow(ctx, workflowID, "", "spatial_assignment", 
                    SpatialAssignmentSignal{
                        ResourceID: conflict.ResourceID,
                        ZoneID: assignment.ZoneID,
                        Boundaries: assignment.Boundaries,
                    }).Get(ctx, nil)
                
                if err != nil {
                    logger.Error("发送空间分配信号失败", "workflow", workflowID, "error", err)
                }
            }
        }
    }
    
    return nil
}

// 确定冲突解决策略
func determineConflictStrategy(ctx workflow.Context, conflict ResourceConflict, activeFlows []ActiveWorkflowInfo) (ConflictStrategy, error) {
    var strategy ConflictStrategy
    
    // 获取冲突工作流的详细信息
    var flowDetails []WorkflowDetails
    for _, flowID := range conflict.ContendingWorkflows {
        for _, flow := range activeFlows {
            if flow.WorkflowID == flowID {
                flowDetails = append(flowDetails, WorkflowDetails{
                    WorkflowID: flowID,
                    SceneID: flow.SceneID,
                    Priority: flow.Priority,
                    StartTime: flow.StartTime,
                    Version: flow.Version,
                })
                break
            }
        }
    }
    
    // 根据资源类型选择不同的策略
    switch conflict.ResourceType {
    // 照明资源可以共享 - 计算平均亮度和颜色
    case "lighting":
        strategy.Type = "shared_resource"
        
        var sharedParams SharedResourceParams
        err := workflow.ExecuteActivity(ctx, activities.CalculateLightingParams, 
            flowDetails).Get(ctx, &sharedParams)
        if err != nil {
            return strategy, err
        }
        
        strategy.SharedParams = sharedParams
        
    // 温度控制通常基于优先级
    case "thermostat":
        strategy.Type = "priority_based"
        
        // 找出最高优先级的工作流
        highestPriority := -1
        var winnerID string
        var losers []string
        
        for _, detail := range flowDetails {
            if detail.Priority > highestPriority {
                if highestPriority >= 0 {
                    losers = append(losers, winnerID)
                }
                highestPriority = detail.Priority
                winnerID = detail.WorkflowID
            } else {
                losers = append(losers, detail.WorkflowID)
            }
        }
        
        strategy.WinnerWorkflowID = winnerID
        strategy.LoserWorkflowIDs = losers
        
    // 音频设备可能需要时间片分配
    case "audio":
        strategy.Type = "time_sliced"
        
        // 根据工作流开始时间排序
        sort.Slice(flowDetails, func(i, j int) bool {
            return flowDetails[i].StartTime.Before(flowDetails[j].StartTime)
        })
        
        // 为每个工作流分配时间片
        now := workflow.Now(ctx)
        sliceDuration := 10 * time.Minute
        
        for i, detail := range flowDetails {
            startTime := now.Add(time.Duration(i) * sliceDuration)
            endTime := startTime.Add(sliceDuration)
            
            strategy.TimeSlices = append(strategy.TimeSlices, TimeSlice{
                WorkflowID: detail.WorkflowID,
                StartTime: startTime,
                EndTime: endTime,
            })
        }
        
    // 窗户和窗帘可能使用版本控制
    case "window", "blinds":
        strategy.Type = "version_based"
        
        // 找出最新版本的操作
        highestVersion := int64(-1)
        var winnerID string
        var losers []string
        
        for _, detail := range flowDetails {
            if detail.Version > highestVersion {
                if highestVersion >= 0 {
                    losers = append(losers, winnerID)
                }
                highestVersion = detail.Version
                winnerID = detail.WorkflowID
            } else {
                losers = append(losers, detail.WorkflowID)
            }
        }
        
        strategy.WinnerWorkflowID = winnerID
        strategy.WinnerVersion = highestVersion
        strategy.LoserWorkflowIDs = losers
        
    // RGB照明条可以使用空间锁定
    case "rgb_strip":
        strategy.Type = "spatial_locking"
        
        // 将灯带划分为等份区域
        var spatialAssignments []SpatialAssignment
        totalLEDs := 300 // 假设一个灯带有300个LED
        segmentSize := totalLEDs / len(flowDetails)
        
        for i, detail := range flowDetails {
            startLED := i * segmentSize
            endLED := (i + 1) * segmentSize
            if i == len(flowDetails) - 1 {
                endLED = totalLEDs // 最后一个分配到末尾
            }
            
            spatialAssignments = append(spatialAssignments, SpatialAssignment{
                WorkflowID: detail.WorkflowID,
                ZoneID: fmt.Sprintf("segment_%d", i),
                Boundaries: fmt.Sprintf("%d-%d", startLED, endLED),
            })
        }
        
        strategy.SpatialAssignments = spatialAssignments
        
    default:
        // 默认使用优先级策略
        strategy.Type = "priority_based"
        
        // 简单找出最高优先级
        highestPriority := -1
        var winnerID string
        var losers []string
        
        for _, detail := range flowDetails {
            if detail.Priority > highestPriority {
                if highestPriority >= 0 {
                    losers = append(losers, winnerID)
                }
                highestPriority = detail.Priority
                winnerID = detail.WorkflowID
            } else {
                losers = append(losers, detail.WorkflowID)
            }
        }
        
        strategy.WinnerWorkflowID = winnerID
        strategy.LoserWorkflowIDs = losers
    }
    
    return strategy, nil
}
```

## 七、工作流设计中的关键挑战与解决方案

### 1. 长时间运行工作流与心跳机制

```go
// 用于长时间监控的工作流模式 - 例如能源使用监控
func LongRunningMonitorWorkflow(ctx workflow.Context, params MonitoringParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动长时间监控工作流", "type", params.Type, "duration", params.Duration)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 2 * time.Minute,
        HeartbeatTimeout: 30 * time.Second, // 添加心跳超时
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 初始化监控状态
    monitoringState := MonitoringState{
        StartTime: workflow.Now(ctx),
        LastCheckpoint: workflow.Now(ctx),
        CheckCount: 0,
        AlertsTriggered: 0,
    }
    
    // 2. 确定结束时间
    var endTime time.Time
    if params.Duration > 0 {
        endTime = workflow.Now(ctx).Add(params.Duration)
    } else {
        // 使用非常长的持续时间作为"无限"监控
        endTime = workflow.Now(ctx).AddDate(10, 0, 0) // 10年
    }
    
    // 3. 设置监控检查间隔
    checkInterval := 5 * time.Minute
    if params.CheckInterval > 0 {
        checkInterval = params.CheckInterval
    }
    
    // 4. 创建停止监控信号通道
    stopChan := workflow.GetSignalChannel(ctx, "stop_monitoring")
    
    // 5. 创建配置更新信号通道
    configUpdateChan := workflow.GetSignalChannel(ctx, "update_monitoring_config")
    
    // 6. 主监控循环
    for workflow.Now(ctx).Before(endTime) {
        // 创建选择器处理多种事件
        selector := workflow.NewSelector(ctx)
        
        // 设置下一次检查的定时器
        timer := workflow.NewTimer(ctx, workflow.Now(ctx).Add(checkInterval))
        
        // 添加定时器处理
        selector.AddFuture(timer.Future, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            logger.Info("执行定期监控检查", "checkCount", monitoringState.CheckCount+1)
        })
        
        // 添加停止信号处理
        selector.AddReceive(stopChan, func(c workflow.ReceiveChannel, more bool) {
            var stopSignal StopMonitoringSignal
            c.Receive(ctx, &stopSignal)
            logger.Info("收到停止监控信号", "reason", stopSignal.Reason)
            endTime = workflow.Now(ctx) // 立即结束循环
        })
        
        // 添加配置更新信号处理
        selector.AddReceive(configUpdateChan, func(c workflow.ReceiveChannel, more bool) {
            var configUpdate MonitoringConfigUpdate
            c.Receive(ctx, &configUpdate)
            logger.Info("收到监控配置更新", "newInterval", configUpdate.CheckInterval)
            
            // 更新检查间隔
            if configUpdate.CheckInterval > 0 {
                checkInterval = configUpdate.CheckInterval
            }
            
            // 取消现有定时器，将在下一轮循环创建新的定时器
            timer.Cancel()
        })
        
        // 等待任一事件发生
        selector.Select(ctx)
        
        // 如果收到停止信号，循环条件将失败
        if !workflow.Now(ctx).Before(endTime) {
            break
        }
        
        // 7. 执行监控活动并包含心跳机制
        var monitorResult MonitoringResult
        err := workflow.ExecuteActivity(ctx, activities.PerformMonitoringWithHeartbeat, 
            MonitoringRequest{
                Type: params.Type,
                HomeID: params.HomeID,
                CurrentState: monitoringState,
                Thresholds: params.Thresholds,
            }).Get(ctx, &monitorResult)
        
        // 8. 处理监控结果
        if err != nil {
            var heartbeatTimeoutErr *temporal.HeartbeatTimeoutError
            if errors.As(err, &heartbeatTimeoutErr) {
                logger.Warn("监控活动心跳超时，可能有硬件问题", "error", err)
                
                // 记录异常并触发告警
                _ = workflow.ExecuteActivity(ctx, activities.RecordMonitoringAnomaly, AnomalyReport{
                    Type: "heartbeat_timeout",
                    MonitorType: params.Type,
                    Timestamp: workflow.Now(ctx),
                    Details: fmt.Sprintf("监控活动心跳超时: %v", err),
                }).Get(ctx, nil)
                
                // 继续监控
                monitoringState.CheckCount++
                continue
            } else {
                logger.Error("监控活动执行失败", "error", err)
                
                // 记录错误但继续监控
                monitoringState.FailedChecks++
                
                // 如果连续失败次数过多，可以触发告警
                if monitoringState.FailedChecks >= 3 {
                    _ = workflow.ExecuteActivity(ctx, activities.TriggerMonitoringAlert, AlertRequest{
                        Type: "consecutive_failures",
                        MonitorType: params.Type,
                        Count: monitoringState.FailedChecks,
                        LastError: err.Error(),
                    }).Get(ctx, nil)
                }
                
                monitoringState.CheckCount++
                continue
            }
        }
        
        // 9. 处理正常监控结果
        monitoringState.CheckCount++
        monitoringState.LastCheckpoint = workflow.Now(ctx)
        monitoringState.LastResult = monitorResult
        monitoringState.FailedChecks = 0 // 重置连续失败计数
        
        // 10. 处理告警触发
        if len(monitorResult.TriggeredAlerts) > 0 {
            logger.Info("监控发现告警", "alerts", len(monitorResult.TriggeredAlerts))
            
            monitoringState.AlertsTriggered += len(monitorResult.TriggeredAlerts)
            
            // 启动子工作流处理每个告警
            for _, alert := range monitorResult.TriggeredAlerts {
                cwo := workflow.ChildWorkflowOptions{
                    WorkflowID: fmt.Sprintf("alert-handler-%s-%s", 
                        alert.ID, workflow.Now(ctx).Format("20060102-150405")),
                }
                alertCtx := workflow.WithChildOptions(ctx, cwo)
                
                // 异步启动告警处理工作流
                _ = workflow.ExecuteChildWorkflow(alertCtx, AlertHandlingWorkflow, AlertHandlingParams{
                    Alert: alert,
                    HomeID: params.HomeID,
                    MonitorType: params.Type,
                })
            }
        }
        
        // 11. 定期持久化监控状态（作为检查点）
        if monitoringState.CheckCount % 12 == 0 { // 大约每小时一次（假设5分钟检查间隔）
            err := workflow.ExecuteActivity(ctx, activities.PersistMonitoringState, 
                PersistStateRequest{
                    Type: params.Type,
                    HomeID: params.HomeID,
                    State: monitoringState,
                }).Get(ctx, nil)
            
            if err != nil {
                logger.Error("保存监控状态失败", "error", err)
            }
        }
    }
    
    // 12. 监控结束，执行清理
    logger.Info("长时间监控工作流结束", "checkCount", monitoringState.CheckCount, 
        "alertsTriggered", monitoringState.AlertsTriggered)
    
    // 记录监控统计信息
    _ = workflow.ExecuteActivity(ctx, activities.RecordMonitoringStats, MonitoringStats{
        Type: params.Type,
        HomeID: params.HomeID,
        StartTime: monitoringState.StartTime,
        EndTime: workflow.Now(ctx),
        TotalChecks: monitoringState.CheckCount,
        TotalAlerts: monitoringState.AlertsTriggered,
    }).Get(ctx, nil)
    
    return nil
}

// 带心跳的监控活动实现
func PerformMonitoringWithHeartbeat(ctx context.Context, request MonitoringRequest) (MonitoringResult, error) {
    logger := activity.GetLogger(ctx)
    logger.Info("开始执行监控活动", "type", request.Type)
    
    result := MonitoringResult{
        Timestamp: time.Now(),
    }
    
    // 1. 初始化监控数据收集
    var dataPoints []DataPoint
    var alertsToTrigger []Alert
    
    // 2. 根据监控类型执行不同的监控逻辑
    switch request.Type {
    case "energy":
        // 能源监控 - 可能需要读取多个设备的功耗数据
        devices, err := getEnergyConsumingDevices(request.HomeID)
        if err != nil {
            return result, fmt.Errorf("获取能源设备失败: %w", err)
        }
        
        // 每收集5个设备数据发送一次心跳
        for i, device := range devices {
            // 发送进度心跳
            if i > 0 && i % 5 == 0 {
                progress := float64(i) / float64(len(devices)) * 100.0
                activity.RecordHeartbeat(ctx, HeartbeatDetails{
                    Progress: progress,
                    DevicesProcessed: i,
                    TotalDevices: len(devices),
                })
            }
            
            // 检查是否请求取消
            if ctx.Err() != nil {
                return result, ctx.Err()
            }
            
            // 收集设备能源数据
            deviceData, err := getDeviceEnergyData(device.ID)
            if err != nil {
                logger.Error("获取设备能源数据失败", "device", device.ID, "error", err)
                continue
            }
            
            dataPoints = append(dataPoints, DataPoint{
                DeviceID: device.ID,
                Timestamp: time.Now(),
                Value: deviceData.PowerConsumption,
                Unit: "watts",
            })
            
            // 检查是否超过阈值
            if deviceData.PowerConsumption > getDeviceThreshold(device.ID, request.Thresholds) {
                alertsToTrigger = append(alertsToTrigger, Alert{
                    ID: uuid.New().String(),
                    Type: "high_energy_consumption",
                    DeviceID: device.ID,
                    Value: deviceData.PowerConsumption,
                    Threshold: getDeviceThreshold(device.ID, request.Thresholds),
                    Timestamp: time.Now(),
                })
            }
        }
        
    case "temperature":
        // 温度监控 - 收集各个房间的温度数据
        rooms, err := getHomeRooms(request.HomeID)
        if err != nil {
            return result, fmt.Errorf("获取房间列表失败: %w", err)
        }
        
        for i, room := range rooms {
            // 每收集3个房间数据发送一次心跳
            if i > 0 && i % 3 == 0 {
                progress := float64(i) / float64(len(rooms)) * 100.0
                activity.RecordHeartbeat(ctx, HeartbeatDetails{
                    Progress: progress,
                    RoomsProcessed: i,
                    TotalRooms: len(rooms),
                })
            }
            
            // 检查是否请求取消
            if ctx.Err() != nil {
                return result, ctx.Err()
            }
            
            // 获取房间温度
            tempData, err := getRoomTemperature(room.ID)
            if err != nil {
                logger.Error("获取房间温度失败", "room", room.ID, "error", err)
                continue
            }
            
            dataPoints = append(dataPoints, DataPoint{
                RoomID: room.ID,
                Timestamp: time.Now(),
                Value: tempData.Temperature,
                Unit: "celsius",
            })
            
            // 检查是否超出舒适范围
            if tempData.Temperature < request.Thresholds.MinTemp || 
               tempData.Temperature > request.Thresholds.MaxTemp {
                alertsToTrigger = append(alertsToTrigger, Alert{
                    ID: uuid.New().String(),
                    Type: "temperature_out_of_range",
                    RoomID: room.ID,
                    Value: tempData.Temperature,
                    MinThreshold: request.Thresholds.MinTemp,
                    MaxThreshold: request.Thresholds.MaxTemp,
                    Timestamp: time.Now(),
                })
            }
        }
        
    case "security":
        // 安全监控 - 检查门窗传感器、运动探测器等
        securityDevices, err := getSecurityDevices(request.HomeID)
        if err != nil {
            return result, fmt.Errorf("获取安全设备失败: %w", err)
        }
        
        for i, device := range securityDevices {
            // 发送心跳
            if i > 0 && i % 5 == 0 {
                activity.RecordHeartbeat(ctx, HeartbeatDetails{
                    Progress: float64(i) / float64(len(securityDevices)) * 100.0,
                    DevicesProcessed: i,
                    TotalDevices: len(securityDevices),
                })
            }
            
            // 检查设备状态
            deviceStatus, err := getSecurityDeviceStatus(device.ID)
            if err != nil {
                logger.Error("获取安全设备状态失败", "device", device.ID, "error", err)
                continue
            }
            
            dataPoints = append(dataPoints, DataPoint{
                DeviceID: device.ID,
                Timestamp: time.Now(),
                Value: deviceStatusToValue(deviceStatus),
                Status: deviceStatus.Status,
            })
            
            // 检查是否触发警报
            if isSecurityAlert(deviceStatus, request.Thresholds) {
                alertsToTrigger = append(alertsToTrigger, Alert{
                    ID: uuid.New().String(),
                    Type: "security_alert",
                    DeviceID: device.ID,
                    Status: deviceStatus.Status,
                    Timestamp: time.Now(),
                    Details: deviceStatus.Details,
                })
            }
        }
    }
    
    // 发送最终心跳
    activity.RecordHeartbeat(ctx, HeartbeatDetails{
        Progress: 100,
        Status: "completed",
        AlertCount: len(alertsToTrigger),
    })
    
    // 3. 整理返回结果
    result.DataPoints = dataPoints
    result.TriggeredAlerts = alertsToTrigger
    
    // 计算聚合统计数据
    result.AggregatedStats = calculateAggregatedStats(dataPoints, request.Type)
    
    return result, nil
}
```

### 2. 动态工作流与运行时决策

```go
// 自适应场景工作流 - 根据环境变化动态调整
func AdaptiveSceneWorkflow(ctx workflow.Context, params AdaptiveSceneParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动自适应场景工作流", "sceneID", params.SceneID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 15 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取场景定义
    var sceneDefinition AdaptiveSceneDefinition
    err := workflow.ExecuteActivity(ctx, activities.GetAdaptiveSceneDefinition, 
        params.SceneID).Get(ctx, &sceneDefinition)
    if err != nil {
        return fmt.Errorf("获取自适应场景定义失败: %w", err)
    }
    
    // 2. 初始化自适应参数
    adaptiveParams := AdaptiveParams{
        LightLevel: 50, // 默认亮度50%
        Temperature: 22.0, // 默认温度22°C
        AudioVolume: 30, // 默认音量30%
    }
    
    // 3. 执行初始环境评估
    var envContext EnvironmentContext
    err = workflow.ExecuteActivity(ctx, activities.EvaluateEnvironmentContext, 
        EnvironmentRequest{
            HomeID: params.HomeID,
            RoomID: params.RoomID,
            ContextFactors: sceneDefinition.ContextFactors,
        }).Get(ctx, &envContext)
    
    if err != nil {
        logger.Error("环境评估失败，使用默认参数", "error", err)
    } else {
        // 4. 基于环境初始化自适应参数
        adaptiveParams = calculateInitialAdaptiveParams(envContext, sceneDefinition)
    }
    
    // 5. 注册事件监听通道
    contextUpdateChan := workflow.GetSignalChannel(ctx, "context_update_signal")
    preferenceUpdateChan := workflow.GetSignalChannel(ctx, "preference_update_signal")
    terminateSignalChan := workflow.GetSignalChannel(ctx, "terminate_scene_signal")
    
    // 确定场景执行的结束时间
    var endTime time.Time
    if params.Duration > 0 {
        endTime = workflow.Now(ctx).Add(params.Duration)
    } else {
        // 默认持续1小时
        endTime = workflow.Now(ctx).Add(1 * time.Hour)
    }
    
    // 6. 初始设备操作循环 - 首次执行场景
    initialActions := determineDeviceActions(adaptiveParams, sceneDefinition)
    executeDeviceActions(ctx, initialActions)
    
    // 7. 主适配循环
    for workflow.Now(ctx).Before(endTime) {
        // 创建选择器处理多种事件
        selector := workflow.NewSelector(ctx)
        
        // 设置环境重新评估的定时器（每15分钟）
        reassessmentInterval := 15 * time.Minute
        if sceneDefinition.ReassessmentInterval > 0 {
            reassessmentInterval = sceneDefinition.ReassessmentInterval
        }
        
        reassessTimer := workflow.NewTimer(ctx, workflow.Now(ctx).Add(reassessmentInterval))
        
        // 添加定时器处理
        selector.AddFuture(reassessTimer.Future, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            logger.Info("执行定期环境重新评估")
        })
        
        // 添加环境上下文更新信号处理
        selector.AddReceive(contextUpdateChan, func(c workflow.ReceiveChannel, more bool) {
            var contextUpdate ContextUpdateSignal
            c.Receive(ctx, &contextUpdate)
            logger.Info("收到环境上下文更新", "factor", contextUpdate.Factor)
            
            // 更新环境上下文
            envContext.ContextValues[contextUpdate.Factor] = contextUpdate.Value
        })
        
        // 添加用户偏好更新信号处理
        selector.AddReceive(preferenceUpdateChan, func(c workflow.ReceiveChannel, more bool) {
            var prefUpdate PreferenceUpdateSignal
            c.Receive(ctx, &prefUpdate)
            logger.Info("收到用户偏好更新", "parameter", prefUpdate.Parameter)
            
            // 直接更新适应性参数
            updateAdaptiveParamsByPreference(&adaptiveParams, prefUpdate)
        })
        
        // 添加终止信号处理
        selector.AddReceive(terminateSignalChan, func(c workflow.ReceiveChannel, more bool) {
            var termSignal TerminateSignal
            c.Receive(ctx, &termSignal)
            logger.Info("收到场景终止信号", "reason", termSignal.Reason)
            
            // 设置结束时间为现在，使循环条件失效
            endTime = workflow.Now(ctx)
        })
        
        // 等待任一事件发生
        selector.Select(ctx)
        
        // 检查是否应该终止
        if !workflow.Now(ctx).Before(endTime) {
            break
        }
        
        // 8. 定期对环境进行重新评估
        if reassessTimer.Future.IsReady() {
            var newEnvContext EnvironmentContext
            err = workflow.ExecuteActivity(ctx, activities.EvaluateEnvironmentContext, 
                EnvironmentRequest{
                    HomeID: params.HomeID,
                    RoomID: params.RoomID,
                    ContextFactors: sceneDefinition.ContextFactors,
                }).Get(ctx, &newEnvContext)
            
            if err != nil {
                logger.Error("环境重新评估失败", "error", err)
            } else {
                // 更新环境上下文
                envContext = newEnvContext
            }
        }
        
        // 9. 动态决策 - 计算新的适应性参数
        newAdaptiveParams := calculateAdaptiveParams(adaptiveParams, envContext, sceneDefinition)
        
        // 10. 检测参数变化并执行设备操作
        if paramsChangedSignificantly(adaptiveParams, newAdaptiveParams, sceneDefinition.ChangeThresholds) {
            logger.Info("适应性参数发生显著变化，更新设备设置")
            
            // 更新适应性参数
            adaptiveParams = newAdaptiveParams
            
            // 确定新的设备操作
            actions := determineDeviceActions(adaptiveParams, sceneDefinition)
            
            // 执行设备操作
            executeDeviceActions(ctx, actions)
        }
    }
    
    // 11. 场景结束 - 执行清理
    logger.Info("自适应场景工作流结束")
    
    // 恢复默认设置或执行退出操作
    if sceneDefinition.HasExitActions {
        exitActions := sceneDefinition.ExitActions
        executeDeviceActions(ctx, exitActions)
    } else {
        // 默认清理 - 根据用户偏好恢复设备状态
        var defaultSettings []DeviceAction
        err := workflow.ExecuteActivity(ctx, activities.GetDefaultDeviceSettings, 
            params.RoomID).Get(ctx, &defaultSettings)
        
        if err != nil {
            logger.Error("获取默认设备设置失败", "error", err)
        } else {
            executeDeviceActions(ctx, defaultSettings)
        }
    }
    
    // 12. 记录自适应场景使用情况
    _ = workflow.ExecuteActivity(ctx, activities.RecordAdaptiveSceneUsage, AdaptiveSceneUsageRecord{
        SceneID: params.SceneID,
        StartTime: workflow.GetInfo(ctx).StartTime,
        EndTime: workflow.Now(ctx),
        RoomID: params.RoomID,
        AdaptationCount: 0, // 这里应该是真实的自适应次数
        UserInteractions: 0, // 这里应该是真实的用户交互次数
    }).Get(ctx, nil)
    
    return nil
}

// 辅助函数：计算初始自适应参数
func calculateInitialAdaptiveParams(envContext EnvironmentContext, sceneDefinition AdaptiveSceneDefinition) AdaptiveParams {
    params := AdaptiveParams{
        LightLevel: 50,
        Temperature: 22.0,
        AudioVolume: 30,
    }
    
    // 根据环境上下文应用自适应规则
    for _, rule := range sceneDefinition.AdaptiveRules {
        // 检查规则条件是否满足
        if evaluateRuleCondition(rule.Condition, envContext) {
            // 应用规则的参数调整
            applyRuleAdjustment(&params, rule.Adjustments)
        }
    }
    
    // 确保参数在有效范围内
    validateAndAdjustParams(&params, sceneDefinition.ParameterConstraints)
    
    return params
}

// 辅助函数：评估规则条件
func evaluateRuleCondition(condition RuleCondition, envContext EnvironmentContext) bool {
    // 获取条件因子的当前值
    factorValue, exists := envContext.ContextValues[condition.Factor]
    if !exists {
        return false
    }
    
    // 根据操作符评估条件
    switch condition.Operator {
    case "eq":
        return factorValue == condition.Value
    case "gt":
        return factorValue > condition.Value
    case "lt":
        return factorValue < condition.Value
    case "gte":
        return factorValue >= condition.Value
    case "lte":
        return factorValue <= condition.Value
    case "between":
        return factorValue >= condition.MinValue && factorValue <= condition.MaxValue
    default:
        return false
    }
}

// 辅助函数：应用规则调整
func applyRuleAdjustment(params *AdaptiveParams, adjustments []ParameterAdjustment) {
    for _, adj := range adjustments {
        switch adj.Parameter {
        case "light_level":
            if adj.AdjustmentType == "absolute" {
                params.LightLevel = adj.Value
            } else {
                params.LightLevel += adj.Value
            }
        case "temperature":
            if adj.AdjustmentType == "absolute" {
                params.Temperature = adj.Value
            } else {
                params.Temperature += adj.Value
            }
        case "audio_volume":
            if adj.AdjustmentType == "absolute" {
                params.AudioVolume = adj.Value
            } else {
                params.AudioVolume += adj.Value
            }
        }
    }
}

// 辅助函数：基于当前环境计算新的适应性参数
func calculateAdaptiveParams(currentParams AdaptiveParams, envContext EnvironmentContext, 
    sceneDefinition AdaptiveSceneDefinition) AdaptiveParams {
    
    // 复制当前参数作为初始值
    newParams := currentParams
    
    // 应用所有适用的规则
    for _, rule := range sceneDefinition.AdaptiveRules {
        if evaluateRuleCondition(rule.Condition, envContext) {
            applyRuleAdjustment(&newParams, rule.Adjustments)
        }
    }
    
    // 验证并调整参数范围
    validateAndAdjustParams(&newParams, sceneDefinition.ParameterConstraints)
    
    // 应用平滑过渡（避免突变）
    smoothParams(&newParams, currentParams, sceneDefinition.TransitionSettings)
    
    return newParams
}

// 辅助函数：验证并调整参数范围
func validateAndAdjustParams(params *AdaptiveParams, constraints ParameterConstraints) {
    // 亮度控制在0-100之间
    if params.LightLevel < constraints.MinLightLevel {
        params.LightLevel = constraints.MinLightLevel
    } else if params.LightLevel > constraints.MaxLightLevel {
        params.LightLevel = constraints.MaxLightLevel
    }
    
    // 温度控制在允许范围内
    if params.Temperature < constraints.MinTemperature {
        params.Temperature = constraints.MinTemperature
    } else if params.Temperature > constraints.MaxTemperature {
        params.Temperature = constraints.MaxTemperature
    }
    
    // 音量控制在0-100之间
    if params.AudioVolume < constraints.MinVolume {
        params.AudioVolume = constraints.MinVolume
    } else if params.AudioVolume > constraints.MaxVolume {
        params.AudioVolume = constraints.MaxVolume
    }
}

// 辅助函数：平滑参数过渡
func smoothParams(newParams *AdaptiveParams, currentParams AdaptiveParams, transitionSettings TransitionSettings) {
    // 计算最大允许变化量
    maxLightChange := transitionSettings.MaxLightChangePerStep
    maxTempChange := transitionSettings.MaxTempChangePerStep
    maxVolumeChange := transitionSettings.MaxVolumeChangePerStep
    
    // 限制亮度变化
    lightDiff := newParams.LightLevel - currentParams.LightLevel
    if math.Abs(lightDiff) > maxLightChange {
        if lightDiff > 0 {
            newParams.LightLevel = currentParams.LightLevel + maxLightChange
        } else {
            newParams.LightLevel = currentParams.LightLevel - maxLightChange
        }
    }
    
    // 限制温度变化
    tempDiff := newParams.Temperature - currentParams.Temperature
    if math.Abs(tempDiff) > maxTempChange {
        if tempDiff > 0 {
            newParams.Temperature = currentParams.Temperature + maxTempChange
        } else {
            newParams.Temperature = currentParams.Temperature - maxTempChange
        }
    }
    
    // 限制音量变化
    volumeDiff := newParams.AudioVolume - currentParams.AudioVolume
    if math.Abs(volumeDiff) > maxVolumeChange {
        if volumeDiff > 0 {
            newParams.AudioVolume = currentParams.AudioVolume + maxVolumeChange
        } else {
            newParams.AudioVolume = currentParams.AudioVolume - maxVolumeChange
        }
    }
}

// 辅助函数：检测参数是否发生显著变化
func paramsChangedSignificantly(oldParams, newParams AdaptiveParams, thresholds ChangeThresholds) bool {
    // 检查亮度变化
    if math.Abs(newParams.LightLevel - oldParams.LightLevel) >= thresholds.LightLevelThreshold {
        return true
    }
    
    // 检查温度变化
    if math.Abs(newParams.Temperature - oldParams.Temperature) >= thresholds.TemperatureThreshold {
        return true
    }
    
    // 检查音量变化
    if math.Abs(newParams.AudioVolume - oldParams.AudioVolume) >= thresholds.VolumeThreshold {
        return true
    }
    
    return false
}

// 辅助函数：更新适应性参数基于用户偏好
func updateAdaptiveParamsByPreference(params *AdaptiveParams, prefUpdate PreferenceUpdateSignal) {
    switch prefUpdate.Parameter {
    case "light_level":
        params.LightLevel = prefUpdate.Value
    case "temperature":
        params.Temperature = prefUpdate.Value
    case "audio_volume":
        params.AudioVolume = prefUpdate.Value
    }
}

// 辅助函数：根据适应性参数确定设备操作
func determineDeviceActions(params AdaptiveParams, sceneDefinition AdaptiveSceneDefinition) []DeviceAction {
    var actions []DeviceAction
    
    // 1. 转换灯光参数为具体设备操作
    if sceneDefinition.ControlsLighting {
        for _, lightDevice := range sceneDefinition.LightingDevices {
            actions = append(actions, DeviceAction{
                DeviceID: lightDevice.DeviceID,
                ActionType: "set_brightness",
                Value: params.LightLevel,
                Priority: lightDevice.Priority,
                Options: map[string]interface{}{
                    "transition_time": 2000, // 过渡时间（毫秒）
                },
            })
            
            // 如果设备支持色温调节
            if lightDevice.SupportsColorTemp {
                // 根据环境计算合适的色温
                colorTemp := calculateColorTemp(params.LightLevel, sceneDefinition.LightingPreferences)
                
                actions = append(actions, DeviceAction{
                    DeviceID: lightDevice.DeviceID,
                    ActionType: "set_color_temp",
                    Value: colorTemp,
                    Priority: lightDevice.Priority,
                })
            }
        }
    }
    
    // 2. 转换温度参数为恒温器操作
    if sceneDefinition.ControlsTemperature {
        for _, thermostat := range sceneDefinition.ThermostatDevices {
            // 设置目标温度
            actions = append(actions, DeviceAction{
                DeviceID: thermostat.DeviceID,
                ActionType: "set_temperature",
                Value: params.Temperature,
                Priority: thermostat.Priority,
            })
            
            // 设置适当的模式（制热/制冷）
            mode := "auto"
            if params.Temperature < 20 {
                mode = "heat"
            } else if params.Temperature > 25 {
                mode = "cool"
            }
            
            actions = append(actions, DeviceAction{
                DeviceID: thermostat.DeviceID,
                ActionType: "set_mode",
                StringValue: mode,
                Priority: thermostat.Priority,
            })
        }
    }
    
    // 3. 转换音频参数为音频设备操作
    if sceneDefinition.ControlsAudio {
        for _, audioDevice := range sceneDefinition.AudioDevices {
            actions = append(actions, DeviceAction{
                DeviceID: audioDevice.DeviceID,
                ActionType: "set_volume",
                Value: params.AudioVolume,
                Priority: audioDevice.Priority,
            })
            
            // 如果定义了场景的音频内容
            if audioDevice.PlayContentOnStart && len(sceneDefinition.AudioContent) > 0 {
                actions = append(actions, DeviceAction{
                    DeviceID: audioDevice.DeviceID,
                    ActionType: "play_content",
                    StringValue: sceneDefinition.AudioContent,
                    Priority: audioDevice.Priority,
                })
            }
        }
    }
    
    // 4. 添加额外的场景特定操作
    actions = append(actions, sceneDefinition.AdditionalActions...)
    
    // 5. 按优先级排序操作
    sort.Slice(actions, func(i, j int) bool {
        return actions[i].Priority > actions[j].Priority
    })
    
    return actions
}

// 辅助函数：根据亮度计算适合的色温
func calculateColorTemp(brightness float64, preferences LightingPreferences) float64 {
    // 基本逻辑：亮度低时使用温暖光（低色温），亮度高时使用冷光（高色温）
    // 色温范围通常从2000K（温暖）到6500K（冷光）
    
    if brightness < 30 {
        // 低亮度使用更温暖的光
        return preferences.LowBrightnessColorTemp
    } else if brightness > 70 {
        // 高亮度使用更冷的光
        return preferences.HighBrightnessColorTemp
    } else {
        // 中等亮度线性插值
        ratio := (brightness - 30) / 40 // 从30到70的比例
        return preferences.LowBrightnessColorTemp + ratio * (preferences.HighBrightnessColorTemp - preferences.LowBrightnessColorTemp)
    }
}

// 辅助函数：执行设备操作
func executeDeviceActions(ctx workflow.Context, actions []DeviceAction) {
    logger := workflow.GetLogger(ctx)
    
    // 按优先级分组操作，高优先级先执行
    priorityGroups := make(map[int][]DeviceAction)
    for _, action := range actions {
        priorityGroups[action.Priority] = append(priorityGroups[action.Priority], action)
    }
    
    // 从高到低按优先级执行
    priorities := make([]int, 0, len(priorityGroups))
    for priority := range priorityGroups {
        priorities = append(priorities, priority)
    }
    sort.Sort(sort.Reverse(sort.IntSlice(priorities)))
    
    for _, priority := range priorities {
        actionsInGroup := priorityGroups[priority]
        
        // 同一优先级的操作并行执行
        futures := make([]workflow.Future, len(actionsInGroup))
        for i, action := range actionsInGroup {
            futures[i] = workflow.ExecuteActivity(ctx, activities.ExecuteDeviceAction, action)
        }
        
        // 等待本组操作全部完成
        for i, future := range futures {
            err := future.Get(ctx, nil)
            if err != nil {
                logger.Error("设备操作执行失败", "action", actionsInGroup[i], "error", err)
            }
        }
    }
}
```

### 3. 工作流版本管理与向后兼容性

```go
// 版本化工作流实现
func VersionedSceneWorkflow(ctx workflow.Context, params SceneExecutionParams) error {
    logger := workflow.GetLogger(ctx)
    
    // 获取工作流版本信息
    version := workflow.GetVersion(ctx, "scene_workflow", workflow.DefaultVersion, 2)
    
    logger.Info("执行场景工作流", "sceneID", params.SceneID, "version", version)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 15 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取场景定义
    var sceneDefinition SceneDefinition
    err := workflow.ExecuteActivity(ctx, activities.GetSceneDefinition, 
        params.SceneID).Get(ctx, &sceneDefinition)
    if err != nil {
        return fmt.Errorf("获取场景定义失败: %w", err)
    }
    
    // 2. 版本化工作流逻辑
    if version == workflow.DefaultVersion {
        // 旧版本逻辑
        return executeSceneV1(ctx, params, sceneDefinition)
    } else {
        // 新版本逻辑（版本2）
        return executeSceneV2(ctx, params, sceneDefinition)
    }
}

// 版本1逻辑（旧版本，保持向后兼容）
func executeSceneV1(ctx workflow.Context, params SceneExecutionParams, sceneDefinition SceneDefinition) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("使用V1逻辑执行场景", "sceneID", params.SceneID)
    
    // 1. 顺序执行所有设备操作
    for i, action := range sceneDefinition.DeviceActions {
        logger.Info("执行设备操作", "device", action.DeviceID, "action", action.ActionType)
        
        err := workflow.ExecuteActivity(ctx, activities.ExecuteDeviceAction, 
            action).Get(ctx, nil)
        
        if err != nil {
            logger.Error("设备操作失败", "index", i, "error", err)
            
            // 在V1中，任何操作失败都会导致整个场景执行失败
            return fmt.Errorf("设备操作 %d 失败: %w", i, err)
        }
    }
    
    return nil
}

// 版本2逻辑（新版本，新功能和改进）
func executeSceneV2(ctx workflow.Context, params SceneExecutionParams, sceneDefinition SceneDefinition) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("使用V2逻辑执行场景", "sceneID", params.SceneID)
    
    // 1. 首先验证所有条件
    if len(sceneDefinition.Conditions) > 0 {
        logger.Info("评估场景条件", "count", len(sceneDefinition.Conditions))
        
        var conditionResult ConditionEvaluationResult
        err := workflow.ExecuteActivity(ctx, activities.EvaluateSceneConditions, 
            sceneDefinition.Conditions).Get(ctx, &conditionResult)
        
        if err != nil {
            logger.Error("条件评估失败", "error", err)
            return fmt.Errorf("场景条件评估失败: %w", err)
        }
        
        if !conditionResult.IsSatisfied {
            logger.Info("场景条件不满足，不执行操作", 
                "failedConditions", conditionResult.FailedConditions)
            return nil
        }
    }
    
    // 2. 按优先级分组设备操作
    priorityGroups := make(map[int][]DeviceAction)
    for _, action := range sceneDefinition.DeviceActions {
        priorityGroups[action.Priority] = append(priorityGroups[action.Priority], action)
    }
    
    // 3. 从高到低按优先级执行
    priorities := make([]int, 0, len(priorityGroups))
    for priority := range priorityGroups {
        priorities = append(priorities, priority)
    }
    sort.Sort(sort.Reverse(sort.IntSlice(priorities)))
    
    for _, priority := range priorities {
        actionsInGroup := priorityGroups[priority]
        logger.Info("执行优先级组设备操作", "priority", priority, "count", len(actionsInGroup))
        
        // 同一优先级的操作并行执行
        futures := make([]workflow.Future, len(actionsInGroup))
        for i, action := range actionsInGroup {
            futures[i] = workflow.ExecuteActivity(ctx, activities.ExecuteDeviceAction, action)
        }
        
        // 等待本组操作全部完成
        var errors []error
        for i, future := range futures {
            err := future.Get(ctx, nil)
            if err != nil {
                logger.Error("设备操作执行失败", "action", actionsInGroup[i], "error", err)
                errors = append(errors, err)
            }
        }
        
        // 在V2中，只有标记为关键的操作失败才会导致整个场景执行失败
        for i, err := range errors {
            if actionsInGroup[i].IsCritical {
                return fmt.Errorf("关键设备操作失败: %w", err)
            }
        }
    }
    
    // 4. V2新增：执行后续操作
    if params.ExecutePostActions && len(sceneDefinition.PostExecutionActions) > 0 {
        logger.Info("执行后续操作", "count", len(sceneDefinition.PostExecutionActions))
        
        // 执行后置操作（如发送通知、记录使用情况等）
        for _, postAction := range sceneDefinition.PostExecutionActions {
            // 使用动态活动选择
            err := executePostAction(ctx, postAction)
            if err != nil {
                logger.Error("后续操作执行失败", "action", postAction.Type, "error", err)
                // 后续操作失败不影响场景执行结果
            }
        }
    }
    
    // 5. V2新增：学习用户偏好
    if params.EnableLearning {
        logger.Info("记录场景执行以学习用户偏好")
        
        _ = workflow.ExecuteActivity(ctx, activities.RecordSceneExecution, RecordSceneParams{
            SceneID: params.SceneID,
            UserID: params.UserID,
            ExecutionTime: workflow.Now(ctx),
            Context: params.ExecutionContext,
        }).Get(ctx, nil)
    }
    
    return nil
}

// 基于操作类型动态选择活动
func executePostAction(ctx workflow.Context, action PostExecutionAction) error {
    switch action.Type {
    case "notify":
        return workflow.ExecuteActivity(ctx, activities.SendNotification, 
            action.Params).Get(ctx, nil)
    case "record_usage":
        return workflow.ExecuteActivity(ctx, activities.RecordUsageStatistics, 
            action.Params).Get(ctx, nil)
    case "schedule":
        return workflow.ExecuteActivity(ctx, activities.ScheduleFollowupScene, 
            action.Params).Get(ctx, nil)
    default:
        return fmt.Errorf("未知的后续操作类型: %s", action.Type)
    }
}

// 迁移工作流 - 将旧版本场景定义升级到新版本
func SceneMigrationWorkflow(ctx workflow.Context, params MigrationParams) error {
    logger := workflow.GetLogger(ctx)
    logger.Info("开始场景迁移工作流", "fromVersion", params.FromVersion, "toVersion", params.ToVersion)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second, // 迁移可能需要更长时间
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 5,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 获取需要迁移的场景列表
    var scenesToMigrate []string
    err := workflow.ExecuteActivity(ctx, activities.GetScenesByVersion, 
        params.FromVersion).Get(ctx, &scenesToMigrate)
    if err != nil {
        return fmt.Errorf("获取待迁移场景列表失败: %w", err)
    }
    
    logger.Info("找到需要迁移的场景", "count", len(scenesToMigrate))
    
    // 2. 批量处理，每批100个场景
    batchSize := 100
    if params.BatchSize > 0 {
        batchSize = params.BatchSize
    }
    
    totalScenes := len(scenesToMigrate)
    migratedCount := 0
    failedScenes := make(map[string]string) // 场景ID -> 错误信息
    
    for i := 0; i < totalScenes; i += batchSize {
        end := i + batchSize
        if end > totalScenes {
            end = totalScenes
        }
        
        batch := scenesToMigrate[i:end]
        logger.Info("处理场景批次", "batch", i/batchSize+1, "size", len(batch))
        
        // 并行处理批次中的场景
        futures := make([]workflow.Future, len(batch))
        for j, sceneID := range batch {
            futures[j] = workflow.ExecuteActivity(ctx, activities.MigrateScene, MigrateSceneParams{
                SceneID: sceneID,
                FromVersion: params.FromVersion,
                ToVersion: params.ToVersion,
                MigrationRules: params.MigrationRules,
            })
        }
        
        // 等待批次完成
        for j, future := range futures {
            sceneID := batch[j]
            var migrationResult MigrationResult
            err := future.Get(ctx, &migrationResult)
            
            if err != nil {
                logger.Error("场景迁移失败", "sceneID", sceneID, "error", err)
                failedScenes[sceneID] = err.Error()
            } else if !migrationResult.Success {
                logger.Error("场景迁移不成功", "sceneID", sceneID, "reason", migrationResult.FailureReason)
                failedScenes[sceneID] = migrationResult.FailureReason
            } else {
                migratedCount++
            }
        }
        
        // 进度汇报
        logger.Info("批次迁移完成", "progress", fmt.Sprintf("%d/%d", migratedCount, totalScenes))
    }
    
    // 3. 迁移总结
    if len(failedScenes) > 0 {
        logger.Error("场景迁移部分失败", "succeeded", migratedCount, "failed", len(failedScenes))
        
        // 记录失败的场景
        _ = workflow.ExecuteActivity(ctx, activities.RecordMigrationFailures, 
            failedScenes).Get(ctx, nil)
        
        return fmt.Errorf("场景迁移部分失败：成功 %d 个，失败 %d 个", migratedCount, len(failedScenes))
    }
    
    logger.Info("场景迁移全部成功", "total", totalScenes)
    
    // 4. 更新系统版本记录
    _ = workflow.ExecuteActivity(ctx, activities.UpdateSystemVersionRecord, VersionUpdateParams{
        ComponentName: "scene_definitions",
        FromVersion: params.FromVersion,
        ToVersion: params.ToVersion,
        MigratedCount: migratedCount,
        CompletedAt: workflow.Now(ctx),
    }).Get(ctx, nil)
    
    return nil
}
```

## 八、系统集成与协同工作

### 1. 智能家居系统的工作流层次结构

```text
顶层协调工作流 (Cloud)
+-- 场景编排工作流 (Cloud/Edge)
|   +-- 区域控制工作流 (Edge)
|   |   +-- 设备控制工作流 (Edge/Device)
|   |   +-- 数据采集工作流 (Edge/Device)
|   +-- 用户交互工作流 (Cloud/Edge)
|   +-- 外部服务集成工作流 (Cloud)
+-- 学习与优化工作流 (Cloud)
|   +-- 用户偏好分析工作流 (Cloud)
|   +-- 场景推荐工作流 (Cloud)
+-- 系统维护工作流 (Cloud/Edge)
    +-- 状态同步工作流 (Cloud/Edge)
    +-- 故障检测工作流 (Cloud/Edge)
    +-- 固件更新工作流 (Cloud/Edge/Device)
```

### 2. Temporal集成API层设计

```go
// 智能家居系统的Temporal工作流集成API
package homesystem

import (
    "context"
    "fmt"
    "time"
    
    "go.temporal.io/sdk/client"
    "go.temporal.io/sdk/worker"
)

// WorkflowManager 管理与Temporal工作流引擎的交互
type WorkflowManager struct {
    // Temporal客户端
    client client.Client
    
    // 工作器映射，按任务队列名称索引
    workers map[string]worker.Worker
    
    // 通用配置
    config WorkflowManagerConfig
    
    // 流程映射，将业务操作映射到工作流ID
    workflowMappings map[string]WorkflowMapping
}

// WorkflowManagerConfig 工作流管理器配置
type WorkflowManagerConfig struct {
    // Temporal服务地址
    TemporalAddress string
    
    // 命名空间
    Namespace string
    
    // 默认任务队列
    DefaultTaskQueue string
    
    // 边缘计算模式
    EdgeComputingMode bool
    
    // 每个工作器的轮询线程数
    PollerCount int
    
    // 重试策略
    DefaultRetryPolicy RetryPolicyConfig
}

// RetryPolicyConfig 重试策略配置
type RetryPolicyConfig struct {
    InitialInterval time.Duration
    MaximumInterval time.Duration
    MaximumAttempts int
    BackoffCoefficient float64
}

// WorkflowMapping 工作流映射定义
type WorkflowMapping struct {
    // 工作流类型名称
    WorkflowType string
    
    // 任务队列
    TaskQueue string
    
    // 工作流ID前缀
    IDPrefix string
    
    // 工作流执行超时
    ExecutionTimeout time.Duration
    
    // 运行模式（云端、边缘或者自动选择）
    RunMode string
}

// NewWorkflowManager 创建新的工作流管理器
func NewWorkflowManager(config WorkflowManagerConfig) (*WorkflowManager, error) {
    // 创建Temporal客户端
    clientOptions := client.Options{
        Namespace: config.Namespace,
    }
    c, err := client.NewClient(clientOptions)
    if err != nil {
        return nil, fmt.Errorf("无法创建Temporal客户端: %w", err)
    }
    
    wfm := &WorkflowManager{
        client:  c,
        workers: make(map[string]worker.Worker),
        config:  config,
        workflowMappings: make(map[string]WorkflowMapping),
    }
    
    return wfm, nil
}

// RegisterWorkflowMapping 注册业务操作到工作流的映射
func (wfm *WorkflowManager) RegisterWorkflowMapping(operationType string, mapping WorkflowMapping) {
    wfm.workflowMappings[operationType] = mapping
}

// StartWorkers 启动指定任务队列的工作器
func (wfm *WorkflowManager) StartWorkers(taskQueues []string, workflows map[string]interface{}, activities map[string]interface{}) error {
    for _, taskQueue := range taskQueues {
        // 为每个任务队列创建工作器
        w := worker.New(wfm.client, taskQueue, worker.Options{
            MaxConcurrentActivityExecutionSize: wfm.config.PollerCount,
            MaxConcurrentWorkflowTaskExecutionSize: wfm.config.PollerCount,
        })
        
        // 注册工作流
        for name, workflowFunc := range workflows {
            w.RegisterWorkflowWithOptions(workflowFunc, workflow.RegisterOptions{
                Name: name,
            })
        }
        
        // 注册活动
        for name, activityFunc := range activities {
            w.RegisterActivityWithOptions(activityFunc, activity.RegisterOptions{
                Name: name,
            })
        }
        
        // 启动工作器
        err := w.Start()
        if err != nil {
            return fmt.Errorf("启动任务队列 %s 的工作器失败: %w", taskQueue, err)
        }
        
        wfm.workers[taskQueue] = w
    }
    
    return nil
}

// StopWorkers 停止所有工作器
func (wfm *WorkflowManager) StopWorkers() {
    for _, w := range wfm.workers {
        w.Stop()
    }
}

// ExecuteOperation 执行业务操作，内部映射到相应的工作流
func (wfm *WorkflowManager) ExecuteOperation(ctx context.Context, operationType string, params interface{}) (string, error) {
    mapping, exists := wfm.workflowMappings[operationType]
    if !exists {
        return "", fmt.Errorf("未找到操作类型的工作流映射: %s", operationType)
    }
    
    // 确定任务队列
    taskQueue := mapping.TaskQueue
    if taskQueue == "" {
        taskQueue = wfm.config.DefaultTaskQueue
    }
    
    // 生成工作流ID
    workflowID := fmt.Sprintf("%s-%s", mapping.IDPrefix, uuid.New().String())
    
    // 设置工作流选项
    options := client.StartWorkflowOptions{
        ID:        workflowID,
        TaskQueue: taskQueue,
    }
    
    // 设置执行超时
    if mapping.ExecutionTimeout > 0 {
        options.WorkflowExecutionTimeout = mapping.ExecutionTimeout
    }
    
    // 启动工作流
    execution, err := wfm.client.ExecuteWorkflow(ctx, options, mapping.WorkflowType, params)
    if err != nil {
        return "", fmt.Errorf("启动工作流失败: %w", err)
    }
    
    return execution.GetID(), nil
}

// GetOperationStatus 获取操作状态
func (wfm *WorkflowManager) GetOperationStatus(ctx context.Context, workflowID string) (OperationStatus, error) {
    // 获取工作流执行描述
    desc, err := wfm.client.DescribeWorkflowExecution(ctx, workflowID, "")
    if err != nil {
        return OperationStatus{}, fmt.Errorf("获取工作流状态失败: %w", err)
    }
    
    status := OperationStatus{
        ID:        workflowID,
        StartTime: desc.WorkflowExecutionInfo.StartTime,
        State:     string(desc.WorkflowExecutionInfo.Status),
    }
    
    // 如果工作流已完成，尝试获取结果
    if desc.WorkflowExecutionInfo.Status == workflow.StatusCompleted ||
       desc.WorkflowExecutionInfo.Status == workflow.StatusFailed ||
       desc.WorkflowExecutionInfo.Status == workflow.StatusCanceled ||
       desc.WorkflowExecutionInfo.Status == workflow.StatusTerminated {
        
        status.EndTime = desc.WorkflowExecutionInfo.CloseTime
        
        // 只有已完成的工作流才获取结果
        if desc.WorkflowExecutionInfo.Status == workflow.StatusCompleted {
            var result interface{}
            execution := wfm.client.GetWorkflow(ctx, workflowID, "")
            err := execution.Get(ctx, &result)
            if err == nil {
                status.Result = result
            }
        } else if desc.WorkflowExecutionInfo.Status == workflow.StatusFailed {
            execution := wfm.client.GetWorkflow(ctx, workflowID, "")
            err := execution.Get(ctx, nil)
            if err != nil {
                status.Error = err.Error()
            }
        }
    }
    
    return status, nil
}

// CancelOperation 取消正在执行的操作
func (wfm *WorkflowManager) CancelOperation(ctx context.Context, workflowID string, reason string) error {
    return wfm.client.CancelWorkflow(ctx, workflowID, "", reason)
}

// SignalOperation 向正在执行的操作发送信号
func (wfm *WorkflowManager) SignalOperation(ctx context.Context, workflowID string, signalName string, signalData interface{}) error {
    return wfm.client.SignalWorkflow(ctx, workflowID, "", signalName, signalData)
}

// Close 关闭工作流管理器
func (wfm *WorkflowManager) Close() {
    // 首先停止所有工作器
    wfm.StopWorkers()
    
    // 然后关闭客户端
    wfm.client.Close()
}
```

## 九、最佳实践与模式总结

### 1. 智能家居工作流的最佳实践

1. **职责分离与层次结构**
   - 将设备控制、场景编排和用户交互分为不同层次的工作流
   - 每个工作流专注于单一责任，通过组合实现复杂功能

2. **多级容错机制**
   - 设备级：自动重试、降级到备用设备、备选执行路径
   - 场景级：部分失败继续执行、补偿操作、回滚机制
   - 系统级：心跳监控、自动恢复、异常报告

3. **数据一致性保障**
   - 使用版本控制和时间戳解决冲突
   - 实现最终一致性的同步策略
   - 关键操作的事务语义（Saga模式）

4. **可扩展性设计**
   - 分离工作流定义和执行逻辑
   - 支持工作流版本管理和平滑升级
   - 模块化设计支持新设备类型和场景类型的添加

5. **边缘与云端协同**
   - 根据网络状态自动选择执行位置
   - 边缘节点优先处理实时性要求高的任务
   - 云端负责复杂计算和全局优化

### 2. 实现Temporal工作流的关键点

1. **工作流设计技巧**
   - 保持工作流代码是确定性的，避免使用随机数、本地时间等不确定因素
   - 将业务逻辑和执行细节分离，活动(Activity)专注于执行，工作流(Workflow)专注于编排
   - 使用信号(Signal)实现工作流的动态控制，使用查询(Query)安全地获取工作流状态

2. **活动设计最佳实践**
   - 设计幂等活动，确保重复执行不产生副作用
   - 对长时间运行的活动实现心跳机制，及时检测活动执行状态
   - 为不同类型的设备操作设计专用活动，并实现适当的重试策略

3. **性能优化考虑**
   - 将大批量操作分解为小批次处理，避免单个活动执行时间过长
   - 合理使用并行执行(ExecuteActivity并行调用)加速处理
   - 使用本地缓存减少对数据库和外部服务的频繁访问

4. **工作流存储与历史管理**
   - 实现过期历史记录清理策略，避免历史记录过度膨胀
   - 对关键操作结果进行持久化存储，支持系统重启后的状态恢复
   - 记录工作流执行的关键指标，便于后续分析和优化

5. **错误处理策略**
   - 区分暂时性错误和永久性错误，对暂时性错误实施重试
   - 对关键节点进行检查点标记(Checkpoint)，支持从故障点恢复
   - 实现降级策略，在资源受限时保证核心功能正常运行

### 3. 智能家居常见工作流模式汇总

```text
+------------------------------------+-----------------------------------------+
| 工作流模式                         | 适用场景                                |
+------------------------------------+-----------------------------------------+
| 序列执行模式                       | 需要按特定顺序控制多个设备              |
| (Sequential Execution)             | 例如：依次打开走廊灯、客厅灯、调整温度   |
+------------------------------------+-----------------------------------------+
| 并行控制模式                       | 同时控制多个不相关的设备                |
| (Parallel Control)                 | 例如：同时调整多个房间的灯光亮度        |
+------------------------------------+-----------------------------------------+
| 条件分支模式                       | 基于环境条件或用户设置选择执行路径      |
| (Conditional Branching)            | 例如：根据当前光照决定是否开灯          |
+------------------------------------+-----------------------------------------+
| 事件驱动模式                       | 响应传感器触发或用户操作                |
| (Event-Driven)                     | 例如：检测到动作时开灯，无动作自动关闭  |
+------------------------------------+-----------------------------------------+
| 长时间监控模式                     | 持续监测设备或环境状态                  |
| (Long-Running Monitoring)          | 例如：监控家庭能耗，异常时报警          |
+------------------------------------+-----------------------------------------+
| 自适应控制模式                     | 根据环境变化动态调整参数                |
| (Adaptive Control)                 | 例如：根据室外温度调整室内目标温度      |
+------------------------------------+-----------------------------------------+
| 故障恢复模式                       | 处理设备离线或操作失败情况              |
| (Fault Recovery)                   | 例如：主设备失败时切换到备用设备        |
+------------------------------------+-----------------------------------------+
| 数据同步模式                       | 保证云端和边缘数据一致性                |
| (Data Synchronization)             | 例如：网络恢复后同步离线收集的数据      |
+------------------------------------+-----------------------------------------+
| 用户交互模式                       | 在工作流执行过程中响应用户输入          |
| (User Interaction)                 | 例如：播放电影时接收音量调整命令        |
+------------------------------------+-----------------------------------------+
| 版本迁移模式                       | 平滑升级场景定义和工作流逻辑            |
| (Version Migration)                | 例如：将V1格式场景定义升级至V2格式      |
+------------------------------------+-----------------------------------------+
| 资源竞争解决模式                   | 处理多个场景对同一设备的控制冲突        |
| (Resource Contention Resolution)   | 例如：决定哪个场景获得灯光控制权        |
+------------------------------------+-----------------------------------------+
| 学习优化模式                       | 收集用户习惯并优化未来场景执行          |
| (Learning Optimization)            | 例如：记录用户调整并在未来自动应用      |
+------------------------------------+-----------------------------------------+
| 多级协调模式                       | 跨房间或家庭的复杂场景调度              |
| (Multi-level Coordination)         | 例如：离家模式同时控制多个房间设备      |
+------------------------------------+-----------------------------------------+
| 外部服务集成模式                   | 与第三方系统协同工作                    |
| (External Service Integration)     | 例如：根据天气预报调整家庭暖通系统      |
+------------------------------------+-----------------------------------------+
```

### 4. 实际项目的集成路径

#### 渐进式集成Temporal的步骤

1. **评估阶段**
   - 识别现有系统中适合迁移到工作流的业务流程
   - 确定优先级：通常从复杂场景编排、长时间运行任务开始
   - 分析技术依赖和集成点

2. **概念验证**
   - 使用Temporal实现1-2个代表性场景
   - 测试边缘节点和云端部署模式
   - 验证性能、容错性和可扩展性

3. **基础架构准备**
   - 搭建Temporal服务器集群（云端）
   - 准备边缘节点的工作器部署
   - 建立监控和日志系统

4. **核心组件迁移**
   - 开发工作流集成层
   - 实现设备控制活动库
   - 构建基础工作流模板

5. **渐进式扩展**
   - 从单一场景类型扩展到多类型
   - 增加高级功能：自适应学习、冲突解决
   - 迁移历史数据和用户场景

6. **持续优化**
   - 监控工作流性能和资源使用
   - 根据使用模式优化工作流设计
   - 建立版本升级和迁移流程

#### Temporal与现有系统的集成模式

1. **API网关模式**

   ```text
   用户请求 -> API网关 -> 工作流管理器 -> Temporal工作流 -> 设备控制API
                 ^                            |
                 |                            v
                 +---- 状态查询 <--- 工作流状态存储
   ```

2. **事件总线模式**

   ```text
   设备事件 -> 事件总线 -> 事件处理器 -> 工作流触发器 -> Temporal工作流
                ^                                         |
                |                                         v
   设备控制 <-- 命令总线 <---- 工作流活动执行 <---- 活动工作器
   ```

3. **混合架构模式**

   ```text
   云端:    Temporal集群 <-> 数据存储 <-> AI服务
              ^   ^
              |   |
   边缘:  边缘工作器 <-> 本地缓存 <-> 边缘计算节点
              ^   ^
              |   |
   设备:  设备适配层 <-> 设备网络 <-> 智能设备
   ```

## 十、工作流与AI集成

### 1. 基于AI的场景推荐工作流

```go
// AI驱动的场景推荐工作流
func AISceneRecommendationWorkflow(ctx workflow.Context, params RecommendationParams) ([]SceneRecommendation, error) {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动AI场景推荐工作流", "userID", params.UserID)
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 3,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 数据收集阶段 - 并行获取多种数据
    
    // 1.1 获取用户历史场景使用数据
    var userHistoryFuture workflow.Future
    userHistoryFuture = workflow.ExecuteActivity(ctx, activities.GetUserSceneHistory, 
        UserHistoryRequest{
            UserID: params.UserID,
            Days: 30, // 获取30天的历史
        })
    
    // 1.2 获取用户设备状态数据
    var deviceStatusFuture workflow.Future
    deviceStatusFuture = workflow.ExecuteActivity(ctx, activities.GetUserDeviceStatus, 
        params.HomeID)
    
    // 1.3 获取环境数据
    var environmentFuture workflow.Future
    environmentFuture = workflow.ExecuteActivity(ctx, activities.GetEnvironmentData, 
        EnvironmentRequest{
            HomeID: params.HomeID,
            IncludeWeather: true,
            IncludeTimeFactors: true,
        })
    
    // 等待所有数据收集完成
    var userHistory UserSceneHistory
    err := userHistoryFuture.Get(ctx, &userHistory)
    if err != nil {
        logger.Error("获取用户历史失败", "error", err)
        // 继续执行，使用部分数据
    }
    
    var deviceStatus HomeDeviceStatus
    err = deviceStatusFuture.Get(ctx, &deviceStatus)
    if err != nil {
        logger.Error("获取设备状态失败", "error", err)
        // 继续执行，使用部分数据
    }
    
    var environment EnvironmentData
    err = environmentFuture.Get(ctx, &environment)
    if err != nil {
        logger.Error("获取环境数据失败", "error", err)
        // 继续执行，使用部分数据
    }
    
    // 2. 数据预处理 - 准备AI模型输入
    var modelInput AIRecommendationInput
    err = workflow.ExecuteActivity(ctx, activities.PrepareRecommendationModelInput, 
        PrepareInputParams{
            UserHistory: userHistory,
            DeviceStatus: deviceStatus,
            Environment: environment,
            UserPreferences: params.UserPreferences,
        }).Get(ctx, &modelInput)
    
    if err != nil {
        return nil, fmt.Errorf("准备模型输入失败: %w", err)
    }
    
    // 3. AI模型推理 - 生成场景推荐
    // 设置更长的超时，因为AI推理可能较慢
    aiCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
        StartToCloseTimeout: 2 * time.Minute,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
        },
    })
    
    var rawRecommendations AIModelOutput
    err = workflow.ExecuteActivity(aiCtx, activities.InvokeAIRecommendationModel, 
        modelInput).Get(aiCtx, &rawRecommendations)
    
    if err != nil {
        // AI推理失败，降级到基于规则的推荐
        logger.Error("AI模型推理失败，降级到规则引擎", "error", err)
        
        var fallbackRecommendations []SceneRecommendation
        err = workflow.ExecuteActivity(ctx, activities.GenerateRuleBasedRecommendations, 
            RuleBasedRequest{
                UserHistory: userHistory,
                Environment: environment,
                DeviceStatus: deviceStatus,
            }).Get(ctx, &fallbackRecommendations)
        
        if err != nil {
            return nil, fmt.Errorf("生成规则推荐也失败: %w", err)
        }
        
        return fallbackRecommendations, nil
    }
    
    // 4. 后处理 - 验证和丰富推荐结果
    var processedRecommendations []SceneRecommendation
    err = workflow.ExecuteActivity(ctx, activities.PostProcessRecommendations, 
        PostProcessParams{
            RawRecommendations: rawRecommendations,
            HomeID: params.HomeID,
            UserID: params.UserID,
            MaxResults: params.MaxResults,
        }).Get(ctx, &processedRecommendations)
    
    if err != nil {
        return nil, fmt.Errorf("推荐后处理失败: %w", err)
    }
    
    // 5. 记录推荐结果用于未来学习
    _ = workflow.ExecuteActivity(ctx, activities.RecordRecommendationEvent, 
        RecommendationRecord{
            UserID: params.UserID,
            Timestamp: workflow.Now(ctx),
            Recommendations: processedRecommendations,
            Context: environment,
        }).Get(ctx, nil)
    
    return processedRecommendations, nil
}
```

### 2. AI自动场景生成工作流

```go
// AI自动场景生成工作流
func AISceneGenerationWorkflow(ctx workflow.Context, params SceneGenerationParams) (GeneratedSceneResult, error) {
    logger := workflow.GetLogger(ctx)
    logger.Info("启动AI场景生成工作流", "userID", params.UserID, "description", params.Description)
    
    result := GeneratedSceneResult{
        Status: "pending",
    }
    
    // 设置活动选项
    activityOptions := workflow.ActivityOptions{
        StartToCloseTimeout: 30 * time.Second,
        RetryPolicy: &temporal.RetryPolicy{
            MaximumAttempts: 2,
        },
    }
    ctx = workflow.WithActivityOptions(ctx, activityOptions)
    
    // 1. 收集可用设备和用户偏好
    var homeDevices []DeviceInfo
    err := workflow.ExecuteActivity(ctx, activities.GetHomeDevices, 
        params.HomeID).Get(ctx, &homeDevices)
    if err != nil {
        result.Status = "failed"
        result.Error = fmt.Sprintf("获取家庭设备失败: %v", err)
        return result, nil
    }
    
    var userPreferences UserPreferences
    err = workflow.ExecuteActivity(ctx, activities.GetUserPreferences, 
        params.UserID).Get(ctx, &userPreferences)
    if err != nil {
        logger.Error("获取用户偏好失败，使用默认值", "error", err)
        // 继续使用默认偏好
        userPreferences = getDefaultUserPreferences()
    }
    
    // 2. 准备AI生成提示
    var generationPrompt SceneGenerationPrompt
    err = workflow.ExecuteActivity(ctx, activities.PrepareSceneGenerationPrompt, 
        PreparePromptParams{
            UserDescription: params.Description,
            AvailableDevices: homeDevices,
            UserPreferences: userPreferences,
            GenerationType: params.GenerationType,
        }).Get(ctx, &generationPrompt)
    
    if err != nil {
        result.Status = "failed"
        result.Error = fmt.Sprintf("准备生成提示失败: %v", err)
        return result, nil
    }
    
    // 3. 调用AI模型生成场景
    // 使用更长的超时时间
    aiCtx := workflow.WithActivityOptions(ctx, workflow.ActivityOptions{
        StartToCloseTimeout: 3 * time.Minute,
    })
    
    var generatedScene GeneratedScene
    err = workflow.ExecuteActivity(aiCtx, activities.GenerateSceneWithAI, 
        generationPrompt).Get(aiCtx, &generatedScene)
    
    if err != nil {
        // 如果是用户描述明确的简单场景，可以尝试规则引擎
        if params.GenerationType == "simple" {
            logger.Info("AI生成失败，尝试使用规则引擎", "error", err)
            
            err = workflow.ExecuteActivity(ctx, activities.GenerateSceneWithRules, 
                RuleGenerationParams{
                    Keyword: extractKeywords(params.Description),
                    Devices: homeDevices,
                    Preferences: userPreferences,
                }).Get(ctx, &generatedScene)
            
            if err != nil {
                result.Status = "failed"
                result.Error = fmt.Sprintf("场景生成失败: %v", err)
                return result, nil
            }
        } else {
            result.Status = "failed"
            result.Error = fmt.Sprintf("AI场景生成失败: %v", err)
            return result, nil
        }
    }
    
    // 4. 验证生成的场景
    var validationResult SceneValidationResult
    err = workflow.ExecuteActivity(ctx, activities.ValidateGeneratedScene, 
        ValidationParams{
            Scene: generatedScene,
            HomeID: params.HomeID,
        }).Get(ctx, &validationResult)
    
    if err != nil || !validationResult.IsValid {
        result.Status = "invalid"
        result.GeneratedScene = generatedScene
        result.ValidationIssues = validationResult.Issues
        return result, nil
    }
    
    // 5. 优化生成的场景
    var optimizedScene GeneratedScene
    err = workflow.ExecuteActivity(ctx, activities.OptimizeGeneratedScene, 
        OptimizationParams{
            Scene: generatedScene,
            ValidationResult: validationResult,
            UserPreferences: userPreferences,
        }).Get(ctx, &optimizedScene)
    
    if err != nil {
        logger.Error("场景优化失败，使用原始场景", "error", err)
        optimizedScene = generatedScene
    }
    
    // 6. 用户确认步骤（如果需要）
    if params.RequireUserConfirmation {
        // 发送场景预览请求给用户
        var previewRequest PreviewRequest
        err = workflow.ExecuteActivity(ctx, activities.CreateScenePreview, 
            optimizedScene).Get(ctx, &previewRequest)
        
        if err != nil {
            result.Status = "preview_failed"
            result.GeneratedScene = optimizedScene
            result.Error = fmt.Sprintf("创建场景预览失败: %v", err)
            return result, nil
        }
        
        // 发送预览通知
        _ = workflow.ExecuteActivity(ctx, activities.SendScenePreviewNotification, 
            NotificationParams{
                UserID: params.UserID,
                PreviewID: previewRequest.PreviewID,
                SceneName: optimizedScene.Name,
            }).Get(ctx, nil)
        
        // 等待用户确认
        userConfirmationChan := workflow.GetSignalChannel(ctx, "scene_confirmation_signal")
        
        // 设置30分钟超时
        selector := workflow.NewSelector(ctx)
        timerFuture := workflow.NewTimer(ctx, workflow.Now(ctx).Add(30*time.Minute)).Future
        
        var userConfirmed bool
        var confirmationReceived bool
        
        selector.AddFuture(timerFuture, func(f workflow.Future) {
            _ = f.Get(ctx, nil)
            // 超时，自动拒绝
            confirmationReceived = true
            userConfirmed = false
        })
        
        selector.AddReceive(userConfirmationChan, func(c workflow.ReceiveChannel, more bool) {
            var signal UserConfirmationSignal
            c.Receive(ctx, &signal)
            confirmationReceived = true
            userConfirmed = signal.Confirmed
        })
        
        // 等待确认或超时
        for !confirmationReceived {
            selector.Select(ctx)
        }
        
        if !userConfirmed {
            result.Status = "rejected"
            result.GeneratedScene = optimizedScene
            return result, nil
        }
    }
    
    // 7. 保存场景
    var savedScene SavedScene
    err = workflow.ExecuteActivity(ctx, activities.SaveGeneratedScene, 
        SaveSceneParams{
            Scene: optimizedScene,
            UserID: params.UserID,
            HomeID: params.HomeID,
            GenerationType: "ai",
        }).Get(ctx, &savedScene)
    
    if err != nil {
        result.Status = "save_failed"
        result.GeneratedScene = optimizedScene
        result.Error = fmt.Sprintf("保存场景失败: %v", err)
        return result, nil
    }
    
    // 8. 记录AI生成数据用于改进模型
    _ = workflow.ExecuteActivity(ctx, activities.RecordAIGenerationData, 
        GenerationRecord{
            UserID: params.UserID,
            Description: params.Description,
            GeneratedScene: optimizedScene,
            Successful: true,
            Timestamp: workflow.Now(ctx),
        }).Get(ctx, nil)
    
    // 返回成功结果
    result.Status = "success"
    result.GeneratedScene = optimizedScene
    result.SavedSceneID = savedScene.ID
    
    return result, nil
}
```

## 总结：工作流如何解决智能家居系统难题

1. **复杂协调问题**
   - Temporal工作流提供了声明式编排框架，简化了多设备、多房间协调逻辑
   - 子工作流和信号机制支持模块化和松散耦合的组件交互

2. **可靠性挑战**
   - 自动重试、检查点和状态持久化确保即使在设备或网络故障时也能恢复执行
   - 降级策略和补偿机制处理部分失败场景

3. **一致性保障**
   - 事件溯源和版本控制机制解决分布式环境下的数据一致性问题
   - 冲突解决策略确保多个场景合理共享资源

4. **灵活适应变化**
   - 动态工作流支持根据环境和用户行为自适应执行
   - 版本化工作流允许系统平滑升级而不中断服务

5. **扩展性与维护性**
   - 明确分离控制流和执行逻辑，简化维护和调试
   - 基于活动的抽象使得添加新设备类型和功能变得简单

智能家居系统通过工作流范式将复杂的自动化逻辑转化为可管理、可靠且灵活的软件组件，为用户提供无缝的智能生活体验，同时为开发者提供强大而清晰的实现框架。
