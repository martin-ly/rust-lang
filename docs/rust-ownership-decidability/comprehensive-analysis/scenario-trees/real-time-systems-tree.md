# 实时系统应用场景树

> **从硬实时到软实时的Rust解决方案**

---

## 1. 实时系统分类

```text
实时系统需求
      │
      ├──▶ 截止时间要求? ──▶ 严格(错过=失败) ──▶ 硬实时
      │                          ├── 航空航天
      │                          ├── 汽车控制
      │                          └── 医疗设备
      │
      └──▶ 是 ──▶ 宽松(错过=降级) ──▶ 软实时
                  ├── 音视频处理
                  ├── 游戏
                  └── 网络服务
```

---

## 2. 硬实时系统

### 2.1 汽车电子控制单元 (ECU)

```text
汽车ECU
      │
      ├──▶ 动力控制 ──▶ 引擎管理
      │                  ├── 点火时机控制 (μs级)
      │                  ├── 燃油喷射 (μs级)
      │                  └── 废气再循环 (ms级)
      │
      │                  Rust解决方案:
      │                  ├── RTIC框架
      │                  ├── 确定性调度
      │                  └── 无动态分配
      │
      ├──▶ 底盘控制 ──▶ 防抱死制动 (ABS)
      │                  ├── 轮速监测 (1-10ms)
      │                  ├── 压力调节 (ms级)
      │                  └── 稳定性控制 (ESC)
      │
      │                  安全要求:
      │                  ├── ISO 26262 ASIL-D
      │                  ├── 故障检测
      │                  └── 冗余设计
      │
      └──▶ 车身控制 ──▶ 门窗座椅
                         ├── 响应时间 < 100ms
                         ├── 多任务处理
                         └── 低功耗
```

### 2.2 航空航天系统

```text
飞行控制
      │
      ├──▶ 飞控计算机 ──▶ 主飞控
      │                     ├── 姿态控制 (1-10ms)
      │                     ├── 自动驾驶 (10-100ms)
      │                     └── 故障切换 (< 10ms)
      │
      │                     Rust优势:
      │                     ├── 内存安全 (无UAF)
      │                     ├── 零成本抽象
      │                     └── 形式化验证支持
      │
      └──▶ 机载系统 ──▶ 导航通信
                        ├── GPS处理 (1Hz-10Hz)
                        ├── 数据链 (异步)
                        └── 传感器融合
```

### 2.3 医疗设备

```text
医疗仪器
      │
      ├──▶ 生命支持 ──▶ 呼吸机
      │                  ├── 呼吸周期控制 (精确到ms)
      │                  ├── 压力监测 (连续)
      │                  └── 报警系统 (< 100ms)
      │
      │                  认证要求:
      │                  ├── FDA Class II/III
      │                  ├── IEC 62304
      │                  └── 风险管理
      │
      └──▶ 影像设备 ──▶ MRI/CT控制
                        ├── 扫描序列控制
                        ├── 数据采集 (μs级)
                        └── 实时重建
```

---

## 3. 软实时系统

### 3.1 音视频处理

```text
多媒体系统
      │
      ├──▶ 视频编码 ──▶ 实时编码
      │                  ├── 帧率维护 (33ms @ 30fps)
      │                  ├── 码率控制
      │                  └── 延迟预算
      │
      │                  Rust实现:
      │                  ├── rav1e (AV1编码器)
      │                  ├── 零拷贝处理
      │                  └── SIMD优化
      │
      ├──▶ 音频处理 ──▶ 低延迟音频
      │                  ├── 缓冲区管理 (< 10ms)
      │                  ├── 实时效果处理
      │                  └── 同步播放
      │
      └──▶ 流媒体 ──▶ 直播服务
                      ├── 端到端延迟 (< 3s)
                      ├── 自适应码率
                      └── 容错恢复
```

### 3.2 游戏开发

```text
游戏引擎
      │
      ├──▶ 渲染循环 ──▶ 主循环
      │                  ├── 目标帧率 (16.6ms @ 60fps)
      │                  ├── 渲染提交
      │                  └── 垂直同步
      │
      │                  Rust引擎:
      │                  ├── Bevy (ECS)
      │                  ├── wgpu (跨平台渲染)
      │                  └── 确定性模拟
      │
      ├──▶ 物理模拟 ──▶ 刚体动力学
      │                  ├── 固定时间步长
      │                  ├── 碰撞检测
      │                  └── 网络同步
      │
      └──▶ 网络同步 ──▶ 多人游戏
                         ├── 状态同步 (20-50Hz)
                         ├── 客户端预测
                         └── 回滚系统
```

---

## 4. Rust实时解决方案

### 4.1 硬实时框架对比

| 框架 | 调度策略 | WCET分析 | 内存 | 适用场景 |
|:---:|:---:|:---:|:---:|:---|
| **RTIC** | 静态优先级 | ⭐⭐⭐⭐⭐ | 无堆 | 汽车、工业 |
| **Embassy** | 协作式 | ⭐⭐⭐ | 无堆 | IoT、传感器 |
| **Tock OS** | 抢占式 | ⭐⭐⭐ | 无堆 | 安全关键 |
| **Hubris** | 固定优先级 | ⭐⭐⭐⭐ | 无堆 | 嵌入式 |

### 4.2 确定性编程模式

```rust
// RTIC确定性示例
#[rtic::app(device = stm32f4xx_hal::pac)]
mod app {
    // 共享资源声明 - 编译时确定
    #[shared]
    struct Shared {
        sensor_data: SensorData,
    }

    // 本地资源
    #[local]
    struct Local {
        adc: Adc,
    }

    // 初始化 - 运行一次
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        let adc = configure_adc(cx.device.ADC1);
        (
            Shared { sensor_data: SensorData::new() },
            Local { adc },
        )
    }

    // 周期性任务 - 保证执行时间
    #[task(shared = [sensor_data], priority = 2, binds = TIM2)]
    fn read_sensor(mut cx: read_sensor::Context) {
        // WCET可分析 - 无动态分配，无阻塞
        let value = cx.local.adc.read();
        cx.shared.sensor_data.lock(|data| {
            data.update(value);
        });
    }

    // 中断处理 - 严格时间约束
    #[task(binds = EXTI0, priority = 1)]
    fn emergency_stop(_cx: emergency_stop::Context) {
        // 最高优先级，响应时间 < 1μs
        disable_motor();
    }
}
```

### 4.3 无锁数据结构

```rust
// 实时系统中的无锁队列
use crossbeam::queue::ArrayQueue;

static EVENT_QUEUE: ArrayQueue<Event, 128> = ArrayQueue::new();

// 生产者 (中断上下文)
#[interrupt]
fn SENSOR_IRQ() {
    let reading = read_sensor();
    // 无分配，无阻塞，O(1)
    let _ = EVENT_QUEUE.push(Event::Sensor(reading));
}

// 消费者 (主循环)
fn process_events() {
    while let Ok(event) = EVENT_QUEUE.pop() {
        handle(event);
    }
}
```

---

## 5. 性能保证技术

### 5.1 WCET分析

```text
最坏情况执行时间分析:

代码特性              分析复杂度    Rust支持
─────────────────────────────────────────────
简单顺序执行          线性          完全支持
条件分支              分支分析      完全支持
循环                  边界分析      需要标注
函数调用              调用图        支持
动态分配              不可分析      禁止使用
递归                  不可分析      禁止使用
```

### 5.2 内存分配策略

| 策略 | 分配时间 | 碎片 | 确定性 | 适用场景 |
|:---:|:---:|:---:|:---:|:---|
| **栈分配** | O(1) | 无 | ⭐⭐⭐⭐⭐ | 固定大小数据 |
| **静态分配** | 编译时 | 无 | ⭐⭐⭐⭐⭐ | 全局状态 |
| **池分配** | O(1) | 可控 | ⭐⭐⭐⭐ | 固定大小对象 |
| **线性分配** | O(1) | 无 | ⭐⭐⭐⭐ | Arena模式 |
| **堆分配** | 不定 | 有 | ⭐ | 禁止在实时路径 |

---

## 6. 认证与合规

### 6.1 功能安全标准

```text
功能安全标准映射:

ISO 26262 (汽车)          IEC 61508 (工业)
     │                           │
     ├── ASIL-A (最低)          ├── SIL-1
     ├── ASIL-B                 ├── SIL-2
     ├── ASIL-C                 ├── SIL-3
     └── ASIL-D (最高)          └── SIL-4

Rust优势:
├── 内存安全消除一类故障
├── 类型系统防止状态错误
├── 形式化验证工具支持
└── unsafe代码边界可控
```

### 6.2 工具链认证

| 工具 | 用途 | 认证支持 |
|:---|:---|:---:|
| rustc | 编译 | 可被认证 |
| cargo | 构建 | 需包装 |
| Miri | 运行时检查 | 开发期 |
| Kani | 模型检测 | 验证辅助 |
| clippy | 静态分析 | 开发期 |

---

## 7. 实际案例

### 7.1 汽车制动系统

```rust
// 简化ABS控制逻辑
struct AbsController {
    wheel_speeds: [f32; 4],
    brake_pressure: f32,
    state: AbsState,
}

enum AbsState {
    Idle,
    PressureHold,
    PressureRelease,
    PressureApply,
}

impl AbsController {
    // 10ms控制周期
    #[rtic::task(priority = 1)]
    fn control_cycle(&mut self) {
        let slip = self.calculate_slip();

        self.state = match self.state {
            AbsState::Idle if slip > 0.3 => AbsState::PressureHold,
            AbsState::PressureHold if slip > 0.5 => AbsState::PressureRelease,
            AbsState::PressureRelease if slip < 0.1 => AbsState::PressureApply,
            AbsState::PressureApply if slip > 0.3 => AbsState::PressureHold,
            _ => self.state,
        };

        self.apply_pressure();
    }
}
```

### 7.2 无人机飞控

```rust
// 姿态控制回路
struct FlightController {
    attitude: Attitude,      // 当前姿态
    target: Attitude,        // 目标姿态
    pid_roll: PidController,
    pid_pitch: PidController,
    pid_yaw: PidController,
}

// 1kHz控制频率
#[interrupt(binds = TIM7, priority = 1)]
fn attitude_control() {
    let fc = unsafe { FLIGHT_CONTROLLER.as_mut().unwrap() };

    // 读取传感器
    let (gyro, accel) = read_imu();
    fc.update_attitude(gyro, accel);

    // PID计算
    let roll_out = fc.pid_roll.update(fc.target.roll - fc.attitude.roll);
    let pitch_out = fc.pid_pitch.update(fc.target.pitch - fc.attitude.pitch);
    let yaw_out = fc.pid_yaw.update(fc.target.yaw - fc.attitude.yaw);

    // 输出到电机
    set_motors(roll_out, pitch_out, yaw_out);
}
```

---

## 8. 结论

```text
┌─────────────────────────────────────────────────────────────────┐
│                Rust实时系统总结                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  硬实时适用性: ⭐⭐⭐⭐                                        │
│  - RTIC提供确定性调度                                            │
│  - 借用检查消除内存故障                                           │
│  - 无堆分配模式成熟                                               │
│                                                                 │
│  软实时适用性: ⭐⭐⭐⭐⭐                                      │
│  - Embassy异步框架                                               │
│  - 性能与安全性兼顾                                               │
│  - 丰富的生态系统                                                │
│                                                                 │
│  关键成功因素:                                                   │
│  1. 静态分析优先                                                 │
│  2. 无动态分配                                                   │
│  3. 确定性调度                                                   │
│  4. 形式化验证                                                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

**维护者**: Rust Real-Time Systems Team
**更新日期**: 2026-03-05
