//! RTIC 框架 —— 实时中断驱动并发 (Real-Time Interrupt-driven Concurrency)
//!
//! # 概述
//!
//! [RTIC](https://rtic.rs/) (以前叫 Real-Time For the Masses) 是一个用于
//! ARM Cortex-M 微控制器的并发框架，利用 NVIC 硬件优先级实现**零成本**
//! 任务调度和资源共享。
//!
//! # 核心特性
//!
//! | 特性 | 说明 |
//! |------|------|
//! | **零成本抽象** | 无运行时开销，直接映射到硬件中断 |
//! | **基于优先级** | 利用 NVIC 抢占实现硬实时 |
//! | **资源模型** | 编译期保证无数据竞争 |
//! | **任务调度** | 软件任务 + 硬件任务统一模型 |
//! | **延迟保证** | 可计算的 WCET (Worst Case Execution Time) |
//!
//! # 设计哲学
//!
//! RTIC 的核心洞察：**Cortex-M NVIC 已经是一个完美的实时调度器**。
//! RTIC 只需将软件任务映射到 NVIC 优先级，即可获得：
//! - 硬件级抢占
//! - 零上下文切换开销（Tail-chaining）
//! - 确定性延迟
//!
//! # 参考
//! - [RTIC Book](https://rtic.rs/2/book/en/)
//! - [RTIC GitHub](https://github.com/rtic-rs/rtic)

// =========================================================================
// 1. RTIC 应用结构
// =========================================================================

/// # RTIC 应用骨架
///
// RTIC 使用 `#[rtic::app]` 属性宏定义整个嵌入式应用：
// - `device` — PAC (Peripheral Access Crate)
// - `dispatchers` — 用于软件任务的闲置中断向量
// - `shared` — 共享资源（自动实现互斥）
// - `local` — 任务本地资源
///
// ```ignore
// #[rtic::app(device = stm32f4xx_hal::pac, dispatchers = [TIM2, TIM3])]
// mod app {
//     // 共享资源
//     #[shared]
//     struct Shared {
//         led: LED,
//         sensor_data: SensorData,
//     }
//
//     // 本地资源
//     #[local]
//     struct Local {
//         button: Button,
//     }
//
//     // 初始化
//     #[init]
//     fn init(cx: init::Context) -> (Shared, Local) {
//         // 初始化硬件...
//         (Shared { led, sensor_data }, Local { button })
//     }
//
//     // 空闲循环
//     #[idle]
//     fn idle(_: idle::Context) -> ! {
//         loop { cortex_m::asm::wfi(); }
//     }
//
//     // 硬件任务（绑定到中断）
//     #[task(binds = EXTI0, shared = [led])]
//     fn button_press(cx: button_press::Context) {
//         cx.shared.led.lock(|led| led.toggle());
//     }
//
//     // 软件任务（由调度器调度）
//     #[task(shared = [sensor_data])]
//     fn process_sensor(cx: process_sensor::Context) {
//         cx.shared.sensor_data.lock(|data| {
//             data.temperature = read_adc();
//         });
//     }
// }
// ```
pub struct RticAppStructure;

impl RticAppStructure {
    pub fn explain_structure() -> &'static str {
        r#"
RTIC 应用结构解析:

1. #[rtic::app]
   - 标记整个模块为 RTIC 应用
   - 指定设备 PAC 和可用的 dispatcher 中断

2. #[shared]
   - 定义多个任务共享的资源
   - RTIC 自动生成基于优先级的锁（无运行时开销）

3. #[local]
   - 定义仅单个任务访问的资源
   - 无需锁，零开销

4. #[init]
   - 系统启动时执行一次
   - 初始化所有硬件和外设
   - 返回 Shared 和 Local 结构体

5. #[idle]
   - 最低优先级任务，在没有其他任务时运行
   - 通常进入 WFI (Wait For Interrupt) 省电

6. #[task]
   - binds = 硬件中断向量（硬件任务）
   - 无 binds = 软件任务（由 spawn 触发）
"#
    }
}

// =========================================================================
// 2. 资源模型与锁机制
// =========================================================================

/// # RTIC 资源模型
///
// RTIC 的资源模型是**零成本互斥**的核心：
// - 高优先级任务自动抢占低优先级任务
// - 低优先级任务访问共享资源时，RTIC 自动生成**基于优先级的临界区**
// - 无需 `Mutex`、`Atomic` 或关中断（除非优先级相同）
pub struct RticResourceModel;

impl RticResourceModel {
    pub fn locking_mechanism() -> &'static str {
        r#"
RTIC 锁机制 (Priority Ceiling Protocol):

场景: 任务 A (优先级 3) 和任务 B (优先级 1) 共享资源 R

1. 任务 B 运行，尝试访问 R:
   - RTIC 临时提升 B 的优先级到 R 的天花板优先级
   - 等价于: 阻止了所有可能访问 R 的更高优先级任务抢占
   - 无需关中断！

2. 任务 A 触发（硬件中断）:
   - A 的优先级 > R 的天花板
   - A 抢占 B（即使 B 持有 R 的锁）
   - 但 A 如果也访问 R，会阻塞直到 B 释放

3. 任务 B 完成 R 访问:
   - 优先级恢复
   - A 立即抢占 B（如果 A 在等待）

关键保证:
- 无优先级反转（Priority Inversion）
- 无死锁（单持有者 + 优先级顺序）
- 锁的获取/释放是单条机器指令（提升/恢复 BASEPRI）
"#
    }

    /// 资源使用示例
    pub fn resource_example() -> &'static str {
        r#"
// 共享资源定义
#[shared]
struct Shared {
    uart: Tx<USART1>,
    buffer: [u8; 64],
}

// 硬件任务：UART 接收中断（高优先级）
#[task(binds = USART1, shared = [uart, buffer], priority = 3)]
fn uart_rx(cx: uart_rx::Context) {
    let uart = cx.shared.uart;
    let buffer = cx.shared.buffer;

    // 同时锁定多个资源
    (uart, buffer).lock(|uart, buffer| {
        if let Ok(b) = uart.read() {
            buffer[head] = b;
        }
    });
}

// 软件任务：处理数据（低优先级）
#[task(shared = [buffer], priority = 1)]
fn process_data(cx: process_data::Context) {
    cx.shared.buffer.lock(|buffer| {
        // 处理缓冲区数据
        parse_protocol(buffer);
    });
}
"#
    }
}

// =========================================================================
// 3. 软件任务与消息传递
// =========================================================================

/// # RTIC 软件任务
///
// 软件任务不绑定到硬件中断，而是由 `spawn`/`schedule` 触发，
// 通过 `dispatchers` 中指定的闲置中断向量进行调度。
pub struct RticSoftwareTasks;

impl RticSoftwareTasks {
    pub fn software_task_concepts() -> &'static str {
        r#"
RTIC 软件任务:

1. spawn (立即调度)
   #[task]
   fn my_task(cx: my_task::Context, arg: i32) { ... }

   // 从其他任务触发
   my_task::spawn(42).unwrap();

2. schedule (延迟调度)
   #[task]
   fn delayed_task(cx: delayed_task::Context) { ... }

   // 1000 个 tick 后执行
   delayed_task::schedule(cx.scheduled + 1000.millis()).unwrap();

3. 消息队列
   - 软件任务有一个隐式的消息队列
   - 队列深度默认 1，可通过 #[task(capacity = N)] 配置
   - spawn 在队列满时返回错误
"#
    }

    pub fn spawn_example() -> &'static str {
        r#"
// 生产者-消费者 模式（RTIC）
#[shared]
struct Shared {
    producer_ready: bool,
}

#[task(priority = 2)]
fn producer(cx: producer::Context) {
    let data = read_sensor();
    // 触发消费者（如果队列未满）
    consumer::spawn(data).ok();
}

#[task(priority = 1)]
fn consumer(_cx: consumer::Context, data: SensorData) {
    process(data);
    // 触发下一个周期
    producer::spawn().ok();
}
"#
    }
}

// =========================================================================
// 4. 单调调度与定时器
// =========================================================================

/// # RTIC Monotonic Timer
///
// RTIC 使用 `Monotonic` trait 提供统一的定时器抽象，
// 支持软件任务的延迟调度（`schedule_at`）。
pub struct RticMonotonicTimer;

impl RticMonotonicTimer {
    pub fn monotonic_concept() -> &'static str {
        r#"
RTIC Monotonic Timer:

1. 实现 Monotonic trait 的定时器:
   - Systick (最简单，但精度有限)
   - TIMx (通用定时器，推荐)
   - DWT CYCCNT (CPU 周期计数)

2. 调度语义:
   #[task(schedule = [my_task])]
   fn timer_task(cx: timer_task::Context) {
       // 每 100ms 执行一次
       my_task::schedule(cx.scheduled + 100.millis()).unwrap();
   }

3. 精度保证:
   - 调度点在 tick 边界
   - 抖动 < 1 tick
   - 无累积误差（基于硬件计数器）
"#
    }

    pub fn periodic_task_pattern() -> &'static str {
        r#"
// 严格周期性任务（RTIC + Monotonic）
#[task(local = [ticker])]
fn control_loop(cx: control_loop::Context) {
    let ticker = cx.local.ticker;

    // 执行控制算法
    let output = pid_controller.update(sensor.read());
    actuator.set(output);

    // 精确调度下一次执行
    let next = ticker.next_tick();
    control_loop::schedule_at(next).unwrap();
}
"#
    }
}

// =========================================================================
// 5. 与 Embassy 的互操作
// =========================================================================

/// # RTIC + Embassy 组合
///
// RTIC 和 Embassy 可以共存：
// - RTIC 管理**硬实时**任务（电机控制、紧急停止）
// - Embassy 运行**软实时**协议栈（网络、USB、文件系统）
pub struct RticEmbassyInterop;

impl RticEmbassyInterop {
    pub fn interop_pattern() -> &'static str {
        r#"
RTIC + Embassy 组合架构:

1. RTIC 作为底层调度器:
   - 最高优先级: 电机控制 (RTIC 硬件任务)
   - 中优先级: 传感器采集 (RTIC 软件任务)
   - 低优先级: Embassy Executor 运行 (作为 RTIC idle 任务)

2. 通信机制:
   - RTIC → Embassy: 无锁环形缓冲区 (spsc)
   - Embassy → RTIC: 软件中断触发 (pend RTIC 任务)

3. 代码结构:
   #[rtic::app(device = pac, dispatchers = [TIM2])]
   mod app {
       #[shared]
       struct Shared {
           cmd_queue: CommandQueue,
       }

       #[init]
       fn init(cx: init::Context) -> (Shared, Local) {
           // 启动 Embassy executor 作为低优先级任务
           embassy_executor::init();

           (Shared { cmd_queue }, Local {})
       }

       #[idle]
       fn idle(_: idle::Context) -> ! {
           // 运行 Embassy executor
           embassy_executor::run(|spawner| {
               spawner.spawn(network_task()).unwrap();
           });
       }

       #[task(binds = TIM1_UP, shared = [cmd_queue], priority = 5)]
       fn motor_control(cx: motor_control::Context) {
           // 硬实时控制
       }
   }
"#
    }
}

// =========================================================================
// 6. 实时分析
// =========================================================================

/// # RTIC 实时性分析
///
// RTIC 提供了静态分析工具，可计算：
// - 任务响应时间
// - 上下文切换开销
// - 资源锁持有时间
///
// 这使得 RTIC 适用于安全关键系统（如汽车、医疗、航空）。
pub struct RticRealTimeAnalysis;

impl RticRealTimeAnalysis {
    pub fn schedulability_analysis() -> &'static str {
        r#"
RTIC 可调度性分析:

1. 响应时间分析 (RTA):
   R_i = C_i + sum(ceil((R_i + J_j) / T_j) * C_j)
   其中:
   - R_i: 任务 i 的最坏响应时间
   - C_i: 任务 i 的最坏执行时间
   - T_j: 更高优先级任务 j 的周期
   - J_j: 任务 j 的抖动

2. RTIC 优势:
   - 无运行时调度开销（硬件 NVIC 调度）
   - 无优先级反转（Priority Ceiling）
   - 锁持有时间可精确计算
   - 中断延迟 = 12 时钟周期（Cortex-M）

3. 分析工具:
   - `cargo rtic-scope` — 逻辑分析仪集成
   - `defmt` + `probe-rs` — 运行时追踪
"#
    }
}

// =========================================================================
// 测试
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rtic_structure_concepts() {
        let explanation = RticAppStructure::explain_structure();
        assert!(explanation.contains("#[rtic::app]"));
        assert!(explanation.contains("#[shared]"));
    }

    #[test]
    fn test_priority_ceiling_concept() {
        let lock = RticResourceModel::locking_mechanism();
        assert!(lock.contains("Priority Ceiling"));
    }

    #[test]
    fn test_rtic_vs_embassy_interop() {
        let pattern = RticEmbassyInterop::interop_pattern();
        assert!(pattern.contains(" Embassy "));
    }
}
