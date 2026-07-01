# 嵌入式系统场景

> **Bloom 层级**: 应用 → 分析
> **来源: [Rust Embedded WG](https://rust-embedded.github.io/book/)** · **[来源: Embassy/RTIC 文档]** ✅

---

## 场景 1：物联网传感器节点

**背景**: 电池供电的温湿度传感器，通过 LoRa 传输数据。

**约束**:

- RAM: 64KB
- Flash: 256KB
- 功耗: 待机 < 10μA
- 无线协议: LoRaWAN

**Rust 方案**:

```rust
use embassy_stm32::{
    gpio::*,
    i2c::I2c,
    low_power::enter_stop,
};
use embassy_time::{Duration, Timer};

// 异步主循环：传感器读取 → 数据打包 → LoRa 发送 → 深度睡眠
#[embassy_executor::main]
async fn main() {
    let p = embassy_stm32::init(Default::default());
    let i2c = I2c::new(p.I2C1, p.PB6, p.PB7, Hertz(100_000));
    let lora = LoRa::new(p.SPI1, p.PA4).await;

    loop {
        // 读取传感器
        let (temp, hum) = read_sht30(&mut i2c).await;

        // 打包并发送
        let payload = encode_payload(temp, hum);
        lora.send(&payload).await;

        // 进入 STOP 模式 5 分钟
        enter_stop(Duration::from_secs(300)).await;
    }
}
```
**关键决策**:

- 框架: Embassy（异步低功耗管理）
- 协议: `lorawan` crate
- 内存: 静态分配，无 `alloc`

---

## 场景 2：电机控制器（硬实时）

**背景**: 无刷直流电机（BLDC）FOC 控制，电流环 50kHz。

**约束**:

- 电流环延迟: < 20μs（确定性）
- 位置环: 1kHz
- 安全: 过流保护 < 5μs

**Rust 方案**:

```rust
use rtic::app;

#[app(device = stm32g4xx_hal::pac, peripherals = true)]
mod app {
    #[shared]
    struct Shared {
        current_setpoint: i16,
    }

    #[local]
    struct Local {
        adc: Adc,
        pwm: Pwm,
    }

    // 电流环: 最高优先级硬件中断
    #[task(binds = ADC1_2, priority = 3, shared = [current_setpoint], local = [adc, pwm])]
    fn current_loop(cx: current_loop::Context) {
        let adc_sample = cx.local.adc.read();
        let error = cx.shared.current_setpoint.lock(|sp| *sp - adc_sample);
        let duty = pi_controller.update(error);
        cx.local.pwm.set_duty(duty);
    }

    // 位置环: 较低优先级
    #[task(binds = TIM2, priority = 2, shared = [current_setpoint])]
    fn position_loop(cx: position_loop::Context) {
        let position = encoder.read();
        let current = position_pid.update(position_target - position);
        cx.shared.current_setpoint.lock(|sp| *sp = current);
    }
}
```
**关键决策**:

- 框架: RTIC（硬件优先级保证确定性）
- 无 `alloc`，完全静态
- FPU 加速（`cortex-m4f`）

---

## 场景 3：汽车 ECU（功能安全）

**背景**: 车身控制模块（BCM），ISO 26262 ASIL B。

**约束**:

- 确定性执行
- 故障检测与 safe state
- 代码覆盖率: MC/DC

**Rust 方案**:

```rust
#![no_std]
#![no_main]
#![forbid(unsafe)] // FLS 要求

use ferrocene::prelude::*;

// 安全关键状态机
enum BcmState {
    Init,
    Normal,
    Degraded,
    SafeState,
}

fn state_machine(event: Event, state: &mut BcmState) -> Result<(), BcmError> {
    match (&state, event) {
        (BcmState::Init, Event::SelfTestPass) => {
            *state = BcmState::Normal;
            Ok(())
        }
        (BcmState::Normal, Event::FaultDetected(fault)) if fault.critical() => {
            *state = BcmState::SafeState;
            enter_safe_state();
            Ok(())
        }
        _ => Err(BcmError::InvalidTransition),
    }
}
```
**关键决策**:

- 工具链: Ferrocene（ISO 26262 认证）
- 规范: FLS + MISRA Rust
- 验证: Kani 形式化验证 + MC/DC 测试

---

> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
