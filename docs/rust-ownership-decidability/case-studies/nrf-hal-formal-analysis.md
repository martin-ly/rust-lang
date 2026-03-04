# nRF HAL硬件抽象层形式化分析

> **主题**: Nordic nRF系列芯片HAL
> **形式化框架**: 外设状态机 + 低功耗模式 + PPI
> **参考**: nrf-hal crate (<https://github.com/nrf-rs/nrf-hal>)

---

## 目录

- [nRF HAL硬件抽象层形式化分析](#nrf-hal硬件抽象层形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 外设所有权模型](#2-外设所有权模型)
    - [定义 PERIPH-1 ( 外设分区 )](#定义-periph-1--外设分区-)
    - [定理 OWN-T1 ( 外设唯一性 )](#定理-own-t1--外设唯一性-)
  - [3. 低功耗模式](#3-低功耗模式)
    - [定义 POWER-1 ( 功耗模式 )](#定义-power-1--功耗模式-)
    - [定义 POWER-2 ( 模式转换 )](#定义-power-2--模式转换-)
  - [4. PPI可编程外设互联](#4-ppi可编程外设互联)
    - [定义 PPI-1 ( 通道模型 )](#定义-ppi-1--通道模型-)
    - [定义 PPI-2 ( 通道组 )](#定义-ppi-2--通道组-)
    - [定理 PPI-T1 ( 零延迟 )](#定理-ppi-t1--零延迟-)
  - [5. EasyDMA](#5-easydma)
    - [定义 DMA-1 ( 缓冲区安全 )](#定义-dma-1--缓冲区安全-)
    - [定理 DMA-T1 ( 安全传输 )](#定理-dma-t1--安全传输-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 SAFE-T1 ( 配置安全 )](#定理-safe-t1--配置安全-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: UART with EasyDMA](#示例1-uart-with-easydma)
    - [示例2: PPI自动触发](#示例2-ppi自动触发)
    - [示例3: 低功耗模式](#示例3-低功耗模式)
    - [示例4: SAADC采样](#示例4-saadc采样)

---

## 1. 引言

nRF HAL为Nordic nRF52/nRF53/nRF91系列提供：

- 类型状态机
- 低功耗管理
- PPI硬件事件系统
- EasyDMA零拷贝

---

## 2. 外设所有权模型

### 定义 PERIPH-1 ( 外设分区 )

$$
\text{Peripherals} = \text{UARTE} \uplus \text{SPIM} \uplus \text{TWIM} \uplus \text{TIMER} \uplus \text{RTC} \uplus \text{SAADC} \uplus \ldots
$$

**特性**: 每个外设只能实例化一次。

```rust
let p = pac::Peripherals::take().unwrap();
let uart = Uarte::new(p.UARTE0, ...);
// p.UARTE0 已消费，不能再次使用
```

### 定理 OWN-T1 ( 外设唯一性 )

每个外设实例在编译时唯一。

$$
\forall p : \text{Peripheral}.\ \exists! i : \text{Instance}.\ i \text{ controls } p
$$

---

## 3. 低功耗模式

### 定义 POWER-1 ( 功耗模式 )

| 模式 | 功耗 | 唤醒源 |
| :--- | :--- | :--- |
| System ON | ~10mA | - |
| Constant Latency | ~5mA | - |
| Low Power | ~1mA | 任何中断 |
| System OFF | ~1μA | RESET, GPIO, LPcomp |

### 定义 POWER-2 ( 模式转换 )

$$
\delta : \text{PowerMode} \times \text{Event} \to \text{PowerMode}
$$

---

## 4. PPI可编程外设互联

### 定义 PPI-1 ( 通道模型 )

$$
\text{PPI} = \{ (E, T) \mid E : \text{Event}, T : \text{Task} \}
$$

**连接**: 事件触发任务，无需CPU介入。

### 定义 PPI-2 ( 通道组 )

```rust
ppi.channel0.set_event_endpoint(timer.compare0());
ppi.channel0.set_task_endpoint(uart.starttx());
ppi.channel0.enable();
```

$$
\text{ChannelGroup} = \{ c_1, c_2, \ldots, c_n \}
$$

### 定理 PPI-T1 ( 零延迟 )

PPI事件到任务延迟是确定性的。

$$
\text{delay}(E \to T) \leq 1 \text{ clock cycle}
$$

---

## 5. EasyDMA

### 定义 DMA-1 ( 缓冲区安全 )

EasyDMA要求缓冲区在DMA传输期间有效。

$$
\text{EasyDMA}(buf) \text{ requires } \text{buf} : 'static \lor \text{scope}(buf) \supseteq \text{transfer}
$$

### 定理 DMA-T1 ( 安全传输 )

EasyDMA传输不会访问无效内存。

$$
\forall t : \text{Transfer}.\ \text{access}(t) \subseteq \text{valid\_memory}
$$

---

## 6. 定理与证明

### 定理 SAFE-T1 ( 配置安全 )

无效外设配置在编译时被拒绝。

$$
\forall c : \text{Config}.\ \text{valid}(c) \lor \text{compile\_error}
$$

---

## 7. 代码示例

### 示例1: UART with EasyDMA

```rust
use nrf_hal::uarte::{Uarte, Pins};
use nrf_hal::gpio::Level;

fn uarte_example(p: pac::Peripherals) {
    let port0 = nrf_hal::gpio::p0::Parts::new(p.P0);

    let uart = Uarte::new(
        p.UARTE0,
        Pins {
            rxd: port0.p0_08.into_floating_input().degrade(),
            txd: port0.p0_06.into_push_pull_output(Level::High).degrade(),
            cts: None,
            rts: None,
        },
        nrf_hal::uarte::Baudrate::BAUD115200,
        nrf_hal::uarte::Parity::EXCLUDED,
    );

    // 静态缓冲区供EasyDMA使用
    static mut TX_BUF: [u8; 32] = [0; 32];

    unsafe {
        TX_BUF[..12].copy_from_slice(b"Hello nRF52!");
        uart.write(&TX_BUF[..12]).unwrap();
    }
}
```

### 示例2: PPI自动触发

```rust
use nrf_hal::ppi::Ppi;
use nrf_hal::timer::Timer;
use nrf_hal::gpio::Pin;

fn ppi_example(p: pac::Peripherals) {
    let mut timer = Timer::new(p.TIMER0);
    let ppi = Ppi::new(p.PPI);

    // 定时器每1秒触发GPIO翻转
    timer.set_period(1_000_000u32); // 1秒

    ppi.channel0.set_event_endpoint(timer.cc0());
    ppi.channel0.set_task_endpoint(pin.outtask());
    ppi.channel0.enable();

    timer.start();
    // GPIO每1秒自动翻转，无需CPU
}
```

### 示例3: 低功耗模式

```rust
use nrf_hal::power::Power;

fn low_power_example(p: pac::Peripherals) {
    let mut power = Power::new(p.POWER);
    let port0 = nrf_hal::gpio::p0::Parts::new(p.P0);

    // 配置按钮唤醒
    let button = port0.p0_13.into_pullup_input();
    power.config_wakeup(button);

    // 进入System OFF模式
    power.system_off();
    // 电流降至~1μA
}
```

### 示例4: SAADC采样

```rust
use nrf_hal::saadc::{Saadc, SaadcConfig, ChannelConfig, Reference, Gain};

fn saadc_example(p: pac::Peripherals) {
    let port0 = nrf_hal::gpio::p0::Parts::new(p.P0);

    let adc = Saadc::new(
        p.SAADC,
        SaadcConfig::default(),
        [
            ChannelConfig {
                pin: port0.p0_02.into_floating_input().degrade(),
                reference: Reference::VDD4,
                gain: Gain::GAIN1_4,
                ..Default::default()
            },
        ],
    );

    let mut buf = [0i16; 1];
    adc.sample(&mut buf).unwrap();
    defmt::info!("ADC value: {}", buf[0]);
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
