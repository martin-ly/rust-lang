# 动手实验练习

## 概述

本指南提供Rust安全关键系统开发的动手实验，从基础练习到高级项目，帮助学习者巩固理论知识。

---

## 实验1: 安全LED闪烁器 (入门)

### 目标

创建一个带故障检测的LED闪烁器

### 要求

- 使用`no_std`
- 实现看门狗喂狗
- 添加故障安全模式

### 代码框架

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;
use stm32f4::stm32f407::Peripherals;

/// 安全LED控制器
pub struct SafeLed {
    gpio: GpioHandle,
    watchdog: Watchdog,
    fault_count: u32,
}

impl SafeLed {
    pub fn new(gpio: GpioHandle, watchdog: Watchdog) -> Self {
        Self {
            gpio,
            watchdog,
            fault_count: 0,
        }
    }

    /// 安全闪烁 - 带看门狗
    pub fn blink_safe(&mut self, times: u32, delay_ms: u32) {
        for _ in 0..times {
            // 检查故障计数
            if self.fault_count > MAX_FAULTS {
                self.enter_fault_mode();
                return;
            }

            // 切换LED
            self.gpio.toggle();

            // 喂狗
            self.watchdog.pet();

            // 延迟
            self.delay_ms(delay_ms);
        }
    }

    fn enter_fault_mode(&mut self) {
        // 故障模式: 快速闪烁
        loop {
            self.gpio.toggle();
            self.delay_ms(100);
        }
    }

    fn delay_ms(&self, ms: u32) {
        // 简单延时
        for _ in 0..ms * 1000 {
            cortex_m::asm::nop();
        }
    }
}

#[entry]
fn main() -> ! {
    let dp = Peripherals::take().unwrap();

    // 配置GPIO
    dp.GPIOA.moder.modify(|_, w| w.moder5().output());

    // 创建安全LED
    let mut led = SafeLed::new(
        GpioHandle::new(&dp.GPIOA),
        Watchdog::new(),
    );

    // 运行
    loop {
        led.blink_safe(5, 500);
    }
}

// TODO: 实现GpioHandle和Watchdog
struct GpioHandle;
struct Watchdog;
```

### 验证点

- [ ] LED按预期闪烁
- [ ] 看门狗正常喂狗
- [ ] 故障模式正确进入

---

## 实验2: 环形缓冲区 (基础)

### 目标

实现一个线程安全的无锁环形缓冲区

### 要求

- 静态分配
- 无锁实现
- 完全测试覆盖

### 代码框架

```rust
//! 无锁环形缓冲区

use core::sync::atomic::{AtomicUsize, Ordering};

pub struct RingBuffer<T, const N: usize> {
    buffer: [T; N],
    head: AtomicUsize,
    tail: AtomicUsize,
}

impl<T: Copy + Default, const N: usize> RingBuffer<T, N> {
    pub fn new() -> Self {
        Self {
            buffer: [T::default(); N],
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
        }
    }

    /// 尝试入队
    pub fn try_push(&self, item: T) -> Result<(), BufferError> {
        let head = self.head.load(Ordering::Relaxed);
        let next_head = (head + 1) % N;

        // 检查满
        if next_head == self.tail.load(Ordering::Acquire) {
            return Err(BufferError::Full);
        }

        // 写入数据
        unsafe {
            core::ptr::write(&self.buffer[head] as *const _ as *mut T, item);
        }

        // 更新head
        self.head.store(next_head, Ordering::Release);

        Ok(())
    }

    /// 尝试出队
    pub fn try_pop(&self) -> Result<T, BufferError> {
        let tail = self.tail.load(Ordering::Relaxed);

        // 检查空
        if tail == self.head.load(Ordering::Acquire) {
            return Err(BufferError::Empty);
        }

        // 读取数据
        let item = unsafe {
            core::ptr::read(&self.buffer[tail])
        };

        // 更新tail
        self.tail.store((tail + 1) % N, Ordering::Release);

        Ok(item)
    }

    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire) == self.tail.load(Ordering::Acquire)
    }

    pub fn is_full(&self) -> bool {
        let next_head = (self.head.load(Ordering::Acquire) + 1) % N;
        next_head == self.tail.load(Ordering::Acquire)
    }
}

#[derive(Debug)]
pub enum BufferError {
    Full,
    Empty,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let buf: RingBuffer<u32, 4> = RingBuffer::new();

        assert!(buf.is_empty());

        buf.try_push(1).unwrap();
        buf.try_push(2).unwrap();

        assert_eq!(buf.try_pop().unwrap(), 1);
        assert_eq!(buf.try_pop().unwrap(), 2);
        assert!(buf.is_empty());
    }

    #[test]
    fn test_full() {
        let buf: RingBuffer<u32, 2> = RingBuffer::new();

        buf.try_push(1).unwrap();
        buf.try_push(2).unwrap(); // 满

        assert!(buf.try_push(3).is_err()); // 失败
    }
}

// TODO:
// 1. 添加Miri测试验证内存安全
// 2. 添加并发压力测试
// 3. 实现Iterator trait
```

---

## 实验3: 状态机控制器 (中级)

### 目标

实现一个带安全监控的状态机

### 要求

- 类型状态模式
- 无效状态转换防护
- 故障恢复

### 代码框架

```rust
//! 类型状态模式实现

/// 状态标记
pub struct Init;
pub struct Ready;
pub struct Running;
pub struct Error;
pub struct Shutdown;

/// 状态机
pub struct StateMachine<S> {
    state: PhantomData<S>,
    data: InternalData,
}

struct InternalData {
    counter: u32,
    error_count: u32,
}

impl StateMachine<Init> {
    pub fn new() -> Self {
        Self {
            state: PhantomData,
            data: InternalData {
                counter: 0,
                error_count: 0,
            },
        }
    }

    pub fn initialize(self) -> Result<StateMachine<Ready>, ErrorCode> {
        // 初始化检查
        if self.self_test() {
            Ok(StateMachine {
                state: PhantomData,
                data: self.data,
            })
        } else {
            Err(ErrorCode::InitFailed)
        }
    }

    fn self_test(&self) -> bool {
        // 自检逻辑
        true
    }
}

impl StateMachine<Ready> {
    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            state: PhantomData,
            data: self.data,
        }
    }
}

impl StateMachine<Running> {
    pub fn process(&mut self) -> Result<(), ErrorCode> {
        self.data.counter += 1;

        if self.data.counter > 100 {
            return Err(ErrorCode::Overflow);
        }

        Ok(())
    }

    pub fn stop(self) -> StateMachine<Ready> {
        StateMachine {
            state: PhantomData,
            data: self.data,
        }
    }

    pub fn handle_error(self, _err: ErrorCode) -> StateMachine<Error> {
        StateMachine {
            state: PhantomData,
            data: InternalData {
                counter: 0,
                error_count: self.data.error_count + 1,
            },
        }
    }
}

impl StateMachine<Error> {
    pub fn can_recover(&self) -> bool {
        self.data.error_count < 3
    }

    pub fn recover(self) -> Option<StateMachine<Init>> {
        if self.can_recover() {
            Some(StateMachine {
                state: PhantomData,
                data: InternalData {
                    counter: 0,
                    error_count: self.data.error_count,
                },
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum ErrorCode {
    InitFailed,
    Overflow,
    InvalidTransition,
}

// TODO:
// 1. 添加事件队列
// 2. 实现日志记录
// 3. 添加超时处理
```

---

## 实验4: 传感器驱动 (高级)

### 目标

实现一个带校准和故障检测的传感器驱动

### 要求

- 硬件抽象层
- 数据滤波
- 故障注入测试

### 代码框架

```rust
//! 传感器驱动

/// 传感器接口
trait Sensor {
    type Error;
    fn read_raw(&mut self) -> Result<u16, Self::Error>;
    fn is_connected(&self) -> bool;
}

/// 温度传感器驱动
pub struct TemperatureSensor<S: Sensor> {
    sensor: S,
    calibration: CalibrationData,
    history: [f32; 10],
    index: usize,
}

struct CalibrationData {
    offset: f32,
    gain: f32,
}

impl<S: Sensor> TemperatureSensor<S> {
    pub fn new(sensor: S) -> Self {
        Self {
            sensor,
            calibration: CalibrationData {
                offset: 0.0,
                gain: 1.0,
            },
            history: [0.0; 10],
            index: 0,
        }
    }

    /// 读取温度
    pub fn read_temperature(&mut self) -> Result<f32, SensorError> {
        // 检查连接
        if !self.sensor.is_connected() {
            return Err(SensorError::Disconnected);
        }

        // 读取原始值
        let raw = self.sensor.read_raw()
            .map_err(|_| SensorError::ReadFailed)?;

        // 转换为温度
        let temp = self.convert(raw);

        // 合理性检查
        if !self.is_plausible(temp) {
            return Err(SensorError::OutOfRange);
        }

        // 滤波
        let filtered = self.filter(temp);

        // 更新历史
        self.history[self.index] = filtered;
        self.index = (self.index + 1) % 10;

        Ok(filtered)
    }

    fn convert(&self, raw: u16) -> f32 {
        (raw as f32 * self.calibration.gain) + self.calibration.offset
    }

    fn is_plausible(&self, temp: f32) -> bool {
        temp >= -40.0 && temp <= 125.0
    }

    fn filter(&self, new_value: f32) -> f32 {
        // 简单移动平均
        let sum: f32 = self.history.iter().sum();
        (sum + new_value) / 11.0
    }

    /// 校准
    pub fn calibrate(&mut self, reference: f32) -> Result<(), SensorError> {
        let raw = self.sensor.read_raw()
            .map_err(|_| SensorError::CalibrationFailed)?;

        let measured = raw as f32;
        self.calibration.gain = reference / measured;

        Ok(())
    }
}

#[derive(Debug)]
pub enum SensorError {
    Disconnected,
    ReadFailed,
    OutOfRange,
    CalibrationFailed,
}

// TODO:
// 1. 实现更多滤波算法
// 2. 添加故障注入测试
// 3. 实现看门狗监控
```

---

## 实验5: 安全通信协议 (专家)

### 目标

实现一个带E2E保护的简单通信协议

### 要求

- CRC校验
- 序列号验证
- 重放攻击防护

### 代码框架

```rust
//! 安全通信协议

use crc::{Crc, CRC_16_USB};

const CRC: Crc<u16> = Crc::<u16>::new(&CRC_16_USB);

/// 安全帧
pub struct SecureFrame {
    sequence_number: u32,
    data: [u8; 64],
    data_len: u8,
    crc: u16,
}

/// 通信端点
pub struct SecureEndpoint {
    tx_seq: u32,
    rx_seq: u32,
    last_rx_time: u64,
    timeout_ms: u64,
}

impl SecureEndpoint {
    pub fn new(timeout_ms: u64) -> Self {
        Self {
            tx_seq: 0,
            rx_seq: 0,
            last_rx_time: 0,
            timeout_ms,
        }
    }

    /// 发送帧
    pub fn send(&mut self, data: &[u8]) -> SecureFrame {
        assert!(data.len() <= 64);

        let mut frame = SecureFrame {
            sequence_number: self.tx_seq,
            data: [0; 64],
            data_len: data.len() as u8,
            crc: 0,
        };

        frame.data[..data.len()].copy_from_slice(data);
        frame.crc = self.calculate_crc(&frame);

        self.tx_seq = self.tx_seq.wrapping_add(1);

        frame
    }

    /// 接收帧
    pub fn receive(&mut self, frame: &SecureFrame, current_time: u64) -> Result<&[u8], CommError> {
        // 检查超时
        if current_time - self.last_rx_time > self.timeout_ms {
            return Err(CommError::Timeout);
        }

        // CRC验证
        if frame.crc != self.calculate_crc(frame) {
            return Err(CommError::CrcError);
        }

        // 序列号验证
        if frame.sequence_number != self.rx_seq {
            return Err(CommError::SequenceError);
        }

        // 更新接收状态
        self.rx_seq = self.rx_seq.wrapping_add(1);
        self.last_rx_time = current_time;

        Ok(&frame.data[..frame.data_len as usize])
    }

    fn calculate_crc(&self, frame: &SecureFrame) -> u16 {
        let mut digest = CRC.digest();
        digest.update(&frame.sequence_number.to_le_bytes());
        digest.update(&frame.data);
        digest.update(&[frame.data_len]);
        digest.finalize()
    }
}

#[derive(Debug)]
pub enum CommError {
    Timeout,
    CrcError,
    SequenceError,
    BufferOverflow,
}

// TODO:
// 1. 添加加密层
// 2. 实现重传机制
// 3. 添加认证
```

---

## 实验检查清单

### 实验1: LED闪烁器

- [ ] 代码编译通过
- [ ] 看门狗正确喂狗
- [ ] 故障模式测试通过
- [ ] 代码审查完成

### 实验2: 环形缓冲区

- [ ] Miri测试通过
- [ ] 单元测试100%覆盖
- [ ] 并发测试通过
- [ ] 边界测试完成

### 实验3: 状态机

- [ ] 类型状态模式正确
- [ ] 无效转换被阻止
- [ ] 状态转换测试覆盖
- [ ] 故障恢复测试

### 实验4: 传感器驱动

- [ ] 校准功能正确
- [ ] 滤波算法验证
- [ ] 故障注入测试
- [ ] 性能测试通过

### 实验5: 通信协议

- [ ] CRC校验正确
- [ ] 序列号验证
- [ ] 重放攻击防护
- [ ] 边界条件测试

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用级别**: 初学者到专家

---

*实践是掌握Rust安全关键开发的最佳途径。*
