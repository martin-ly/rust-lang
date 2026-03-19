# IEC 61508 Rust实施指南

## 概述

IEC 61508是工业领域功能安全的国际标准，涵盖电气/电子/可编程电子系统的安全生命周期。本指南提供使用Rust满足IEC 61508要求的详细实施路径。

---

## IEC 61508结构概览

```
IEC 61508-x:
├── Part 1: 一般要求
├── Part 2: 电气/电子/可编程电子系统的要求
├── Part 3: 软件要求 ⭐ 核心关注
├── Part 4: 定义和缩略语
├── Part 5: 确定安全完整性等级的方法示例
├── Part 6: 应用指南2 (软件)
├── Part 7: 技术和措施概览
└── Part 8: 应用指南1 (整体安全生命周期)
```

---

## Part 3: 软件要求详解

### 7.4.2 软件安全需求规范

#### 安全完整性等级(SIL)映射

| SIL | 风险降低因子 | Rust适用性 | 关键要求 |
|-----|--------------|------------|----------|
| **SIL 4** | > 10,000 | 高 | 形式化验证 + 多样性 |
| **SIL 3** | 1,000-10,000 | 高 | 强类型 + 静态分析 |
| **SIL 2** | 100-1,000 | 很高 | 标准Rust + 测试 |
| **SIL 1** | 10-100 | 很高 | 标准Rust |

#### Rust优势在IEC 61508中的体现

```rust
//! SIL 3级工业控制器示例
//!
//! IEC 61508-3 Table A.1 技术措施Rust实现

#![forbid(unsafe_code)]  // 7.4.2.3a: 结构化编程
#![deny(clippy::all)]

/// 7.4.2.3a: 模块化设计
pub mod safety_functions {
    /// 7.4.2.3b: 强类型
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Pressure(u16);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Temperature(i16);

    /// 7.4.2.3e: 范围检查
    impl Pressure {
        pub const MIN: u16 = 0;
        pub const MAX: u16 = 1000; // 10 bar * 100

        pub fn new(raw: u16) -> Result<Self, SafetyError> {
            if raw <= Self::MAX {
                Ok(Self(raw))
            } else {
                Err(SafetyError::OutOfRange)
            }
        }

        pub fn as_bar(&self) -> f64 {
            f64::from(self.0) / 100.0
        }
    }

    /// 7.4.2.3c: 防御性编程
    pub fn calculate_safety_action(
        pressure: Pressure,
        temperature: Temperature,
        mode: OperationMode,
    ) -> SafetyAction {
        // 参数已经在类型层面验证

        match mode {
            OperationMode::Normal => {
                if pressure.as_bar() > 8.5 {
                    SafetyAction::OpenReliefValve
                } else if temperature.0 > 150 {
                    SafetyAction::ReducePower
                } else {
                    SafetyAction::Continue
                }
            }
            OperationMode::Maintenance => {
                // 维护模式: 更保守的阈值
                if pressure.as_bar() > 5.0 {
                    SafetyAction::OpenReliefValve
                } else {
                    SafetyAction::Continue
                }
            }
            OperationMode::Emergency => {
                // 紧急模式: 立即安全动作
                SafetyAction::EmergencyShutdown
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum OperationMode {
    Normal,
    Maintenance,
    Emergency,
}

#[derive(Debug, Clone, Copy)]
pub enum SafetyAction {
    Continue,
    ReducePower,
    OpenReliefValve,
    EmergencyShutdown,
}

#[derive(Debug, Clone, Copy)]
pub enum SafetyError {
    OutOfRange,
    CommunicationFailure,
    SensorFault,
}
```

### 7.4.3 软件安全验证

#### 验证方法表(Annex B)

| 方法 | SIL 1 | SIL 2 | SIL 3 | SIL 4 | Rust工具 |
|------|-------|-------|-------|-------|----------|
| 静态分析 | R | R | HR | HR | Clippy |
| 动态分析 | R | HR | HR | HR | Miri, Valgrind |
| 数据记录分析 | - | R | HR | HR | tracing |
| 功能测试 | HR | HR | HR | HR | cargo test |
| 边界值分析 | R | R | HR | HR | proptest |
| 等价类划分 | R | HR | HR | HR | quickcheck |
| 现场测试 | R | R | HR | HR | - |
| 形式化验证 | - | - | R | HR | Kani, Verus |
| 模型检查 | - | - | R | HR | Kani |

```rust
/// SIL 3形式化验证示例
///
/// 使用Kani验证安全功能

#[cfg(kani)]
mod verification {
    use super::*;
    use kani::proof;

    /// 验证: 高压总是触发安全动作
    #[proof]
    fn verify_high_pressure_safety() {
        let pressure = Pressure::new(kani::any()).unwrap();
        let temperature = Temperature(kani::any());
        let mode = OperationMode::Normal;

        // 假设: 压力超过8.5 bar
        kani::assume(pressure.as_bar() > 8.5);

        let action = calculate_safety_action(pressure, temperature, mode);

        // 验证: 必须打开安全阀
        assert!(matches!(action, SafetyAction::OpenReliefValve | SafetyAction::EmergencyShutdown));
    }

    /// 验证: 紧急模式总是紧急关闭
    #[proof]
    fn verify_emergency_mode() {
        let pressure = Pressure::new(kani::any()).unwrap();
        let temperature = Temperature(kani::any());

        let action = calculate_safety_action(
            pressure,
            temperature,
            OperationMode::Emergency
        );

        assert_eq!(action, SafetyAction::EmergencyShutdown);
    }
}
```

---

## Part 6: 软件开发和验证技术

### Table A.1 - 设计和编码技术

```rust
//! IEC 61508-3 Table A.1 Rust实现

/// 1a. 模块化
pub mod modular_design {
    /// 独立功能模块
    pub struct SafetyChannel {
        sensor: SensorInterface,
        logic: SafetyLogic,
        output: OutputInterface,
    }

    impl SafetyChannel {
        /// 独立执行周期
        pub fn cycle(&mut self) -> Result<OutputState, ChannelError> {
            let input = self.sensor.read()?;
            let decision = self.logic.evaluate(input)?;
            self.output.set(decision)
        }
    }
}

/// 1b. 组件大小限制
/// Clippy配置: cognitive-complexity-threshold = 15

/// 2a. 强类型
pub struct Celsius(f64);
pub struct Fahrenheit(f64);

impl Celsius {
    pub fn new(value: f64) -> Result<Self, Error> {
        if value >= -273.15 {
            Ok(Self(value))
        } else {
            Err(Error::BelowAbsoluteZero)
        }
    }
}

impl TryFrom<Fahrenheit> for Celsius {
    type Error = Error;

    fn try_from(f: Fahrenheit) -> Result<Self, Self::Error> {
        let c = (f.0 - 32.0) * 5.0 / 9.0;
        Self::new(c)
    }
}

/// 2b. 数据流分析 - 借用检查器自动执行
fn data_flow_example() {
    let data = vec![1, 2, 3];
    let ref1 = &data;  // 创建引用
    let ref2 = &data;  // 另一个共享引用
    // data.push(4);   // 编译错误: 不能修改已借用的数据
    println!("{} {}", ref1[0], ref2[0]);
}

/// 3. 复杂度限制
/// clippy.toml配置:
/// cognitive-complexity-threshold = 15
/// cyclomatic-complexity-threshold = 10
/// too-many-lines-threshold = 50

/// 4. 编码标准
/// rustfmt.toml配置统一格式

/// 7. 使用已验证的软件模块/组件
pub struct ValidatedComponent {
    // 核心功能已验证
    inner: core::ValidatedLogic,
}

/// 8. 内存动态影响分析
/// Miri运行检测

/// 9. 通信故障处理
#[derive(Debug)]
pub enum CommunicationResult<T> {
    Success(T),
    Timeout,
    ChecksumError,
    SequenceError,
}
```

### Table A.2 - 数据导向技术

```rust
//! IEC 61508-3 Table A.2 Rust实现

/// 1a. 等价类分析 - 使用property testing
#[cfg(test)]
mod equivalence_classes {
    use proptest::prelude::*;

    proptest! {
        /// 测试等价类: 正压/负压
        #[test]
        fn pressure_equivalence_classes(raw in 0u16..=1000) {
            let pressure = Pressure::new(raw);
            prop_assert!(pressure.is_ok());
        }
    }
}

/// 1b. 边界值分析
#[test]
fn boundary_value_analysis() {
    // 最小边界
    assert!(Pressure::new(0).is_ok());

    // 最大边界
    assert!(Pressure::new(1000).is_ok());

    // 超出边界
    assert!(Pressure::new(1001).is_err());

    // 边界附近
    assert!(Pressure::new(999).is_ok());
}

/// 2. 基于概率测试
/// cargo-fuzz集成

/// 3. 数据记录分析
use tracing::{info, warn, error};

pub fn monitored_operation() {
    info!("操作开始");

    match perform_safety_check() {
        Ok(result) => info!(result = ?result, "检查通过"),
        Err(e) => {
            error!(error = ?e, "安全违规");
            enter_safe_state();
        }
    }
}

fn perform_safety_check() -> Result<SafetyResult, SafetyError> {
    // 实现...
    Ok(SafetyResult::Safe)
}

fn enter_safe_state() {
    warn!("进入安全状态");
}
```

---

## Part 7: 技术和措施

### 系统性能力(SCL)评估

```
系统能力等级评估矩阵:

                    SIL 1   SIL 2   SIL 3   SIL 4
系统性能力        SCL 1   SCL 2   SCL 3   SCL 4
系统性能力3       R       R       HR      HR
系统性能力2       R       HR      HR      -
系统性能力1       HR      HR      -       -

Rust适用性: SCL 2-3
```

### 硬件容错要求

```rust
//! IEC 61508-2 硬件容错架构Rust实现

/// 1oo1架构 - 单通道
pub struct SingleChannel {
    logic: SafetyLogic,
}

/// 1oo2架构 - 双通道比较
pub struct DualChannel {
    channel_a: SafetyChannel,
    channel_b: SafetyChannel,
    comparator: Comparator,
}

impl DualChannel {
    pub fn evaluate(&mut self, input: SensorInput) -> SafetyOutput {
        let output_a = self.channel_a.process(input);
        let output_b = self.channel_b.process(input);

        self.comparator.compare(output_a, output_b)
    }
}

/// 2oo3架构 - 三取二
pub struct TripleModularRedundancy {
    channels: [SafetyChannel; 3],
    voter: Voter,
}

impl TripleModularRedundancy {
    pub fn vote(&mut self, input: SensorInput) -> SafetyOutput {
        let outputs = [
            self.channels[0].process(input),
            self.channels[1].process(input),
            self.channels[2].process(input),
        ];

        self.voter.majority_vote(&outputs)
    }
}

struct Voter;

impl Voter {
    fn majority_vote(&self, outputs: &[SafetyOutput; 3]) -> SafetyOutput {
        // 如果至少两个输出一致，返回该输出
        // 否则进入安全状态
        if outputs[0] == outputs[1] {
            outputs[0]
        } else if outputs[0] == outputs[2] {
            outputs[0]
        } else if outputs[1] == outputs[2] {
            outputs[1]
        } else {
            SafetyOutput::SafeState
        }
    }
}
```

---

## 工业协议集成

### Modbus RTU/TCP

```rust
//! SIL 2级Modbus实现

use std::time::Duration;

/// Modbus从站(工业控制器)
pub struct ModbusSlave {
    registers: [u16; 1000],
    coils: [bool; 1000],
    client: Box<dyn ModbusTransport>,
}

impl ModbusSlave {
    /// 处理请求
    pub fn handle_request(&mut self, request: Request) -> Result<Response, ModbusError> {
        match request.function_code {
            0x03 => self.read_holding_registers(request),
            0x04 => self.read_input_registers(request),
            0x06 => self.write_single_register(request),
            _ => Err(ModbusError::IllegalFunction),
        }
    }

    fn read_holding_registers(&self, request: Request) -> Result<Response, ModbusError> {
        let start = request.address as usize;
        let count = request.quantity as usize;

        // 边界检查
        if start + count > self.registers.len() {
            return Err(ModbusError::IllegalDataAddress);
        }

        let data = &self.registers[start..start + count];
        Ok(Response {
            data: data.to_vec(),
        })
    }

    fn write_single_register(&mut self, request: Request) -> Result<Response, ModbusError> {
        let addr = request.address as usize;

        if addr >= self.registers.len() {
            return Err(ModbusError::IllegalDataAddress);
        }

        // 安全检查: 某些寄存器只读
        if !self.is_writable(addr) {
            return Err(ModbusError::IllegalDataValue);
        }

        self.registers[addr] = request.value;
        Ok(Response { data: vec![] })
    }

    fn is_writable(&self, addr: usize) -> bool {
        // 系统寄存器保护
        addr >= 100
    }
}

pub trait ModbusTransport {
    fn send(&mut self, data: &[u8]) -> Result<(), TransportError>;
    fn receive(&mut self, timeout: Duration) -> Result<Vec<u8>, TransportError>;
}
```

### OPC UA

```rust
//! SIL 3级OPC UA服务器

use opcua::server::prelude::*;

pub struct SafetyOpcUaServer {
    server: Server,
    safety_namespace: u16,
}

impl SafetyOpcUaServer {
    pub fn new() -> Self {
        let server = ServerBuilder::new()
            .application_name("Safety OPC UA Server")
            .application_uri("urn:safety:opcua:server")
            .create_sample_keypair(true)
            .host_and_port("0.0.0.0", 4840)
            .server()
            .unwrap();

        Self {
            server,
            safety_namespace: 1,
        }
    }

    pub fn add_safety_variables(&mut self) {
        let address_space = self.server.address_space();
        let ns = self.safety_namespace;

        // 添加安全相关变量
        address_space.add_variables(vec![
            Variable::new(
                &NodeId::new(ns, "Pressure"),
                "Pressure",
                "Pressure",
                DataValue::new(0.0f64),
            ),
            Variable::new(
                &NodeId::new(ns, "Temperature"),
                "Temperature",
                "Temperature",
                DataValue::new(0.0f64),
            ),
            Variable::new(
                &NodeId::new(ns, "SafetyState"),
                "SafetyState",
                "Safety State",
                DataValue::new("Normal"),
            ),
        ]);
    }
}
```

---

## 开发检查表

### SIL 4项目完整检查表

#### 需求阶段

- [ ] 安全功能需求规范(SRS)完成
- [ ] 安全完整性等级确定
- [ ] 风险分析完成
- [ ] 需求追溯矩阵建立

#### 设计阶段

- [ ] 软件架构设计(SAD)完成
- [ ] 模块化设计验证
- [ ] 接口定义审查
- [ ] 故障树分析(FTA)完成
- [ ] 共因失效分析(CCF)完成

#### 实现阶段

- [ ] 编码标准遵守(MISRA Rust)
- [ ] 圈复杂度<=10
- [ ] 无unsafe代码
- [ ] 静态分析通过(Clippy)
- [ ] 形式化验证通过(Kani)

#### 验证阶段

- [ ] 单元测试100% MC/DC覆盖
- [ ] 集成测试完成
- [ ] 故障注入测试
- [ ] 形式化验证报告
- [ ] 静态分析报告
- [ ] 资源使用分析

#### 认证阶段

- [ ] 功能安全评估(FSA)
- [ ] 安全案例准备
- [ ] 工具链鉴定报告
- [ ] 审核支持

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用标准**: IEC 61508:2010 (Parts 2, 3, 6, 7)

---

*本文档应与IEC 61508标准原文配合使用。*
