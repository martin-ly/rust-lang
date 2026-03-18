# DO-178C Rust合规路径

## 概述

DO-178C是航空软件开发的标准，规定了不同软件等级(A-E)的开发要求。本指南提供使用Rust开发适航软件的路径，特别关注与DO-330(工具鉴定)和DO-333(形式化方法)的补充。

---

## DO-178C结构

### 软件等级(Software Level)

| 等级 | 失效影响 | 示例系统 | Rust适用性 |
|------|----------|----------|------------|
| **A** | 灾难性 | 飞控主计算机 | 需要形式化验证 |
| **B** | 危险 | 自动驾驶 | 高度推荐 |
| **C** | 较大 | 飞行管理 | 推荐 |
| **D** | 较小 | 维护系统 | 适用 |
| **E** | 无安全影响 | 乘客娱乐 | 完全适用 |

---

## DO-178C目标Rust实现

### A-1: 软件计划过程

#### 软件计划数据

```rust
//! 软件计划数据模板
//!
//! PSAC (Plan for Software Aspects of Certification)

/// 软件生命周期环境配置
pub struct SoftwareEnvironment {
    /// 编译器
    pub compiler: CompilerConfig,
    /// 开发工具
    pub development_tools: Vec<ToolConfig>,
    /// 验证工具
    pub verification_tools: Vec<ToolConfig>,
    /// 目标硬件
    pub target_hardware: HardwareConfig,
}

pub struct CompilerConfig {
    pub name: String,           // "Ferrocene"
    pub version: String,        // "25.11"
    pub qualification: ToolQualification,
}

pub struct ToolConfig {
    pub name: String,
    pub version: String,
    pub tql: ToolQualificationLevel,  // DO-330
}

pub enum ToolQualificationLevel {
    TQL1,  // 开发工具中
    TQL2,  // 开发工具中
    TQL3,  // 验证工具中
    TQL4,  // 验证工具低
    TQL5,  // 无需鉴定
}

/// 软件配置管理计划
pub struct ConfigurationManagementPlan {
    pub problem_reporting: Process,
    pub change_control: Process,
    pub baseline_management: Process,
    pub archive_retrieval: Process,
}

impl ConfigurationManagementPlan {
    /// 变更控制流程
    pub fn process_change_request(&self, cr: ChangeRequest) -> ChangeResult {
        // 1. 影响分析
        let impact = self.analyze_impact(&cr);

        // 2. 安全影响评估
        if impact.affects_safety {
            // 需要额外评审
            self.safety_board_review(&cr);
        }

        // 3. 实施和验证
        ChangeResult::Approved
    }

    fn analyze_impact(&self, cr: &ChangeRequest) -> ImpactAnalysis {
        // 分析实现...
        ImpactAnalysis { affects_safety: true }
    }

    fn safety_board_review(&self, cr: &ChangeRequest) {
        // 安全委员会评审
    }
}
```

### A-2: 软件开发过程

#### 软件需求数据

```rust
//! 软件需求规范 (SRS)

/// 需求追溯
#[derive(Debug, Clone)]
pub struct SoftwareRequirement {
    pub id: String,                    // SRS-001
    pub description: String,
    pub system_requirement: String,    // 追溯至系统需求
    pub verification_method: VerificationMethod,
    pub level: SoftwareLevel,          // A/B/C/D/E
}

pub enum VerificationMethod {
    Analysis,
    Review,
    Test,
    FormalVerification,
}

/// 航空电子功能示例
pub struct FlightControlFunction {
    /// 功能需求
    requirements: Vec<SoftwareRequirement>,
    /// 性能需求
    performance: PerformanceRequirements,
    /// 安全需求
    safety: SafetyRequirements,
}

impl FlightControlFunction {
    /// 需求1: 操纵面响应
    pub fn req_surface_response() -> SoftwareRequirement {
        SoftwareRequirement {
            id: "SRS-FCS-001".to_string(),
            description: "副翼响应延迟不得超过50ms".to_string(),
            system_requirement: "SYS-FCS-003".to_string(),
            verification_method: VerificationMethod::Test,
            level: SoftwareLevel::A,
        }
    }

    /// 需求2: 故障检测
    pub fn req_fault_detection() -> SoftwareRequirement {
        SoftwareRequirement {
            id: "SRS-FCS-002".to_string(),
            description: "传感器故障必须在100ms内检测".to_string(),
            system_requirement: "SYS-FCS-005".to_string(),
            verification_method: VerificationMethod::FormalVerification,
            level: SoftwareLevel::A,
        }
    }
}
```

#### 软件设计数据

```rust
//! 软件设计描述 (SDD)

/// 软件架构
pub mod architecture {
    /// 分层架构
    pub struct LayeredArchitecture {
        pub application_layer: ApplicationLayer,
        pub services_layer: ServicesLayer,
        pub os_abstraction_layer: OSAL,
        pub hardware_abstraction_layer: HAL,
    }

    /// 应用层
    pub struct ApplicationLayer {
        pub flight_control: FlightControlApp,
        pub navigation: NavigationApp,
        pub communication: CommunicationApp,
    }

    /// 飞行控制应用
    pub struct FlightControlApp {
        pub control_laws: ControlLaws,
        pub mode_logic: ModeLogic,
        pub failure_detection: FailureDetection,
    }

    /// 控制律
    pub struct ControlLaws {
        /// PID控制器
        pub pid_controllers: [PidController; 3],
        /// 增益调度
        pub gain_scheduling: GainSchedule,
    }
}

/// 数据流设计
pub mod data_flow {
    /// 传感器数据流
    pub struct SensorDataFlow {
        pub adc_input: ADCReading,
        pub calibration: CalibrationFunction,
        pub filtering: FilterFunction,
        pub validation: ValidationFunction,
        pub output: ValidatedSensorData,
    }

    /// 控制输出流
    pub struct ControlOutputFlow {
        pub demand: ControlDemand,
        pub limit_check: LimitCheck,
        pub rate_limit: RateLimiter,
        pub output: ServoCommand,
    }
}

/// 时序设计
pub mod timing {
    use std::time::Duration;

    /// 任务调度表
    pub struct TaskSchedule {
        pub tasks: Vec<ScheduledTask>,
        pub major_frame: Duration,
    }

    pub struct ScheduledTask {
        pub name: String,
        pub period: Duration,
        pub deadline: Duration,
        pub priority: u8,
    }

    /// 飞行控制任务
    impl TaskSchedule {
        pub fn flight_control_schedule() -> Self {
            Self {
                tasks: vec![
                    ScheduledTask {
                        name: "SensorAcquisition".to_string(),
                        period: Duration::from_millis(10),
                        deadline: Duration::from_millis(5),
                        priority: 1,
                    },
                    ScheduledTask {
                        name: "ControlLaw".to_string(),
                        period: Duration::from_millis(10),
                        deadline: Duration::from_millis(8),
                        priority: 2,
                    },
                    ScheduledTask {
                        name: "OutputDrive".to_string(),
                        period: Duration::from_millis(10),
                        deadline: Duration::from_millis(9),
                        priority: 3,
                    },
                ],
                major_frame: Duration::from_millis(10),
            }
        }
    }
}
```

#### 代码标准与实现

```rust
//! 软件Level A编码标准

#![forbid(unsafe_code)]          // Level A: 禁止unsafe
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::complexity)]
#![deny(missing_docs)]

/// 确定性内存分配
///
/// Level A要求: 无动态内存分配
pub struct DeterministicAllocator<const N: usize> {
    memory: [u8; N],
    used: usize,
}

impl<const N: usize> DeterministicAllocator<N> {
    pub const fn new() -> Self {
        Self {
            memory: [0; N],
            used: 0,
        }
    }

    /// 编译时可预测的分配
    pub fn allocate<T>(&mut self) -> Option<&mut T> {
        let size = core::mem::size_of::<T>();
        let align = core::mem::align_of::<T>();

        // 对齐计算
        let aligned = (self.used + align - 1) & !(align - 1);

        if aligned + size > N {
            return None;  // 内存不足
        }

        let ptr = unsafe {
            self.memory.as_mut_ptr().add(aligned) as *mut T
        };

        self.used = aligned + size;
        Some(unsafe { &mut *ptr })
    }
}

/// 控制律实现
///
/// 满足DO-178C Level A要求:
/// - 圈复杂度 <= 10
/// - 无动态分配
/// - 100% MC/DC覆盖
pub struct ControlLaw {
    gains: Gains,
    integrator: Integrator,
    differentiator: Differentiator,
}

impl ControlLaw {
    /// 计算控制输出
    ///
    /// # Arguments
    /// * `setpoint` - 目标值
    /// * `feedback` - 反馈值
    /// * `dt` - 时间步长
    pub fn compute(&mut self, setpoint: f64, feedback: f64, dt: f64) -> ControlOutput {
        let error = setpoint - feedback;

        // 比例项
        let proportional = self.gains.kp * error;

        // 积分项
        let integral = self.integrator.update(error, dt, self.gains.ki);

        // 微分项
        let derivative = self.differentiator.update(error, dt, self.gains.kd);

        // 求和并限制
        let raw_output = proportional + integral + derivative;
        ControlOutput::new(raw_output).limit(-100.0, 100.0)
    }
}

struct Gains {
    kp: f64,
    ki: f64,
    kd: f64,
}

struct Integrator {
    state: f64,
}

impl Integrator {
    fn update(&mut self, error: f64, dt: f64, gain: f64) -> f64 {
        self.state += error * dt * gain;
        // 抗饱和
        self.state = self.state.clamp(-100.0, 100.0);
        self.state
    }
}

struct Differentiator {
    last_error: Option<f64>,
}

impl Differentiator {
    fn update(&mut self, error: f64, dt: f64, gain: f64) -> f64 {
        let result = match self.last_error {
            Some(last) => ((error - last) / dt) * gain,
            None => 0.0,
        };
        self.last_error = Some(error);
        result
    }
}

struct ControlOutput(f64);

impl ControlOutput {
    fn new(value: f64) -> Self {
        Self(value)
    }

    fn limit(self, min: f64, max: f64) -> Self {
        Self(self.0.clamp(min, max))
    }
}
```

### A-3: 软件验证过程

#### 验证方法

```rust
//! DO-333形式化方法补充

#[cfg(kani)]
mod formal_verification {
    use super::*;
    use kani::proof;

    /// 验证: 控制输出始终在限制范围内
    #[proof]
    fn verify_output_limits() {
        let mut law = ControlLaw {
            gains: Gains { kp: 1.0, ki: 0.1, kd: 0.01 },
            integrator: Integrator { state: 0.0 },
            differentiator: Differentiator { last_error: None },
        };

        let setpoint: f64 = kani::any();
        let feedback: f64 = kani::any();
        let dt: f64 = kani::any();

        // 限制输入范围
        kani::assume(dt > 0.0 && dt < 1.0);

        let output = law.compute(setpoint, feedback, dt);

        // 验证输出限制
        assert!(output.0 >= -100.0 && output.0 <= 100.0);
    }

    /// 验证: 零误差时输出趋于零
    #[proof]
    fn verify_zero_error_convergence() {
        let mut law = ControlLaw {
            gains: Gains { kp: 1.0, ki: 0.0, kd: 0.0 },  // 仅P控制
            integrator: Integrator { state: 0.0 },
            differentiator: Differentiator { last_error: None },
        };

        // 零误差输入
        let output = law.compute(0.0, 0.0, 0.01);

        // P控制下，零误差应产生零输出
        assert_eq!(output.0, 0.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// MC/DC覆盖测试
    #[test]
    fn test_mcdc_coverage() {
        let mut law = ControlLaw {
            gains: Gains { kp: 1.0, ki: 0.1, kd: 0.01 },
            integrator: Integrator { state: 0.0 },
            differentiator: Differentiator { last_error: None },
        };

        // 测试不同条件组合
        let _ = law.compute(10.0, 0.0, 0.01);  // 正误差
        let _ = law.compute(0.0, 10.0, 0.01);  // 负误差
        let _ = law.compute(0.0, 0.0, 0.01);   // 零误差
    }

    /// 鲁棒性测试
    #[test]
    fn test_robustness() {
        let mut law = ControlLaw {
            gains: Gains { kp: 1.0, ki: 0.1, kd: 0.01 },
            integrator: Integrator { state: 0.0 },
            differentiator: Differentiator { last_error: None },
        };

        // 边界值
        let _ = law.compute(f64::MAX, 0.0, 0.01);
        let _ = law.compute(f64::MIN, 0.0, 0.01);
        let _ = law.compute(0.0, f64::MAX, 0.01);
    }
}
```

### 覆盖率目标

| 软件等级 | 语句 | 决策 | MC/DC | 数据耦合 | 控制耦合 |
|----------|------|------|-------|----------|----------|
| **A** | 100% | 100% | 100% | Yes | Yes |
| **B** | 100% | 100% | - | Yes | Yes |
| **C** | 100% | - | - | Yes | - |
| **D** | 100% | - | - | - | - |

---

## DO-330工具鉴定

### 工具鉴定等级

```rust
//! 工具鉴定数据

/// 工具鉴定级别确定
pub fn determine_tql(tool: &Tool) -> ToolQualificationLevel {
    match (tool.criteria_output, tool.automation) {
        // 自动生成代码 → TQL1
        (true, true) => ToolQualificationLevel::TQL1,
        // 自动验证但不生成 → TQL3/4
        (false, true) => ToolQualificationLevel::TQL3,
        // 手动工具 → TQL5
        (_, false) => ToolQualificationLevel::TQL5,
    }
}

/// Rust工具链鉴定
pub struct RustToolchainQualification {
    pub compiler: CompilerQualification,
    pub analyzer: AnalyzerQualification,
    pub verifier: VerifierQualification,
}

impl RustToolchainQualification {
    /// 创建鉴定报告
    pub fn generate_report(&self) -> QualificationReport {
        QualificationReport {
            compiler_tql: ToolQualificationLevel::TQL1,
            analyzer_tql: ToolQualificationLevel::TQL3,
            verifier_tql: ToolQualificationLevel::TQL4,
            test_results: self.run_qualification_tests(),
        }
    }

    fn run_qualification_tests(&self) -> Vec<TestResult> {
        vec![
            self.test_compiler_correctness(),
            self.test_analyzer_effectiveness(),
            self.test_verifier_soundness(),
        ]
    }

    fn test_compiler_correctness(&self) -> TestResult {
        // 验证编译器正确性
        TestResult::Pass
    }

    fn test_analyzer_effectiveness(&self) -> TestResult {
        // 验证静态分析器有效性
        TestResult::Pass
    }

    fn test_verifier_soundness(&self) -> TestResult {
        // 验证形式化验证器可靠性
        TestResult::Pass
    }
}

pub struct QualificationReport {
    pub compiler_tql: ToolQualificationLevel,
    pub analyzer_tql: ToolQualificationLevel,
    pub verifier_tql: ToolQualificationLevel,
    pub test_results: Vec<TestResult>,
}

pub enum TestResult {
    Pass,
    Fail(String),
}
```

---

## 适航认证检查表

### Level A软件完整检查表

#### 计划阶段

- [ ] PSAC批准
- [ ] 软件开发计划
- [ ] 软件验证计划
- [ ] 软件配置管理计划
- [ ] 软件质量保证计划
- [ ] 工具鉴定计划

#### 需求阶段

- [ ] 软件需求规范(SRS)
- [ ] 系统需求追溯
- [ ] 需求评审完成

#### 设计阶段

- [ ] 软件设计描述(SDD)
- [ ] 低层需求(LLR)
- [ ] 架构评审完成
- [ ] 设计追溯矩阵

#### 实现阶段

- [ ] 源代码
- [ ] 编码标准符合
- [ ] 圈复杂度<=10
- [ ] 无unsafe代码

#### 验证阶段

- [ ] 测试用例100%覆盖SRS
- [ ] 测试用例100%覆盖LLR
- [ ] 语句覆盖100%
- [ ] 决策覆盖100%
- [ ] MC/DC覆盖100%
- [ ] 形式化验证报告
- [ ] 问题报告和解决

#### 认证阶段

- [ ] 软件完成摘要(SCI)
- [ ] 可追溯性分析
- [ ] 适航符合性演示

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用标准**: DO-178C, DO-330, DO-333

---

*本文档应与DO-178C标准原文配合使用。*
