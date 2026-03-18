# 安全完整性等级选择指南

## 概述

本指南帮助功能安全工程师根据系统风险评估选择适当的安全完整性等级(SIL/ASIL)，并提供Rust实现建议。

---

## 1. 风险评估基础

### 1.1 风险公式

```
风险 = 严重性(S) × 暴露率(E) × 可控性(C)

严重性(S):
├── S0: 无伤害
├── S1: 轻/中度伤害
├── S2: 重度/危及生命伤害
└── S3: 致命伤害

暴露率(E):
├── E1: 极低概率
├── E2: 低概率
├── E3: 中等概率
└── E4: 高概率

可控性(C):
├── C0: 完全可控
├── C1: 简单可控
├── C2: 一般可控(>90%)
├── C3: 难以可控(<90%)
└── C4: 不可控
```

### 1.2 ASIL等级确定矩阵

```
          E1    E2    E3    E4
    +-----+-----+-----+-----+
S1  | QM  | QM  | QM  | ASIL|
    |     |     |     |  A  |
    +-----+-----+-----+-----+
S2  | QM  | ASIL| ASIL| ASIL|
    |     |  A  |  B  |  C  |
    +-----+-----+-----+-----+
S3  | ASIL| ASIL| ASIL| ASIL|
    |  A  |  B  |  C  |  D  |
    +-----+-----+-----+-----+

注: 可控性假设为C2(一般可控)
```

---

## 2. 等级决策树

### 2.1 汽车系统ASIL选择

```
开始
  │
  ├── 系统功能是什么？
  │   │
  │   ├── 制动控制 ──► S3, E4, C3 ──► ASIL D
  │   │
  │   ├── 转向控制 ──► S3, E4, C3 ──► ASIL D
  │   │
  │   ├── 动力控制 ──► S3, E3, C2 ──► ASIL C
  │   │
  │   ├── 气囊控制 ──► S3, E2, C4 ──► ASIL D
  │   │
  │   ├── 巡航控制 ──► S2, E3, C2 ──► ASIL B
  │   │
  │   ├── 信息娱乐 ──► S1, E4, C0 ──► QM
  │   │
  │   └── 座椅调节 ──► S1, E3, C0 ──► QM
  │
  └── 确定ASIL等级
```

### 2.2 工业系统SIL选择

```
开始
  │
  ├── 系统类型？
  │   │
  │   ├── 紧急停车系统 ──► 高危险频率 ──► SIL 3
  │   │
  │   ├── 燃烧器管理 ──► 高危险频率 ──► SIL 3
  │   │
  │   ├── 压力保护 ──► 中等危险 ──► SIL 2
  │   │
  │   ├── 液位控制 ──► 低危险 ──► SIL 1
  │   │
  │   └── 监控系统 ──► 信息性 ──► SIL 1
  │
  └── 考虑风险降低因子
          │
          ├── <10 ──► SIL 1
          ├── 10-100 ──► SIL 2
          ├── 100-1000 ──► SIL 3
          └── 1000-10000 ──► SIL 4
```

### 2.3 航空系统DAL选择

```
开始
  │
  ├── 失效影响？
  │   │
  │   ├── 阻止安全飞行和着陆 ──► 灾难性 ──► Level A
  │   │
  │   ├── 降低安全余度/机组负荷 ──► 危险 ──► Level B
  │   │
  │   ├── 降低安全余度/乘客不适 ──► 较大 ──► Level C
  │   │
  │   ├── 无安全影响 ──► 无 ──► Level E
  │   │
  └── 考虑系统独立性
          │
          ├── 独立系统 ──► 可降低一级
          └── 共因失效 ──► 保持原级
```

---

## 3. 等级分解策略

### 3.1 ASIL分解

```
ASIL D分解选项:

选项1: D = D + QM
├── 要求: 要素充分独立
├── 适用: 简单冗余
└── Rust实现: 主通道(Rust) + 监控通道(Rust)

选项2: D = C + C
├── 要求: 高独立性
├── 适用: 多样性设计
└── Rust实现: 算法A(Rust) + 算法B(Rust)

选项3: D = B + B
├── 要求: 非常高独立性
├── 适用: 三模冗余
└── Rust实现: 三通道投票

选项4: D = D(A) + D(B)
├── 要求: 软件分区
├── 适用: 混合关键系统
└── Rust实现: 分区内核 + 独立应用
```

### 3.2 SIL分解

```rust
//! SIL分解Rust实现示例

/// 2x2取2架构 (SIL 4)
pub struct TwoOutOfTwo {
    channel_a: SafetyChannel,
    channel_b: SafetyChannel,
    comparator: Comparator,
}

impl TwoOutOfTwo {
    pub fn process(&mut self, input: Input) -> Output {
        let result_a = self.channel_a.process(input);
        let result_b = self.channel_b.process(input);

        match self.comparator.compare(result_a, result_b) {
            ComparisonResult::Agree(output) => output,
            ComparisonResult::Disagree => {
                self.enter_safe_state();
                Output::SafeState
            }
        }
    }
}

/// 1oo2架构 (SIL 3)
pub struct OneOutOfTwo {
    channel_1: SafetyChannel,
    channel_2: SafetyChannel,
}

impl OneOutOfTwo {
    pub fn process(&mut self, input: Input) -> Output {
        let result_1 = self.channel_1.process(input);
        let result_2 = self.channel_2.process(input);

        // 任一通道请求安全动作即执行
        if result_1.is_safe() || result_2.is_safe() {
            Output::SafeState
        } else {
            Output::Normal
        }
    }
}
```

---

## 4. Rust实现建议

### 4.1 ASIL A实现

```rust
//! ASIL A级实现要求

#![forbid(unsafe_code)]  // 推荐

/// 基本错误处理
pub fn asil_a_function(input: Input) -> Result<Output, Error> {
    // 输入验证
    if !input.is_valid() {
        return Err(Error::InvalidInput);
    }

    // 处理
    let result = process(input)?;

    // 输出验证
    if !result.is_within_bounds() {
        return Err(Error::OutOfBounds);
    }

    Ok(result)
}

/// 覆盖率要求:
/// - 语句覆盖: 90%
/// - 分支覆盖: 80%
```

### 4.2 ASIL B实现

```rust
//! ASIL B级实现要求

#![forbid(unsafe_code)]  // 要求
#![deny(clippy::all)]

/// 防御性编程
pub fn asil_b_function(input: Input) -> Result<Output, Error> {
    // 前置条件检查
    assert!(input.check_preconditions());

    // 范围检查
    let validated = input.validate_ranges()?;

    // 处理
    let result = process_with_checkpoints(validated)?;

    // 后置条件检查
    assert!(result.check_postconditions());

    Ok(result)
}

/// 覆盖率要求:
/// - 语句覆盖: 100%
/// - 分支覆盖: 90%
```

### 4.3 ASIL C实现

```rust
//! ASIL C级实现要求

#![forbid(unsafe_code)]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]

use static_assertions::const_assert;

/// 编译时验证
const_assert!(MAX_BUFFER_SIZE <= 1024);

/// 强类型设计
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidatedValue {
    value: u32,
}

impl ValidatedValue {
    pub fn new(value: u32) -> Option<Self> {
        if value <= MAX_VALID_VALUE {
            Some(Self { value })
        } else {
            None
        }
    }

    pub fn get(&self) -> u32 {
        self.value
    }
}

/// 静态分析要求:
/// - Clippy无警告
/// - 复杂度<=15
/// - 无unsafe代码

/// 覆盖率要求:
/// - 语句覆盖: 100%
/// - 分支覆盖: 100%
```

### 4.4 ASIL D实现

```rust
//! ASIL D级实现要求

#![forbid(unsafe_code)]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::restriction)]

/// 形式化验证标记
#[cfg(kani)]
mod verification {
    use super::*;
    use kani::proof;

    #[proof]
    fn verify_safety_property() {
        // 安全属性验证
    }
}

/// 冗余设计
pub struct AsilDProcessor {
    primary: PrimaryChannel,
    secondary: MonitorChannel,
    voter: Voter,
}

impl AsilDProcessor {
    pub fn process(&mut self, input: Input) -> SafetyOutput {
        let result_p = self.primary.process(input);
        let result_s = self.secondary.monitor(input);

        // 比较结果
        match self.voter.vote(result_p, result_s) {
            VoteResult::Agree(output) => SafetyOutput::Valid(output),
            VoteResult::Disagree => {
                self.enter_safe_state();
                SafetyOutput::SafeState
            }
        }
    }

    fn enter_safe_state(&mut self) {
        // 执行安全动作
    }
}

/// 代码度量要求:
/// - 圈复杂度 <= 10
/// - 函数长度 <= 50行
/// - 参数数量 <= 5

/// 覆盖率要求:
/// - 语句覆盖: 100%
/// - 分支覆盖: 100%
/// - MC/DC: 100%

/// 分析要求:
/// - FTA完成
/// - FMEA完成
/// - 共因失效分析
```

---

## 5. 降级与升级策略

### 5.1 等级降级条件

```
允许降级的情况:
├── 独立冗余系统
├── 经充分验证的COTS组件
├── 简化的安全功能
└── 外部风险缓解措施

降级限制:
├── ASIL D → 最低ASIL B
├── ASIL C → 最低ASIL A
├── ASIL B → QM
└── 需要文档化论证
```

### 5.2 等级升级触发

```
需要升级的情况:
├── 新增危险识别
├── 事故/事件调查
├── 标准更新
├── 技术变更
└── 监管要求变化
```

---

## 6. 检查清单

### ASIL确定检查表

- [ ] 危害分析完成
- [ ] 严重性评估正确
- [ ] 暴露率评估正确
- [ ] 可控性评估正确
- [ ] 独立性分析完成
- [ ] 分解策略确定
- [ ] 残余风险可接受
- [ ] 利益相关方评审

### 等级实现检查表

#### ASIL A

- [ ] 基本错误处理
- [ ] 语句覆盖90%
- [ ] 代码审查完成

#### ASIL B

- [ ] 防御性编程
- [ ] 语句覆盖100%
- [ ] 分支覆盖90%
- [ ] 静态分析通过

#### ASIL C

- [ ] 强类型设计
- [ ] 语句覆盖100%
- [ ] 分支覆盖100%
- [ ] 无Clippy警告
- [ ] FMEA完成

#### ASIL D

- [ ] 冗余设计
- [ ] MC/DC 100%
- [ ] 形式化验证
- [ ] 圈复杂度<=10
- [ ] FTA/FMEA完成
- [ ] CCF分析完成

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**适用标准**: ISO 26262, IEC 61508, DO-178C

---

*安全完整性等级的正确选择是功能安全的基础，必须基于充分的风险分析。*
