# Rust安全关键系统培训计划

## 培训体系概述

本培训计划旨在为安全关键系统开发培养合格的Rust工程师，从基础语法到功能安全认证的全流程覆盖。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Rust安全关键系统培训体系                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Level 1          Level 2          Level 3          Level 4        │
│  基础 (2周)       进阶 (2周)       专业 (2周)       认证 (2周)      │
│     │                │                │                │           │
│     ▼                ▼                ▼                ▼           │
│  ┌─────┐         ┌─────┐         ┌─────┐         ┌─────┐         │
│  │语法 │    →    │系统 │    →    │安全 │    →    │认证 │         │
│  │基础 │         │编程 │         │关键 │         │准备 │         │
│  └─────┘         └─────┘         └─────┘         └─────┘         │
│                                                                     │
│  目标:            目标:            目标:            目标:          │
│  通过考试         独立开发         安全设计         认证通过        │
│  (80%+)          嵌入式应用        ASIL B+系统      (FSC/FSE)      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Level 1: Rust基础 (2周)

### 第1周: 语法与语义

#### 模块1: 所有权系统 (2天)

- **理论** (4h)
  - 所有权三原则
  - 移动语义
  - 复制trait
  - Drop trait

- **实践** (4h)

  ```rust
  // 练习1: 所有权转移
  fn main() {
      let s1 = String::from("hello");
      let s2 = s1; // 所有权转移
      // println!("{}", s1); // 错误! s1已失效
      println!("{}", s2);
  }

  // 练习2: 借用规则
  fn calculate(data: &Vec<i32>) -> i32 {
      data.iter().sum()
  }
  ```

#### 模块2: 借用与生命周期 (2天)

- **理论** (4h)
  - 不可变借用
  - 可变借用
  - 生命周期标注
  - 生命周期省略

- **实践** (4h)

  ```rust
  // 练习: 解析器实现
  struct Parser<'a> {
      input: &'a str,
      position: usize,
  }

  impl<'a> Parser<'a> {
      fn new(input: &'a str) -> Self {
          Parser { input, position: 0 }
      }

      fn peek(&self) -> Option<char> {
          self.input.chars().nth(self.position)
      }
  }
  ```

#### 模块3: 类型系统 (1天)

- **理论** (2h)
  - 代数数据类型
  - Option和Result
  - trait系统
  - 泛型

- **实践** (2h)
  - 状态机实现
  - 错误处理模式

### 第2周: 基础应用

#### 模块4: 错误处理 (2天)

- panic vs Result
- ?操作符
- 自定义错误类型
- 错误传播策略

#### 模块5: 集合与迭代器 (2天)

- Vec, HashMap, HashSet
- 迭代器模式
- 性能考量

#### 模块6: 测试基础 (1天)

- 单元测试
- 集成测试
- 文档测试
- 代码覆盖率

### Level 1 评估

- **理论考试**: 50道选择题 (80%通过)
- **编程作业**: 实现命令行工具
- **代码审查**: 导师一对一审查

---

## Level 2: 系统编程 (2周)

### 第3周: 底层编程

#### 模块7: 智能指针 (2天)

- Box, Rc, Arc
- RefCell, Mutex, RwLock
- 内部可变性模式
- 线程安全保证

#### 模块8: 不安全Rust (2天)

- **理论** (4h)
  - unsafe关键字
  - 原始指针
  - FFI基础
  - 不变量文档

- **实践** (4h)

  ```rust
  // 安全封装示例
  pub struct SafeBuffer {
      ptr: *mut u8,
      len: usize,
  }

  impl SafeBuffer {
      /// # Safety
      /// ptr必须指向至少len字节的有效内存
      pub unsafe fn from_raw_parts(ptr: *mut u8, len: usize) -> Self {
          SafeBuffer { ptr, len }
      }

      pub fn get(&self, index: usize) -> Option<u8> {
          if index < self.len {
              Some(unsafe { *self.ptr.add(index) })
          } else {
              None
          }
      }
  }
  ```

#### 模块9: 并发编程 (1天)

- 线程管理
- 消息传递
- 共享状态
- Send和Sync trait

### 第4周: 嵌入式Rust

#### 模块10: 无标准库编程 (2天)

- #![no_std]
- core库
- alloc库
- 嵌入式生态系统

#### 模块11: 硬件抽象层 (2天)

- embedded-hal
- 寄存器访问
- 中断处理
- DMA

#### 模块12: 实时系统 (1天)

- RTIC框架
- 任务调度
- 资源共享
- 优先级管理

### Level 2 评估

- **项目**: 嵌入式传感器驱动
- **代码审查**: unsafe代码审查
- **性能分析**: 内存和CPU使用

---

## Level 3: 安全关键 (2周)

### 第5周: 功能安全基础

#### 模块13: 功能安全标准 (3天)

- **ISO 26262** (汽车)
  - ASIL等级
  - 安全生命周期
  - 需求管理

- **IEC 61508** (工业)
  - SIL等级
  - 系统安全
  - 硬件软件接口

- **DO-178C** (航空)
  - DAL等级
  - 基于需求的测试
  - 工具鉴定

#### 模块14: Rust安全子集 (2天)

- 安全编码规范
- unsafe代码策略
- 依赖管理
- 静态分析工具

### 第6周: 验证与确认

#### 模块15: 高级测试技术 (2天)

- 基于属性的测试 (proptest)
- 模糊测试 (cargo-fuzz)
- 变异测试
- MC/DC覆盖

#### 模块16: 形式化方法 (2天)

- **Kani**: 模型检查

  ```rust
  #[kani::proof]
  fn verify_addition() {
      let a: u32 = kani::any();
      let b: u32 = kani::any();
      kani::assume(a <= 100 && b <= 100);
      let result = a + b;
      assert!(result <= 200);
  }
  ```

- **Miri**: UB检测
- **Verus**: 定理证明

#### 模块17: 认证准备 (1天)

- 证据包准备
- 文档审查
- 审计模拟

### Level 3 评估

- **项目**: ASIL B模块开发
- **验证报告**: 测试覆盖率>90%
- **文档审查**: 需求追溯矩阵

---

## Level 4: 认证与专业 (2周)

### 第7周: 认证考试准备

#### 模块18: 功能安全认证 (FSC)

- 考试要点复习
- 样题练习
- 案例分析
- 考试策略

#### 模块19: Rust专业认证

- Ferrocene用户认证
- 编码规范考试
- 工具链熟练度

### 第8周: 实战项目

#### 模块20: 完整项目开发

- 从需求到交付
- 团队协作
- 代码审查
- 认证文档

### Level 4 评估

- **FSC考试**: 80%+
- **项目答辩**: 技术评审
- **导师评价**: 综合能力

---

## 培训资源

### 在线课程

| 资源 | 类型 | 费用 | 推荐度 |
|------|------|------|--------|
| [Rustlings](https://github.com/rust-lang/rustlings) | 自学 | 免费 | ⭐⭐⭐⭐⭐ |
| [Rust by Example](https://doc.rust-lang.org/rust-by-example/) | 文档 | 免费 | ⭐⭐⭐⭐⭐ |
| [Ferrous Systems Training](https://ferrous-systems.com/training/) | 专业 | €€€ | ⭐⭐⭐⭐⭐ |
| [High Assurance Rust](https://highassurance.rs) | 自学 | 免费 | ⭐⭐⭐⭐ |

### 实验环境

```bash
# 推荐工具链
rustup component add clippy rustfmt llvm-tools-preview
cargo install cargo-audit cargo-fuzz cargo-tarpaulin
cargo install kani-verifier verus
```

### 参考书籍

1. **《The Rust Programming Language》** - 官方教程
2. **《Rust for Rustaceans》** - 进阶内容
3. **《High Assurance Rust》** - 安全关键开发
4. **《Embedded Rust》** - 嵌入式应用

---

## 认证路径

### 个人认证

```
路径1: Rust Foundation认证
├── Certified Rust Programmer
└── 在线考试，$100

路径2: 功能安全认证
├── Functional Safety Certified (FSC)
│   ├── 基础: FSC - 入门
│   ├── 进阶: FSE - 专家
│   └── 管理: FSM - 经理
└── 考试费用: $2000-4000

路径3: 工具链认证
├── Ferrocene用户认证
├── AdaCore培训认证
└── 厂商提供
```

### 组织认证

- ISO 9001 (质量管理体系)
- ISO 26262 (汽车功能安全)
- IEC 61508 (工业功能安全)
- TISAX (汽车行业信息安全)

---

## 培训计划表

### 8周密集班

| 周 | 主题 | 课时 | 评估 |
|----|------|------|------|
| 1 | Rust基础 | 40h | 理论考试 |
| 2 | 基础应用 | 40h | 编程作业 |
| 3 | 系统编程 | 40h | 项目 |
| 4 | 嵌入式 | 40h | 驱动开发 |
| 5 | 功能安全 | 40h | 标准测试 |
| 6 | 验证确认 | 40h | 验证报告 |
| 7 | 认证准备 | 40h | 模拟考试 |
| 8 | 实战项目 | 40h | 项目答辩 |

### 兼职学习班 (16周)

- 每周2天，每天8小时
- 适合在职工程师
- 更多自学时间

---

## 成功指标

### 学员能力评估

| 能力 | Level 1 | Level 2 | Level 3 | Level 4 |
|------|---------|---------|---------|---------|
| 语法掌握 | 80% | 95% | 98% | 100% |
| 安全编程 | 60% | 80% | 95% | 98% |
| 系统设计 | - | 60% | 80% | 95% |
| 认证准备 | - | - | 70% | 90% |

### 就业方向

- 嵌入式Rust工程师
- 功能安全工程师
- Rust编译器开发
- 安全研究员

---

## 联系与注册

- **培训机构**: [Ferrous Systems](https://ferrous-systems.com/training/)
- **在线课程**: [Rust Learning](https://www.rust-lang.org/learn)
- **社区支持**: [Rust Embedded Matrix](https://matrix.to/#/#rust-embedded:matrix.org)

---

**培训计划版本**: 1.0
**最后更新**: 2026-03-18
**维护者**: Rust安全关键系统培训团队
