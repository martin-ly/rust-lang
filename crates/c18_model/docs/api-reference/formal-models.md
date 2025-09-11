# 形式化方法模型 API 参考

> 返回索引：`docs/README.md`

## 概述

本节涵盖有限状态机、时序逻辑与进程代数等形式化方法核心组件的 API。示例仅展示典型用法，具体模块路径以实际代码为准。

> 导航：如需从业务状态机到协议验证的端到端流程，请参阅 `guides/fsm-to-protocol.md`；关于系统建模的更大粒度组织与推进，参阅 `guides/system-modeling.md`。

## 基础类型与结构

### State

- **描述**: 状态机中的状态，通常以字符串或枚举标识。
- **核心接口**:
  - `new(name: impl Into<String>) -> State`
  - `name(&self) -> &str`

### Transition

- **描述**: 状态间转换，包含源、目标与可选的守卫/动作。
- **核心接口**:
  - `new(from: StateId, to: StateId, label: impl Into<String>) -> Transition`
  - 可能的扩展字段: `guard`, `action`

### FiniteStateMachine {#finitestatemachine}

- **描述**: 有限状态机，支持添加状态、转换与运行时推进。
- **核心接口**:
  - `new(initial: impl Into<String>) -> FiniteStateMachine`
  - `add_state(state: State) -> StateId`
  - `add_transition(t: Transition)`
  - `current(&self) -> &State`
  - `step(event: &str) -> Result<(), Error>`

示例:

```rust
use c18_model::FiniteStateMachine;

let mut fsm = FiniteStateMachine::new("idle");
// let s_work = fsm.add_state(State::new("working"));
// fsm.add_transition(Transition::new(s_idle, s_work, "start"));
// fsm.step("start")?;
```

## 时序逻辑

### TemporalFormula

- **描述**: LTL/CTL 等时序逻辑公式的抽象表示。
- **核心接口**:
  - `and(a, b)`, `or(a, b)`, `not(a)`
  - `globally(p)`, `eventually(p)`, `until(p, q)`

### TemporalModelChecker {#temporalmodelchecker}

- **描述**: 时序逻辑模型检查器，对给定模型验证公式是否成立。
- **核心接口**:
  - `new() -> TemporalModelChecker`
  - `check<M: KripkeLike>(model: &M, formula: &TemporalFormula) -> CheckResult`

示例:

```rust
// let formula = TemporalFormula::globally(prop!("safe"));
// let result = TemporalModelChecker::new().check(&model, &formula);
// assert!(result.is_satisfied());
```

## 进程代数

### ProcessTerm

- **描述**: 进程代数项（如 CCS/CSP 风格）。
- **核心构造**:
  - `nil()`, `action(a)`, `seq(p, q)`, `par(p, q)`, `choice(p, q)`

### ProcessAlgebraInterpreter {#processalgebrainterpreter}

- **描述**: 对进程项进行语义解释与执行/等价性分析。
- **核心接口**:
  - `simulate(term: &ProcessTerm, steps: usize) -> Trace`
  - `bisimilar(a: &ProcessTerm, b: &ProcessTerm) -> bool`

## 错误处理

- 统一错误类型 `Error`（或 `ModelError`），建议使用 `thiserror` 风格枚举。
- 常见错误: `InvalidState`, `NoTransition`, `UnsatisfiedGuard`, `Timeout`。

> 一致性说明：本页 `FiniteStateMachine`/`TemporalModelChecker` 的接口与指南示例保持等价层级；若签名存在轻微差异，以示例所示用法为准，面向“可达性/死锁/反例生成”的能力保持一致。

## 性能与实现建议

- 使用紧凑的状态/转换表示（如 `u32` 索引）提升性能。
- 对频繁查询的边集建立邻接索引或压缩结构。
- 对模型检查使用 BDD/SAT/bitset 优化（按需）。

## 示例与最佳实践

1. 将状态定义为小而稳定的集合，避免运行时频繁分配。
2. 对外暴露不可变视图，内部使用 `Vec`/`IndexMap` 管理标识与名称映射。
3. 测试覆盖: 单步转移、不可达、死锁、公式边界用例。

## 版本

- 适配版本: 0.2.0（Rust 1.70+）

## 快速索引

- 状态机：`State`、`Transition`、`FiniteStateMachine`
- 时序逻辑：`TemporalFormula`、`TemporalModelChecker`
- 进程代数：`ProcessTerm`、`ProcessAlgebraInterpreter`

跨页跳转：

- 指南（状态机→协议验证）：`guides/fsm-to-protocol.md`
- 指南（系统建模推进）：`guides/system-modeling.md`

## 术语表

- 可达性（Reachability）：从初始状态出发能到达的状态集合。
- 死锁（Deadlock）：无任何后继转换的状态。
- 不变式（Invariant）：在所有可达状态上都成立的性质。
- 反例（Counterexample）：违背性质的执行路径示例。

## 1. 形式化方法模型 API 参考

## 1.1 目录

- [形式化方法模型 API 参考](#形式化方法模型-api-参考)
  - [概述](#概述)
  - [基础类型与结构](#基础类型与结构)
    - [State](#state)
    - [Transition](#transition)
    - [FiniteStateMachine {#finitestatemachine}](#finitestatemachine-finitestatemachine)
  - [时序逻辑](#时序逻辑)
    - [TemporalFormula](#temporalformula)
    - [TemporalModelChecker {#temporalmodelchecker}](#temporalmodelchecker-temporalmodelchecker)
  - [进程代数](#进程代数)
    - [ProcessTerm](#processterm)
    - [ProcessAlgebraInterpreter {#processalgebrainterpreter}](#processalgebrainterpreter-processalgebrainterpreter)
  - [错误处理](#错误处理)
  - [性能与实现建议](#性能与实现建议)
  - [示例与最佳实践](#示例与最佳实践)
  - [版本](#版本)
  - [快速索引](#快速索引)
  - [术语表](#术语表)
  - [1. 形式化方法模型 API 参考](#1-形式化方法模型-api-参考)
  - [1.1 目录](#11-目录)
  - [1.2 概述](#12-概述)
  - [1.3 基础形式化模型](#13-基础形式化模型)
    - [1.3.1 State](#131-state)
      - [1.3.1.1 构造函数](#1311-构造函数)
      - [1.3.1.2 主要方法](#1312-主要方法)
    - [1.3.2 Transition](#132-transition)
      - [1.3.2.1 构造函数](#1321-构造函数)
      - [1.3.2.2 主要方法](#1322-主要方法)
    - [1.3.3 FiniteStateMachine](#133-finitestatemachine)
      - [1.3.3.1 构造函数](#1331-构造函数)
      - [1.3.3.2 主要方法](#1332-主要方法)
    - [1.3.4 TemporalFormula](#134-temporalformula)
    - [1.3.5 TemporalModelChecker](#135-temporalmodelchecker)
      - [1.3.5.1 构造函数](#1351-构造函数)
      - [1.3.5.2 主要方法](#1352-主要方法)
    - [1.3.6 ProcessTerm](#136-processterm)
    - [1.3.7 ProcessAlgebraInterpreter](#137-processalgebrainterpreter)
      - [1.3.7.1 构造函数](#1371-构造函数)
      - [1.3.7.2 主要方法](#1372-主要方法)
  - [1.4 高级形式化方法](#14-高级形式化方法)
    - [1.4.1 形式化描述语言](#141-形式化描述语言)
      - [1.4.1.1 AlgebraicLanguage](#1411-algebraiclanguage)
      - [1.4.1.2 LogicLanguage](#1412-logiclanguage)
      - [1.4.1.3 SetLanguage](#1413-setlanguage)
      - [1.4.1.4 ProcessLanguage](#1414-processlanguage)
    - [1.4.2 验证技术](#142-验证技术)
      - [1.4.2.1 TheoremProving](#1421-theoremproving)
      - [1.4.2.2 ModelChecking](#1422-modelchecking)
      - [1.4.2.3 EquivalenceChecking](#1423-equivalencechecking)
    - [1.4.3 模型转换](#143-模型转换)
      - [1.4.3.1 AlgebraicTransformation](#1431-algebraictransformation)
      - [1.4.3.2 CategoryTheory](#1432-categorytheory)
  - [1.5 具体实现](#15-具体实现)
    - [1.5.1 NaturalNumberAlgebra](#151-naturalnumberalgebra)
    - [1.5.2 PropositionalLogic](#152-propositionallogic)
    - [1.5.3 FiniteSet](#153-finiteset)
  - [1.6 工具集](#16-工具集)
    - [1.6.1 FormalMethodsToolkit](#161-formalmethodstoolkit)
      - [1.6.1.1 主要方法](#1611-主要方法)
    - [1.6.2 AdvancedFormalMethodsToolkit](#162-advancedformalmethodstoolkit)
      - [1.6.2.1 主要方法](#1621-主要方法)
  - [1.7 使用示例](#17-使用示例)
    - [1.7.1 基础状态机](#171-基础状态机)
    - [1.7.2 时序逻辑模型检查](#172-时序逻辑模型检查)
    - [1.7.3 进程代数](#173-进程代数)
    - [1.7.4 高级形式化方法](#174-高级形式化方法)
  - [1.8 错误处理](#18-错误处理)
  - [1.9 性能考虑](#19-性能考虑)
  - [1.10 使用建议](#110-使用建议)

## 1.2 概述

形式化方法模型模块提供了各种形式化方法的实现，包括有限状态机、时序逻辑、进程代数等，以及高级形式化方法如形式化描述语言、验证技术、模型转换等。

## 1.3 基础形式化模型

### 1.3.1 State

状态机状态，表示有限状态机中的一个状态。

```rust
pub struct State {
    pub id: String,                          // 状态ID
    pub properties: HashMap<String, bool>,   // 状态属性
}
```

#### 1.3.1.1 构造函数

```rust
pub fn new(id: String) -> Self
```

#### 1.3.1.2 主要方法

```rust
// 添加属性
pub fn with_property(mut self, key: String, value: bool) -> Self

// 获取属性值
pub fn get_property(&self, key: &str) -> Option<bool>

// 检查是否满足属性
pub fn satisfies(&self, key: &str) -> bool
```

### 1.3.2 Transition

状态转换，表示状态机中的转换。

```rust
pub struct Transition {
    pub from: String,        // 源状态ID
    pub to: String,          // 目标状态ID
    pub event: String,       // 触发事件
    pub condition: Option<String>,  // 转换条件
    pub action: Option<String>,     // 转换动作
}
```

#### 1.3.2.1 构造函数

```rust
pub fn new(from: String, to: String, event: String) -> Self
```

#### 1.3.2.2 主要方法

```rust
// 添加条件
pub fn with_condition(mut self, condition: String) -> Self

// 添加动作
pub fn with_action(mut self, action: String) -> Self
```

### 1.3.3 FiniteStateMachine

有限状态机，支持状态转换、死锁检测、可达性分析等功能。

```rust
pub struct FiniteStateMachine {
    pub states: HashMap<String, State>,  // 状态集合
    pub transitions: Vec<Transition>,    // 转换集合
    pub initial_state: String,           // 初始状态
    pub current_state: String,           // 当前状态
}
```

#### 1.3.3.1 构造函数

```rust
pub fn new(initial_state: String) -> Self
```

#### 1.3.3.2 主要方法

```rust
// 添加状态
pub fn add_state(&mut self, state: State)

// 添加转换
pub fn add_transition(&mut self, transition: Transition)

// 执行状态转换
pub fn transition(&mut self, event: &str) -> Result<(), String>

// 获取当前状态
pub fn get_current_state(&self) -> &State

// 获取可达状态
pub fn get_reachable_states(&self) -> HashSet<String>

// 检查死锁
pub fn has_deadlock(&self) -> bool

// 检查不变式
pub fn check_invariant(&self, invariant: &str) -> bool
```

### 1.3.4 TemporalFormula

时序逻辑公式。

```rust
pub enum TemporalFormula {
    Atomic(String),                    // 原子命题
    Not(Box<TemporalFormula>),         // 否定
    And(Box<TemporalFormula>, Box<TemporalFormula>), // 合取
    Or(Box<TemporalFormula>, Box<TemporalFormula>),  // 析取
    Implies(Box<TemporalFormula>, Box<TemporalFormula>), // 蕴含
    Always(Box<TemporalFormula>),      // 总是 (G)
    Eventually(Box<TemporalFormula>),  // 最终 (F)
    Next(Box<TemporalFormula>),        // 下一步 (X)
    Until(Box<TemporalFormula>, Box<TemporalFormula>), // 直到 (U)
}
```

### 1.3.5 TemporalModelChecker

时序逻辑模型检查器。

```rust
pub struct TemporalModelChecker {
    fsm: FiniteStateMachine,
}
```

#### 1.3.5.1 构造函数

```rust
pub fn new(fsm: FiniteStateMachine) -> Self
```

#### 1.3.5.2 主要方法

```rust
// 检查公式
pub fn check_formula(&self, formula: &TemporalFormula) -> bool

// 生成反例
pub fn generate_counterexample(&self, formula: &TemporalFormula) -> Option<Vec<String>>
```

### 1.3.6 ProcessTerm

进程代数项。

```rust
pub enum ProcessTerm {
    Nil,                                    // 空进程
    Prefix(String, Box<ProcessTerm>),       // 前缀
    Choice(Box<ProcessTerm>, Box<ProcessTerm>), // 选择
    Parallel(Box<ProcessTerm>, Box<ProcessTerm>), // 并行
    Sequence(Box<ProcessTerm>, Box<ProcessTerm>), // 序列
}
```

### 1.3.7 ProcessAlgebraInterpreter

进程代数解释器。

```rust
pub struct ProcessAlgebraInterpreter {
    // 内部状态
}
```

#### 1.3.7.1 构造函数

```rust
pub fn new() -> Self
```

#### 1.3.7.2 主要方法

```rust
// 执行进程
pub fn execute(&self, process: &ProcessTerm) -> Vec<String>

// 检查等价性
pub fn are_equivalent(&self, p1: &ProcessTerm, p2: &ProcessTerm) -> bool
```

## 1.4 高级形式化方法

### 1.4.1 形式化描述语言

#### 1.4.1.1 AlgebraicLanguage

代数语言trait。

```rust
pub trait AlgebraicLanguage {
    type Element;
    type Operation;
    
    fn identity(&self) -> Self::Element;
    fn operation(&self, op: Self::Operation, a: Self::Element, b: Self::Element) -> Self::Element;
    fn inverse(&self, element: Self::Element) -> Option<Self::Element>;
}
```

#### 1.4.1.2 LogicLanguage

逻辑语言trait。

```rust
pub trait LogicLanguage {
    type Formula;
    type Connective;
    
    fn conjunction(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula;
    fn disjunction(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula;
    fn negation(&self, formula: Self::Formula) -> Self::Formula;
    fn implication(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula;
}
```

#### 1.4.1.3 SetLanguage

集合语言trait。

```rust
pub trait SetLanguage {
    type Element;
    type Set;
    
    fn empty_set(&self) -> Self::Set;
    fn singleton(&self, element: Self::Element) -> Self::Set;
    fn union(&self, a: Self::Set, b: Self::Set) -> Self::Set;
    fn intersection(&self, a: Self::Set, b: Self::Set) -> Self::Set;
    fn complement(&self, set: Self::Set) -> Self::Set;
}
```

#### 1.4.1.4 ProcessLanguage

过程语言trait。

```rust
pub trait ProcessLanguage {
    type Process;
    type Action;
    
    fn nil(&self) -> Self::Process;
    fn action(&self, action: Self::Action) -> Self::Process;
    fn choice(&self, a: Self::Process, b: Self::Process) -> Self::Process;
    fn parallel(&self, a: Self::Process, b: Self::Process) -> Self::Process;
    fn sequence(&self, a: Self::Process, b: Self::Process) -> Self::Process;
}
```

### 1.4.2 验证技术

#### 1.4.2.1 TheoremProving

定理证明trait。

```rust
pub trait TheoremProving {
    type Theorem;
    type Proof;
    
    fn prove(&self, theorem: Self::Theorem) -> Result<Self::Proof, String>;
    fn verify_proof(&self, proof: Self::Proof) -> bool;
}
```

#### 1.4.2.2 ModelChecking

模型检查trait。

```rust
pub trait ModelChecking {
    type Model;
    type Property;
    
    fn check_property(&self, model: Self::Model, property: Self::Property) -> bool;
    fn find_counterexample(&self, model: Self::Model, property: Self::Property) -> Option<Self::Model>;
}
```

#### 1.4.2.3 EquivalenceChecking

等价性检查trait。

```rust
pub trait EquivalenceChecking {
    type System;
    
    fn are_equivalent(&self, system1: Self::System, system2: Self::System) -> bool;
    fn find_difference(&self, system1: Self::System, system2: Self::System) -> Option<String>;
}
```

### 1.4.3 模型转换

#### 1.4.3.1 AlgebraicTransformation

代数转换trait。

```rust
pub trait AlgebraicTransformation {
    type Expression;
    
    fn simplify(&self, expression: Self::Expression) -> Self::Expression;
    fn factorize(&self, expression: Self::Expression) -> Self::Expression;
    fn expand(&self, expression: Self::Expression) -> Self::Expression;
}
```

#### 1.4.3.2 CategoryTheory

范畴论trait。

```rust
pub trait CategoryTheory {
    type Object;
    type Morphism;
    
    fn identity(&self, object: Self::Object) -> Self::Morphism;
    fn compose(&self, f: Self::Morphism, g: Self::Morphism) -> Self::Morphism;
    fn is_isomorphic(&self, a: Self::Object, b: Self::Object) -> bool;
}
```

## 1.5 具体实现

### 1.5.1 NaturalNumberAlgebra

自然数代数实现。

```rust
pub struct NaturalNumberAlgebra;

impl AlgebraicLanguage for NaturalNumberAlgebra {
    type Element = u32;
    type Operation = String;
    
    fn identity(&self) -> Self::Element { 0 }
    fn operation(&self, op: Self::Operation, a: Self::Element, b: Self::Element) -> Self::Element
    fn inverse(&self, _element: Self::Element) -> Option<Self::Element> { None }
}
```

### 1.5.2 PropositionalLogic

命题逻辑实现。

```rust
pub struct PropositionalLogic;

impl LogicLanguage for PropositionalLogic {
    type Formula = String;
    type Connective = String;
    
    fn conjunction(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula
    fn disjunction(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula
    fn negation(&self, formula: Self::Formula) -> Self::Formula
    fn implication(&self, a: Self::Formula, b: Self::Formula) -> Self::Formula
}
```

### 1.5.3 FiniteSet

有限集合实现。

```rust
pub struct FiniteSet<T> {
    elements: Vec<T>,
}

impl<T: Clone + PartialEq> SetLanguage for FiniteSet<T> {
    type Element = T;
    type Set = FiniteSet<T>;
    
    fn empty_set(&self) -> Self::Set
    fn singleton(&self, element: Self::Element) -> Self::Set
    fn union(&self, a: Self::Set, b: Self::Set) -> Self::Set
    fn intersection(&self, a: Self::Set, b: Self::Set) -> Self::Set
    fn complement(&self, set: Self::Set) -> Self::Set
}
```

## 1.6 工具集

### 1.6.1 FormalMethodsToolkit

基础形式化方法工具集。

```rust
pub struct FormalMethodsToolkit {
    pub fsm: Option<FiniteStateMachine>,
    pub model_checker: Option<TemporalModelChecker>,
    pub process_interpreter: ProcessAlgebraInterpreter,
}
```

#### 1.6.1.1 主要方法

```rust
// 创建新工具包
pub fn new() -> Self

// 设置状态机
pub fn set_fsm(&mut self, fsm: FiniteStateMachine)

// 验证代数性质
pub fn verify_algebraic_property(&self, property: &str) -> bool

// 执行模型检查
pub fn model_check(&self, formula: &TemporalFormula) -> ModelCheckingResult
```

### 1.6.2 AdvancedFormalMethodsToolkit

高级形式化方法工具集。

```rust
pub struct AdvancedFormalMethodsToolkit {
    pub algebraic_language: NaturalNumberAlgebra,
    pub logic_language: PropositionalLogic,
    pub process_language: ProcessCalculus,
    pub theorem_prover: SimpleTheoremProver,
    pub model_checker: SimpleModelChecker,
    pub equivalence_checker: SimpleEquivalenceChecker,
    pub algebraic_transformer: AlgebraicTransformer,
    pub category_theory: SimpleCategory,
}
```

#### 1.6.2.1 主要方法

```rust
// 创建新工具包
pub fn new() -> Self

// 验证代数性质
pub fn verify_algebraic_property(&self, property: &str) -> bool

// 检查逻辑公式
pub fn check_logical_formula(&self, formula: &str) -> bool

// 验证进程等价性
pub fn verify_process_equivalence(&self, process1: &str, process2: &str) -> bool
```

## 1.7 使用示例

### 1.7.1 基础状态机

```rust
use c18_model::{FiniteStateMachine, State, Transition};

let mut fsm = FiniteStateMachine::new("idle".to_string());

// 添加状态
let working_state = State::new("working".to_string())
    .with_property("busy".to_string(), true);
fsm.add_state(working_state);

// 添加转换
let transition = Transition::new("idle".to_string(), "working".to_string(), "start".to_string());
fsm.add_transition(transition);

// 执行转换
fsm.transition("start")?;
println!("当前状态: {}", fsm.get_current_state().id);
```

### 1.7.2 时序逻辑模型检查

```rust
use c18_model::{TemporalFormula, TemporalModelChecker};

let formula = TemporalFormula::Always(Box::new(TemporalFormula::Atomic("safe".to_string())));
let checker = TemporalModelChecker::new(fsm);
let result = checker.check_formula(&formula);
println!("公式满足: {}", result);
```

### 1.7.3 进程代数

```rust
use c18_model::{ProcessTerm, ProcessAlgebraInterpreter};

let process = ProcessTerm::Prefix("send".to_string(), 
    Box::new(ProcessTerm::Prefix("receive".to_string(), 
        Box::new(ProcessTerm::Nil))));

let interpreter = ProcessAlgebraInterpreter::new();
let trace = interpreter.execute(&process);
println!("执行轨迹: {:?}", trace);
```

### 1.7.4 高级形式化方法

```rust
use c18_model::{AdvancedFormalMethodsToolkit, formal_languages};

let toolkit = AdvancedFormalMethodsToolkit::new();

// 验证代数性质
let is_associative = toolkit.verify_algebraic_property("associativity");

// 检查逻辑公式
let is_valid = toolkit.check_logical_formula("P → Q");

// 验证进程等价性
let are_equivalent = toolkit.verify_process_equivalence("a.b.0", "a.b.0");
```

## 1.8 错误处理

所有形式化方法操作都可能返回错误：

- **状态转换错误**: 无效的事件或条件
- **模型检查错误**: 公式语法错误或模型不匹配
- **进程执行错误**: 无效的进程项或执行失败
- **验证错误**: 证明失败或反例生成失败

建议始终处理这些错误情况：

```rust
match fsm.transition("invalid_event") {
    Ok(()) => println!("转换成功"),
    Err(e) => println!("转换失败: {}", e),
}
```

## 1.9 性能考虑

- 状态机操作：O(1) 时间复杂度
- 模型检查：指数时间复杂度（LTL模型检查）
- 进程执行：线性时间复杂度
- 内存使用：与状态数量和转换数量成正比

## 1.10 使用建议

1. **状态设计**: 保持状态数量合理，避免状态爆炸
2. **公式复杂度**: 控制时序逻辑公式的复杂度
3. **进程项大小**: 避免过深的进程项嵌套
4. **验证策略**: 结合多种验证技术提高可靠性
