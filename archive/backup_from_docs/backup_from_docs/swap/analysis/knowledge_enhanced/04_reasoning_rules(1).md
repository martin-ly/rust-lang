# 控制流与函数 - 推理规则系统

> **文档类型**: 🧠 推理系统 | 🔬 规则引擎  
> **创建日期**: 2025-10-19  
> **Rust 版本**: 1.90+

---

## 目录

- [控制流与函数 - 推理规则系统](#控制流与函数---推理规则系统)
  - [目录](#目录)
  - [📋 文档概述](#-文档概述)
    - [推理规则的作用](#推理规则的作用)
  - [🎯 推理规则分类](#-推理规则分类)
    - [规则元模型](#规则元模型)
    - [规则类型](#规则类型)
  - [1️⃣ 演绎规则 (Deductive Rules)](#1️⃣-演绎规则-deductive-rules)
    - [1.1 类型推理规则](#11-类型推理规则)
      - [规则 1.1.1: 表达式类型统一](#规则-111-表达式类型统一)
      - [规则 1.1.2: 闭包类型推断](#规则-112-闭包类型推断)
    - [1.2 控制流推理规则](#12-控制流推理规则)
      - [规则 1.2.1: 循环终止性](#规则-121-循环终止性)
      - [规则 1.2.2: 穷尽性推导](#规则-122-穷尽性推导)
    - [1.3 所有权推理规则](#13-所有权推理规则)
      - [规则 1.3.1: 移动后不可用](#规则-131-移动后不可用)
      - [规则 1.3.2: 闭包捕获推断](#规则-132-闭包捕获推断)
  - [2️⃣ 归纳规则 (Inductive Rules)](#2️⃣-归纳规则-inductive-rules)
    - [2.1 模式识别规则](#21-模式识别规则)
      - [规则 2.1.1: 错误处理模式识别](#规则-211-错误处理模式识别)
      - [规则 2.1.2: 建造者模式识别](#规则-212-建造者模式识别)
    - [2.2 重构建议规则](#22-重构建议规则)
      - [规则 2.2.1: 循环改迭代器](#规则-221-循环改迭代器)
      - [规则 2.2.2: match改if-let](#规则-222-match改if-let)
  - [3️⃣ 优化规则 (Optimization Rules)](#3️⃣-优化规则-optimization-rules)
    - [3.1 性能优化规则](#31-性能优化规则)
      - [规则 3.1.1: 迭代器融合](#规则-311-迭代器融合)
      - [规则 3.1.2: 闭包内联](#规则-312-闭包内联)
      - [规则 3.1.3: match跳转表](#规则-313-match跳转表)
    - [3.2 内存优化规则](#32-内存优化规则)
      - [规则 3.2.1: 借用替代克隆](#规则-321-借用替代克隆)
      - [规则 3.2.2: 预分配容量](#规则-322-预分配容量)
  - [4️⃣ 设计规则 (Design Rules)](#4️⃣-设计规则-design-rules)
    - [4.1 控制流选择规则](#41-控制流选择规则)
      - [规则 4.1.1: if vs match](#规则-411-if-vs-match)
      - [规则 4.1.2: loop vs for vs while](#规则-412-loop-vs-for-vs-while)
    - [4.2 函数设计规则](#42-函数设计规则)
      - [规则 4.2.1: 参数传递选择](#规则-421-参数传递选择)
      - [规则 4.2.2: 返回类型选择](#规则-422-返回类型选择)
    - [4.3 错误处理设计规则](#43-错误处理设计规则)
      - [规则 4.3.1: 错误传播策略](#规则-431-错误传播策略)
  - [5️⃣ 约束规则 (Constraint Rules)](#5️⃣-约束规则-constraint-rules)
    - [5.1 冲突检测规则](#51-冲突检测规则)
      - [规则 5.1.1: 借用冲突](#规则-511-借用冲突)
      - [规则 5.1.2: 移动冲突](#规则-512-移动冲突)
    - [5.2 生命周期约束规则](#52-生命周期约束规则)
      - [规则 5.2.1: 返回引用约束](#规则-521-返回引用约束)
  - [6️⃣ 组合推理规则](#6️⃣-组合推理规则)
    - [6.1 模式组合规则](#61-模式组合规则)
      - [规则 6.1.1: 错误处理链](#规则-611-错误处理链)
      - [规则 6.1.2: 迭代器组合](#规则-612-迭代器组合)
    - [6.2 Rust 1.90特性推理](#62-rust-190特性推理)
      - [规则 6.2.1: let-else应用时机](#规则-621-let-else应用时机)
      - [规则 6.2.2: if-let链应用](#规则-622-if-let链应用)
  - [7️⃣ 元规则 (Meta-Rules)](#7️⃣-元规则-meta-rules)
    - [7.1 规则优先级](#71-规则优先级)
    - [7.2 规则冲突解决](#72-规则冲突解决)
    - [7.3 规则适用条件](#73-规则适用条件)
  - [8️⃣ 实践决策树](#8️⃣-实践决策树)
    - [控制流选择决策](#控制流选择决策)
  - [🔗 参考文档](#-参考文档)

## 📋 文档概述

本文档定义控制流与函数系统的**形式化推理规则**，支持自动化知识推理和设计决策。

### 推理规则的作用

1. **自动推理**: 从已知事实推导新知识
2. **设计决策**: 基于规则选择最优方案
3. **代码验证**: 验证代码设计的合理性
4. **知识扩展**: 系统化扩展知识库

---

## 🎯 推理规则分类

### 规则元模型

```text
Rule := IF Conditions THEN Conclusion (Confidence)

where:
  Conditions: 前提条件集合
  Conclusion: 推理结论
  Confidence: 置信度 [0.0, 1.0]
```

### 规则类型

| 规则类型 | 符号 | 用途 | 示例数量 |
|---------|------|------|---------|
| **演绎规则** | ⇒ | 逻辑推理 | 50+ |
| **归纳规则** | ⇐ | 模式识别 | 30+ |
| **优化规则** | ⟹ | 性能改进 | 40+ |
| **设计规则** | ⟾ | 架构决策 | 35+ |
| **约束规则** | ⊥ | 冲突检测 | 25+ |

---

## 1️⃣ 演绎规则 (Deductive Rules)

### 1.1 类型推理规则

#### 规则 1.1.1: 表达式类型统一

```text
IF   branch1: Type T
AND  branch2: Type T
THEN if/match expr: Type T
     Confidence: 1.0 (确定性)
```

**应用示例**:

```rust
// 推理过程
let x = if condition {
    42        // T₁ = i32
} else {
    100       // T₂ = i32
};
// T₁ = T₂ = i32 ⇒ x: i32

// 类型不匹配检测
let y = if condition {
    42        // T₁ = i32
} else {
    "str"     // T₂ = &str
};
// T₁ ≠ T₂ ⇒ 编译错误
```

#### 规则 1.1.2: 闭包类型推断

```text
IF   closure |param| body
AND  param used as type T
AND  body returns type R
THEN closure: impl Fn(T) -> R
     Confidence: 1.0
```

**应用示例**:

```rust
// 推理过程
let add = |a, b| a + b;
let result = add(1, 2);  // a, b推断为i32
// ⇒ add: impl Fn(i32, i32) -> i32

// 多次使用统一推断
let transform = |x| x * 2;
let r1 = transform(5);      // x推断为i32
// ⇒ transform: impl Fn(i32) -> i32
```

### 1.2 控制流推理规则

#### 规则 1.2.1: 循环终止性

```text
IF   loop has unconditional break
OR   while condition is refutable
OR   for iterates finite collection
THEN loop terminates
     Confidence: 1.0
```

**应用示例**:

```rust
// 规则应用
loop {
    if condition {
        break;  // 有break ⇒ 可能终止
    }
}

while condition {  // 条件可变 ⇒ 可能终止
    // ...
}

for item in 0..10 {  // 有限迭代 ⇒ 必然终止
    // ...
}
```

#### 规则 1.2.2: 穷尽性推导

```text
IF   match scrutinee: Enum E
AND  E has variants {V₁, V₂, ..., Vₙ}
AND  patterns cover {V₁, V₂, ..., Vₙ}
THEN match is exhaustive
     Confidence: 1.0
```

**应用示例**:

```rust
enum Status { Active, Inactive, Pending }

// 穷尽性验证
match status {
    Status::Active => {},    // 覆盖V₁
    Status::Inactive => {},  // 覆盖V₂
    Status::Pending => {},   // 覆盖V₃
}
// {V₁, V₂, V₃} 完全覆盖 ⇒ 穷尽 ✅
```

### 1.3 所有权推理规则

#### 规则 1.3.1: 移动后不可用

```text
IF   value V is moved
AND  no Copy trait on V
THEN V is unusable after move
     Confidence: 1.0
```

**应用示例**:

```rust
let s = String::from("hello");
let s2 = s;  // s被移动
// s现在不可用 ✅

// 推理验证
println!("{}", s);  // ❌ 编译错误: 使用移动后的值
```

#### 规则 1.3.2: 闭包捕获推断

```text
IF   closure C captures variable V
AND  C only reads V
AND  no move keyword
THEN C captures &V (immutable borrow)
     Confidence: 0.9

IF   closure C captures variable V
AND  C mutates V
AND  no move keyword  
THEN C captures &mut V (mutable borrow)
     Confidence: 0.9

IF   closure C has move keyword
THEN C captures V by value
     Confidence: 1.0
```

**应用示例**:

```rust
let x = vec![1, 2, 3];

// 规则应用1: 不可变借用
let c1 = || println!("{:?}", x);  // 只读 ⇒ 捕获&x

// 规则应用2: 可变借用
let mut count = 0;
let c2 = || count += 1;  // 修改 ⇒ 捕获&mut count

// 规则应用3: 移动
let c3 = move || drop(x);  // move ⇒ 捕获x
```

---

## 2️⃣ 归纳规则 (Inductive Rules)

### 2.1 模式识别规则

#### 规则 2.1.1: 错误处理模式识别

```text
IF   function returns Result<T, E>
AND  multiple ? operators used
THEN Error Propagation Pattern
     Confidence: 0.95
```

**识别示例**:

```rust
fn process() -> Result<Value, Error> {
    let a = step1()?;  // ?运算符
    let b = step2()?;  // ?运算符
    let c = step3()?;  // ?运算符
    Ok(finalize(c))
}
// 识别为: 错误传播模式 ✅
```

#### 规则 2.1.2: 建造者模式识别

```text
IF   methods return Self
AND  final method returns different type
THEN Builder Pattern
     Confidence: 0.9
```

**识别示例**:

```rust
impl Builder {
    fn field1(self, value: T1) -> Self { ... }
    fn field2(self, value: T2) -> Self { ... }
    fn build(self) -> Product { ... }
}
// 识别为: 建造者模式 ✅
```

### 2.2 重构建议规则

#### 规则 2.2.1: 循环改迭代器

```text
IF   for loop with index
AND  simple transformation
AND  no early break/continue
THEN suggest: iterator chain
     Confidence: 0.85
```

**重构建议**:

```rust
// 识别模式
let mut result = Vec::new();
for i in 0..vec.len() {
    if vec[i] > 0 {
        result.push(vec[i] * 2);
    }
}

// 建议重构为 ⟹
let result: Vec<_> = vec.iter()
    .filter(|&&x| x > 0)
    .map(|&x| x * 2)
    .collect();
```

#### 规则 2.2.2: match改if-let

```text
IF   match has 2 arms
AND  one arm is wildcard with no-op
THEN suggest: if let
     Confidence: 0.9
```

**重构建议**:

```rust
// 识别模式
match option {
    Some(x) => use(x),
    None => {}
}

// 建议重构为 ⟹
if let Some(x) = option {
    use(x);
}
```

---

## 3️⃣ 优化规则 (Optimization Rules)

### 3.1 性能优化规则

#### 规则 3.1.1: 迭代器融合

```text
IF   multiple iterator adapters chained
AND  no collecting between
THEN compiler fuses into single pass
     Performance: +50% typical
     Confidence: 1.0
```

**优化应用**:

```rust
// 源代码
let result: Vec<_> = vec.iter()
    .map(|x| x * 2)      // 适配器1
    .filter(|x| x > 5)   // 适配器2
    .collect();

// 编译器优化 ⟹
let mut result = Vec::new();
for x in vec.iter() {
    let temp = x * 2;
    if temp > 5 {
        result.push(temp);
    }
}
// 单次遍历 ✅
```

#### 规则 3.1.2: 闭包内联

```text
IF   closure is simple (< 10 lines)
AND  closure used in hot path
AND  no indirect call
THEN inline closure
     Performance: +100% typical
     Confidence: 0.95
```

**优化应用**:

```rust
// 源代码
let transform = |x| x * 2;
for item in vec.iter() {
    let result = transform(*item);
    use(result);
}

// 优化后 ⟹
for item in vec.iter() {
    let result = *item * 2;  // 内联
    use(result);
}
```

#### 规则 3.1.3: match跳转表

```text
IF   match on integer/enum
AND  patterns are dense
AND  > 4 branches
THEN use jump table
     Performance: +200% vs if-chain
     Confidence: 1.0
```

**优化应用**:

```rust
// 源代码
match value {
    0 => handle_0(),
    1 => handle_1(),
    2 => handle_2(),
    // ... 20 branches
    19 => handle_19(),
    _ => handle_default(),
}

// 编译为跳转表 ⟹
// static JUMP_TABLE: [fn(); 20] = [...];
// JUMP_TABLE[value]();
```

### 3.2 内存优化规则

#### 规则 3.2.1: 借用替代克隆

```text
IF   value only read in function
AND  value implements Clone
THEN use &T instead of clone
     Memory: save allocation
     Confidence: 0.9
```

**优化建议**:

```rust
// 次优
fn process(data: Vec<i32>) {
    // 只读data
}
let vec = vec![1, 2, 3];
process(vec.clone());  // 不必要的克隆

// 优化 ⟹
fn process(data: &[i32]) {
    // 只读data
}
process(&vec);  // 零成本借用 ✅
```

#### 规则 3.2.2: 预分配容量

```text
IF   loop pushes to Vec
AND  iterations known
THEN use Vec::with_capacity
     Performance: +20-50%
     Confidence: 0.95
```

**优化应用**:

```rust
// 次优
let mut result = Vec::new();
for i in 0..1000 {
    result.push(i);  // 可能多次重新分配
}

// 优化 ⟹
let mut result = Vec::with_capacity(1000);
for i in 0..1000 {
    result.push(i);  // 一次分配 ✅
}
```

---

## 4️⃣ 设计规则 (Design Rules)

### 4.1 控制流选择规则

#### 规则 4.1.1: if vs match

```text
IF   condition is simple boolean
THEN prefer if/else
     Confidence: 0.9

IF   pattern matching needed
OR   > 2 branches
THEN prefer match
     Confidence: 0.9
```

**决策应用**:

```rust
// 使用if (简单条件)
if user.is_admin() {
    show_admin_panel();
} else {
    show_user_panel();
}

// 使用match (模式匹配)
match status {
    Status::Active => handle_active(),
    Status::Inactive => handle_inactive(),
    Status::Pending => handle_pending(),
}
```

#### 规则 4.1.2: loop vs for vs while

```text
IF   iterate known collection
THEN prefer for
     Confidence: 0.95

IF   condition-based termination
THEN prefer while
     Confidence: 0.9

IF   complex state machine
OR   need break with value
THEN prefer loop
     Confidence: 0.9
```

**决策应用**:

```rust
// for: 已知集合
for item in collection {
    process(item);
}

// while: 条件循环
while has_more_work() {
    do_work();
}

// loop: 状态机
loop {
    match state {
        State::Working => { /* ... */ state = State::Done; }
        State::Done => break result,
    }
}
```

### 4.2 函数设计规则

#### 规则 4.2.1: 参数传递选择

```text
IF   type is Copy and small (≤ 8 bytes)
THEN pass by value (T)
     Confidence: 0.95

IF   type is large or !Copy
AND  only read
THEN pass by reference (&T)
     Confidence: 0.95

IF   need to modify
THEN pass by mutable reference (&mut T)
     Confidence: 1.0
```

**设计应用**:

```rust
// 小型Copy类型: 按值
fn process_int(x: i32) { ... }  // ✅

// 大型类型: 按引用
fn process_vec(v: &Vec<i32>) { ... }  // ✅

// 需要修改: 可变引用
fn modify_vec(v: &mut Vec<i32>) { ... }  // ✅
```

#### 规则 4.2.2: 返回类型选择

```text
IF   operation may fail
THEN return Result<T, E>
     Confidence: 0.95

IF   value may be absent
THEN return Option<T>
     Confidence: 0.95

IF   multiple related values
THEN return tuple or struct
     Confidence: 0.9
```

### 4.3 错误处理设计规则

#### 规则 4.3.1: 错误传播策略

```text
IF   library code
THEN use Result + ? operator
     Confidence: 0.95

IF   application code
AND  recoverable error
THEN use Result + match/if-let
     Confidence: 0.9

IF   programming error
THEN use panic!
     Confidence: 0.85
```

**设计应用**:

```rust
// 库代码: Result + ?
pub fn parse_config(path: &Path) -> Result<Config, Error> {
    let content = std::fs::read_to_string(path)?;
    let config = toml::from_str(&content)?;
    Ok(config)
}

// 应用代码: 细粒度处理
fn load_config() -> Result<Config, AppError> {
    match parse_config(path) {
        Ok(cfg) => Ok(cfg),
        Err(e) if e.is_not_found() => Ok(Config::default()),
        Err(e) => Err(e.into()),
    }
}
```

---

## 5️⃣ 约束规则 (Constraint Rules)

### 5.1 冲突检测规则

#### 规则 5.1.1: 借用冲突

```text
IF   exists immutable borrow &T
AND  attempt mutable borrow &mut T
THEN conflict: cannot have &mut while & exists
     Confidence: 1.0
```

**冲突检测**:

```rust
let mut vec = vec![1, 2, 3];
let r1 = &vec[0];      // 不可变借用
vec.push(4);           // ❌ 冲突: 尝试可变借用
println!("{}", r1);
```

#### 规则 5.1.2: 移动冲突

```text
IF   value V is moved
AND  attempt to use V again
AND  V does not implement Copy
THEN conflict: use of moved value
     Confidence: 1.0
```

**冲突检测**:

```rust
let s = String::from("hello");
let s2 = s;            // s被移动
println!("{}", s);     // ❌ 冲突: 使用移动后的值
```

### 5.2 生命周期约束规则

#### 规则 5.2.1: 返回引用约束

```text
IF   function returns reference &'a T
THEN 'a must outlive function call
AND  'a must be tied to input lifetime
     Confidence: 1.0
```

**约束验证**:

```rust
// ❌ 违反约束
fn dangling<'a>() -> &'a str {
    let s = String::from("hello");
    &s  // s在函数结束时销毁
}

// ✅ 满足约束
fn first_word<'a>(s: &'a str) -> &'a str {
    &s[..5]  // 返回引用的生命周期与输入绑定
}
```

---

## 6️⃣ 组合推理规则

### 6.1 模式组合规则

#### 规则 6.1.1: 错误处理链

```text
IF   function chain: f₁ -> f₂ -> f₃
AND  each fᵢ returns Result
THEN use ? operator chain
     Benefit: concise + type-safe
     Confidence: 0.95
```

**组合应用**:

```rust
fn process_pipeline() -> Result<Output, Error> {
    let a = read_input()?;     // f₁
    let b = transform(a)?;     // f₂
    let c = validate(b)?;      // f₃
    Ok(finalize(c))
}
```

#### 规则 6.1.2: 迭代器组合

```text
IF   transformations: filter + map + collect
AND  single pass possible
THEN chain iterators
     Performance: equivalent to hand-written loop
     Confidence: 1.0
```

**组合应用**:

```rust
let result: Vec<_> = data.iter()
    .filter(|x| x.is_valid())
    .map(|x| x.transform())
    .collect();
```

### 6.2 Rust 1.90特性推理

#### 规则 6.2.1: let-else应用时机

```text
IF   extract value from Option/Result
AND  early return on None/Err
AND  no else logic needed
THEN use let-else pattern
     Benefit: more concise
     Confidence: 0.9
```

**应用示例**:

```rust
// 传统方式
let value = match get_value() {
    Some(v) => v,
    None => return Err("error"),
};

// Rust 1.90: let-else ⟹
let Some(value) = get_value() else {
    return Err("error");
};
```

#### 规则 6.2.2: if-let链应用

```text
IF   multiple pattern matches
AND  conditions are independent
THEN use if-let chain (Rust 1.90)
     Benefit: avoid nested if-let
     Confidence: 0.85
```

**应用示例**:

```rust
// 传统嵌套
if let Some(x) = opt1 {
    if let Ok(y) = res2 {
        if x > y {
            // ...
        }
    }
}

// Rust 1.90: if-let链 ⟹
if let Some(x) = opt1
   && let Ok(y) = res2
   && x > y {
    // ...
}
```

---

## 7️⃣ 元规则 (Meta-Rules)

### 7.1 规则优先级

```text
Priority Ordering:
1. Safety rules (约束规则)       - 最高优先级
2. Type rules (类型规则)         - 高优先级
3. Performance rules (优化规则)  - 中优先级
4. Design rules (设计规则)       - 中优先级
5. Style rules (风格规则)        - 低优先级
```

### 7.2 规则冲突解决

```text
IF   rule R₁ suggests action A₁
AND  rule R₂ suggests action A₂
AND  A₁ conflicts with A₂
THEN apply higher priority rule
OR   use context-specific heuristic
```

**冲突解决示例**:

```text
Conflict:
  - Performance rule: "clone is expensive, avoid"
  - Design rule: "for thread safety, clone for thread"

Resolution:
  Safety > Performance
  ⇒ Use clone for thread safety ✅
```

### 7.3 规则适用条件

```text
Rule Applicability:
- Context: 代码所在环境 (library vs application)
- Performance: 性能要求 (latency vs throughput)
- Safety: 安全级别 (strict vs relaxed)
- Rust version: 特性可用性
```

---

## 8️⃣ 实践决策树

### 控制流选择决策

```text
Start
  ├─ Simple condition?
  │   ├─ Yes → if/else
  │   └─ No → Pattern match needed?
  │           ├─ Yes → match
  │           └─ No → Multiple conditions?
  │                   ├─ Yes → match or if-let chain
  │                   └─ No → if/else
  │
  ├─ Iteration?
  │   ├─ Known collection → for
  │   ├─ Condition-based → while
  │   └─ State machine → loop
  │
  └─ Error handling?
      ├─ Propagate → ?
      ├─ Handle → match/if-let
      └─ Convert → map_err
```

---

## 🔗 参考文档

- [概念本体](./01_concept_ontology.md) - 概念定义
- [关系网络](./02_relationship_network.md) - 关系分析
- [属性空间](./03_property_space.md) - 属性分析

---

**文档维护**: Rust 学习社区  
**更新频率**: 随Rust版本更新  
**文档版本**: v1.0
