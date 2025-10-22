# 控制流与函数 - 概念本体定义

> **文档类型**: 📚 知识本体 | 🔬 形式化定义  
> **创建日期**: 2025-10-19  
> **Rust 版本**: 1.90+

---

## 目录

- [控制流与函数 - 概念本体定义](#控制流与函数---概念本体定义)
  - [目录](#目录)
  - [📋 文档概述](#-文档概述)
    - [知识本体的作用](#知识本体的作用)
  - [🎯 本体结构](#-本体结构)
  - [1️⃣ 核心抽象层概念](#1️⃣-核心抽象层概念)
    - [1.1 表达式 (Expression)](#11-表达式-expression)
    - [1.2 语句 (Statement)](#12-语句-statement)
    - [1.3 块表达式 (Block Expression)](#13-块表达式-block-expression)
  - [2️⃣ 控制流层概念](#2️⃣-控制流层概念)
    - [2.1 条件表达式 (Conditional Expression)](#21-条件表达式-conditional-expression)
      - [2.1.1 if表达式](#211-if表达式)
      - [2.1.2 match表达式](#212-match表达式)
      - [2.1.3 if let表达式](#213-if-let表达式)
      - [2.1.4 let-else模式](#214-let-else模式)
    - [2.2 循环控制 (Loop Control)](#22-循环控制-loop-control)
      - [2.2.1 loop循环](#221-loop循环)
      - [2.2.2 while循环](#222-while循环)
      - [2.2.3 while let循环](#223-while-let循环)
      - [2.2.4 for循环](#224-for循环)
    - [2.3 跳转控制 (Jump Control)](#23-跳转控制-jump-control)
      - [2.3.1 break](#231-break)
      - [2.3.2 continue](#232-continue)
      - [2.3.3 return](#233-return)
  - [3️⃣ 函数层概念](#3️⃣-函数层概念)
    - [3.1 函数定义 (Function Definition)](#31-函数定义-function-definition)
    - [3.2 函数类型](#32-函数类型)
      - [3.2.1 普通函数 (Free Function)](#321-普通函数-free-function)
      - [3.2.2 关联函数 (Associated Function)](#322-关联函数-associated-function)
      - [3.2.3 方法 (Method)](#323-方法-method)
    - [3.3 参数传递 (Parameter Passing)](#33-参数传递-parameter-passing)
    - [3.4 返回类型 (Return Type)](#34-返回类型-return-type)
  - [4️⃣ 模式层概念](#4️⃣-模式层概念)
    - [4.1 模式类型 (Pattern Types)](#41-模式类型-pattern-types)
      - [4.1.1 模式分类](#411-模式分类)
      - [4.1.2 可反驳性 (Refutability)](#412-可反驳性-refutability)
    - [4.2 模式特性](#42-模式特性)
      - [4.2.1 绑定模式 (@-binding)](#421-绑定模式--binding)
      - [4.2.2 引用模式](#422-引用模式)
      - [4.2.3 守卫条件 (Pattern Guards)](#423-守卫条件-pattern-guards)
    - [4.3 穷尽性检查 (Exhaustiveness Checking)](#43-穷尽性检查-exhaustiveness-checking)
  - [5️⃣ 组合层概念](#5️⃣-组合层概念)
    - [5.1 闭包系统 (Closure System)](#51-闭包系统-closure-system)
      - [5.1.1 捕获模式](#511-捕获模式)
      - [5.1.2 Fn Traits](#512-fn-traits)
    - [5.2 迭代器系统 (Iterator System)](#52-迭代器系统-iterator-system)
      - [5.2.1 迭代器分类](#521-迭代器分类)
      - [5.2.2 所有权模式](#522-所有权模式)
    - [5.3 错误处理系统 (Error Handling System)](#53-错误处理系统-error-handling-system)
      - [5.3.1 Result类型](#531-result类型)
      - [5.3.2 Option类型](#532-option类型)
      - [5.3.3 ?运算符](#533-运算符)
  - [6️⃣ 类型系统集成](#6️⃣-类型系统集成)
    - [6.1 Never类型 (!)](#61-never类型-)
    - [6.2 类型推断](#62-类型推断)
    - [6.3 类型统一](#63-类型统一)
  - [🔗 概念关系总结](#-概念关系总结)
    - [核心依赖关系](#核心依赖关系)
    - [组合关系](#组合关系)
  - [📚 参考资料](#-参考资料)

## 📋 文档概述

本文档提供 Rust 控制流与函数系统的**形式化概念定义**，构建领域知识的本体结构。

### 知识本体的作用

1. **统一术语**: 提供标准、精确的概念定义
2. **关系基础**: 为关系网络提供节点定义
3. **推理基础**: 为自动推理提供形式化规则
4. **知识共享**: 促进团队间的知识交流

---

## 🎯 本体结构

```text
控制流与函数本体
├── 核心抽象层
│   ├── 表达式系统
│   ├── 类型系统
│   └── 执行语义
├── 控制流层
│   ├── 条件控制
│   ├── 循环控制
│   └── 跳转控制
├── 函数层
│   ├── 函数定义
│   ├── 参数传递
│   └── 返回机制
├── 模式层
│   ├── 模式类型
│   ├── 匹配语义
│   └── 解构绑定
└── 组合层
    ├── 闭包系统
    ├── 迭代器系统
    └── 错误处理系统
```

---

## 1️⃣ 核心抽象层概念

### 1.1 表达式 (Expression)

**形式化定义**:

```text
Expression := Value | Operation | ControlFlow
where:
  - Value: 字面量或变量
  - Operation: 函数调用或运算符
  - ControlFlow: if | match | loop | block
```

**本体属性**:

- **语义类型** (Semantic Type): 求值型 (Evaluates to value)
- **副作用** (Side Effects): 可能有
- **返回值** (Return Value): 类型T
- **组合性** (Composability): 高

**实例**:

```rust
// 表达式求值
let x = 5 + 3;                    // 算术表达式
let y = if cond { 1 } else { 2 }; // 控制流表达式
let z = { let a = 1; a + 2 };     // 块表达式
```

**公理**:

1. 所有表达式都有类型
2. 表达式可以嵌套组合
3. 最后的表达式决定块的返回值

### 1.2 语句 (Statement)

**形式化定义**:

```text
Statement := LetBinding | Expression; | Item
where:
  - LetBinding: let pattern = expr
  - Expression;: 表达式 + 分号
  - Item: 函数/结构体/impl定义
```

**本体属性**:

- **语义类型**: 执行型 (Executes for effect)
- **副作用**: 通常有
- **返回值**: () (单元类型)
- **组合性**: 低

**区别表达式**:

```rust
// 语句
let x = 5;           // let语句
println!("Hello");   // 表达式语句（有分号）

// 表达式
x + 1                // 无分号，有返回值
if x > 0 { x }       // 控制流表达式
```

### 1.3 块表达式 (Block Expression)

**形式化定义**:

```text
Block := { Statement* Expression? }
return_value := 
  | Expression  (if present)
  | ()          (if absent or last is statement)
```

**本体属性**:

- **作用域**: 创建新作用域
- **返回值**: 最后表达式的值
- **生命周期**: 块内变量在块结束时销毁

**示例**:

```rust
let result = {
    let temp = expensive_computation();
    temp * 2  // 返回值（无分号）
};
```

---

## 2️⃣ 控制流层概念

### 2.1 条件表达式 (Conditional Expression)

#### 2.1.1 if表达式

**形式化定义**:

```text
IfExpr := if Condition Block (else Block)?
where:
  Condition: bool类型表达式
  所有分支类型必须统一
```

**本体属性**:

- **条件类型**: 布尔表达式
- **穷尽性**: 可选else分支
- **返回类型**: 所有分支的统一类型
- **编译时检查**: 类型统一性

**类型规则**:

```text
Γ ⊢ cond: bool
Γ ⊢ then_block: T
Γ ⊢ else_block: T
─────────────────────────────
Γ ⊢ if cond then_block else else_block: T
```

**Rust 1.90 增强**:

- 更好的类型推断
- 改进的错误消息

#### 2.1.2 match表达式

**形式化定义**:

```text
MatchExpr := match Scrutinee { Pattern => Expression,+ }
where:
  Scrutinee: 被匹配的值
  Pattern: 模式（必须穷尽）
  Expression: 分支表达式
```

**本体属性**:

- **穷尽性**: 编译时强制检查
- **模式类型**: 字面量、变量、结构、枚举、通配符
- **守卫条件**: 可选的if条件
- **性能**: 优化为跳转表或决策树

**穷尽性规则**:

```text
match scrutinee {
    Pattern_1 => expr_1,
    ...
    Pattern_n => expr_n,
}

Required: Pattern_1 | ... | Pattern_n = Universal Set
```

**示例**:

```rust
match value {
    Some(x) if x > 0 => println!("正数"),  // 带守卫
    Some(x) => println!("非正数"),
    None => println!("无值"),
}  // ✅ 穷尽
```

#### 2.1.3 if let表达式

**形式化定义**:

```text
IfLetExpr := if let Pattern = Scrutinee Block (else Block)?
where:
  Pattern: 单个模式
  Scrutinee: 被匹配的值
```

**本体属性**:

- **模式数量**: 单个模式
- **穷尽性**: 不要求
- **语法糖**: match的简化形式

**等价转换**:

```rust
// if let
if let Some(x) = option {
    use(x);
}

// 等价于
match option {
    Some(x) => use(x),
    _ => {}
}
```

**Rust 1.90: if-let 链**:

```rust
if let Some(x) = opt1 
   && let Ok(y) = res2 
   && x > y {
    // 链式匹配
}
```

#### 2.1.4 let-else模式

**形式化定义**:

```text
LetElseStmt := let Pattern = Scrutinee else Block;
where:
  Pattern: 可反驳模式
  Block: 发散块 (必须return/break/panic)
```

**本体属性**:

- **Rust版本**: 1.89+ (1.90稳定)
- **用途**: 早期返回模式
- **发散要求**: else块必须发散

**示例**:

```rust
fn process(opt: Option<i32>) -> Result<i32, &'static str> {
    let Some(value) = opt else {
        return Err("无值");  // 必须发散
    };
    Ok(value * 2)
}
```

### 2.2 循环控制 (Loop Control)

#### 2.2.1 loop循环

**形式化定义**:

```text
LoopExpr := ('label:)? loop Block
where:
  'label: 可选的生命周期标签
  Block: 循环体
  终止: 显式break
```

**本体属性**:

- **终止条件**: 显式break
- **返回值**: break表达式的值
- **类型**: break值的类型
- **标签**: 支持多层循环控制

**break with value** (Rust 1.0+):

```rust
let result = loop {
    if condition {
        break compute_value();  // 返回值
    }
};
```

**标签块** (Rust 1.90增强):

```rust
'outer: loop {
    'inner: loop {
        break 'outer;  // 跳出外层循环
    }
}
```

#### 2.2.2 while循环

**形式化定义**:

```text
WhileExpr := while Condition Block
where:
  Condition: bool表达式
  Block: 循环体
```

**本体属性**:

- **终止条件**: 条件为false
- **返回值**: ()
- **类型**: 单元类型

#### 2.2.3 while let循环

**形式化定义**:

```text
WhileLetExpr := while let Pattern = Scrutinee Block
where:
  Pattern: 模式
  Scrutinee: 被匹配的表达式
```

**本体属性**:

- **终止条件**: 模式匹配失败
- **典型用途**: 遍历直到None

**Rust 1.90: while-let链**:

```rust
while let Some(x) = iter.next() 
      && x > 0 {
    // 链式条件
}
```

#### 2.2.4 for循环

**形式化定义**:

```text
ForExpr := for Pattern in IntoIterator Block
where:
  Pattern: 模式
  IntoIterator: impl IntoIterator
  Block: 循环体
```

**本体属性**:

- **终止条件**: 迭代器耗尽
- **所有权**: 取决于into_iter/iter/iter_mut
- **返回值**: ()

**所有权模式**:

```rust
for item in vec        // into_iter: 移动
for item in &vec       // iter: 不可变借用
for item in &mut vec   // iter_mut: 可变借用
```

### 2.3 跳转控制 (Jump Control)

#### 2.3.1 break

**形式化定义**:

```text
BreakExpr := break ('label)? Expression?
where:
  'label: 可选标签
  Expression: 可选返回值
```

**本体属性**:

- **作用**: 退出循环
- **返回值**: 可携带值
- **目标**: 最近的循环或标签块

#### 2.3.2 continue

**形式化定义**:

```text
ContinueExpr := continue ('label)?
```

**本体属性**:

- **作用**: 跳到下次迭代
- **返回值**: ! (never类型)

#### 2.3.3 return

**形式化定义**:

```text
ReturnExpr := return Expression?
```

**本体属性**:

- **作用**: 从函数返回
- **返回值**: ! (never类型)
- **提前退出**: 可在任何位置

---

## 3️⃣ 函数层概念

### 3.1 函数定义 (Function Definition)

**形式化定义**:

```text
Function := fn name<Generics>(Parameters) -> ReturnType
            where Bounds
            { Body }
where:
  Generics: 类型参数
  Parameters: (pattern: Type),*
  ReturnType: 返回类型（默认()）
  Bounds: where子句约束
  Body: 函数体表达式
```

**本体属性**:

- **命名**: 标识符
- **参数**: 参数列表
- **返回类型**: 显式或推断
- **泛型**: 可选类型参数
- **可见性**: pub/pub(crate)/private

### 3.2 函数类型

#### 3.2.1 普通函数 (Free Function)

**定义**: 独立的函数，不属于任何类型

**示例**:

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

#### 3.2.2 关联函数 (Associated Function)

**定义**: 与类型关联的函数，无self参数

**示例**:

```rust
impl MyType {
    fn new() -> Self { ... }  // 构造函数
}
```

#### 3.2.3 方法 (Method)

**定义**: 与类型关联的函数，有self参数

**self模式**:

```rust
impl MyType {
    fn by_value(self) { ... }      // 移动所有权
    fn by_ref(&self) { ... }       // 不可变借用
    fn by_mut_ref(&mut self) { ... }  // 可变借用
}
```

### 3.3 参数传递 (Parameter Passing)

**形式化定义**:

```text
Parameter := 
  | T               // 按值传递
  | &T              // 不可变引用
  | &mut T          // 可变引用
  | impl Trait      // impl Trait语法
```

**本体属性**:

| 模式 | 所有权 | 可变性 | 性能 | 适用场景 |
|------|-------|-------|------|---------|
| T | 转移 | 取决于绑定 | 可能复制 | 消费值 |
| &T | 借用 | 不可变 | 零成本 | 只读访问 |
| &mut T | 借用 | 可变 | 零成本 | 修改数据 |

### 3.4 返回类型 (Return Type)

**形式化定义**:

```text
ReturnType := 
  | T                    // 具体类型
  | impl Trait          // impl Trait
  | -> !                // Never类型
  | (省略)              // 默认()
```

**impl Trait** (Rust 1.26+):

```rust
fn make_iter() -> impl Iterator<Item = i32> {
    vec![1, 2, 3].into_iter()
}
```

**Never类型** (Rust 1.90):

```rust
fn diverges() -> ! {
    panic!("永远不返回");
}
```

---

## 4️⃣ 模式层概念

### 4.1 模式类型 (Pattern Types)

#### 4.1.1 模式分类

**形式化定义**:

```text
Pattern := 
  | Literal           // 字面量: 1, "str"
  | Variable          // 变量: x, mut y
  | Wildcard          // 通配符: _
  | Tuple             // 元组: (a, b, c)
  | Struct            // 结构: Point { x, y }
  | Enum              // 枚举: Some(x), None
  | Reference         // 引用: &x, ref x
  | Range             // 范围: 1..=10
```

#### 4.1.2 可反驳性 (Refutability)

**形式化定义**:

```text
Irrefutable Pattern: 总是匹配成功
  - 变量模式: x
  - 通配符: _
  - 元组模式（所有子模式不可反驳）

Refutable Pattern: 可能匹配失败
  - 字面量: 42
  - 枚举变体: Some(x)
  - 范围: 1..=10
```

**使用规则**:

```rust
// let需要不可反驳模式
let x = 5;           // ✅
let Some(x) = opt;   // ❌ 可反驳

// if let/match允许可反驳模式
if let Some(x) = opt { ... }  // ✅
match opt {
    Some(x) => ...,
    None => ...,
}  // ✅
```

### 4.2 模式特性

#### 4.2.1 绑定模式 (@-binding)

**形式化定义**:

```text
@-Pattern := identifier @ Pattern
```

**用途**: 同时匹配和绑定

**示例**:

```rust
match value {
    x @ 1..=5 => println!("1-5范围: {}", x),
    x @ 6..=10 => println!("6-10范围: {}", x),
    _ => {}
}
```

#### 4.2.2 引用模式

**两种形式**:

```rust
// 1. &模式 - 匹配引用
match &value {
    &Some(x) => use(x),
    &None => {}
}

// 2. ref关键字 - 创建引用
match value {
    Some(ref x) => use(x),  // x是&T
    None => {}
}
```

#### 4.2.3 守卫条件 (Pattern Guards)

**形式化定义**:

```text
GuardedPattern := Pattern if Condition
where Condition: bool表达式
```

**示例**:

```rust
match value {
    Some(x) if x > 0 => println!("正数"),
    Some(x) if x < 0 => println!("负数"),
    Some(0) => println!("零"),
    None => println!("无值"),
}
```

### 4.3 穷尽性检查 (Exhaustiveness Checking)

**形式化定义**:

```text
Exhaustiveness := ∀v ∈ T, ∃i ∈ {1..n}, Pattern_i matches v
```

**检查算法**: 基于决策树的符号执行

**Rust 1.90 改进**:

- 更精确的穷尽性分析
- 更好的不可达代码检测

---

## 5️⃣ 组合层概念

### 5.1 闭包系统 (Closure System)

**形式化定义**:

```text
Closure := |Parameters| Body
         | |Parameters| -> ReturnType Body
         | move |Parameters| Body
where:
  Parameters: 参数列表（类型可推断）
  Body: 表达式或块
  move: 显式移动捕获
```

**本体属性**:

- **匿名性**: 无需命名
- **环境捕获**: 可访问外部变量
- **类型推断**: 参数和返回类型可推断
- **Fn Traits**: 实现Fn/FnMut/FnOnce

#### 5.1.1 捕获模式

**形式化定义**:

```text
Capture := 
  | Borrow(&T)          // 不可变借用
  | MutBorrow(&mut T)   // 可变借用
  | Move(T)             // 移动所有权
```

**自动推断规则**:

```rust
// 规则1: 默认最小化捕获
let x = vec![1, 2, 3];
let closure = || println!("{:?}", x);  // 捕获&x

// 规则2: 根据使用推断
let mut count = 0;
let mut inc = || count += 1;  // 捕获&mut count

// 规则3: move强制移动
let closure = move || drop(x);  // 移动x
```

**Rust 1.90 改进**: 更精确的捕获（捕获字段而非整个结构体）

#### 5.1.2 Fn Traits

**形式化定义**:

```text
trait FnOnce<Args> {
    type Output;
    fn call_once(self, args: Args) -> Self::Output;
}

trait FnMut<Args>: FnOnce<Args> {
    fn call_mut(&mut self, args: Args) -> Self::Output;
}

trait Fn<Args>: FnMut<Args> {
    fn call(&self, args: Args) -> Self::Output;
}
```

**层次关系**:

```text
Fn ⊂ FnMut ⊂ FnOnce

Fn:     可多次调用，不可变借用
FnMut:  可多次调用，可变借用
FnOnce: 只能调用一次，消费self
```

### 5.2 迭代器系统 (Iterator System)

**形式化定义**:

```text
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    
    // 大量默认方法...
}

trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}
```

**本体属性**:

- **惰性求值**: 方法链不立即执行
- **零成本抽象**: 优化后等价手写循环
- **迭代器融合**: 多次遍历合并为单次

#### 5.2.1 迭代器分类

**按方法类型**:

```text
Adapter:   返回新迭代器（惰性）
  - map, filter, take, skip, chain, zip, flat_map

Consumer:  消费迭代器，返回值（立即）
  - collect, fold, reduce, sum, count

Searcher:  搜索元素（短路）
  - find, any, all, position
```

#### 5.2.2 所有权模式

**三种迭代方式**:

```rust
let vec = vec![1, 2, 3];

vec.into_iter()  // 消费vec，获得T
vec.iter()       // 借用vec，获得&T
vec.iter_mut()   // 可变借用vec，获得&mut T
```

### 5.3 错误处理系统 (Error Handling System)

#### 5.3.1 Result类型

**形式化定义**:

```text
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

**本体属性**:

- **类型**: 枚举
- **语义**: 成功或失败
- **单子**: 实现Monad模式

#### 5.3.2 Option类型

**形式化定义**:

```text
enum Option<T> {
    Some(T),
    None,
}
```

**本体属性**:

- **类型**: 枚举
- **语义**: 有值或无值
- **单子**: 实现Monad模式

#### 5.3.3 ?运算符

**形式化定义**:

```text
expr? := 
  match expr {
      Ok(val) => val,
      Err(e) => return Err(From::from(e)),
  }

  // 或对于Option:
  match expr {
      Some(val) => val,
      None => return None,
  }
```

**本体属性**:

- **语法糖**: 简化错误传播
- **类型转换**: 自动From转换
- **控制流**: 早期返回

**Trait支持**:

```rust
trait Try {
    type Output;
    type Residual;
    
    fn from_output(output: Self::Output) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

trait FromResidual<R> {
    fn from_residual(residual: R) -> Self;
}
```

---

## 6️⃣ 类型系统集成

### 6.1 Never类型 (!)

**形式化定义**:

```text
! := 空类型（无值）
```

**本体属性**:

- **值**: 无（uninhabited type）
- **用途**: 表示永不返回
- **类型强制**: 可转换为任何类型
- **Rust 1.90**: 完全稳定

**示例**:

```rust
fn diverges() -> ! {
    panic!("never returns");
}

let x: i32 = if cond {
    42
} else {
    diverges()  // ! coerces to i32
};
```

### 6.2 类型推断

**本体属性**:

- **局部推断**: 函数内类型推断
- **全局推断**: 泛型参数推断
- **双向推断**: 从返回类型推断参数

### 6.3 类型统一

**形式化规则**:

```text
Unification Rule (if表达式):
Γ ⊢ then_branch: T₁
Γ ⊢ else_branch: T₂
T₁ = T₂  (或 T₁/T₂ 可协变)
────────────────────────
Γ ⊢ if expr { then } else { els }: T₁
```

---

## 🔗 概念关系总结

### 核心依赖关系

```text
表达式 ──is-base-of──→ 控制流
类型系统 ──constrains──→ 所有概念
模式匹配 ──enables──→ match/if-let/let-else
函数 ──is-generalized-by──→ 闭包
迭代器 ──uses──→ for循环
Result/Option ──enables──→ ?运算符
```

### 组合关系

```text
循环 + 模式 = while-let
条件 + 模式 = if-let
模式 + 早返回 = let-else
函数 + 捕获 = 闭包
Iterator + 方法链 = 声明式编程
```

---

## 📚 参考资料

- [关系网络](./02_relationship_network.md) - 概念间的详细关系
- [属性空间](./03_property_space.md) - 多维属性分析
- [推理规则](./04_reasoning_rules.md) - 自动推理规则
- [Rust Reference - Expressions](https://doc.rust-lang.org/reference/expressions.html)

---

**文档维护**: Rust 学习社区  
**更新频率**: 随Rust版本更新  
**文档版本**: v1.0
