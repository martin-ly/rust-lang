# 2.1 if表达式形式化

## 目录

1. [基本定义](#1-基本定义)
2. [形式化语义](#2-形式化语义)
3. [类型系统分析](#3-类型系统分析)
4. [所有权与借用](#4-所有权与借用)
5. [编译时检查](#5-编译时检查)
6. [优化策略](#6-优化策略)
7. [实际应用](#7-实际应用)

---

## 1. 基本定义

### 1.1 语法定义

**定义 1.1.1**: if表达式的语法形式

```
if_expr ::= if condition { block_true } [else { block_false }]
condition ::= expression : bool
block_true ::= { statements* }
block_false ::= { statements* }
```

### 1.2 语义定义

**定义 1.1.2**: if表达式的语义
if表达式根据条件表达式的值选择性地执行代码块：

- 当条件为 `true` 时，执行 `block_true`
- 当条件为 `false` 时，执行 `block_false`（如果存在）

---

## 2. 形式化语义

### 2.1 操作语义

**定义 2.1.1**: if表达式的操作语义
对于if表达式 `if C then T else F`，其操作语义定义为：

$$\frac{\langle C, \sigma \rangle \rightarrow \langle \text{true}, \sigma' \rangle \quad \langle T, \sigma' \rangle \rightarrow \langle v, \sigma'' \rangle}{\langle \text{if } C \text{ then } T \text{ else } F, \sigma \rangle \rightarrow \langle v, \sigma'' \rangle}$$

$$\frac{\langle C, \sigma \rangle \rightarrow \langle \text{false}, \sigma' \rangle \quad \langle F, \sigma' \rangle \rightarrow \langle v, \sigma'' \rangle}{\langle \text{if } C \text{ then } T \text{ else } F, \sigma \rangle \rightarrow \langle v, \sigma'' \rangle}$$

其中：

- $\sigma$ 表示程序状态
- $v$ 表示表达式的值
- $\rightarrow$ 表示状态转换关系

### 2.2 指称语义

**定义 2.1.2**: if表达式的指称语义
if表达式的指称语义函数 $\mathcal{E}$ 定义为：

$$\mathcal{E}[\text{if } C \text{ then } T \text{ else } F] = \lambda \sigma. \begin{cases}
\mathcal{E}[T](\sigma) & \text{if } \mathcal{E}[C](\sigma) = \text{true} \\
\mathcal{E}[F](\sigma) & \text{if } \mathcal{E}[C](\sigma) = \text{false}
\end{cases}$$

### 2.3 公理语义

**公理 2.1.1**: if表达式的霍尔逻辑公理
对于if表达式 `if C then T else F`，霍尔逻辑公理为：

$$\frac{\{P \land C\} T \{Q\} \quad \{P \land \neg C\} F \{Q\}}{\{P\} \text{ if } C \text{ then } T \text{ else } F \{Q\}}$$

其中：
- $P$ 是前置条件
- $Q$ 是后置条件
- $C$ 是条件表达式

---

## 3. 类型系统分析

### 3.1 类型推导规则

**规则 3.1.1**: if表达式的类型推导
$$\frac{\Gamma \vdash C : \text{bool} \quad \Gamma \vdash T : \tau \quad \Gamma \vdash F : \tau}{\Gamma \vdash \text{if } C \text{ then } T \text{ else } F : \tau}$$

**规则 3.1.2**: 无else分支的if表达式类型推导
$$\frac{\Gamma \vdash C : \text{bool} \quad \Gamma \vdash T : \text{unit}}{\Gamma \vdash \text{if } C \text{ then } T : \text{unit}}$$

### 3.2 类型一致性要求

**定理 3.2.1**: if表达式类型一致性
对于if表达式 `if C then T else F`，必须满足：
$$\text{typeof}(T) = \text{typeof}(F)$$

**证明**: 假设 $\text{typeof}(T) \neq \text{typeof}(F)$，则表达式的类型无法在编译时确定，违反了Rust的类型安全原则。

### 3.3 类型推断算法

**算法 3.3.1**: if表达式类型推断
```rust
fn infer_if_type(condition: Type, then_block: Type, else_block: Option<Type>) -> Result<Type, TypeError> {
    // 检查条件类型
    if condition != Type::Bool {
        return Err(TypeError::ExpectedBool);
    }

    // 检查分支类型一致性
    match else_block {
        Some(else_type) => {
            if then_block == else_type {
                Ok(then_block)
            } else {
                Err(TypeError::BranchTypeMismatch)
            }
        }
        None => {
            if then_block == Type::Unit {
                Ok(Type::Unit)
            } else {
                Err(TypeError::MissingElseBranch)
            }
        }
    }
}
```

---

## 4. 所有权与借用

### 4.1 借用检查规则

**规则 4.1.1**: if表达式中的借用检查
在if表达式中，借用检查器会分析每个分支内的所有权变化：

1. **分支内借用**: 每个分支内的借用必须在该分支结束时失效
2. **分支间一致性**: 所有分支后的变量状态必须一致
3. **表达式后可用性**: 表达式结束后，变量要么都被移动，要么都可用

### 4.2 所有权转移分析

**定理 4.2.1**: if表达式所有权一致性
对于if表达式 `if C then T else F`，若变量 $v$ 在某个分支中被移动，则：
- 要么所有分支都移动 $v$
- 要么 $v$ 在表达式后不可用

**证明**: 通过借用检查器的静态分析实现。编译器会跟踪每个分支中的所有权变化，确保一致性。

### 4.3 生命周期约束

**约束 4.3.1**: if表达式生命周期约束
在if表达式中，引用的生命周期必须满足：
$$\forall r \in \text{References}, \text{Lifetime}(r) \subseteq \text{Scope}(\text{if expression})$$

---

## 5. 编译时检查

### 5.1 条件类型检查

**检查 5.1.1**: 条件表达式类型检查
编译器确保条件表达式 $C$ 的类型为 `bool`：
$$\text{typeof}(C) = \text{bool}$$

### 5.2 分支可达性检查

**检查 5.2.1**: 分支可达性分析
编译器分析每个分支的可达性：
- 如果条件为常量 `true`，则 `else` 分支不可达
- 如果条件为常量 `false`，则 `then` 分支不可达

### 5.3 死代码消除

**优化 5.3.1**: 死代码消除
对于不可达的分支，编译器会进行死代码消除：
```rust
// 优化前
if true {
    println!("Always executed");
} else {
    println!("Never executed"); // 死代码
}

// 优化后
println!("Always executed");
```

---

## 6. 优化策略

### 6.1 常量折叠

**优化 6.1.1**: 常量条件折叠
当条件表达式在编译时已知时，编译器会进行常量折叠：
```rust
// 优化前
if 2 + 2 == 4 {
    println!("Math works!");
} else {
    println!("Math is broken!");
}

// 优化后
println!("Math works!");
```

### 6.2 分支合并

**优化 6.2.1**: 相同分支合并
当多个分支执行相同代码时，编译器会合并分支：
```rust
// 优化前
if condition {
    println!("Same action");
} else {
    println!("Same action");
}

// 优化后
println!("Same action");
```

### 6.3 条件重排

**优化 6.3.1**: 条件重排优化
编译器会根据分支的执行频率重排条件：
```rust
// 优化前
if rare_condition {
    // 很少执行的代码
} else if common_condition {
    // 经常执行的代码
}

// 优化后
if common_condition {
    // 经常执行的代码
} else if rare_condition {
    // 很少执行的代码
}
```

---

## 7. 实际应用

### 7.1 基本用法示例

```rust
// 基本if表达式
fn describe_number(n: i32) -> &'static str {
    if n > 0 {
        "positive"
    } else if n < 0 {
        "negative"
    } else {
        "zero"
    }
}

// 条件赋值
fn get_max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
```

### 7.2 所有权管理示例

```rust
fn process_string(s: String) {
    if s.len() > 10 {
        // 在此分支中使用s，但不消耗它
        println!("Long string: {}", s);
    } else {
        // 在此分支中移动s
        let processed = s.to_uppercase();
        println!("Processed: {}", processed);
    }
    // 编译错误：s的状态在不同分支中不一致
    // println!("{}", s);
}
```

### 7.3 错误处理示例

```rust
fn safe_divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 {
        None
    } else {
        Some(a / b)
    }
}

fn process_result(result: Option<f64>) {
    if let Some(value) = result {
        println!("Result: {}", value);
    } else {
        println!("No result available");
    }
}
```

### 7.4 性能优化示例

```rust
fn optimized_search<T: PartialEq>(items: &[T], target: &T) -> Option<usize> {
    // 使用if表达式进行早期返回
    if items.is_empty() {
        return None;
    }

    if items.len() == 1 {
        return if items[0] == *target { Some(0) } else { None };
    }

    // 执行二分搜索
    let mut left = 0;
    let mut right = items.len() - 1;

    while left <= right {
        let mid = (left + right) / 2;
        if items[mid] == *target {
            return Some(mid);
        } else if items[mid] < *target {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    None
}
```

---

## 总结

if表达式是Rust控制流系统的核心组件，通过严格的类型检查和所有权约束，提供了安全、高效的条件执行机制。

**关键特性**:
- 表达式优先设计
- 严格的类型一致性要求
- 所有权系统的深度集成
- 编译时优化支持

**安全保证**:
- 类型安全
- 内存安全
- 线程安全

**性能特性**:
- 零成本抽象
- 编译时优化
- 运行时高效

---

**版本**: 1.0  
**更新时间**: 2025-01-27
