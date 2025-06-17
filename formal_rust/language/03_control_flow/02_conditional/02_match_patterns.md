# 2.2 match表达式与模式匹配

## 目录

1. [基本定义](#1-基本定义)
2. [模式匹配理论](#2-模式匹配理论)
3. [形式化语义](#3-形式化语义)
4. [穷尽性分析](#4-穷尽性分析)
5. [类型系统集成](#5-类型系统集成)
6. [所有权与借用](#6-所有权与借用)
7. [编译时优化](#7-编译时优化)
8. [实际应用](#8-实际应用)

---

## 1. 基本定义

### 1.1 语法定义

**定义 1.1.1**: match表达式的语法形式

```
match_expr ::= match expression { match_arms* }
match_arms ::= pattern => expression [,]
pattern ::= literal_pattern | identifier_pattern | wildcard_pattern | 
           tuple_pattern | struct_pattern | enum_pattern | 
           reference_pattern | slice_pattern | range_pattern |
           guard_pattern
guard_pattern ::= pattern if condition
```

### 1.2 语义定义

**定义 1.1.2**: match表达式的语义
match表达式将一个值与一系列模式进行比较，执行第一个匹配成功的分支：

- 按顺序检查每个模式
- 执行第一个匹配成功的分支
- 必须穷尽所有可能的值

---

## 2. 模式匹配理论

### 2.1 模式定义

**定义 2.1.1**: 模式（Pattern）
模式是一个用于解构和匹配值的语法结构，具有以下性质：

- 可以绑定变量
- 可以解构复合类型
- 可以包含守卫条件

### 2.2 模式匹配关系

**定义 2.1.2**: 模式匹配关系
对于值 $v$ 和模式 $p$，匹配关系 $v \sim p$ 定义为：

$$\begin{align}
v \sim \text{literal}(l) &\iff v = l \\
v \sim \text{wildcard}(\_) &\iff \text{always true} \\
v \sim \text{identifier}(x) &\iff \text{bind } x \text{ to } v \\
v \sim \text{tuple}(p_1, p_2, \ldots) &\iff v = (v_1, v_2, \ldots) \land v_1 \sim p_1 \land v_2 \sim p_2 \land \ldots \\
v \sim \text{struct}\{f_1: p_1, f_2: p_2, \ldots\} &\iff v = \{f_1: v_1, f_2: v_2, \ldots\} \land v_1 \sim p_1 \land v_2 \sim p_2 \land \ldots
\end{align}$$

### 2.3 模式优先级

**定义 2.1.3**: 模式优先级
模式的优先级决定了匹配的顺序：
1. 字面量模式（最高优先级）
2. 标识符模式
3. 通配符模式（最低优先级）

---

## 3. 形式化语义

### 3.1 操作语义

**定义 3.1.1**: match表达式的操作语义
对于match表达式 `match v with p₁ => e₁ | p₂ => e₂ | ... | pₙ => eₙ`：

$$\frac{v \sim p_i \quad \langle e_i, \sigma \rangle \rightarrow \langle v', \sigma' \rangle}{\langle \text{match } v \text{ with } p_1 \Rightarrow e_1 | \ldots | p_n \Rightarrow e_n, \sigma \rangle \rightarrow \langle v', \sigma' \rangle}$$

其中 $i$ 是第一个匹配的模式索引。

### 3.2 指称语义

**定义 3.1.2**: match表达式的指称语义
match表达式的指称语义函数 $\mathcal{M}$ 定义为：

$$\mathcal{M}[\text{match } v \text{ with } p_1 \Rightarrow e_1 | \ldots | p_n \Rightarrow e_n] = \lambda \sigma. \mathcal{E}[e_i](\sigma)$$

其中 $i = \min\{j \mid v \sim p_j\}$。

### 3.3 公理语义

**公理 3.1.1**: match表达式的霍尔逻辑公理
对于match表达式，霍尔逻辑公理为：

$$\frac{\{P \land v \sim p_1\} e_1 \{Q\} \quad \ldots \quad \{P \land v \sim p_n\} e_n \{Q\}}{\{P\} \text{ match } v \text{ with } p_1 \Rightarrow e_1 | \ldots | p_n \Rightarrow e_n \{Q\}}$$

---

## 4. 穷尽性分析

### 4.1 穷尽性定义

**定义 4.1.1**: 模式穷尽性
模式集合 $\{p_1, p_2, \ldots, p_n\}$ 对于类型 $\tau$ 是穷尽的，当且仅当：
$$\forall v: \tau, \exists i \in \{1, 2, \ldots, n\}, v \sim p_i$$

### 4.2 穷尽性检查算法

**算法 4.2.1**: 穷尽性检查
```rust
fn check_exhaustiveness(patterns: &[Pattern], value_type: Type) -> Result<(), ExhaustivenessError> {
    let uncovered = compute_uncovered(patterns, value_type);
    if uncovered.is_empty() {
        Ok(())
    } else {
        Err(ExhaustivenessError::UncoveredPatterns(uncovered))
    }
}

fn compute_uncovered(patterns: &[Pattern], value_type: Type) -> Vec<Value> {
    match value_type {
        Type::Enum(variants) => {
            let covered_variants: HashSet<_> = patterns
                .iter()
                .flat_map(|p| extract_enum_variants(p))
                .collect();

            variants
                .into_iter()
                .filter(|v| !covered_variants.contains(v))
                .map(|v| Value::Enum(v))
                .collect()
        }
        Type::Bool => {
            let has_true = patterns.iter().any(|p| matches_bool(p, true));
            let has_false = patterns.iter().any(|p| matches_bool(p, false));

            let mut uncovered = Vec::new();
            if !has_true { uncovered.push(Value::Bool(true)); }
            if !has_false { uncovered.push(Value::Bool(false)); }
            uncovered
        }
        _ => {
            // 对于其他类型，检查是否有通配符模式
            if patterns.iter().any(|p| is_wildcard(p)) {
                Vec::new()
            } else {
                vec![Value::Any] // 表示有未覆盖的值
            }
        }
    }
}
```

### 4.3 穷尽性证明

**定理 4.3.1**: 穷尽性保证
如果编译器接受match表达式，则该表达式的模式集合是穷尽的。

**证明**: 通过结构归纳法证明。基础情况是基本类型，归纳步骤考虑复合类型的解构。

---

## 5. 类型系统集成

### 5.1 类型推导规则

**规则 5.1.1**: match表达式的类型推导
$$\frac{\Gamma \vdash v : \tau \quad \Gamma \vdash e_1 : \tau' \quad \ldots \quad \Gamma \vdash e_n : \tau'}{\Gamma \vdash \text{match } v \text{ with } p_1 \Rightarrow e_1 | \ldots | p_n \Rightarrow e_n : \tau'}$$

**规则 5.1.2**: 模式绑定类型推导
$$\frac{\Gamma \vdash v : \tau \quad v \sim p \quad \Gamma, x: \tau \vdash e : \tau'}{\Gamma \vdash \text{match } v \text{ with } p \Rightarrow e : \tau'}$$

### 5.2 类型一致性

**定理 5.2.1**: match表达式类型一致性
对于match表达式，所有分支必须返回相同类型：
$$\text{typeof}(e_1) = \text{typeof}(e_2) = \ldots = \text{typeof}(e_n)$$

### 5.3 类型推断

**算法 5.3.1**: match表达式类型推断
```rust
fn infer_match_type(value_type: Type, arms: &[(Pattern, Expression)]) -> Result<Type, TypeError> {
    let mut arm_types = Vec::new();

    for (pattern, expression) in arms {
        // 创建新的类型环境，包含模式绑定的变量
        let mut env = TypeEnvironment::new();
        bind_pattern_variables(pattern, &value_type, &mut env)?;

        // 推断分支表达式的类型
        let arm_type = infer_expression_type(expression, &env)?;
        arm_types.push(arm_type);
    }

    // 检查所有分支类型是否一致
    let first_type = arm_types.first().ok_or(TypeError::NoArms)?;
    for arm_type in arm_types.iter().skip(1) {
        if arm_type != first_type {
            return Err(TypeError::ArmTypeMismatch);
        }
    }

    Ok(first_type.clone())
}
```

---

## 6. 所有权与借用

### 6.1 模式中的所有权

**规则 6.1.1**: 模式所有权规则
在模式匹配中：
- 默认情况下，模式通过值匹配（移动所有权）
- 使用 `ref` 关键字创建引用绑定
- 使用 `ref mut` 关键字创建可变引用绑定

### 6.2 借用检查

**定理 6.2.1**: match表达式借用安全
match表达式保证：
1. 所有分支中的借用都是有效的
2. 不会创建悬垂引用
3. 所有权转移是一致的

### 6.3 生命周期约束

**约束 6.3.1**: 模式匹配生命周期约束
在模式匹配中，引用的生命周期必须满足：
$$\forall r \in \text{References}, \text{Lifetime}(r) \subseteq \text{Scope}(\text{match expression})$$

---

## 7. 编译时优化

### 7.1 模式优化

**优化 7.1.1**: 模式重排
编译器会根据模式的匹配频率重排模式：
```rust
// 优化前
match value {
    RareVariant => handle_rare(),
    CommonVariant => handle_common(),
}

// 优化后
match value {
    CommonVariant => handle_common(),
    RareVariant => handle_rare(),
}
```

### 7.2 跳转表优化

**优化 7.2.1**: 跳转表生成
对于枚举类型的match表达式，编译器会生成跳转表：
```rust
// 源代码
match enum_value {
    Variant1 => action1(),
    Variant2 => action2(),
    Variant3 => action3(),
}

// 生成的跳转表
let jump_table = [action1, action2, action3];
jump_table[enum_value.discriminant()]();
```

### 7.3 死代码消除

**优化 7.3.1**: 不可达分支消除
编译器会消除不可达的分支：
```rust
// 优化前
match Some(42) {
    Some(x) => println!("{}", x),
    None => unreachable!(), // 死代码
}

// 优化后
println!("42");
```

---

## 8. 实际应用

### 8.1 基本用法示例

```rust
// 基本模式匹配
fn describe_number(n: i32) -> &'static str {
    match n {
        0 => "zero",
        1 => "one",
        2 => "two",
        _ => "many",
    }
}

// 枚举模式匹配
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn process_message(msg: Message) {
    match msg {
        Message::Quit => println!("退出"),
        Message::Move { x, y } => println!("移动到 ({}, {})", x, y),
        Message::Write(text) => println!("写入: {}", text),
        Message::ChangeColor(r, g, b) => println!("颜色: ({}, {}, {})", r, g, b),
    }
}
```

### 8.2 高级模式匹配

```rust
// 多重模式
fn is_zero_or_one(n: i32) -> bool {
    match n {
        0 | 1 => true,
        _ => false,
    }
}

// 范围模式
fn describe_range(n: i32) -> &'static str {
    match n {
        1..=5 => "small",
        6..=10 => "medium",
        11..=20 => "large",
        _ => "huge",
    }
}

// 守卫模式
fn describe_with_guard(n: i32) -> &'static str {
    match n {
        x if x < 0 => "negative",
        x if x > 0 => "positive",
        _ => "zero",
    }
}
```

### 8.3 所有权管理示例

```rust
// 通过值匹配（移动所有权）
fn process_owned_string(s: String) {
    match s {
        s if s.len() > 10 => println!("长字符串: {}", s),
        s => println!("短字符串: {}", s),
    }
    // s在这里不可用，因为所有权被移动
}

// 通过引用匹配（保留所有权）
fn process_string_ref(s: &String) {
    match s {
        s if s.len() > 10 => println!("长字符串: {}", s),
        s => println!("短字符串: {}", s),
    }
    // s在这里仍然可用
}

// 使用ref关键字
fn process_with_ref(s: String) {
    match s {
        ref s_ref if s_ref.len() > 10 => {
            println!("长字符串: {}", s_ref);
            // s在这里仍然可用
        }
        ref s_ref => {
            println!("短字符串: {}", s_ref);
            // s在这里仍然可用
        }
    }
    println!("原始字符串: {}", s); // 仍然可用
}
```

### 8.4 错误处理示例

```rust
// Result类型处理
fn divide_and_process(a: f64, b: f64) -> Result<String, String> {
    let result = match (a, b) {
        (_, 0.0) => Err("除数不能为零".to_string()),
        (x, y) if x < 0.0 && y < 0.0 => Ok("两个负数相除".to_string()),
        (x, y) => Ok(format!("结果: {}", x / y)),
    };

    result
}

// Option类型处理
fn safe_array_access<T>(arr: &[T], index: usize) -> Option<&T> {
    match arr.get(index) {
        Some(element) => Some(element),
        None => None,
    }
}

// 使用?运算符的简化版本
fn safe_array_access_simple<T>(arr: &[T], index: usize) -> Option<&T> {
    Some(arr.get(index)?)
}
```

### 8.5 性能优化示例

```rust
// 使用match进行早期返回
fn find_element<T: PartialEq>(items: &[T], target: &T) -> Option<usize> {
    match items.len() {
        0 => None,
        1 => if items[0] == *target { Some(0) } else { None },
        _ => {
            // 执行线性搜索
            for (i, item) in items.iter().enumerate() {
                if item == target {
                    return Some(i);
                }
            }
            None
        }
    }
}

// 使用match进行状态机
enum State {
    Initial,
    Processing,
    Complete,
    Error,
}

fn process_state_machine(state: State, input: &str) -> State {
    match (state, input) {
        (State::Initial, "start") => State::Processing,
        (State::Processing, "continue") => State::Processing,
        (State::Processing, "finish") => State::Complete,
        (State::Processing, "error") => State::Error,
        (State::Complete, _) => State::Complete,
        (State::Error, _) => State::Error,
        _ => State::Error,
    }
}
```

---

## 总结

match表达式是Rust模式匹配系统的核心，提供了强大、安全、高效的值解构和分支选择机制。

**关键特性**:
- 穷尽性检查保证所有情况都被处理
- 强大的模式匹配能力
- 与所有权系统的深度集成
- 编译时优化支持

**安全保证**:
- 类型安全
- 内存安全
- 穷尽性安全

**性能特性**:
- 零成本抽象
- 跳转表优化
- 死代码消除

---

**版本**: 1.0  
**更新时间**: 2025-01-27
