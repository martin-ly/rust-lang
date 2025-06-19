# 03.02 形式化模式匹配系统 (Formal Pattern Matching System)

## 目录

1. [引言与基础定义](#1-引言与基础定义)
2. [模式语法与语义](#2-模式语法与语义)
3. [模式匹配算法](#3-模式匹配算法)
4. [穷尽性检查](#4-穷尽性检查)
5. [所有权与借用](#5-所有权与借用)
6. [模式守卫](#6-模式守卫)
7. [形式化验证](#7-形式化验证)
8. [定理与证明](#8-定理与证明)

---

## 1. 引言与基础定义

### 1.1 模式匹配基础

**定义 1.1** (模式)
模式是用于解构和匹配值的语法结构，形式化定义为：
$$\text{Pattern} = \text{Literal} \mid \text{Variable} \mid \text{Wildcard} \mid \text{Constructor} \mid \text{Ref} \mid \text{Slice}$$

**定义 1.2** (模式匹配)
模式匹配是值v与模式p的匹配关系：
$$\text{match}: \text{Value} \times \text{Pattern} \rightarrow \text{Option<Substitution>}$$

**定义 1.3** (替换)
替换是从变量到值的映射：
$$\text{Substitution} = \text{Var} \rightarrow \text{Value}$$

### 1.2 模式匹配系统

**定义 1.4** (模式匹配系统)
模式匹配系统是三元组：
$$\mathcal{PM} = (\mathcal{P}, \mathcal{V}, \text{match})$$
其中：

- $\mathcal{P}$ 是模式集合
- $\mathcal{V}$ 是值集合
- $\text{match}$ 是匹配函数

---

## 2. 模式语法与语义

### 2.1 基本模式

**定义 2.1** (字面量模式)
字面量模式匹配具体值：
$$\text{match}(v, \text{lit}) = \begin{cases}
\text{Some}(\emptyset) & \text{if } v = \text{lit} \\
\text{None} & \text{otherwise}
\end{cases}$$

**定义 2.2** (变量模式)
变量模式绑定值到变量：
$$\text{match}(v, x) = \text{Some}(\{x \mapsto v\})$$

**定义 2.3** (通配符模式)
通配符模式匹配任意值：
$$\text{match}(v, \_) = \text{Some}(\emptyset)$$

**示例 2.1** (基本模式)
```rust
match value {
    42 => "forty-two",           // 字面量模式
    x => format!("got {}", x),   // 变量模式
    _ => "anything else",        // 通配符模式
}
```

### 2.2 构造器模式

**定义 2.4** (元组模式)
元组模式匹配元组值：
$$\text{match}((v_1, ..., v_n), (p_1, ..., p_n)) = \begin{cases}
\text{Some}(\sigma_1 \cup ... \cup \sigma_n) & \text{if } \forall i: \text{match}(v_i, p_i) = \text{Some}(\sigma_i) \\
\text{None} & \text{otherwise}
\end{cases}$$

**定义 2.5** (结构体模式)
结构体模式匹配结构体值：
$$\text{match}(\text{Struct}\{f_1: v_1, ..., f_n: v_n\}, \text{Struct}\{f_1: p_1, ..., f_n: p_n\}) = \begin{cases}
\text{Some}(\sigma_1 \cup ... \cup \sigma_n) & \text{if } \forall i: \text{match}(v_i, p_i) = \text{Some}(\sigma_i) \\
\text{None} & \text{otherwise}
\end{cases}$$

**定义 2.6** (枚举模式)
枚举模式匹配枚举值：
$$\text{match}(\text{Variant}_i(v_1, ..., v_n), \text{Variant}_i(p_1, ..., p_n)) = \begin{cases}
\text{Some}(\sigma_1 \cup ... \cup \sigma_n) & \text{if } \forall i: \text{match}(v_i, p_i) = \text{Some}(\sigma_i) \\
\text{None} & \text{otherwise}
\end{cases}$$

**示例 2.2** (构造器模式)
```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

match msg {
    Message::Quit => "退出",
    Message::Move { x, y } => format!("移动到 ({}, {})", x, y),
    Message::Write(text) => format!("写入: {}", text),
    Message::ChangeColor(r, g, b) => format!("颜色: ({}, {}, {})", r, g, b),
}
```

### 2.3 引用模式

**定义 2.7** (引用模式)
引用模式匹配引用值：
$$\text{match}(\&v, \&p) = \text{match}(v, p)$$
$$\text{match}(\&v, \text{ref } x) = \text{Some}(\{x \mapsto \&v\})$$

**定义 2.8** (可变引用模式)
可变引用模式匹配可变引用：
$$\text{match}(\&mut v, \&mut p) = \text{match}(v, p)$$
$$\text{match}(\&mut v, \text{ref mut } x) = \text{Some}(\{x \mapsto \&mut v\})$$

**示例 2.3** (引用模式)
```rust
let value = 42;
match &value {
    &42 => "forty-two",
    ref x => format!("got {}", x),
}

let mut value = 42;
match &mut value {
    &mut 42 => "forty-two",
    ref mut x => {
        *x += 1;
        "incremented"
    },
}
```

### 2.4 切片模式

**定义 2.9** (切片模式)
切片模式匹配切片值：
$$\text{match}([v_1, ..., v_n], [p_1, ..., p_m]) = \begin{cases}
\text{Some}(\sigma_1 \cup ... \cup \sigma_m) & \text{if } n = m \land \forall i: \text{match}(v_i, p_i) = \text{Some}(\sigma_i) \\
\text{None} & \text{otherwise}
\end{cases}$$

**定义 2.10** (范围模式)
范围模式匹配范围内的值：
$$\text{match}(v, \text{start}..\text{end}) = \begin{cases}
\text{Some}(\emptyset) & \text{if } \text{start} \leq v < \text{end} \\
\text{None} & \text{otherwise}
\end{cases}$$

**示例 2.4** (切片模式)
```rust
match slice {
    [first, second, ..] => format!("前两个: {}, {}", first, second),
    [single] => format!("单个: {}", single),
    [] => "空切片",
}

match value {
    1..=5 => "一到五",
    6..10 => "六到九",
    _ => "其他",
}
```

---

## 3. 模式匹配算法

### 3.1 匹配算法

**算法 3.1** (模式匹配算法)
```rust
fn match_pattern(value: Value, pattern: Pattern) -> Option<Substitution> {
    match pattern {
        Literal(lit) => {
            if value == lit {
                Some(Substitution::new())
            } else {
                None
            }
        }
        Variable(name) => {
            let mut subst = Substitution::new();
            subst.insert(name, value);
            Some(subst)
        }
        Wildcard => Some(Substitution::new()),
        Constructor(name, patterns) => {
            if let Constructor(value_name, values) = value {
                if name == value_name && patterns.len() == values.len() {
                    let mut combined_subst = Substitution::new();
                    for (pattern, value) in patterns.iter().zip(values.iter()) {
                        if let Some(subst) = match_pattern(value.clone(), pattern.clone()) {
                            combined_subst.extend(subst);
                        } else {
                            return None;
                        }
                    }
                    Some(combined_subst)
                } else {
                    None
                }
            } else {
                None
            }
        }
        // ... 其他模式类型
    }
}
```

### 3.2 匹配顺序

**定义 3.1** (模式优先级)
模式按以下优先级匹配：
1. 字面量模式
2. 变量模式
3. 通配符模式
4. 构造器模式

**定理 3.1** (匹配顺序无关性)
对于不重叠的模式，匹配顺序不影响结果。

**证明**：
由于模式不重叠，每个值最多匹配一个模式，因此顺序无关。

---

## 4. 穷尽性检查

### 4.1 穷尽性定义

**定义 4.1** (穷尽性)
模式匹配是穷尽的，如果所有可能的值都被至少一个模式覆盖：
$$\text{exhaustive}(patterns, type) \Leftrightarrow \forall v \in \text{values}(type): \exists p \in patterns: \text{match}(v, p) \neq \text{None}$$

### 4.2 穷尽性检查算法

**算法 4.1** (穷尽性检查)
```rust
fn is_exhaustive(patterns: &[Pattern], value_type: Type) -> bool {
    match value_type {
        Type::Enum(variants) => {
            // 检查所有枚举变体是否被覆盖
            for variant in variants {
                if !patterns.iter().any(|p| covers_variant(p, variant)) {
                    return false;
                }
            }
            true
        }
        Type::Bool => {
            // 检查true和false是否被覆盖
            patterns.iter().any(|p| matches_bool(p, true)) &&
            patterns.iter().any(|p| matches_bool(p, false))
        }
        Type::Integer => {
            // 整数类型需要通配符模式
            patterns.iter().any(|p| matches_wildcard(p))
        }
        // ... 其他类型
    }
}
```

### 4.3 穷尽性定理

**定理 4.1** (枚举穷尽性)
对于枚举类型，当且仅当所有变体都被模式覆盖时，匹配是穷尽的。

**证明**：
1. 必要性：如果某个变体未被覆盖，存在值不匹配任何模式
2. 充分性：如果所有变体都被覆盖，每个值都匹配某个模式

**定理 4.2** (布尔穷尽性)
对于布尔类型，当且仅当true和false都被覆盖时，匹配是穷尽的。

**证明**：
布尔类型只有两个值，必须都覆盖。

---

## 5. 所有权与借用

### 5.1 模式中的所有权

**定义 5.1** (模式绑定)
模式绑定决定变量的所有权：
$$\text{binding}(pattern) = \begin{cases}
\text{move} & \text{if } \text{consumes}(pattern) \\
\text{borrow} & \text{if } \text{borrows}(pattern) \\
\text{copy} & \text{if } \text{copies}(pattern)
\end{cases}$$

**规则 5.1** (移动绑定)
默认情况下，模式绑定移动值：
```rust
match value {
    Pattern(x) => {
        // x获得value的所有权
    }
}
```

**规则 5.2** (引用绑定)
使用ref关键字创建引用绑定：
```rust
match value {
    Pattern(ref x) => {
        // x是对value的引用
    }
}
```

### 5.2 借用检查

**定理 5.1** (模式借用安全)
模式匹配中的借用必须满足借用检查器规则。

**证明**：
借用检查器分析模式匹配过程中的所有权转移，确保：
1. 没有悬垂引用
2. 没有数据竞争
3. 借用生命周期有效

**示例 5.1** (模式借用)
```rust
let mut value = Some(String::from("hello"));

match value {
    Some(ref s) => {
        // s是&String，value仍然可用
        println!("{}", s);
    }
    None => {}
}

// value在这里仍然可用
value = Some(String::from("world"));
```

---

## 6. 模式守卫

### 6.1 模式守卫定义

**定义 6.1** (模式守卫)
模式守卫是模式匹配的附加条件：
$$\text{PatternGuard} = \text{Pattern} \text{ if } \text{Expression}$$

**定义 6.2** (守卫匹配)
带守卫的模式匹配：
$$\text{match}(v, p \text{ if } g) = \begin{cases}
\text{match}(v, p) & \text{if } eval(g) = \text{true} \\
\text{None} & \text{otherwise}
\end{cases}$$

### 6.2 守卫语义

**语义规则 6.1** (守卫求值)
守卫表达式在模式匹配成功后求值：
```rust
match value {
    Pattern(x) if condition(x) => {
        // 只有当condition(x)为true时执行
    }
    _ => {}
}
```

**示例 6.1** (模式守卫)
```rust
match value {
    Some(x) if x > 0 => format!("正数: {}", x),
    Some(x) if x < 0 => format!("负数: {}", x),
    Some(0) => "零".to_string(),
    None => "无值".to_string(),
}
```

---

## 7. 形式化验证

### 7.1 模式匹配正确性

**定义 7.1** (模式匹配正确性)
模式匹配算法是正确的，如果：
$$\forall v, p: \text{match}(v, p) = \text{Some}(\sigma) \Rightarrow \text{apply}(\sigma, p) = v$$

**定理 7.1** (基本模式正确性)
基本模式（字面量、变量、通配符）的匹配是正确的。

**证明**：
1. 字面量模式：直接比较值
2. 变量模式：创建绑定
3. 通配符模式：总是匹配

**定理 7.2** (构造器模式正确性)
构造器模式的匹配是正确的。

**证明**：
通过结构归纳，每个字段的匹配都是正确的。

### 7.2 穷尽性验证

**定义 7.2** (穷尽性验证)
穷尽性检查算法是正确的，如果：
$$\text{is_exhaustive}(patterns, type) \Leftrightarrow \text{exhaustive}(patterns, type)$$

**定理 7.3** (穷尽性检查正确性)
Rust编译器的穷尽性检查是正确的。

**证明**：
编译器通过静态分析验证所有可能的值都被覆盖。

---

## 8. 定理与证明

### 8.1 核心定理

**定理 8.1** (模式匹配确定性)
对于给定的值和模式，匹配结果是确定的。

**证明**：
模式匹配算法是确定性的，没有随机性或不确定性。

**定理 8.2** (模式匹配终止性)
模式匹配算法总是终止。

**证明**：
模式的结构是有限的，递归调用总是处理更小的子模式。

**定理 8.3** (模式匹配完整性)
如果值匹配模式，算法会找到匹配。

**证明**：
通过结构归纳，算法覆盖了所有可能的模式类型。

### 8.2 实现验证

**验证 8.1** (模式匹配实现)
Rust编译器的模式匹配实现与形式化定义一致。

**验证方法**：
1. 类型检查器验证模式类型
2. 借用检查器验证所有权
3. 穷尽性检查器验证覆盖

### 8.3 优化定理

**定理 8.4** (模式优化)
编译器可以优化模式匹配，生成高效的代码。

**证明**：
1. 跳转表优化
2. 决策树优化
3. 模式合并优化

---

## 总结

Rust的模式匹配系统提供了：

1. **丰富的模式语法**：支持各种数据结构的解构
2. **类型安全保证**：编译时检查模式类型
3. **所有权集成**：与所有权系统无缝集成
4. **穷尽性检查**：确保所有情况都被处理
5. **高效实现**：编译为优化的机器码

这些特性使模式匹配成为Rust中最强大的控制流机制之一。
