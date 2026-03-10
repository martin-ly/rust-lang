# Proptest/QuickCheck 属性测试形式化分析

> **主题**: 基于属性的随机测试
>
> **形式化框架**: 属性不变式 +  shrinking
>
> **参考**: proptest Documentation; quickcheck Documentation

---

## 目录

- [Proptest/QuickCheck 属性测试形式化分析](#proptestquickcheck-属性测试形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 属性定义](#2-属性定义)
    - [定理 2.1 (属性即不变式)](#定理-21-属性即不变式)
  - [3. 随机生成](#3-随机生成)
    - [定理 3.1 (策略组合)](#定理-31-策略组合)
  - [4. Shrinking](#4-shrinking)
    - [定理 4.1 (最小反例)](#定理-41-最小反例)
  - [5. 状态机测试](#5-状态机测试)
    - [定理 5.1 (状态转换)](#定理-51-状态转换)
  - [6. 反例](#6-反例)
    - [反例 6.1 (不够通用)](#反例-61-不够通用)
    - [反例 6.2 (忽略前提)](#反例-62-忽略前提)

---

## 1. 引言

属性测试框架:

- **QuickCheck**: Haskell风格，简单属性
- **Proptest**: 高级shrinking，状态机测试

---

## 2. 属性定义

### 定理 2.1 (属性即不变式)

> 属性定义输入输出关系。

```rust
// QuickCheck
quickcheck! {
    fn prop_reverse_reverse(xs: Vec<u32>) -> bool {
        let rev: Vec<_> = xs.clone().into_iter().rev().rev().collect();
        xs == rev
    }
}

// Proptest
proptest! {
    #[test]
    fn prop_add_commutative(a: i32, b: i32) {
        assert_eq!(add(a, b), add(b, a));
    }
}
```

∎

---

## 3. 随机生成

### 定理 3.1 (策略组合)

> 生成器可组合。

```rust
let user_strategy = (any::<String>(), 0..100u8)
    .prop_map(|(name, age)| User { name, age });
```

∎

---

## 4. Shrinking

### 定理 4.1 (最小反例)

> 测试失败时自动简化输入。

```rust
// 原失败输入: [1, 2, 3, 4, 5, ... 100]
// shrink后:    [0, 0]
// 更易于调试
```

∎

---

## 5. 状态机测试

### 定理 5.1 (状态转换)

> Proptest支持状态机模型测试。

```rust
#[derive(Clone, Debug, StateMachineTest)]
ref_state_machine! {
    name = MyStateMachine,
    init = || MyState::default(),
    transitions = add, remove, get
}
```

∎

---

## 6. 反例

### 反例 6.1 (不够通用)

```rust
// 仅测试特定值
#[test]
fn test_add() {
    assert_eq!(add(2, 2), 4);
}

// 更好: 测试属性
proptest! {
    #[test]
    fn prop_add(a: i32, b: i32) {
        assert_eq!(add(a, b), a + b);
    }
}
```

### 反例 6.2 (忽略前提)

```rust
// 未处理除零
fn prop_div(a: i32, b: i32) -> bool {
    a / b == a / b  // b=0时panic
}

// 正确: 添加假设
fn prop_div(a: i32, b: i32) -> TestResult {
    if b == 0 {
        return TestResult::discard();
    }
    TestResult::from_bool(a / b == a / b)
}
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
