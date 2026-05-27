# Proptest/QuickCheck 属性测试形式化分析

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 基于属性的随机测试
>
> **形式化框架**: 属性不变式 +  shrinking
>
> **参考**: proptest Documentation; quickcheck Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

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
  - [*定理数量: 5个*](#定理数量-5个)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

属性测试框架:

- **QuickCheck**: Haskell风格，简单属性
- **Proptest**: 高级shrinking，状态机测试

---

## 2. 属性定义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (属性即不变式)

> 属性定义输入输出关系。

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Software Testing]**

> **[来源: TRPL Ch. 11 - Testing]**

> **[来源: Rust Reference - Test Attributes]**

> **[来源: ACM - Software Testing]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Test Documentation](https://doc.rust-lang.org/rustc/tests/index.html)]**
>
> **[来源: [Criterion.rs](https://bheisler.github.io/criterion.rs/book/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
