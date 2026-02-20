# 研究方法

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> **概念说明**: 研究方法是指在 Rust 形式化工程中进行系统探索的科学方法论，包括问题定义、形式化建模、定理陈述与证明、验证工具应用等步骤。形式化方法通过数学手段验证程序的正确性，确保代码行为符合规范。

> 内容已整合至： [research_methodology.md](../../../../research_notes/research_methodology.md)

[返回主索引](../../00_master_index.md)

---

## 研究方法概述

### 形式化方法研究流程

```
问题定义
    ↓
形式化建模（数学定义）
    ↓
定理陈述
    ↓
证明构造
    ↓
证明验证（人工/工具）
    ↓
文档化
    ↓
代码实现与验证
```

### 研究笔记结构

```markdown
# 研究笔记模板

## 问题陈述
- 研究什么问题
- 为什么重要

## 形式化定义
- 数学符号定义
- 类型/状态定义

## 定理与证明
- 定理陈述
- 证明步骤
- 证明验证

## 实现考虑
- Rust 实现映射
- 边界条件

## 开放问题
- 未解决的疑问
- 进一步研究方向
```

### 证明验证工具

```rust
// 形式化验证工具链

// 1. MIRI：检测未定义行为
cargo miri test

// 2. Kani：模型检查
#[kani::proof]
fn verify_property() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    assert!(x * 2 < 200);
}

// 3. Prusti：基于契约的验证
#[requires(x > 0)]
#[ensures(result > x)]
fn double(x: i32) -> i32 {
    x * 2
}
```

### 研究方法论示例

```rust
// 研究问题：验证 Vec<T> 的 push 操作内存安全

// 1. 形式化建模
// Vec<T> 是一个动态数组，具有以下状态：
// - ptr: 指向堆分配的指针
// - len: 当前元素数量
// - cap: 容量

// 2. 定理陈述
// 定理 T1: push 操作保证内存安全
// ∀ vec: Vec<T>, ∀ item: T
//   vec.len < vec.cap → push 不会重新分配
//   vec.len == vec.cap → push 重新分配成功

// 3. Rust 实现映射
pub struct Vec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    _marker: PhantomData<T>,
}

impl<T> Vec<T> {
    pub fn push(&mut self, item: T) {
        // 预条件：所有权正确
        // 后条件：len 增加 1
        if self.len == self.cap {
            self.grow();
        }
        unsafe {
            ptr::write(self.ptr.as_ptr().add(self.len), item);
        }
        self.len += 1;
    }
}

// 4. 验证测试
#[cfg(test)]
mod verification_tests {
    use super::*;

    #[test]
    fn test_push_invariants() {
        let mut vec = Vec::new();
        assert_eq!(vec.len(), 0);
        assert!(vec.capacity() >= 0);

        vec.push(1);
        assert_eq!(vec.len(), 1);
        assert!(vec.capacity() >= 1);
    }
}
```

### 类型系统研究示例

```rust
// 研究问题：验证类型系统的子类型关系

// 形式化定义
// Γ ⊢ e : T  表示在上下文 Γ 中，表达式 e 具有类型 T

// 定理：子类型传递性
// 如果 T1 <: T2 且 T2 <: T3，则 T1 <: T3

// Rust 实现：生命周期子类型
fn example<'a: 'b, 'b>(x: &'a str) -> &'b str {
    x  // 'a <: 'b，所以 &'a str <: &'b str
}

// 验证：通过借用检查器
fn verify<'long: 'short>(long: &'long str, short: &'short str) {
    let s: &'short str = long;  // OK: 'long <: 'short
    // let l: &'long str = short;  // Error: 'short 不 <: 'long
}
```

### 所有权研究示例

```rust
// 研究问题：验证所有权转移的正确性

// 形式化定义
// own(x) : x 拥有资源 R 的所有权
// move(x → y) : 将 x 的所有权转移给 y
// use(x) : 使用 x
// drop(x) : 释放 x

// 定理：所有权唯一性
// ∀ R, 只有一个变量可以 own(R)

// Rust 实现
fn ownership_transfer() {
    let s1 = String::from("hello");  // s1 owns the string
    let s2 = s1;                      // ownership moved to s2
    // println!("{}", s1);            // Error: s1 no longer owns
    println!("{}", s2);               // OK: s2 owns
}  // s2 dropped, memory freed

// 定理：借用规则
// 给定资源 R：
// - 可以有多个不可变借用 &R
// - 或一个可变借用 &mut R
// - 不能同时存在

fn borrowing_rules() {
    let mut data = vec![1, 2, 3];

    // 多个不可变借用
    let r1 = &data;
    let r2 = &data;
    println!("{} {}", r1[0], r2[0]);

    // 一个可变借用
    let r3 = &mut data;
    r3.push(4);
    // let r4 = &data;  // Error: cannot borrow while mutable borrow active
}
```

### 形式化规范写作

```rust
/// # 规范
///
/// ## 前置条件
/// - `slice` 非空
/// - `predicate` 是纯函数（无副作用）
///
/// ## 后置条件
/// - 返回满足 predicate 的第一个元素
/// - 如果没有元素满足，返回 None
///
/// ## 正确性证明思路
/// 1. 遍历不变量：已检查的元素都不满足 predicate
/// 2. 终止：slice 长度有限
/// 3. 返回：找到的第一个满足条件的元素
pub fn find<T>(slice: &[T], predicate: impl Fn(&T) -> bool) -> Option<&T> {
    for item in slice {
        if predicate(item) {
            return Some(item);
        }
    }
    None
}

// 属性测试验证
#[cfg(test)]
mod property_tests {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn find_returns_first_match(vec: Vec<i32>) {
            prop_assume!(!vec.is_empty());

            let first_positive = vec.iter()
                .find(|&&x| x > 0);

            // 性质：返回的元素（如果存在）满足条件
            if let Some(&x) = first_positive {
                prop_assert!(x > 0);
            }

            // 性质：返回的元素之前的所有元素都不满足条件
            if let Some(pos) = vec.iter().position(|&x| x > 0) {
                for i in 0..pos {
                    prop_assert!(vec[i] <= 0);
                }
            }
        }
    }
}
```

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../../research_notes/formal_methods/README.md](../../../../../research_notes/formal_methods/README.md) |
| 形式化验证指南 | 完整验证流程 | [../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md](../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md) |
| 证明系统指南 | 形式化证明方法 | [../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md](../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) |
| 所有权模型形式化 | 所有权系统数学定义 | [../../../../../research_notes/formal_methods/ownership_model.md](../../../../../research_notes/formal_methods/ownership_model.md) |
| 类型系统形式化 | 类型理论数学定义 | [../../../../../research_notes/formal_methods/type_system_formalization.md](../../../../../research_notes/formal_methods/type_system_formalization.md) |
| 生命周期形式化 | 生命周期理论证明 | [../../../../../research_notes/formal_methods/lifetime_formalization.md](../../../../../research_notes/formal_methods/lifetime_formalization.md) |
| 借用检查器证明 | 借用检查器形式化 | [../../../../../research_notes/formal_methods/borrow_checker_proof.md](../../../../../research_notes/formal_methods/borrow_checker_proof.md) |
| 证明索引 | 形式化证明集合 | [../../../../../research_notes/PROOF_INDEX.md](../../../../../research_notes/PROOF_INDEX.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 研究方法论 | 研究方法指南 | [../../../../../research_notes/research_methodology.md](../../../../../research_notes/research_methodology.md) |
| 形式化验证工具 | 工具使用指南 | [../../../../../research_notes/TOOLS_GUIDE.md](../../../../../research_notes/TOOLS_GUIDE.md) |
| 证明索引 | 形式化证明集合 | [../../../../../research_notes/PROOF_INDEX.md](../../../../../research_notes/PROOF_INDEX.md) |
| 研究路线图 | 长期研究规划 | [../../../../../research_notes/RESEARCH_ROADMAP.md](../../../../../research_notes/RESEARCH_ROADMAP.md) |
| 核心定理证明 | 完整证明文档 | [../../../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md](../../../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md) |
| 形式化证明分析 | 证明分析与计划 | [../../../../../research_notes/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md](../../../../../research_notes/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md) |
| 最佳实践 | 工程最佳实践 | [../../../../../research_notes/BEST_PRACTICES.md](../../../../../research_notes/BEST_PRACTICES.md) |
| 质量检查清单 | 研究笔记质量检查 | [../../../../../research_notes/QUALITY_CHECKLIST.md](../../../../../research_notes/QUALITY_CHECKLIST.md) |

---

[返回主索引](../../00_master_index.md) | [返回研究议程索引](../README.md)
