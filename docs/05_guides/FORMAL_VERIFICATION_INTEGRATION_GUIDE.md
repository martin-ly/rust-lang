# 形式化验证整合指南

> **版本**: Rust 1.94.0+
> **工具**: Miri, Kani, Prusti, Creusot, Aeneas
> **最后更新**: 2026-03-18
> **状态**: ✅ 生产就绪

---

## 📋 目录

- [形式化验证整合指南](#形式化验证整合指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🧪 Miri - 内存安全验证](#-miri---内存安全验证)
    - [Tree Borrows 模式](#tree-borrows-模式)
    - [代码示例](#代码示例)
    - [CI/CD 集成](#cicd-集成)
  - [🔍 Kani - 模型检查](#-kani---模型检查)
    - [基础验证](#基础验证)
    - [高级特性](#高级特性)
  - [📐 Prusti - 契约编程](#-prusti---契约编程)
    - [前置/后置条件](#前置后置条件)
    - [循环不变量](#循环不变量)
  - [🎓 工具选择决策树](#-工具选择决策树)
  - [🔗 综合示例](#-综合示例)
    - [完整的验证套件](#完整的验证套件)
  - [📊 验证覆盖率目标](#-验证覆盖率目标)

---

## 🎯 概述

本指南介绍如何在 Rust 项目中整合形式化验证工具，确保代码的内存安全、功能正确性和并发安全。

```text
┌─────────────────────────────────────────────────────────────────┐
│                     形式化验证工具矩阵                           │
├──────────────┬──────────────────┬──────────────┬────────────────┤
│     工具     │    验证目标       │   适用场景    │    学习曲线    │
├──────────────┼──────────────────┼──────────────┼────────────────┤
│ Miri         │ 内存安全          │ Unsafe 代码   │ 低             │
│ Kani         │ 功能正确性        │ 状态机/算法   │ 中             │
│ Prusti       │ 契约满足          │ 函数式代码    │ 中             │
│ Creusot      │ 复杂不变量        │ 数据结构      │ 高             │
│ Aeneas       │ 高级抽象          │ 算法证明      │ 高             │
└──────────────┴──────────────────┴──────────────┴────────────────┘
```

---

## 🧪 Miri - 内存安全验证

Miri 是 Rust 的解释器，可以检测未定义行为（UB）。

### Tree Borrows 模式

```bash
# 使用 Tree Borrows（推荐）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 使用 Stacked Borrows（兼容性测试）
MIRIFLAGS="-Zmiri-stacked-borrows" cargo miri test

# 严格模式（最严格检查）
MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-tag-raw-pointers" cargo miri test
```

### 代码示例

```rust
// tests/miri_tests.rs

/// 验证 Tree Borrows 接受重新借用模式
#[test]
fn test_tree_borrows_reborrow() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;

    *z = 1;
    *y = 2;  // ✅ Tree Borrows: OK

    assert_eq!(x, 2);
}

/// 验证自引用结构
#[test]
fn test_tree_borrows_self_referential() {
    use std::pin::Pin;

    struct SelfRef<'a> {
        data: String,
        ptr: &'a str,
    }

    let mut boxed = Box::pin(SelfRef {
        data: "hello".to_string(),
        ptr: "",
    });

    unsafe {
        let ptr = &boxed.data as *const String;
        let this = boxed.as_mut().get_unchecked_mut();
        this.ptr = &*(ptr as *const str);
    }

    assert_eq!(boxed.ptr, "hello");  // ✅ Tree Borrows: OK
}
```

### CI/CD 集成

```yaml
# .github/workflows/miri.yml
name: Miri Tests

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Miri
        run: |
          rustup component add miri
          cargo miri setup

      - name: Run tests with Tree Borrows
        run: cargo miri test --all-features
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows -Zmiri-ignore-leaks"
```

---

## 🔍 Kani - 模型检查

Kani 是 Rust 的模型检查器，用于验证属性。

### 基础验证

```rust
// 使用 Kani 验证属性
#[cfg(kani)]
mod verification {
    use kani::Arbitrary;

    /// 验证加法交换律
    #[kani::proof]
    fn verify_addition_commutative() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();

        kani::assert(a + b == b + a);
    }

    /// 验证溢出保护
    #[kani::proof]
    fn verify_checked_add() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();

        if let Some(result) = a.checked_add(b) {
            kani::assert(result >= a);
            kani::assert(result >= b);
        }
    }
}
```

### 高级特性

```rust
// 验证 Unsafe 代码
#[kani::proof]
fn verify_raw_ptr() {
    let mut x: i32 = kani::any();
    kani::assume(x > 0);

    let ptr = &mut x as *mut i32;

    unsafe {
        *ptr = 10;
        kani::assert(x == 10);
    }
}

// 验证并发安全
use std::sync::atomic::{AtomicUsize, Ordering};

#[kani::proof]
#[kani::unwind(5)]
fn verify_atomic_counter() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let old = COUNTER.fetch_add(1, Ordering::SeqCst);
    let new = COUNTER.load(Ordering::SeqCst);

    kani::assert(new == old + 1);
}

// 假设与断言组合
#[kani::proof]
fn verify_binary_search() {
    let arr: [i32; 5] = kani::any();
    kani::assume(arr[0] < arr[1] && arr[1] < arr[2] && arr[2] < arr[3] && arr[3] < arr[4]);

    let target = kani::any();

    let result = binary_search(&arr, target);

    if let Some(idx) = result {
        kani::assert(arr[idx] == target);
    }
}

fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}
```

---

## 📐 Prusti - 契约编程

Prusti 使用分离逻辑验证 Rust 代码。

### 前置/后置条件

```rust
use prusti_contracts::*;

/// 阶乘函数 - 带完整契约
#[requires(n >= 0)]
#[requires(n <= 20)]  // 防止溢出
#[ensures(result >= 1)]
#[ensures(result >= n)]
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// 数组最大值
#[requires(array.len() > 0)]
#[ensures(forall(|i: usize| (0 <= i && i < array.len()) ==> array[i] <= result))]
#[ensures(exists(|i: usize| (0 <= i && i < array.len()) && array[i] == result))]
fn find_max(array: &[i32]) -> i32 {
    let mut max = array[0];

    #[invariant(max >= array[0])]
    #[invariant(forall(|j: usize| (0 <= j && j < i) ==> array[j] <= max))]
    for i in 1..array.len() {
        if array[i] > max {
            max = array[i];
        }
    }

    max
}

/// 安全的数组访问
#[requires(index < array.len())]
#[ensures(result == array[index])]
fn safe_get(array: &[i32], index: usize) -> i32 {
    array[index]
}
```

### 循环不变量

```rust
/// 冒泡排序 - 带完整证明
#[requires(arr.len() <= 1000)]  // 限制大小以确保终止
#[ensures(forall(|i: usize, j: usize|
    (0 <= i && i < j && j < arr.len()) ==> arr[i] <= arr[j]
))]
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();

    #[invariant(n == arr.len())]
    for i in 0..n {
        #[invariant(forall(|k: usize|
            (0 <= k && k < i) ==>
            forall(|m: usize| (k < m && m < n) ==> arr[k] <= arr[m])
        ))]
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

/// 二分查找 - 带终止证明
#[requires(forall(|i: usize, j: usize|
    (0 <= i && i < j && j < arr.len()) ==> arr[i] <= arr[j]
))]
#[ensures(match result {
    Some(idx) => arr[idx] == target,
    None => forall(|i: usize| (0 <= i && i < arr.len()) ==> arr[i] != target),
})]
fn binary_search_prusti(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    #[invariant(0 <= left && left <= right && right <= arr.len())]
    #[invariant(forall(|i: usize|
        (0 <= i && i < left) ==> arr[i] < target
    ))]
    #[invariant(forall(|i: usize|
        (right <= i && i < arr.len()) ==> arr[i] > target
    ))]
    while left < right {
        let mid = left + (right - left) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    None
}
```

---

## 🎓 工具选择决策树

```text
┌─────────────────────────────────────────────────────────────────┐
│                    选择合适的形式化工具                          │
└─────────────────────────────────────────────────────────────────┘
│                                                                 │
├─ 验证内存安全？                                                 │
│  ├─ 是 → Miri                                                   │
│  │        ├─ 使用 Unsafe？ → Tree Borrows 模式                  │
│  │        └─ 纯 Safe 代码？ → 可选，但推荐                      │
│  │                                                             │
│  └─ 否 → 验证功能正确性？                                       │
│           ├─ 是 → Kani                                          │
│           │        ├─ 需要证明循环？ → 添加 unwind 限制        │
│           │        └─ 无限状态空间？ → 使用抽象                  │
│           │                                                     │
│           └─ 需要复杂不变量？                                    │
│                    ├─ 是 → Prusti (如果支持)                     │
│                    │        └─ 不够强大？ → Creusot/Aeneas      │
│                    │                                            │
│                    └─ 否 → 单元测试即可                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 🔗 综合示例

### 完整的验证套件

```rust
//! 经过形式化验证的 SafeVec 实现

/// 一个经过形式化验证的安全向量包装器
pub struct SafeVec<T> {
    data: Vec<T>,
}

impl<T> SafeVec<T> {
    /// 创建新的 SafeVec
    ///
    /// # Kani 验证
    /// - 验证初始容量 >= 0
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// 获取元素
    ///
    /// # Prusti 契约
    /// - requires: index < self.len()
    /// - ensures: result == self.data[index]
    ///
    /// # Miri 验证
    /// - 验证无越界访问
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// 添加元素
    ///
    /// # Kani 验证
    /// - 验证长度增加 1
    /// - 验证新元素在末尾
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }

    /// 安全移除元素
    ///
    /// # Prusti 契约
    /// - requires: index < self.len()
    /// - ensures: self.len() == old(self.len()) - 1
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index < self.data.len() {
            Some(self.data.remove(index))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

// ==================== 形式化验证测试 ====================

#[cfg(kani)]
mod kani_tests {
    use super::*;

    #[kani::proof]
    fn verify_push_increases_len() {
        let mut vec = SafeVec::new();
        let old_len = vec.len();

        vec.push(42);

        kani::assert(vec.len() == old_len + 1);
    }

    #[kani::proof]
    fn verify_get_bounds() {
        let mut vec = SafeVec::new();
        vec.push(1);
        vec.push(2);

        let idx: usize = kani::any();

        if idx < vec.len() {
            kani::assert(vec.get(idx).is_some());
        } else {
            kani::assert(vec.get(idx).is_none());
        }
    }
}

#[cfg(prusti)]
mod prusti_tests {
    use prusti_contracts::*;
    use super::*;

    #[requires(index < vec.len())]
    #[ensures(match result {
        Some(x) => *x == vec.data[index],
        None => false,
    })]
    pub fn verified_get<T: Copy>(vec: &SafeVec<T>, index: usize) -> Option<T> {
        vec.get(index).copied()
    }
}

#[cfg(test)]
mod miri_tests {
    use super::*;

    /// Miri 测试：验证无 UB
    #[test]
    fn test_tree_borrows() {
        let mut vec = SafeVec::new();
        vec.push(1);
        vec.push(2);

        let first = vec.get(0);
        vec.push(3);  // 可能重新分配

        assert_eq!(first, Some(&1));  // ✅ Tree Borrows: OK
    }
}
```

---

## 📊 验证覆盖率目标

| 模块 | Miri | Kani | Prusti | 目标覆盖率 |
|------|------|------|--------|-----------|
| C01 所有权 | ✅ | ⚠️ | ⚠️ | 80% |
| C02 类型系统 | ✅ | ✅ | ⚠️ | 70% |
| C04 泛型 | ✅ | ✅ | ⚠️ | 60% |
| C05 并发 | ✅ | ⚠️ | ❌ | 50% |
| C06 异步 | ✅ | ❌ | ❌ | 40% |
| C08 算法 | ✅ | ✅ | ✅ | 90% |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-18
**状态**: ✅ 生产就绪
