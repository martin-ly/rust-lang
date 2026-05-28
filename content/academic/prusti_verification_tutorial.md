# Prusti 形式化验证教程

> **定位**: Rust 代码的形式化验证入门
> **版本**: Prusti 最新稳定版 (基于 Viper)
> **适用场景**: 安全关键系统、算法正确性证明

---

## 📋 目录

- [Prusti 形式化验证教程](#prusti-形式化验证教程)
  - [📋 目录](#-目录)
  - [🎯 什么是 Prusti](#-什么是-prusti)
  - [⚡ 快速开始](#-快速开始)
    - [前置条件与后置条件](#前置条件与后置条件)
    - [循环不变量](#循环不变量)
  - [🔐 所有权与借用验证](#-所有权与借用验证)
  - [📐 高级规范](#-高级规范)
  - [🔄 与 Miri 对比](#-与-miri-对比)
  - [⚠️ 限制与注意事项](#️-限制与注意事项)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 什么是 Prusti

Prusti 是 Rust 的形式化验证工具，基于 [Viper](https://www.pm.inf.ethz.ch/research/viper.html) 验证架构：

```
┌─────────────────────────────────────────┐
│           Rust 源代码                    │
│    fn abs(x: i32) -> i32 { ... }       │
└────────────────┬────────────────────────┘
                 ↓
┌─────────────────────────────────────────┐
│        Prusti 规范注解                   │
│    #[requires(x != i32::MIN)]           │
│    #[ensures(result >= 0)]              │
└────────────────┬────────────────────────┘
                 ↓
┌─────────────────────────────────────────┐
│      Prusti → VIR → Viper 中间表示      │
└────────────────┬────────────────────────┘
                 ↓
┌─────────────────────────────────────────┐
│      Z3 SMT 求解器验证                   │
│         ✅ 证明通过 / ❌ 反例发现          │
└─────────────────────────────────────────┘
```

**验证维度**:

- **功能正确性**: 输入 → 输出的数学保证
- **内存安全**: 所有权、借用、生命周期
- **Panic 自由**: 证明代码不会 panic

---

## ⚡ 快速开始

### 前置条件与后置条件

```rust
use prusti_contracts::*;

/// 计算绝对值
///
/// # 规范
/// - 前提: x 不能是 i32::MIN（防止溢出）
/// - 后置: 结果总是非负的
#[requires(x != i32::MIN)]
#[ensures(result >= 0)]
#[ensures(result == x || result == -x)]
pub fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}
```

### 循环不变量

```rust
use prusti_contracts::*;

/// 数组求和
#[requires(array.len() <= 1000)] // Prusti 需要有限边界
#[ensures(result == array.iter().sum::<i32>())]
pub fn array_sum(array: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < array.len() {
        body_invariant!(i <= array.len());
        body_invariant!(sum == array[..i].iter().sum::<i32>());

        sum += array[i];
        i += 1;
    }

    sum
}
```

---

## 🔐 所有权与借用验证

Prusti 自动验证 Rust 的所有权规则：

```rust
use prusti_contracts::*;

/// 交换两个值
#[ensures(*a == old(*b))]
#[ensures(*b == old(*a))]
pub fn swap<T>(a: &mut T, b: &mut T) {
    // Prusti 自动验证 a 和 b 不重叠
    std::mem::swap(a, b);
}
```

**纯函数 (Pure Functions)**:

```rust
/// 纯函数: 不修改状态，无副作用
#[pure]
#[requires(index < slice.len())]
pub fn get(slice: &[i32], index: usize) -> i32 {
    slice[index]
}
```

---

## 📐 高级规范

```rust
use prusti_contracts::*;

/// 二分查找
#[requires(array.len() <= 1000)]
#[requires(
    forall(|i: usize, j: usize|
        (0 <= i && i < j && j < array.len())
        ==> array[i] <= array[j]
    )
)]
#[ensures(
    result == None
    ==> forall(|i: usize|
        (0 <= i && i < array.len())
        ==> array[i] != target
    )
)]
#[ensures(
    result == Some(idx)
    ==> (0 <= idx && idx < array.len() && array[idx] == target)
)]
pub fn binary_search(array: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = array.len();

    while left < right {
        body_invariant!(left <= right);
        body_invariant!(right <= array.len());
        body_invariant!(
            forall(|i: usize|
                (0 <= i && i < left) ==> array[i] < target
            )
        );
        body_invariant!(
            forall(|i: usize|
                (right <= i && i < array.len()) ==> array[i] > target
            )
        );

        let mid = left + (right - left) / 2;

        if array[mid] == target {
            return Some(mid);
        } else if array[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    None
}
```

---

## 🔄 与 Miri 对比

| 维度 | Prusti | Miri |
|------|--------|------|
| **验证类型** | 形式化证明 | 动态执行检查 |
| **覆盖** | 所有输入路径 | 单条执行路径 |
| **性能** | 较慢（SMT 求解） | 极慢（解释执行） |
| **用途** | 算法正确性证明 | UB 检测、内存模型验证 |
| **自动化** | 需写规范 | 零注解 |
| **适用** | 关键函数 | 全程序检查 |

**最佳实践**: Miri 用于发现 UB → Prusti 用于证明关键算法正确

---

## ⚠️ 限制与注意事项

1. **不支持**: `unsafe` 代码、部分标准库、并发代码
2. **数组长度**: 通常需要有限上界
3. **规范成本**: 复杂函数需要大量规范注解
4. **编译时间**: 验证可能显著增加编译时间

---

## 🔗 参考资源

- [Prusti 用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [Viper 项目](https://www.pm.inf.ethz.ch/research/viper.html)
- [项目 Miri 指南](../../docs/MIRI_GUIDE.md)
- [项目 academic/ 目录](../academic/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
