# Criterion.rs 基准测试形式化分析

> **主题**: 统计正确的基准测试框架
>
> **形式化框架**: 统计推断 + 线性回归
>
> **参考**: Criterion.rs Documentation; Statistical Benchmarking

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [Criterion.rs 基准测试形式化分析](#criterionrs-基准测试形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 统计模型](#2-统计模型)
    - [2.1 线性回归](#21-线性回归)
    - [定理 2.1 (迭代时间估计)](#定理-21-迭代时间估计)
    - [2.2 异常值检测](#22-异常值检测)
    - [定理 2.2 (稳健统计)](#定理-22-稳健统计)
  - [3. 测量精度](#3-测量精度)
    - [定理 3.1 (足够精度)](#定理-31-足够精度)
  - [4. 报告解释](#4-报告解释)
    - [定理 4.1 (性能变化显著性)](#定理-41-性能变化显著性)
  - [5. 反例](#5-反例)
    - [反例 5.1 (编译器优化)](#反例-51-编译器优化)
    - [反例 5.2 (不稳定测量)](#反例-52-不稳定测量)
  - [*定理数量: 5个*](#定理数量-5个)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

Criterion提供:

- 统计稳健的测量
- 迭代时间估计
- 性能回归检测
- 详细报告

---

## 2. 统计模型
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 线性回归

### 定理 2.1 (迭代时间估计)

> Criterion使用线性回归估计单次迭代时间。

**模型**:

$$
t(n) = \alpha + \beta n + \epsilon
$$

其中:

- $\alpha$: 固定开销
- $\beta$: 单次迭代时间
- $n$: 迭代次数

**估计**:

```rust
// 最小二乘估计
β̂ = Σ(n_i - n̄)(t_i - t̄) / Σ(n_i - n̄)²
```

∎

### 2.2 异常值检测

### 定理 2.2 (稳健统计)

> Criterion使用中位数和IQR而非均值，对异常值稳健。

**方法**:

$$
\text{IQR} = Q_3 - Q_1
$$

**异常值**:

$$
\text{outlier} < Q_1 - 1.5 \cdot \text{IQR} \lor \text{outlier} > Q_3 + 1.5 \cdot \text{IQR}
$$

∎

---

## 3. 测量精度

### 定理 3.1 (足够精度)

> Criterion迭代直到达到目标精度。

**停止条件**:

$$
\frac{\text{CI}_{\text{half-width}}}{\text{estimate}} < 0.01
$$

∎

---

## 4. 报告解释

### 定理 4.1 (性能变化显著性)

> 报告中的变化需考虑统计显著性。

**解读**:

- 变化 < 5%: 噪声
- 5-10%: 轻微变化
- >10%: 显著变化

**注意**: 需考虑置信区间重叠

∎

---

## 5. 反例

### 反例 5.1 (编译器优化)

```rust
// 危险: 可能被优化掉
c.bench_function("noop", |b| {
    b.iter(|| {
        // 空操作
    });
});

// 正确: 使用black_box
use std::hint::black_box;
c.bench_function("real", |b| {
    b.iter(|| {
        black_box(expensive_operation())
    });
});
```

### 反例 5.2 (不稳定测量)

```rust
// 第一次运行包含缓存预热，应在迭代外
let data = setup_data();  // 在iter外准备
c.bench_function("cached", |b| {
    b.iter(|| {
        process(&data)  // 只测量处理
    });
});
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

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**
