# array_windows 语义分析 [Stable 1.94]

> **稳定版本**: Rust 1.94 (2026年3月5日)
> **标准库**: `core::slice` / `std::slice`
> **跟踪 Issue**: #75027

---

## 1. 概述

`array_windows` 是 Rust 1.94 引入的切片迭代方法，返回固定大小的数组窗口迭代器。
与现有的 `windows` 方法不同，`array_windows` 返回的是 `&[T; N]` 而非 `&[T]`，在编译时确定窗口大小，提供更好的类型安全和性能。

### 1.1 与 `windows` 的对比

```rust
// windows (动态大小) - 返回 &[T]
let slice = [1, 2, 3, 4, 5];
for window in slice.windows(2) {
    // window: &[i32]
    println!("{:?}", window); // 需要运行时边界检查
}

// array_windows (固定大小) - 返回 &[T; N]
for window in slice.array_windows() {
    // window: &[i32; 2] - 编译时已知大小
    let [a, b] = window; // 可以直接解构
    println!("{}, {}", a, b);
}
```

---

## 2. 语法定义

### 2.1 方法签名

```rust
impl<T> [T] {
    pub fn array_windows<const N: usize>(&self) -> ArrayWindows<'_, T, N>
    where
        Self: Sized,
    {
        // ...
    }
}
```

### 2.2 形式化定义

```
array_windows: &[T] -> ArrayWindows<'_, T, N>

其中:
- N: 编译时常量，窗口大小
- ArrayWindows<'_, T, N> 实现 Iterator<Item = &[T; N]>
```

---

## 3. 语义分析

### 3.1 类型安全

`array_windows` 的返回类型在编译时确定：

```rust
fn analyze_type_safety() {
    let data = [1, 2, 3, 4];

    // 类型推断：ArrayWindows<'_, i32, 2>
    let iter = data.array_windows();

    // Item 类型是 &[i32; 2]
    for [a, b] in iter {
        // a 和 b 都是 &i32
        println!("{} + {} = {}", a, b, a + b);
    }
}
```

### 3.2 生命周期语义

```rust
fn lifetime_semantics(data: &[i32]) -> impl Iterator<Item = &[i32; 2]> + '_ {
    // 返回的迭代器与输入切片共享生命周期
    data.array_windows()
}

// 等价于:
fn lifetime_semantics_explicit<'a>(data: &'a [i32]) -> ArrayWindows<'a, i32, 2> {
    data.array_windows()
}
```

### 3.3 所有权与借用

```rust
fn ownership_analysis() {
    let data = vec![1, 2, 3, 4, 5];

    // array_windows 对切片进行不可变借用
    let windows = data.array_windows::<2>();

    // 在迭代期间，data 被借用
    for [a, b] in windows {
        println!("{}, {}", a, b);
    }

    // 迭代结束后，可以再次使用 data
    drop(data);
}
```

---

## 4. 形式化语义

### 4.1 操作语义

**ArrayWindows 创建**:

```
〈e, σ〉⇓〈[v₁, v₂, ..., vₙ], σ'〉    n ≥ N
────────────────────────────────────────────
〈e.array_windows::&lt;N&gt;(), σ〉⇓
〈ArrayWindows { slice: [v₁, ..., vₙ], pos: 0 }, σ'〉
```

**Next 操作**:

```
pos ≤ len(slice) - N
────────────────────────────────────────────────────────
〈iter.next(), σ〉⇓〈Some(&[slice[pos], ..., slice[pos+N-1]]), σ〉

pos > len(slice) - N
─────────────────────────────────────
〈iter.next(), σ〉⇓〈None, σ〉
```

### 4.2 类型规则

**T-ArrayWindows**:

```
Γ ⊢ e : &[T]    N 是编译时常量    N > 0
────────────────────────────────────────
Γ ⊢ e.array_windows::<N>() : ArrayWindows<'_, T, N>
```

**T-ArrayWindows-Next**:

```
Γ ⊢ iter : ArrayWindows<'a, T, N>
────────────────────────────────────────
Γ ⊢ iter.next() : Option<&'a [T; N]>
```

---

## 5. 使用模式

### 5.1 滑动窗口计算

```rust
// 计算移动平均
fn moving_average(data: &[f64], window_size: usize) -> Vec<f64> {
    // 注意：这是示例，实际 array_windows 需要编译时常量
    data.windows(window_size)
        .map(|w| w.iter().sum::<f64>() / w.len() as f64)
        .collect()
}

// 使用 array_windows (编译时确定大小)
fn pairwise_differences(data: &[i32]) -> impl Iterator<Item = i32> + '_ {
    data.array_windows::<2>()
        .map(|[a, b]| b - a)
}
```

### 5.2 模式匹配

```rust
// ABBA 模式检测 (Advent of Code 2016)
fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows::<4>()
        .any(|[a, b, c, d]| a != b && a == d && b == c)
}

// 寻找峰值
fn find_peaks(data: &[i32]) -> Vec<usize> {
    data.array_windows::<3>()
        .enumerate()
        .filter(|(_, [a, b, c])]| b > a && b > c)
        .map(|(i, _)| i + 1) // 峰值索引是中间元素
        .collect()
}
```

### 5.3 与其他迭代器方法组合

```rust
fn analyze_trends(data: &[f64]) {
    let trends: Vec<_> = data
        .array_windows::<2>()
        .map(|[prev, curr]| {
            if curr > prev {
                "↗"
            } else if curr < prev {
                "↘"
            } else {
                "→"
            }
        })
        .collect();

    println!("Trends: {:?}", trends);
}
```

---

## 6. 性能特征

### 6.1 与 `windows` 的性能对比

| 特性 | `windows` | `array_windows` |
|------|-----------|-----------------|
| 返回类型 | `&[T]` | `&[T; N]` |
| 大小检查 | 运行时 | 编译时 |
| 索引优化 | 需要边界检查 | 可以消除边界检查 |
| 内存布局 | 动态 | 固定 |

### 6.2 零成本抽象

```rust
// 编译器可以内联和优化
pub fn sum_pairs(data: &[i32]) -> i32 {
    data.array_windows::<2>()
        .map(|[a, b]| a + b)
        .sum()
}

// 生成的机器码等价于手动展开:
// let mut sum = 0;
// for i in 0..data.len()-1 {
//     sum += data[i] + data[i+1];
// }
```

---

## 7. 安全保证

### 7.1 内存安全

```rust
fn memory_safety() {
    let data = [1, 2, 3];

    // 安全：返回的引用在切片生命周期内有效
    let windows = data.array_windows::<2>();

    // 不可能越界：窗口大小在编译时验证
    for [a, b] in windows {
        // a 和 b 都是有效的引用
        println!("{}, {}", a, b);
    }
}
```

### 7.2 类型安全

```rust
// 编译错误：N 必须是编译时常量
fn dynamic_window(data: &[i32], n: usize) {
    // for window in data.array_windows::<n>() { } // 错误！

    // 正确：使用编译时常量
    for window in data.array_windows::<3>() { }
}
```

---

## 8. 实际应用案例

### 8.1 信号处理

```rust
// 简单平滑滤波
fn smooth_signal(signal: &[f64]) -> Vec<f64> {
    signal.array_windows::<3>()
        .map(|[a, b, c]| (a + b + c) / 3.0)
        .collect()
}

// 边缘检测 (Sobel 算子的简化版)
fn detect_edges(image: &[f64], width: usize) -> Vec<f64> {
    image.array_windows::<2>()
        .map(|[a, b]| (b - a).abs())
        .collect()
}
```

### 8.2 文本分析

```rust
// N-gram 生成
fn ngrams(text: &str, n: usize) -> Vec<&str> {
    // 对于动态 n，使用 windows
    text.char_indices()
        .collect::<Vec<_>>()
        .windows(n)
        .map(|w| {
            let start = w[0].0;
            let end = w.last().map(|(i, c)| i + c.len_utf8()).unwrap_or(start);
            &text[start..end]
        })
        .collect()
}

// 固定大小的 bigram (使用 array_windows)
fn bigrams_fixed(text: &[u8]) -> impl Iterator<Item = &[u8; 2]> + '_ {
    text.array_windows::<2>()
}
```

### 8.3 时间序列分析

```rust
// 检测连续增长
fn consecutive_increases(prices: &[f64]) -> usize {
    prices.array_windows::<2>()
        .filter(|[prev, curr]| curr > prev)
        .count()
}

// 计算波动率
fn volatility(prices: &[f64]) -> f64 {
    let diffs: Vec<_> = prices.array_windows::<2>()
        .map(|[a, b]| b - a)
        .collect();

    let mean = diffs.iter().sum::<f64>() / diffs.len() as f64;
    let variance = diffs.iter()
        .map(|d| (d - mean).powi(2))
        .sum::<f64>() / diffs.len() as f64;

    variance.sqrt()
}
```

---

## 9. 与所有权系统的关系

### 9.1 借用检查器交互

```rust
fn borrow_checker_interaction() {
    let mut data = vec![1, 2, 3, 4, 5];

    // array_windows 创建不可变借用
    let windows = data.array_windows::<2>();

    // 在借用期间不能修改
    // data.push(6); // 错误！数据已被借用

    for [a, b] in windows {
        println!("{}, {}", a, b);
    }

    // 借用结束后可以修改
    data.push(6); // OK
}
```

### 9.2 生命周期推断

```rust
fn lifetime_inference(data: &[i32]) -> Option<i32> {
    // 编译器自动推断生命周期
    data.array_windows::<2>()
        .map(|[a, b]| a + b)
        .next()
}

// 显式生命周期标注
fn explicit_lifetimes<'a>(data: &'a [i32]) -> impl Iterator<Item = i32> + 'a {
    data.array_windows::<2>()
        .map(|[a, b]| a + b)
}
```

---

## 10. 总结

`array_windows` 是 Rust 1.94 引入的重要特性，它：

1. **提供编译时类型安全**: 窗口大小在编译时确定
2. **消除运行时边界检查**: 固定大小允许更好的优化
3. **支持模式匹配**: 可以直接解构数组窗口
4. **与所有权系统良好集成**: 遵循 Rust 的借用规则

这个特性体现了 Rust 的核心设计理念：将运行时检查移至编译时，在保证安全的同时提供零成本抽象。

---

**参考资源**:

- [Rust 1.94 Release Notes](https://blog.rust-lang.org/2026/03/06/Rust-1.94.0.html)
- [Slice::array_windows API 文档](https://doc.rust-lang.org/std/primitive.slice.html#method.array_windows)
- [Tracking Issue #75027](https://github.com/rust-lang/rust/issues/75027)
