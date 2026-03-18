# 迭代器 (Iterators)

> **版本**: Rust 1.94.0
> **特性**: `array_windows`, `Peekable::next_if`
> **权威来源**: [Rust 官方文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 `array_windows` 进行滑动窗口迭代
- [ ] 使用 `Peekable::next_if` 条件消费元素
- [ ] 理解迭代器的性能特征
- [ ] 在实际问题中应用这些特性

## 📋 先决条件

- 基础 Rust 语法
- 理解切片和数组
- 了解闭包基础

## 🧠 核心概念

### 1. array_windows - 滑动窗口迭代

`array_windows` 是 Rust 1.94 引入的新方法，用于在数组/切片上以固定大小的窗口进行迭代。

#### 1.1 基础用法

```rust
fn main() {
    let data = [1, 2, 3, 4, 5];

    // 创建大小为 3 的滑动窗口
    for window in data.array_windows::<3>() {
        println!("{:?}", window); // [1, 2, 3], [2, 3, 4], [3, 4, 5]
    }
}
```

#### 1.2 与 `windows` 的对比

| 特性 | `array_windows<N>()` | `windows(n)` |
|------|---------------------|--------------|
| 窗口大小 | 编译期确定 | 运行期确定 |
| 返回类型 | `&[T; N]` (定长数组) | `&[T]` (切片) |
| 性能 | 更快（无需边界检查） | 稍慢 |
| 使用场景 | 已知固定大小 | 动态大小 |

#### 1.3 实际应用：滑动平均

```rust
fn moving_average(data: &[f64], window_size: usize) -> Vec<f64> {
    match window_size {
        2 => data.array_windows::<2>()
            .map(|&[a, b]| (a + b) / 2.0)
            .collect(),
        3 => data.array_windows::<3>()
            .map(|&[a, b, c]| (a + b + c) / 3.0)
            .collect(),
        _ => panic!("Unsupported window size"),
    }
}

fn main() {
    let prices = [10.0, 11.0, 12.0, 11.0, 10.5];
    let avg = moving_average(&prices, 3);
    println!("3-day moving average: {:?}", avg);
    // [11.0, 11.333..., 11.166...]
}
```

#### 1.4 实际应用：模式检测

```rust
fn detect_repeated_pattern(text: &str) -> usize {
    text.as_bytes()
        .array_windows::<4>()
        .filter(|&&[a, b, c, d]| a == d && b == c && a != b)
        .count()
}

fn main() {
    let text = "abbaaccaabbaddacccabba";
    let count = detect_repeated_pattern(text);
    println!("Pattern 'abba' count: {}", count);
}
```

### 2. Peekable::next_if - 条件消费

`Peekable::next_if` 允许你查看下一个元素，仅在满足条件时才消费它。

#### 2.1 基础用法

```rust
fn main() {
    let mut iter = [1, 2, 3, 4, 5].into_iter().peekable();

    // 仅当下一个元素小于 3 时才消费
    while let Some(n) = iter.next_if(|&x| x < 3) {
        println!("Consumed: {}", n);
    }

    // 查看但不消费
    println!("Next: {:?}", iter.peek()); // Some(3)
}
```

#### 2.2 实际应用：解析器

```rust
struct Parser<I: Iterator<Item = char>> {
    input: std::iter::Peekable<I>,
}

impl<I: Iterator<Item = char>> Parser<I> {
    fn new(input: I) -> Self {
        Self {
            input: input.peekable(),
        }
    }

    // 消费空白字符
    fn skip_whitespace(&mut self) {
        while self.input.next_if(|c| c.is_whitespace()).is_some() {}
    }

    // 消费数字
    fn parse_number(&mut self) -> Option<u32> {
        let mut num = 0u32;
        let mut has_digit = false;

        while let Some(digit) = self.input.next_if(|c| c.is_ascii_digit()) {
            has_digit = true;
            num = num * 10 + digit.to_digit(10).unwrap();
        }

        if has_digit { Some(num) } else { None }
    }
}

fn main() {
    let mut parser = Parser::new("  42  ".chars());
    parser.skip_whitespace();
    println!("Number: {:?}", parser.parse_number()); // Some(42)
}
```

#### 2.3 实际应用：分组处理

```rust
fn group_consecutive(data: &[i32]) -> Vec<Vec<i32>> {
    let mut result = Vec::new();
    let mut iter = data.iter().copied().peekable();

    while let Some(first) = iter.next() {
        let mut group = vec![first];

        // 继续添加连续的元素
        while let Some(&next) = iter.peek() {
            if next == group.last().unwrap() + 1 {
                group.push(iter.next().unwrap());
            } else {
                break;
            }
        }

        result.push(group);
    }

    result
}

fn main() {
    let data = [1, 2, 3, 5, 6, 8, 9, 10];
    let groups = group_consecutive(&data);
    println!("{:?}", groups);
    // [[1, 2, 3], [5, 6], [8, 9, 10]]
}
```

## 💻 综合示例

### 示例：数据分析管道

```rust
use std::collections::HashMap;

fn analyze_stock_prices(prices: &[f64]) -> HashMap<String, f64> {
    let mut stats = HashMap::new();

    if prices.len() >= 2 {
        // 计算每日变化率
        let changes: Vec<f64> = prices.array_windows::<2>()
            .map(|&[prev, curr]| (curr - prev) / prev * 100.0)
            .collect();

        // 计算3日移动平均
        let ma3: Vec<f64> = prices.array_windows::<3>()
            .map(|&[a, b, c]| (a + b + c) / 3.0)
            .collect();

        stats.insert("avg_change".to_string(),
            changes.iter().sum::<f64>() / changes.len() as f64);
        stats.insert("volatility".to_string(),
            changes.iter().map(|&x| x.abs()).sum::<f64>() / changes.len() as f64);
        stats.insert("ma3_latest".to_string(), *ma3.last().unwrap_or(&0.0));
    }

    stats
}

fn main() {
    let prices = [100.0, 102.0, 101.0, 103.0, 105.0];
    let stats = analyze_stock_prices(&prices);

    for (key, value) in &stats {
        println!("{}: {:.2}", key, value);
    }
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 解决方案 |
|------|------|----------|
| 窗口大小超过数据长度 | `array_windows` 要求 `N <= len` | 检查数据长度 |
| 编译错误：无法推断窗口大小 | 需要显式指定 `N` | 使用 turbofish: `array_windows::<3>()` |
| `next_if` 后 peek 为 None | 元素已被消费 | 理解消费语义 |

## 🎮 练习

### 练习 1：平滑数据

实现一个函数，使用 `array_windows` 对传感器数据进行平滑处理（窗口平均）。

<details>
<summary>提示</summary>

考虑不同大小的窗口，并处理边界情况。

</details>

### 练习 2：命令解析器

使用 `Peekable::next_if` 实现一个简单的命令行解析器，支持带引号的参数。

<details>
<summary>参考答案</summary>

```rust
fn parse_args(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut iter = input.chars().peekable();

    while iter.peek().is_some() {
        // 跳过空白
        while iter.next_if(|c| c.is_whitespace()).is_some() {}

        let mut arg = String::new();
        let in_quote = iter.next_if(|&c| c == '"').is_some();

        while let Some(c) = if in_quote {
            iter.next_if(|&c| c != '"')
        } else {
            iter.next_if(|c| !c.is_whitespace())
        } {
            arg.push(c);
        }

        if in_quote {
            iter.next_if(|&c| c == '"'); // 消费闭合引号
        }

        if !arg.is_empty() {
            args.push(arg);
        }
    }

    args
}
```

</details>

## 📖 延伸阅读

- [Rust 1.94 Release Notes](https://blog.rust-lang.org/2025/08/...)
- [Iterator trait 文档](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
- [array_windows API](https://doc.rust-lang.org/std/primitive.slice.html#method.array_windows)

## ✅ 自我检测

1. `array_windows` 和 `windows` 的主要区别是什么？
2. `next_if` 在什么场景下特别有用？
3. 如何在编译期确定窗口大小？

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
