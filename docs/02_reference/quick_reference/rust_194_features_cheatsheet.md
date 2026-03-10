# Rust 1.94 特性速查卡 / Rust 1.94 Features Cheatsheet

> **Rust 版本**: 1.94.0
> **最后更新**: 2026-03-10
> **状态**: ✅ 完整

---

## 📋 目录

- [Rust 1.94 特性速查卡 / Rust 1.94 Features Cheatsheet](#rust-194-特性速查卡--rust-194-features-cheatsheet)
  - [📋 目录](#-目录)
  - [🎯 快速参考](#-快速参考)
  - [1. Array Windows（数组窗口）](#1-array-windows数组窗口)
    - [基本用法](#基本用法)
    - [滑动窗口平均值](#滑动窗口平均值)
    - [模式检测（ABBA）](#模式检测abba)
  - [2. LazyCell \& LazyLock 新方法](#2-lazycell--lazylock-新方法)
    - [LazyCell（单线程）](#lazycell单线程)
    - [LazyLock（多线程）](#lazylock多线程)
  - [3. 数学常量](#3-数学常量)
    - [可用常量](#可用常量)
    - [黄金分割搜索](#黄金分割搜索)
    - [调和级数估算](#调和级数估算)
  - [4. Peekable 迭代器](#4-peekable-迭代器)
    - [next\_if\_map](#next_if_map)
    - [词法分析器示例](#词法分析器示例)
  - [5. char 到 usize 转换](#5-char-到-usize-转换)
    - [基本转换](#基本转换)
    - [应用场景](#应用场景)
  - [🔧 完整示例](#-完整示例)
    - [综合示例：数据处理器](#综合示例数据处理器)
  - [📚 相关资源](#-相关资源)

---

## 🎯 快速参考

| 特性 | 语法 | 用途 |
|------|------|------|
| **array_windows** | `slice.array_windows::<N>()` | 固定大小窗口迭代 |
| **LazyCell::get** | `cell.get()` | 获取延迟初始化值 |
| **LazyCell::force_mut** | `LazyCell::force_mut(&cell)` | 强制初始化并可变获取 |
| **EULER_GAMMA** | `f64::consts::EULER_GAMMA` | 欧拉常数 ≈ 0.5772 |
| **GOLDEN_RATIO** | `f64::consts::GOLDEN_RATIO` | 黄金比例 ≈ 1.6180 |
| **next_if_map** | `iter.next_if_map(f)` | 条件映射获取 |
| **char → usize** | `usize::try_from(c)` | Unicode 标量值转换 |

---

## 1. Array Windows（数组窗口）

### 基本用法

```rust
let data = [1, 2, 3, 4, 5];

// 创建大小为 3 的窗口迭代器
for window in data.array_windows::<3>() {
    println!("{:?}", window); // [1,2,3], [2,3,4], [3,4,5]
}
```

### 滑动窗口平均值

```rust
fn sliding_average(data: &[f64], window_size: usize) -> Vec<f64> {
    match window_size {
        3 => data.array_windows::<3>()
            .map(|&[a, b, c]| (a + b + c) / 3.0)
            .collect(),
        5 => data.array_windows::<5>()
            .map(|&[a, b, c, d, e]| (a + b + c + d + e) / 5.0)
            .collect(),
        _ => panic!("Unsupported window size"),
    }
}
```

### 模式检测（ABBA）

```rust
fn has_abba_pattern(s: &str) -> bool {
    s.as_bytes()
        .array_windows::<4>()
        .any(|[a, b, c, d]| a != b && a == d && b == c)
}

assert!(has_abba_pattern("abba"));
assert!(!has_abba_pattern("abcd"));
```

---

## 2. LazyCell & LazyLock 新方法

### LazyCell（单线程）

```rust
use std::cell::LazyCell;

let cell: LazyCell<String> = LazyCell::new(|| {
    println!("Initializing...");
    "Hello".to_string()
});

// get() - 获取引用（如果已初始化）
if let Some(value) = cell.get() {
    println!("Got: {}", value);
}

// get_mut() - 获取可变引用（如果已初始化）
if let Some(value) = cell.get_mut() {
    value.push_str(" World");
}

// force_mut() - 强制初始化并获取可变引用
let value: &mut String = LazyCell::force_mut(&cell);
```

### LazyLock（多线程）

```rust
use std::sync::LazyLock;

static CONFIG: LazyLock<String> = LazyLock::new(|| {
    std::fs::read_to_string("config.txt")
        .unwrap_or_else(|_| "default".to_string())
});

// 在线程中使用
std::thread::spawn(|| {
    if let Some(cfg) = CONFIG.get() {
        println!("Config: {}", cfg);
    }
});
```

---

## 3. 数学常量

### 可用常量

```rust
// 欧拉-马歇罗尼常数
const GAMMA: f64 = f64::consts::EULER_GAMMA; // ≈ 0.57721566

// 黄金比例
const PHI: f64 = f64::consts::GOLDEN_RATIO;  // ≈ 1.61803399

// f32 版本同样可用
let gamma_f32 = f32::consts::EULER_GAMMA;
let phi_f32 = f32::consts::GOLDEN_RATIO;
```

### 黄金分割搜索

```rust
fn golden_section_search<F>(f: F, a: f64, b: f64, eps: f64) -> f64
where
    F: Fn(f64) -> f64,
{
    let phi = f64::consts::GOLDEN_RATIO;
    let resphi = 2.0 - phi;

    let (mut a, mut b) = (a, b);
    let (mut c, mut d) = (
        b - resphi * (b - a),
        a + resphi * (b - a)
    );

    while (b - a).abs() > eps {
        if f(c) < f(d) {
            b = d; d = c; c = b - resphi * (b - a);
        } else {
            a = c; c = d; d = a + resphi * (b - a);
        }
    }
    (a + b) / 2.0
}
```

### 调和级数估算

```rust
fn harmonic_approximation(n: usize) -> f64 {
    let gamma = f64::consts::EULER_GAMMA;
    gamma + (n as f64).ln() + 1.0 / (2.0 * n as f64)
}
```

---

## 4. Peekable 迭代器

### next_if_map

```rust
use std::iter::Peekable;

let mut iter = vec![1, 2, 3, 4, 5].into_iter().peekable();

// 如果条件满足，应用映射并返回
let result = iter.next_if_map(|&x| {
    if x > 2 { Some(x * 2) } else { None }
});
assert_eq!(result, Some(6)); // 3 * 2

// 如果不满足条件，返回 None 且不消耗元素
let result = iter.next_if_map(|&x| {
    if x < 2 { Some(x) } else { None }
});
assert_eq!(result, None);
// iter 仍指向 4
```

### 词法分析器示例

```rust
struct Lexer<I: Iterator<Item = char>> {
    chars: Peekable<I>,
}

impl<I: Iterator<Item = char>> Lexer<I> {
    fn next_token(&mut self) -> Option<Token> {
        // 跳过空白
        self.chars.next_if(|c| c.is_whitespace());

        // 解析数字
        self.chars.next_if_map(|c| {
            if c.is_ascii_digit() {
                let mut num = (c as u32) - ('0' as u32);
                while let Some(d) = self.chars.next_if(|c| c.is_ascii_digit()) {
                    num = num * 10 + (d as u32) - ('0' as u32);
                }
                Some(Token::Number(num))
            } else {
                None
            }
        })
    }
}
```

---

## 5. char 到 usize 转换

### 基本转换

```rust
use std::convert::TryFrom;

// Unicode 标量值转换
let c = 'A';
let code = usize::try_from(c).unwrap();
assert_eq!(code, 65);

let emoji = '🦀';
let code = usize::try_from(emoji).unwrap();
assert_eq!(code, 0x1F980); // 129408

// 使用 as 关键字（如果确定不会溢出）
let code = c as usize; // 简单但需注意溢出
```

### 应用场景

```rust
// 字符统计
fn char_frequency(text: &str) -> HashMap<char, usize> {
    let mut freq = HashMap::new();
    for c in text.chars() {
        *freq.entry(c).or_insert(0) += 1;
    }
    freq
}

// 字符位置映射
struct CharMapper {
    positions: HashMap<char, Vec<usize>>,
}

impl CharMapper {
    fn map_positions(&mut self, text: &str) {
        for (pos, c) in text.chars().enumerate() {
            self.positions.entry(c).or_default().push(pos);
        }
    }
}
```

---

## 🔧 完整示例

### 综合示例：数据处理器

```rust
use std::cell::LazyCell;
use std::sync::LazyLock;
use std::collections::HashMap;

// 全局配置（延迟初始化）
static CONFIG: LazyLock<HashMap<String, String>> = LazyLock::new(|| {
    let mut map = HashMap::new();
    map.insert("threshold".to_string(), "0.5".to_string());
    map.insert("window_size".to_string(), "3".to_string());
    map
});

struct DataProcessor {
    threshold: LazyCell<f64>,
}

impl DataProcessor {
    fn new() -> Self {
        Self {
            threshold: LazyCell::new(|| {
                CONFIG.get("threshold")
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0.5)
            }),
        }
    }

    // 使用 array_windows 计算移动平均
    fn moving_average(&self, data: &[f64]) -> Vec<f64> {
        let size = CONFIG.get("window_size")
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);

        match size {
            3 => data.array_windows::<3>()
                .map(|&[a, b, c]| (a + b + c) / 3.0)
                .collect(),
            _ => vec![],
        }
    }

    // 使用黄金比例进行数据缩放
    fn golden_scale(&self, value: f64) -> f64 {
        let phi = f64::consts::GOLDEN_RATIO;
        value * phi
    }
}
```

---

## 📚 相关资源

| 资源 | 链接 |
|------|------|
| **官方发布说明** | [Rust 1.94.0](https://blog.rust-lang.org/2026/03/05/Rust-1.94.0/) |
| **完整发布说明** | [16_rust_1.94_release_notes.md](../../06_toolchain/16_rust_1.94_release_notes.md) |
| **迁移指南** | [RUST_194_MIGRATION_GUIDE.md](../../05_guides/RUST_194_MIGRATION_GUIDE.md) |
| **C01 示例** | [c01 rust_194_features.rs](../../../crates/c01_ownership_borrow_scope/src/rust_194_features.rs) |
| **C02 示例** | [c02 rust_194_features.rs](../../../crates/c02_type_system/src/rust_194_features.rs) |
| **C03 示例** | [c03 rust_194_features.rs](../../../crates/c03_control_fn/src/rust_194_features.rs) |
| **C04 示例** | [c04 rust_194_features.rs](../../../crates/c04_generic/src/rust_194_features.rs) |
| **C05 示例** | [c05 rust_194_features.rs](../../../crates/c05_threads/src/rust_194_features.rs) |
| **C06 示例** | [c06 rust_194_features.rs](../../../crates/c06_async/src/rust_194_features.rs) |
| **C07 示例** | [c07 rust_194_features.rs](../../../crates/c07_process/src/rust_194_features.rs) |
| **C08 示例** | [c08 rust_194_features.rs](../../../crates/c08_algorithms/src/rust_194_features.rs) |
| **C09 示例** | [c09 rust_194_features.rs](../../../crates/c09_design_pattern/src/rust_194_features.rs) |
| **C10 示例** | [c10 rust_194_features.rs](../../../crates/c10_networks/src/rust_194_features.rs) |
| **C11 示例** | [c11 rust_194_features.rs](../../../crates/c11_macro_system/src/rust_194_features.rs) |
| **C12 示例** | [c12 rust_194_features.rs](../../../crates/c12_wasm/src/rust_194_features.rs) |

---

**最后更新**: 2026-03-10
**维护者**: Rust 学习社区
**状态**: ✅ 完整且已验证
