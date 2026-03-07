# Newtype Pattern in Rust

> **设计模式**: Rust 特有
> **难度**: 🟢 简单
> **应用场景**: 类型安全、单位验证、外部 trait 实现

---

## 概念

Newtype 模式使用单字段元组结构体包装现有类型，提供编译时类型区分，零运行时开销。

---

## 基础示例

```rust
// 基础类型容易混淆
fn calculate_distance(x1: f64, y1: f64, x2: f64, y2: f64) -> f64 {
    ((x2 - x1).powi(2) + (y2 - y1).powi(2)).sqrt()
}

// 使用 Newtype 增加类型安全
pub struct Meters(f64);
pub struct Kilometers(f64);

impl Meters {
    pub fn new(value: f64) -> Self {
        Self(value)
    }

    pub fn to_kilometers(&self) -> Kilometers {
        Kilometers(self.0 / 1000.0)
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

impl Kilometers {
    pub fn new(value: f64) -> Self {
        Self(value)
    }

    pub fn to_meters(&self) -> Meters {
        Meters(self.0 * 1000.0)
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

// 使用 - 编译器防止单位错误
fn travel_distance(meters: Meters) {
    println!("Traveling {} meters", meters.value());
}

fn main() {
    let distance = Meters::new(1500.0);
    travel_distance(distance);

    // travel_distance(Kilometers::new(1.5)); // 编译错误！
}
```

---

## 为外部类型实现 Trait

```rust
use std::fmt;

// 不能直接为外部类型实现外部 trait
// impl fmt::Display for Vec<u8> {} // 错误！

// 使用 Newtype 解决
pub struct HexBytes(pub Vec<u8>);

impl fmt::Display for HexBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in &self.0 {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

impl fmt::LowerHex for HexBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

// 使用
let bytes = HexBytes(vec![0xDE, 0xAD, 0xBE, 0xEF]);
println!("{}", bytes); // deadbeef
```

---

## 形式化定义

```
Newtype<T>(T)

性质:
  1. 结构同构: Newtype<T> ≅ T (运行时)
  2. 类型不同: Newtype<T> ≠ T (编译期)
  3. 零成本: sizeof(Newtype<T>) = sizeof(T)
```
