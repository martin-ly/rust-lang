/*
PartialOrd trait 是 Rust 中用于部分序比较的重要特征。
它定义了 `partial_cmp` 方法，允许类型进行部分序比较。

## 定义

PartialOrd trait 继承自 PartialEq：

```rust
pub trait PartialOrd<Rhs = Self>: PartialEq<Rhs> {
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;

    fn lt(&self, other: &Rhs) -> bool { ... }
    fn le(&self, other: &Rhs) -> bool { ... }
    fn gt(&self, other: &Rhs) -> bool { ... }
    fn ge(&self, other: &Rhs) -> bool { ... }
}
```

## 重要特性

1. **部分序关系**: 允许类型进行部分序比较
2. **继承关系**: 继承自 PartialEq
3. **自动派生**: 可以通过 `#[derive(PartialOrd)]` 自动实现
4. **浮点数支持**: 支持浮点数等不可完全比较的类型

## 部分序关系性质

### 1. 自反性 (Reflexivity)
对于所有值 x，x <= x 为 true

### 2. 反对称性 (Antisymmetry)
如果 x <= y 且 y <= x，那么 x == y

### 3. 传递性 (Transitivity)
如果 x <= y 且 y <= z，那么 x <= z

### 4. 部分性 (Partiality)
某些值可能不可比较（如浮点数的 NaN）

## 实现示例

### 1. 基本结构体实现 PartialOrd

```rust
#[derive(PartialEq, PartialOrd)]
struct Point {
    x: f64,
    y: f64,
}

// 手动实现
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 处理 NaN 情况
        if self.x.is_nan() || self.y.is_nan() ||
           other.x.is_nan() || other.y.is_nan() {
            return None;
        }

        // 先比较 x，再比较 y
        self.x.partial_cmp(&other.x)
            .and_then(|ord| if ord == Ordering::Equal {
                self.y.partial_cmp(&other.y)
            } else {
                Some(ord)
            })
    }
}
```

### 2. 泛型类型实现 PartialOrd

```rust
#[derive(PartialEq, PartialOrd)]
struct Container<T: PartialOrd> {
    value: T,
    count: usize,
}

impl<T: PartialOrd> PartialEq for Container<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.count == other.count
    }
}

impl<T: PartialOrd> PartialOrd for Container<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 先比较 value，再比较 count
        self.value.partial_cmp(&other.value)
            .and_then(|ord| if ord == Ordering::Equal {
                Some(self.count.cmp(&other.count))
            } else {
                Some(ord)
            })
    }
}
```

### 3. 枚举实现 PartialOrd

```rust
#[derive(PartialEq, PartialOrd)]
enum Status {
    Idle,      // 0
    Active,    // 1
    Error,     // 2
}

// 手动实现
impl PartialEq for Status {
    fn eq(&self, other: &Self) -> bool {
        matches!((self, other),
            (Status::Idle, Status::Idle) |
            (Status::Active, Status::Active) |
            (Status::Error, Status::Error))
    }
}

impl PartialOrd for Status {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_val = match self {
            Status::Idle => 0,
            Status::Active => 1,
            Status::Error => 2,
        };
        let other_val = match other {
            Status::Idle => 0,
            Status::Active => 1,
            Status::Error => 2,
        };
        Some(self_val.cmp(&other_val))
    }
}
```

## 使用场景

### 1. 浮点数比较

```rust
fn main() {
    let x = 3.14;
    let y = 2.71;
    let nan = f64::NAN;

    println!("x < y: {}", x < y);           // true
    println!("x > y: {}", x > y);           // false
    println!("x < nan: {}", x < nan);       // false
    println!("nan < x: {}", nan < x);       // false
    println!("nan == nan: {}", nan == nan); // false
}
```

### 2. 部分比较

```rust
fn main() {
    let p1 = Point { x: 1.0, y: 2.0 };
    let p2 = Point { x: 3.0, y: 4.0 };
    let p3 = Point { x: f64::NAN, y: 5.0 };

    if let Some(ord) = p1.partial_cmp(&p2) {
        match ord {
            Ordering::Less => println!("p1 < p2"),
            Ordering::Equal => println!("p1 == p2"),
            Ordering::Greater => println!("p1 > p2"),
        }
    }

    // p3 包含 NaN，无法比较
    if p1.partial_cmp(&p3).is_none() {
        println!("Cannot compare with NaN");
    }
}
```

### 3. 泛型函数

```rust
fn find_min<T: PartialOrd>(items: &[T]) -> Option<&T> {
    items.iter().min_by(|a, b| {
        a.partial_cmp(b).unwrap_or(Ordering::Equal)
    })
}

fn main() {
    let numbers = vec![3.14, 2.71, 1.41, f64::NAN, 2.23];

    if let Some(min) = find_min(&numbers) {
        println!("Minimum: {}", min);
    }
}
```

## 与 Ord 的区别

### 1. 约束强度

- **PartialOrd**: 只要求比较关系是部分序
- **Ord**: 要求比较关系是全序

### 2. 浮点数

- **PartialOrd**: 浮点数可以实现 PartialOrd
- **Ord**: 浮点数不能实现 Ord（因为 NaN 不可比较）

### 3. 用途

- **PartialOrd**: 用于需要处理 NaN 等特殊值的场景
- **Ord**: 用于需要全序关系的场景（如排序、集合）

## 性能考虑

1. **比较效率**: PartialOrd 实现应该高效
2. **NaN 检查**: 快速检测不可比较的值
3. **分支预测**: 优化比较逻辑以改善分支预测
4. **缓存友好**: 考虑数据局部性

## 最佳实践

1. **一致性**: 确保 PartialOrd 实现与 PartialEq 一致
2. **性能**: 实现高效的比较逻辑
3. **NaN 处理**: 正确处理不可比较的值
4. **测试**: 为部分序关系性质编写测试

## 高级用法

### 1. 自定义比较逻辑

```rust
impl PartialOrd for CustomType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 自定义比较逻辑
        if self.priority != other.priority {
            Some(other.priority.cmp(&self.priority))
        } else {
            Some(self.name.cmp(&other.name))
        }
    }
}
```

### 2. 多字段比较

```rust
impl PartialOrd for Person {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 先按年龄排序，再按姓名排序
        self.age.partial_cmp(&other.age)
            .and_then(|ord| if ord == Ordering::Equal {
                Some(self.name.cmp(&other.name))
            } else {
                Some(ord)
            })
    }
}
```

### 3. 条件比较

```rust
impl PartialOrd for ConditionalType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 只有在满足条件时才进行比较
        if self.is_comparable() && other.is_comparable() {
            Some(self.value.cmp(&other.value))
        } else {
            None
        }
    }
}
```

## 总结

PartialOrd trait 为 Rust 提供了部分序比较支持。
通过正确实现 PartialOrd，可以创建灵活的比较功能，
同时需要注意部分序关系的性质和 NaN 等特殊值的处理。
*/

use std::cmp::Ordering;

// 示例结构体
#[derive(Debug)]
pub struct PartialOrdExample {
    pub name: String,
    pub value: f64,
    pub priority: u8,
}

impl PartialEq for PartialOrdExample {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.value == other.value && self.priority == other.priority
    }
}

impl PartialOrd for PartialOrdExample {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 先按优先级排序，再按值排序，最后按名称排序
        let priority_ord = self.priority.partial_cmp(&other.priority)?;
        if priority_ord != Ordering::Equal {
            return Some(priority_ord);
        }
        let value_ord = self.value.partial_cmp(&other.value)?;
        if value_ord != Ordering::Equal {
            return Some(value_ord);
        }
        Some(self.name.cmp(&other.name))
    }
}

// 泛型容器
#[derive(Debug)]
pub struct PartialOrdContainer<T: PartialOrd> {
    pub value: T,
    pub metadata: String,
}

impl<T: PartialOrd> PartialEq for PartialOrdContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.metadata == other.metadata
    }
}

impl<T: PartialOrd> PartialOrd for PartialOrdContainer<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 先比较值，再比较元数据
        self.value.partial_cmp(&other.value).map(|ord| {
            if ord == Ordering::Equal {
                self.metadata.cmp(&other.metadata)
            } else {
                ord
            }
        })
    }
}

// 状态枚举
#[derive(Debug)]
pub enum PartialOrdStatus {
    Idle,     // 0
    Active,   // 1
    Working,  // 2
    Complete, // 3
    Error,    // 4
}

impl PartialEq for PartialOrdStatus {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (PartialOrdStatus::Idle, PartialOrdStatus::Idle)
                | (PartialOrdStatus::Active, PartialOrdStatus::Active)
                | (PartialOrdStatus::Working, PartialOrdStatus::Working)
                | (PartialOrdStatus::Complete, PartialOrdStatus::Complete)
                | (PartialOrdStatus::Error, PartialOrdStatus::Error)
        )
    }
}

impl PartialOrd for PartialOrdStatus {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_val = match self {
            PartialOrdStatus::Idle => 0,
            PartialOrdStatus::Active => 1,
            PartialOrdStatus::Working => 2,
            PartialOrdStatus::Complete => 3,
            PartialOrdStatus::Error => 4,
        };
        let other_val = match other {
            PartialOrdStatus::Idle => 0,
            PartialOrdStatus::Active => 1,
            PartialOrdStatus::Working => 2,
            PartialOrdStatus::Complete => 3,
            PartialOrdStatus::Error => 4,
        };
        Some(self_val.cmp(&other_val))
    }
}

// 浮点几何点
#[derive(Debug)]
pub struct PartialOrdPoint {
    pub x: f64,
    pub y: f64,
}

impl PartialEq for PartialOrdPoint {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl PartialOrd for PartialOrdPoint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 处理 NaN 情况
        if self.x.is_nan() || self.y.is_nan() || other.x.is_nan() || other.y.is_nan() {
            return None;
        }

        // 先比较 x，再比较 y
        self.x.partial_cmp(&other.x).and_then(|ord| {
            if ord == Ordering::Equal {
                self.y.partial_cmp(&other.y)
            } else {
                Some(ord)
            }
        })
    }
}

// 演示函数
pub fn demonstrate_partial_ord() {
    // 基本比较
    let p1 = PartialOrdPoint { x: 1.0, y: 2.0 };
    let p2 = PartialOrdPoint { x: 1.0, y: 3.0 };
    let p3 = PartialOrdPoint { x: 2.0, y: 1.0 };

    println!("p1 < p2: {}", p1 < p2); // true
    println!("p1 < p3: {}", p1 < p3); // true
    println!("p2 < p3: {}", p2 < p3); // true

    // 浮点数 NaN 处理
    let nan_point = PartialOrdPoint {
        x: f64::NAN,
        y: 2.0,
    };
    let normal_point = PartialOrdPoint { x: 1.0, y: 2.0 };

    println!("normal_point < nan_point: {}", normal_point < nan_point); // false
    println!("nan_point < normal_point: {}", nan_point < normal_point); // false

    // false NaN比较
    let nan_point2 = PartialOrdPoint {
        x: f64::NAN,
        y: 3.0,
    };
    println!("nan_point == nan_point2: {}", (nan_point == nan_point2));

    // 结构体比较
    let e1 = PartialOrdExample {
        name: String::from("Alice"),
        value: 100.0,
        priority: 1,
    };

    let e2 = PartialOrdExample {
        name: String::from("Bob"),
        value: 100.0,
        priority: 2,
    };

    let e3 = PartialOrdExample {
        name: String::from("Charlie"),
        value: 200.0,
        priority: 1,
    };

    println!("e1 < e2: {}", e1 < e2); // true (优先级不同)
    println!("e1 < e3: {}", e1 < e3); // true (优先级相同，值不同)

    // 枚举比较
    let s1 = PartialOrdStatus::Idle;
    let s2 = PartialOrdStatus::Active;
    let s3 = PartialOrdStatus::Complete;

    println!("s1 < s2: {}", s1 < s2); // true
    println!("s2 < s3: {}", s2 < s3); // true

    // 浮点数比较演示
    demonstrate_float_comparison();

    // 部分比较演示
    demonstrate_partial_comparison();
}

// 浮点数比较演示
fn demonstrate_float_comparison() {
    let x = std::f64::consts::PI;
    let y = 2.71;
    let nan = f64::NAN;

    println!("Float comparison:");
    println!("x < y: {}", x < y); // true
    println!("x > y: {}", x > y); // false
    println!("x < nan: {}", x < nan); // false
    println!("nan < x: {}", nan < x); // false

    // false NaN比较
    let nan2 = f64::NAN;
    println!("nan == nan2: {}", (nan == nan2));

    // 使用 partial_cmp
    if let Some(ord) = x.partial_cmp(&y) {
        match ord {
            Ordering::Less => println!("x < y"),
            Ordering::Equal => println!("x == y"),
            Ordering::Greater => println!("x > y"),
        }
    }

    if x.partial_cmp(&nan).is_none() {
        println!("Cannot compare x with NaN");
    }
}

// 部分比较演示
fn demonstrate_partial_comparison() {
    let points = [
        PartialOrdPoint { x: 1.0, y: 2.0 },
        PartialOrdPoint { x: 3.0, y: 4.0 },
        PartialOrdPoint {
            x: f64::NAN,
            y: 5.0,
        },
        PartialOrdPoint { x: 2.0, y: 3.0 },
    ];

    println!("Partial comparison:");
    for (i, p1) in points.iter().enumerate() {
        for (j, p2) in points.iter().enumerate() {
            if i == j {
                continue;
            }
            match p1.partial_cmp(p2) {
                Some(Ordering::Less) => println!("p{} < p{}", i, j),
                Some(Ordering::Equal) => println!("p{} == p{}", i, j),
                Some(Ordering::Greater) => println!("p{} > p{}", i, j),
                None => println!("p{} and p{} are incomparable", i, j),
            }
        }
    }
}

// 泛型函数示例
pub fn find_min_partial<T: PartialOrd>(items: &[T]) -> Option<&T> {
    items
        .iter()
        .min_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal))
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partial_ord_example() {
        let e1 = PartialOrdExample {
            name: String::from("Alice"),
            value: 100.0,
            priority: 1,
        };

        let e2 = PartialOrdExample {
            name: String::from("Bob"),
            value: 100.0,
            priority: 2,
        };

        assert!(e1 < e2); // 优先级不同
        assert!(e2 > e1);
    }

    #[test]
    fn test_point_partial_ord() {
        let p1 = PartialOrdPoint { x: 1.0, y: 2.0 };
        let p2 = PartialOrdPoint { x: 1.0, y: 3.0 };
        let p3 = PartialOrdPoint { x: 2.0, y: 1.0 };

        assert!(p1 < p2);
        assert!(p1 < p3);
        assert!(p2 < p3);
    }

    #[test]
    fn test_nan_comparison() {
        let nan_point = PartialOrdPoint {
            x: f64::NAN,
            y: 2.0,
        };
        let normal_point = PartialOrdPoint { x: 1.0, y: 2.0 };

        assert!(nan_point.partial_cmp(&normal_point).is_none());
        assert!(normal_point.partial_cmp(&nan_point).is_none());
    }

    #[test]
    fn test_status_partial_ord() {
        let s1 = PartialOrdStatus::Idle;
        let s2 = PartialOrdStatus::Active;
        let s3 = PartialOrdStatus::Complete;

        assert!(s1 < s2);
        assert!(s2 < s3);
        assert!(s1 < s3); // 传递性
    }

    #[test]
    fn test_find_min_partial() {
        let items = vec![std::f64::consts::PI, 2.71, 1.41, 2.23];

        assert_eq!(find_min_partial(&items), Some(&1.41));
    }
}
