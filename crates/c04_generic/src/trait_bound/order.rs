/*
Ord trait 是 Rust 中用于全序比较的重要特征。
它定义了 `cmp` 方法，允许类型进行全序比较，要求比较关系是总序（全序）。

## 定义

Ord trait 继承自 PartialOrd 和 Eq：

```rust
pub trait Ord: Eq + PartialOrd<Self> {
    fn cmp(&self, other: &Self) -> Ordering;
}
```

## 重要特性

1. **全序关系**: 要求比较关系是总序（全序）
2. **继承关系**: 继承自 PartialOrd 和 Eq
3. **自动派生**: 可以通过 `#[derive(Ord)]` 自动实现
4. **排序支持**: 为排序算法提供基础

## 全序关系性质

### 1. 自反性 (Reflexivity)
对于所有值 x，x <= x 为 true

### 2. 反对称性 (Antisymmetry)
如果 x <= y 且 y <= x，那么 x == y

### 3. 传递性 (Transitivity)
如果 x <= y 且 y <= z，那么 x <= z

### 4. 完全性 (Totality)
对于所有 x 和 y，要么 x <= y，要么 y <= x

## 实现示例

### 1. 基本结构体实现 Ord

```rust
#[derive(Eq, PartialEq, PartialOrd, Ord)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for Point { }

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Point {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先比较 x，再比较 y
        self.x.cmp(&other.x).then(self.y.cmp(&other.y))
    }
}
```

### 2. 泛型类型实现 Ord

```rust
#[derive(Eq, PartialEq, PartialOrd, Ord)]
struct Container<T: Ord> {
    value: T,
    count: usize,
}

impl<T: Ord> PartialEq for Container<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.count == other.count
    }
}

impl<T: Ord> Eq for Container<T> { }

impl<T: Ord> PartialOrd for Container<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord> Ord for Container<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先比较 value，再比较 count
        self.value.cmp(&other.value).then(self.count.cmp(&other.count))
    }
}
```

### 3. 枚举实现 Ord

```rust
#[derive(Eq, PartialEq, PartialOrd, Ord)]
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

impl Eq for Status { }

impl PartialOrd for Status {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Status {
    fn cmp(&self, other: &Self) -> Ordering {
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
        self_val.cmp(&other_val)
    }
}
```

## 使用场景

### 1. 排序

```rust
fn main() {
    let mut points = vec![
        Point { x: 3, y: 1 },
        Point { x: 1, y: 2 },
        Point { x: 2, y: 3 },
        Point { x: 1, y: 1 },
    ];

    points.sort(); // 使用 Ord 进行排序

    for point in points {
        println!("{:?}", point);
    }
}
```

### 2. 集合操作

```rust
use std::collections::BTreeSet;

fn main() {
    let mut set: BTreeSet<Point> = BTreeSet::new();

    set.insert(Point { x: 3, y: 1 });
    set.insert(Point { x: 1, y: 2 });
    set.insert(Point { x: 2, y: 3 });

    // BTreeSet 会自动保持有序
    for point in &set {
        println!("{:?}", point);
    }
}
```

### 3. 泛型约束

```rust
fn find_min<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().min()
}

fn find_max<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().max()
}

fn main() {
    let numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];

    if let Some(min) = find_min(&numbers) {
        println!("Minimum: {}", min);
    }

    if let Some(max) = find_max(&numbers) {
        println!("Maximum: {}", max);
    }
}
```

## 与 PartialOrd 的区别

### 1. 约束强度

- **PartialOrd**: 只要求比较关系是部分序
- **Ord**: 要求比较关系是全序

### 2. 浮点数

- **PartialOrd**: 浮点数可以实现 PartialOrd（NaN 不可比较）
- **Ord**: 浮点数不能实现 Ord（因为 NaN 不可比较）

### 3. 用途

- **PartialOrd**: 用于需要处理 NaN 等特殊值的场景
- **Ord**: 用于需要全序关系的场景（如排序、集合）

## 性能考虑

1. **比较效率**: Ord 实现应该高效
2. **内存访问**: 减少不必要的内存访问
3. **分支预测**: 优化比较逻辑以改善分支预测
4. **缓存友好**: 考虑数据局部性

## 最佳实践

1. **一致性**: 确保 Ord 实现与 PartialOrd 和 Eq 一致
2. **性能**: 实现高效的比较逻辑
3. **测试**: 为全序关系性质编写测试
4. **文档**: 明确说明比较的语义

## 高级用法

### 1. 自定义比较逻辑

```rust
impl Ord for CustomType {
    fn cmp(&self, other: &Self) -> Ordering {
        // 自定义比较逻辑
        if self.priority != other.priority {
            // 优先级高的排在前面
            other.priority.cmp(&self.priority)
        } else {
            // 优先级相同时按名称排序
            self.name.cmp(&other.name)
        }
    }
}
```

### 2. 多字段比较

```rust
impl Ord for Person {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先按年龄排序，再按姓名排序
        self.age.cmp(&other.age)
            .then(self.name.cmp(&other.name))
    }
}
```

### 3. 反向排序

```rust
impl Ord for ReverseOrder {
    fn cmp(&self, other: &Self) -> Ordering {
        // 反向排序
        other.value.cmp(&self.value)
    }
}
```

## 总结

Ord trait 为 Rust 提供了全序比较支持。
通过正确实现 Ord，可以创建可靠的排序和比较功能，
同时需要注意全序关系的性质和性能影响。
*/

use std::cmp::Ordering;

// 示例结构体
#[derive(Debug)]
pub struct OrdExample {
    pub name: String,
    pub value: i32,
    pub priority: u8,
}

impl PartialEq for OrdExample {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.value == other.value && self.priority == other.priority
    }
}

impl Eq for OrdExample {}

impl PartialOrd for OrdExample {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdExample {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先按优先级排序，再按值排序，最后按名称排序
        self.priority
            .cmp(&other.priority)
            .then(self.value.cmp(&other.value))
            .then(self.name.cmp(&other.name))
    }
}

// 泛型容器
#[derive(Debug)]
pub struct OrdContainer<T: Ord> {
    pub value: T,
    pub metadata: String,
}

impl<T: Ord> PartialEq for OrdContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.metadata == other.metadata
    }
}

impl<T: Ord> Eq for OrdContainer<T> {}

impl<T: Ord> PartialOrd for OrdContainer<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord> Ord for OrdContainer<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先比较值，再比较元数据
        self.value
            .cmp(&other.value)
            .then(self.metadata.cmp(&other.metadata))
    }
}

// 状态枚举
#[derive(Debug)]
pub enum OrdStatus {
    Idle,     // 0
    Active,   // 1
    Working,  // 2
    Complete, // 3
    Error,    // 4
}

impl PartialEq for OrdStatus {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (OrdStatus::Idle, OrdStatus::Idle)
                | (OrdStatus::Active, OrdStatus::Active)
                | (OrdStatus::Working, OrdStatus::Working)
                | (OrdStatus::Complete, OrdStatus::Complete)
                | (OrdStatus::Error, OrdStatus::Error)
        )
    }
}

impl Eq for OrdStatus {}

impl PartialOrd for OrdStatus {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdStatus {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_val = match self {
            OrdStatus::Idle => 0,
            OrdStatus::Active => 1,
            OrdStatus::Working => 2,
            OrdStatus::Complete => 3,
            OrdStatus::Error => 4,
        };
        let other_val = match other {
            OrdStatus::Idle => 0,
            OrdStatus::Active => 1,
            OrdStatus::Working => 2,
            OrdStatus::Complete => 3,
            OrdStatus::Error => 4,
        };
        self_val.cmp(&other_val)
    }
}

// 几何点
#[derive(Debug)]
pub struct OrdPoint {
    pub x: i32,
    pub y: i32,
}

impl PartialEq for OrdPoint {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for OrdPoint {}

impl PartialOrd for OrdPoint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdPoint {
    fn cmp(&self, other: &Self) -> Ordering {
        // 先比较 x，再比较 y
        self.x.cmp(&other.x).then(self.y.cmp(&other.y))
    }
}

// 演示函数
pub fn demonstrate_ord() {
    // 基本比较
    let p1 = OrdPoint { x: 1, y: 2 };
    let p2 = OrdPoint { x: 1, y: 3 };
    let p3 = OrdPoint { x: 2, y: 1 };

    println!("p1 < p2: {}", p1 < p2); // true
    println!("p1 < p3: {}", p1 < p3); // true
    println!("p2 < p3: {}", p2 < p3); // true

    // 结构体比较
    let e1 = OrdExample {
        name: String::from("Alice"),
        value: 100,
        priority: 1,
    };

    let e2 = OrdExample {
        name: String::from("Bob"),
        value: 100,
        priority: 2,
    };

    let e3 = OrdExample {
        name: String::from("Charlie"),
        value: 200,
        priority: 1,
    };

    println!("e1 < e2: {}", e1 < e2); // true (优先级不同)
    println!("e1 < e3: {}", e1 < e3); // true (优先级相同，值不同)

    // 枚举比较
    let s1 = OrdStatus::Idle;
    let s2 = OrdStatus::Active;
    let s3 = OrdStatus::Complete;

    println!("s1 < s2: {}", s1 < s2); // true
    println!("s2 < s3: {}", s2 < s3); // true

    // 排序演示
    demonstrate_sorting();

    // 集合操作演示
    demonstrate_collection_operations();
}

// 排序演示
fn demonstrate_sorting() {
    let mut points = vec![
        OrdPoint { x: 3, y: 1 },
        OrdPoint { x: 1, y: 2 },
        OrdPoint { x: 2, y: 3 },
        OrdPoint { x: 1, y: 1 },
        OrdPoint { x: 3, y: 3 },
    ];

    println!("Before sorting: {:?}", points);

    points.sort(); // 使用 Ord 进行排序

    println!("After sorting: {:?}", points);

    // 反向排序
    points.sort_by(|a, b| b.cmp(a));
    println!("After reverse sorting: {:?}", points);
}

// 集合操作演示
fn demonstrate_collection_operations() {
    use std::collections::BTreeSet;

    let mut set: BTreeSet<OrdPoint> = BTreeSet::new();

    set.insert(OrdPoint { x: 3, y: 1 });
    set.insert(OrdPoint { x: 1, y: 2 });
    set.insert(OrdPoint { x: 2, y: 3 });
    set.insert(OrdPoint { x: 1, y: 1 });

    println!("BTreeSet (automatically sorted):");
    for point in &set {
        println!("  {:?}", point);
    }
}

// 泛型函数示例
pub fn find_min<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().min()
}

pub fn find_max<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().max()
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ord_example() {
        let e1 = OrdExample {
            name: String::from("Alice"),
            value: 100,
            priority: 1,
        };

        let e2 = OrdExample {
            name: String::from("Bob"),
            value: 100,
            priority: 2,
        };

        assert!(e1 < e2); // 优先级不同
        assert!(e2 > e1);
    }

    #[test]
    fn test_point_ord() {
        let p1 = OrdPoint { x: 1, y: 2 };
        let p2 = OrdPoint { x: 1, y: 3 };
        let p3 = OrdPoint { x: 2, y: 1 };

        assert!(p1 < p2);
        assert!(p1 < p3);
        assert!(p2 < p3);
    }

    #[test]
    fn test_status_ord() {
        let s1 = OrdStatus::Idle;
        let s2 = OrdStatus::Active;
        let s3 = OrdStatus::Complete;

        assert!(s1 < s2);
        assert!(s2 < s3);
        assert!(s1 < s3); // 传递性
    }

    #[test]
    fn test_sorting() {
        let mut points = vec![
            OrdPoint { x: 3, y: 1 },
            OrdPoint { x: 1, y: 2 },
            OrdPoint { x: 2, y: 3 },
        ];

        points.sort();

        assert_eq!(points[0], OrdPoint { x: 1, y: 2 });
        assert_eq!(points[1], OrdPoint { x: 2, y: 3 });
        assert_eq!(points[2], OrdPoint { x: 3, y: 1 });
    }

    #[test]
    fn test_find_min_max() {
        let items = vec![3, 1, 4, 1, 5, 9, 2, 6];

        assert_eq!(find_min(&items), Some(&1));
        assert_eq!(find_max(&items), Some(&9));
    }
}
