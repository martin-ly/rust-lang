/*
Eq trait 是 Rust 中用于相等性比较的重要特征。
它是 PartialEq 的更强版本，要求相等关系是等价关系（自反、对称、传递）。

## 定义

Eq trait 是一个标记特征，继承自 PartialEq：

```rust
pub trait Eq: PartialEq { }
```

## 重要特性

1. **等价关系**: 要求相等关系满足等价关系的所有性质
2. **自反性**: 对于所有 x，x == x 为真
3. **对称性**: 如果 x == y，那么 y == x
4. **传递性**: 如果 x == y 且 y == z，那么 x == z
5. **自动派生**: 可以通过 `#[derive(Eq)]` 自动实现

## 等价关系性质

### 1. 自反性 (Reflexivity)
对于所有值 x，x == x 必须为 true

### 2. 对称性 (Symmetry)
如果 x == y 为 true，那么 y == x 也必须为 true

### 3. 传递性 (Transitivity)
如果 x == y 为 true 且 y == z 为 true，那么 x == z 也必须为 true

## 实现示例

### 1. 基本类型实现 Eq

```rust
#[derive(Eq, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现（等同于 #[derive(Eq, PartialEq)]）
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for Point { }
```

### 2. 泛型类型实现 Eq

```rust
#[derive(Eq, PartialEq)]
struct Container<T: Eq> {
    value: T,
    count: usize,
}

impl<T: Eq> PartialEq for Container<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.count == other.count
    }
}

impl<T: Eq> Eq for Container<T> { }
```

### 3. 枚举实现 Eq

```rust
#[derive(Eq, PartialEq)]
enum Status {
    Active,
    Inactive,
    Error,
}

impl PartialEq for Status {
    fn eq(&self, other: &Self) -> bool {
        matches!((self, other), 
            (Status::Active, Status::Active) |
            (Status::Inactive, Status::Inactive) |
            (Status::Error, Status::Error))
    }
}

impl Eq for Status { }
```

## 使用场景

### 1. 集合操作

```rust
use std::collections::HashSet;

fn main() {
    let mut set: HashSet<Point> = HashSet::new();
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 1, y: 2 };
    
    set.insert(p1);
    set.insert(p2); // 不会插入，因为 p1 == p2
    
    println!("Set size: {}", set.len()); // 输出: 1
}
```

### 2. 排序

```rust
fn main() {
    let mut points = vec![
        Point { x: 3, y: 1 },
        Point { x: 1, y: 2 },
        Point { x: 2, y: 3 },
    ];
    
    points.sort(); // 需要 Ord trait，但 Ord 要求 Eq
    
    for point in points {
        println!("{:?}", point);
    }
}
```

### 3. 泛型约束

```rust
fn find_duplicates<T: Eq + Clone>(items: &[T]) -> Vec<T> {
    let mut duplicates = Vec::new();
    let mut seen = Vec::new();
    
    for item in items {
        if seen.contains(item) {
            duplicates.push(item.clone());
        } else {
            seen.push(item.clone());
        }
    }
    
    duplicates
}
```

## 与 PartialEq 的区别

### 1. 约束强度

- **PartialEq**: 只要求相等关系是部分等价关系
- **Eq**: 要求相等关系是完整的等价关系

### 2. 浮点数

- **PartialEq**: 浮点数可以实现 PartialEq（NaN != NaN）
- **Eq**: 浮点数不能实现 Eq（因为 NaN != NaN 违反自反性）

### 3. 用途

- **PartialEq**: 用于需要处理 NaN 等特殊值的场景
- **Eq**: 用于需要完整等价关系的场景（如集合、排序）

## 性能考虑

1. **比较效率**: Eq 实现应该高效
2. **内存访问**: 减少不必要的内存访问
3. **分支预测**: 优化比较逻辑以改善分支预测
4. **缓存友好**: 考虑数据局部性

## 最佳实践

1. **一致性**: 确保 Eq 实现与 PartialEq 一致
2. **性能**: 实现高效的比较逻辑
3. **测试**: 为等价关系性质编写测试
4. **文档**: 明确说明相等性的语义

## 高级用法

### 1. 自定义相等性

```rust
impl PartialEq for CustomType {
    fn eq(&self, other: &Self) -> bool {
        // 忽略某些字段的比较
        self.important_field == other.important_field &&
        self.another_field == other.another_field
        // 忽略 self.ignored_field
    }
}

impl Eq for CustomType { }
```

### 2. 引用相等性

```rust
impl PartialEq for ReferenceType {
    fn eq(&self, other: &Self) -> bool {
        // 比较引用而不是内容
        std::ptr::eq(self, other)
    }
}

impl Eq for ReferenceType { }
```

### 3. 深度相等性

```rust
impl PartialEq for DeepType {
    fn eq(&self, other: &Self) -> bool {
        // 递归比较所有字段
        self.field1 == other.field1 &&
        self.field2 == other.field2 &&
        self.nested == other.nested
    }
}

impl Eq for DeepType { }
```

## 总结

Eq trait 为 Rust 提供了完整的等价关系支持。
通过正确实现 Eq，可以创建可靠的相等性比较，
同时需要注意等价关系的性质和性能影响。
*/

// 示例结构体
#[derive(Debug)]
pub struct EqExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

impl PartialEq for EqExample {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && 
        self.value == other.value && 
        self.active == other.active
    }
}

impl Eq for EqExample { }

// 泛型容器
#[derive(Debug)]
pub struct EqContainer<T: Eq> {
    pub value: T,
    pub metadata: String,
}

impl<T: Eq> PartialEq for EqContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.metadata == other.metadata
    }
}

impl<T: Eq> Eq for EqContainer<T> { }

// 状态枚举
#[derive(Debug)]
pub enum EqStatus {
    Idle,
    Active,
    Error,
}

impl PartialEq for EqStatus {
    fn eq(&self, other: &Self) -> bool {
        matches!((self, other),
            (EqStatus::Idle, EqStatus::Idle) |
            (EqStatus::Active, EqStatus::Active) |
            (EqStatus::Error, EqStatus::Error))
    }
}

impl Eq for EqStatus { }

// 几何点
#[derive(Debug, Clone)]
pub struct EqPoint {
    pub x: i32,
    pub y: i32,
}

impl PartialEq for EqPoint {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for EqPoint { }

// 演示函数
pub fn demonstrate_eq() {
    // 基本相等性比较
    let p1 = EqPoint { x: 1, y: 2 };
    let p2 = EqPoint { x: 1, y: 2 };
    let p3 = EqPoint { x: 2, y: 1 };
    
    println!("p1 == p2: {}", p1 == p2); // true
    println!("p1 == p3: {}", p1 == p3); // false
    println!("p1 != p3: {}", p1 != p3); // true
    
    // 结构体相等性
    let e1 = EqExample {
        name: String::from("Test"),
        value: 42,
        active: true,
    };
    
    let e2 = EqExample {
        name: String::from("Test"),
        value: 42,
        active: true,
    };
    
    let e3 = EqExample {
        name: String::from("Different"),
        value: 42,
        active: true,
    };
    
    println!("e1 == e2: {}", e1 == e2); // true
    println!("e1 == e3: {}", e1 == e3); // false
    
    // 枚举相等性
    let s1 = EqStatus::Active;
    let s2 = EqStatus::Active;
    let s3 = EqStatus::Idle;
    
    println!("s1 == s2: {}", s1 == s2); // true
    println!("s1 == s3: {}", s1 == s3); // false
    
    // 泛型容器相等性
    let c1 = EqContainer {
        value: 100,
        metadata: String::from("Container 1"),
    };
    
    let c2 = EqContainer {
        value: 100,
        metadata: String::from("Container 1"),
    };
    
    let c3 = EqContainer {
        value: 200,
        metadata: String::from("Container 1"),
    };
    
    println!("c1 == c2: {}", c1 == c2); // true
    println!("c1 == c3: {}", c1 == c3); // false
    
    // 等价关系测试
    test_equivalence_properties();
}

// 测试等价关系性质
fn test_equivalence_properties() {
    let p1 = EqPoint { x: 1, y: 2 };
    let p2 = EqPoint { x: 1, y: 2 };
    let p3 = EqPoint { x: 1, y: 2 };
    
    // 自反性: p1 == p1
    // 自反性测试
    let p1_copy = p1.clone();
    assert!(p1 == p1_copy, "Reflexivity failed");
    
    // 对称性: 如果 p1 == p2，那么 p2 == p1
    if p1 == p2 {
        assert!(p2 == p1, "Symmetry failed");
    }
    
    // 传递性: 如果 p1 == p2 且 p2 == p3，那么 p1 == p3
    if p1 == p2 && p2 == p3 {
        assert!(p1 == p3, "Transitivity failed");
    }
    
    println!("All equivalence properties satisfied!");
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_eq_example() {
        let e1 = EqExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let e2 = EqExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let e3 = EqExample {
            name: String::from("Different"),
            value: 100,
            active: false,
        };
        
        assert_eq!(e1, e2);
        assert_ne!(e1, e3);
    }
    
    #[test]
    fn test_point_eq() {
        let p1 = EqPoint { x: 1, y: 2 };
        let p2 = EqPoint { x: 1, y: 2 };
        let p3 = EqPoint { x: 2, y: 1 };
        
        assert_eq!(p1, p2);
        assert_ne!(p1, p3);
    }
    
    #[test]
    fn test_status_eq() {
        let s1 = EqStatus::Active;
        let s2 = EqStatus::Active;
        let s3 = EqStatus::Idle;
        
        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
    }
}
