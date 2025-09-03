/*
PartialEq trait 是 Rust 中用于部分相等性比较的重要特征。
它定义了 `eq` 和 `ne` 方法，允许类型进行相等性比较。

## 定义

PartialEq trait 定义了两个方法：

```rust
pub trait PartialEq<Rhs = Self> {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
}
```

## 重要特性

1. **部分相等性**: 允许类型进行相等性比较
2. **自动派生**: 可以通过 `#[derive(PartialEq)]` 自动实现
3. **默认实现**: `ne` 方法有默认实现
4. **泛型支持**: 支持与不同类型进行比较

## 实现示例

### 1. 基本结构体实现 PartialEq

```rust
#[derive(PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现 PartialEq
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}
```

### 2. 泛型类型实现 PartialEq

```rust
#[derive(PartialEq)]
struct Container<T: PartialEq> {
    value: T,
    count: usize,
}

// 手动实现
impl<T: PartialEq> PartialEq for Container<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.count == other.count
    }
}
```

### 3. 枚举实现 PartialEq

```rust
#[derive(PartialEq)]
enum Status {
    Active,
    Inactive,
    Error(String),
}

// 手动实现
impl PartialEq for Status {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Status::Active, Status::Active) => true,
            (Status::Inactive, Status::Inactive) => true,
            (Status::Error(s1), Status::Error(s2)) => s1 == s2,
            _ => false,
        }
    }
}
```

## 使用场景

### 1. 基本比较

```rust
fn main() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 1, y: 2 };
    let p3 = Point { x: 2, y: 1 };
    
    println!("p1 == p2: {}", p1 == p2); // true
    println!("p1 == p3: {}", p1 == p3); // false
    println!("p1 != p3: {}", p1 != p3); // true
}
```

### 2. 集合操作

```rust
fn main() {
    let mut points = vec![
        Point { x: 1, y: 2 },
        Point { x: 3, y: 4 },
        Point { x: 1, y: 2 }, // 重复
    ];
    
    // 移除重复项
    points.dedup();
    println!("Unique points: {:?}", points);
}
```

### 3. 泛型函数

```rust
fn find_item<T: PartialEq>(items: &[T], target: &T) -> Option<usize> {
    items.iter().position(|item| item == target)
}

fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let target = 3;
    
    if let Some(index) = find_item(&numbers, &target) {
        println!("Found {} at index {}", target, index);
    }
}
```

## 与 Eq 的区别

### 1. 约束强度

- **PartialEq**: 只要求相等关系是部分等价关系
- **Eq**: 要求相等关系是完整的等价关系

### 2. 浮点数

- **PartialEq**: 浮点数可以实现 PartialEq
- **Eq**: 浮点数不能实现 Eq（因为 NaN != NaN）

### 3. 用途

- **PartialEq**: 用于需要处理 NaN 等特殊值的场景
- **Eq**: 用于需要完整等价关系的场景

## 性能考虑

1. **比较效率**: PartialEq 实现应该高效
2. **内存访问**: 减少不必要的内存访问
3. **分支预测**: 优化比较逻辑以改善分支预测
4. **缓存友好**: 考虑数据局部性

## 最佳实践

1. **一致性**: 确保 PartialEq 实现的一致性
2. **性能**: 实现高效的比较逻辑
3. **测试**: 为相等性比较编写测试
4. **文档**: 明确说明相等性的语义

## 高级用法

### 1. 跨类型比较

```rust
impl PartialEq<&str> for String {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

fn main() {
    let s = String::from("hello");
    let str_ref = "hello";
    
    println!("s == str_ref: {}", s == str_ref); // true
}
```

### 2. 自定义相等性

```rust
impl PartialEq for CustomType {
    fn eq(&self, other: &Self) -> bool {
        // 忽略某些字段的比较
        self.important_field == other.important_field &&
        self.another_field == other.another_field
        // 忽略 self.ignored_field
    }
}
```

### 3. 引用相等性

```rust
impl PartialEq for ReferenceType {
    fn eq(&self, other: &Self) -> bool {
        // 比较引用而不是内容
        std::ptr::eq(self, other)
    }
}
```

## 总结

PartialEq trait 为 Rust 提供了部分相等性比较支持。
通过正确实现 PartialEq，可以创建灵活的相等性比较，
同时需要注意性能影响和语义一致性。
*/

// 示例结构体
#[derive(Debug)]
pub struct PartialEqExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

impl PartialEq for PartialEqExample {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && 
        self.value == other.value && 
        self.active == other.active
    }
}

// 泛型容器
#[derive(Debug)]
pub struct PartialEqContainer<T: PartialEq> {
    pub value: T,
    pub metadata: String,
}

impl<T: PartialEq> PartialEq for PartialEqContainer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.metadata == other.metadata
    }
}

// 状态枚举
#[derive(Debug)]
pub enum PartialEqStatus {
    Idle,
    Active,
    Error(String),
}

impl PartialEq for PartialEqStatus {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PartialEqStatus::Idle, PartialEqStatus::Idle) => true,
            (PartialEqStatus::Active, PartialEqStatus::Active) => true,
            (PartialEqStatus::Error(s1), PartialEqStatus::Error(s2)) => s1 == s2,
            _ => false,
        }
    }
}

// 几何点
#[derive(Debug)]
pub struct PartialEqPoint {
    pub x: f64,
    pub y: f64,
}

impl PartialEq for PartialEqPoint {
    fn eq(&self, other: &Self) -> bool {
        // 处理浮点数的 NaN 情况
        if self.x.is_nan() && other.x.is_nan() {
            return self.y.is_nan() && other.y.is_nan();
        }
        if self.y.is_nan() && other.y.is_nan() {
            return self.x.is_nan() && other.x.is_nan();
        }
        
        self.x == other.x && self.y == other.y
    }
}

// 演示函数
pub fn demonstrate_partial_eq() {
    // 基本相等性比较
    let p1 = PartialEqPoint { x: 1.0, y: 2.0 };
    let p2 = PartialEqPoint { x: 1.0, y: 2.0 };
    let p3 = PartialEqPoint { x: 2.0, y: 1.0 };
    
    println!("p1 == p2: {}", p1 == p2); // true
    println!("p1 == p3: {}", p1 == p3); // false
    println!("p1 != p3: {}", p1 != p3); // true
    
    // 浮点数 NaN 处理
    let nan_point = PartialEqPoint { x: f64::NAN, y: f64::NAN };
    let another_nan = PartialEqPoint { x: f64::NAN, y: f64::NAN };
    
    println!("nan_point == another_nan: {}", nan_point == another_nan); // true
    
    // 结构体相等性
    let e1 = PartialEqExample {
        name: String::from("Test"),
        value: 42,
        active: true,
    };
    
    let e2 = PartialEqExample {
        name: String::from("Test"),
        value: 42,
        active: true,
    };
    
    let e3 = PartialEqExample {
        name: String::from("Different"),
        value: 42,
        active: true,
    };
    
    println!("e1 == e2: {}", e1 == e2); // true
    println!("e1 == e3: {}", e1 == e3); // false
    
    // 枚举相等性
    let s1 = PartialEqStatus::Active;
    let s2 = PartialEqStatus::Active;
    let s3 = PartialEqStatus::Error(String::from("Something went wrong"));
    let s4 = PartialEqStatus::Error(String::from("Something went wrong"));
    let s5 = PartialEqStatus::Error(String::from("Different error"));
    
    println!("s1 == s2: {}", s1 == s2); // true
    println!("s3 == s4: {}", s3 == s4); // true
    println!("s3 == s5: {}", s3 == s5); // false
    
    // 泛型容器相等性
    let c1 = PartialEqContainer {
        value: 100,
        metadata: String::from("Container 1"),
    };
    
    let c2 = PartialEqContainer {
        value: 100,
        metadata: String::from("Container 1"),
    };
    
    let c3 = PartialEqContainer {
        value: 200,
        metadata: String::from("Container 1"),
    };
    
    println!("c1 == c2: {}", c1 == c2); // true
    println!("c1 == c3: {}", c1 == c3); // false
    
    // 集合操作演示
    demonstrate_collection_operations();
}

// 集合操作演示
fn demonstrate_collection_operations() {
    let mut points = vec![
        PartialEqPoint { x: 1.0, y: 2.0 },
        PartialEqPoint { x: 3.0, y: 4.0 },
        PartialEqPoint { x: 1.0, y: 2.0 }, // 重复
        PartialEqPoint { x: 5.0, y: 6.0 },
    ];
    
    println!("Original points: {:?}", points);
    
    // 移除重复项
    points.dedup();
    println!("After dedup: {:?}", points);
    
    // 查找特定点
    let target = PartialEqPoint { x: 3.0, y: 4.0 };
    if let Some(index) = points.iter().position(|p| p == &target) {
        println!("Found target at index: {}", index);
    }
}

// 泛型查找函数
pub fn find_item<T: PartialEq>(items: &[T], target: &T) -> Option<usize> {
    items.iter().position(|item| item == target)
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_partial_eq_example() {
        let e1 = PartialEqExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let e2 = PartialEqExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let e3 = PartialEqExample {
            name: String::from("Different"),
            value: 100,
            active: false,
        };
        
        assert_eq!(e1, e2);
        assert_ne!(e1, e3);
    }
    
    #[test]
    fn test_point_partial_eq() {
        let p1 = PartialEqPoint { x: 1.0, y: 2.0 };
        let p2 = PartialEqPoint { x: 1.0, y: 2.0 };
        let p3 = PartialEqPoint { x: 2.0, y: 1.0 };
        
        assert_eq!(p1, p2);
        assert_ne!(p1, p3);
    }
    
    #[test]
    fn test_nan_equality() {
        let nan_point = PartialEqPoint { x: f64::NAN, y: f64::NAN };
        let another_nan = PartialEqPoint { x: f64::NAN, y: f64::NAN };
        
        assert_eq!(nan_point, another_nan);
    }
    
    #[test]
    fn test_status_partial_eq() {
        let s1 = PartialEqStatus::Active;
        let s2 = PartialEqStatus::Active;
        let s3 = PartialEqStatus::Idle;
        
        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
    }
    
    #[test]
    fn test_find_item() {
        let items = vec![1, 2, 3, 4, 5];
        let target = 3;
        
        assert_eq!(find_item(&items, &target), Some(2));
        assert_eq!(find_item(&items, &6), None);
    }
}
