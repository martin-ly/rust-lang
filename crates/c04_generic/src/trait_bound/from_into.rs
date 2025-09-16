/*
From 和 Into trait 是 Rust 中用于类型转换的重要特征。
它们提供了一种安全、一致的方式来在不同类型之间进行转换。

## 定义

### From trait
```rust
pub trait From<T> {
    fn from(T) -> Self;
}
```

### Into trait
```rust
pub trait Into<T> {
    fn into(self) -> T;
}
```

## 重要特性

1. **类型安全**: 提供编译时类型安全的转换
2. **自动实现**: Into 会自动为 From 实现
3. **一致性**: 为类型系统提供一致的转换机制
4. **零成本**: 转换通常是零成本的

## 实现示例

### 1. 基本类型实现 From

```rust
struct Point {
    x: i32,
    y: i32,
}

impl From<(i32, i32)> for Point {
    fn from((x, y): (i32, i32)) -> Self {
        Point { x, y }
    }
}

impl From<[i32; 2]> for Point {
    fn from([x, y]: [i32; 2]) -> Self {
        Point { x, y }
    }
}
```

### 2. 泛型类型实现 From

```rust
struct Container<T> {
    value: T,
    metadata: String,
}

impl<T> From<T> for Container<T> {
    fn from(value: T) -> Self {
        Container {
            value,
            metadata: String::from("Default metadata"),
        }
    }
}

impl<T> From<(T, String)> for Container<T> {
    fn from((value, metadata): (T, String)) -> Self {
        Container { value, metadata }
    }
}
```

### 3. 枚举实现 From

```rust
enum Status {
    Idle,
    Active,
    Error(String),
}

impl From<String> for Status {
    fn from(message: String) -> Self {
        Status::Error(message)
    }
}

impl From<&str> for Status {
    fn from(message: &str) -> Self {
        Status::Error(message.to_string())
    }
}

impl From<i32> for Status {
    fn from(code: i32) -> Self {
        match code {
            0 => Status::Idle,
            1 => Status::Active,
            _ => Status::Error(format!("Unknown code: {}", code)),
        }
    }
}
```

## 使用场景

### 1. 基本转换

```rust
fn main() {
    // 使用 From
    let point = Point::from((10, 20));
    let point_array = Point::from([30, 40]);

    // 使用 Into
    let tuple: (i32, i32) = (50, 60);
    let point: Point = tuple.into();

    let array: [i32; 2] = [70, 80];
    let point: Point = array.into();
}
```

### 2. 函数参数

```rust
fn process_point<P: Into<Point>>(point: P) {
    let point = point.into();
    println!("Processing point: {:?}", point);
}

fn main() {
    process_point((1, 2));
    process_point([3, 4]);
    process_point(Point { x: 5, y: 6 });
}
```

### 3. 错误处理

```rust
use std::error::Error;
use std::fmt;

#[derive(Debug)]
struct CustomError {
    message: String,
}

impl From<String> for CustomError {
    fn from(message: String) -> Self {
        CustomError { message }
    }
}

impl From<&str> for CustomError {
    fn from(message: &str) -> Self {
        CustomError {
            message: message.to_string(),
        }
    }
}

impl fmt::Display for CustomError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Custom error: {}", self.message)
    }
}

impl Error for CustomError {}
```

## 与 TryFrom 的区别

### 1. 转换类型

- **From/Into**: 总是成功的转换
- **TryFrom/TryInto**: 可能失败的转换

### 2. 返回值

- **From/Into**: 返回目标类型
- **TryFrom/TryInto**: 返回 Result<T, E>

### 3. 用途

- **From/Into**: 用于安全的、总是成功的转换
- **TryFrom/TryInto**: 用于可能失败的转换

## 性能考虑

1. **零成本**: From/Into 实现通常是零成本的
2. **编译时优化**: 编译器可以优化转换
3. **内存效率**: 避免不必要的内存分配
4. **内联**: 转换函数通常被内联

## 最佳实践

1. **一致性**: 保持转换逻辑的一致性
2. **性能**: 实现高效的转换逻辑
3. **文档**: 明确说明转换的语义
4. **测试**: 为转换逻辑编写测试

## 高级用法

### 1. 链式转换

```rust
impl From<u8> for Point {
    fn from(value: u8) -> Self {
        Point {
            x: value as i32,
            y: value as i32,
        }
    }
}

impl From<Point> for String {
    fn from(point: Point) -> Self {
        format!("({}, {})", point.x, point.y)
    }
}

fn main() {
    let point: Point = 42u8.into();
    let string: String = point.into();
    println!("Result: {}", string); // "(42, 42)"
}
```

### 2. 条件转换

```rust
impl From<ConditionalType> for TargetType {
    fn from(source: ConditionalType) -> Self {
        if source.should_transform() {
            TargetType::Transformed(source.get_value())
        } else {
            TargetType::Default
        }
    }
}
```

### 3. 组合转换

```rust
impl From<(String, i32)> for ComplexType {
    fn from((name, value): (String, i32)) -> Self {
        ComplexType {
            name,
            value,
            metadata: String::from("Generated"),
            timestamp: std::time::SystemTime::now(),
        }
    }
}
```

## 总结

From 和 Into trait 为 Rust 提供了类型转换的基础。
通过正确实现这些 trait，可以创建灵活、安全的类型转换，
同时保持零成本抽象的优势。
*/

// 示例结构体
#[derive(Debug)]
pub struct FromIntoExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

// 从元组转换
impl From<(String, i32, bool)> for FromIntoExample {
    fn from((name, value, active): (String, i32, bool)) -> Self {
        FromIntoExample {
            name,
            value,
            active,
        }
    }
}

// 从字符串和数值转换
impl From<(&str, i32)> for FromIntoExample {
    fn from((name, value): (&str, i32)) -> Self {
        FromIntoExample {
            name: name.to_string(),
            value,
            active: true, // 默认值
        }
    }
}

// 从单个字符串转换
impl From<String> for FromIntoExample {
    fn from(name: String) -> Self {
        FromIntoExample {
            name,
            value: 0,      // 默认值
            active: false, // 默认值
        }
    }
}

// 泛型容器
#[derive(Debug)]
pub struct FromIntoContainer<T> {
    pub value: T,
    pub metadata: String,
}

impl<T> From<T> for FromIntoContainer<T> {
    fn from(value: T) -> Self {
        FromIntoContainer {
            value,
            metadata: String::from("Default metadata"),
        }
    }
}

impl<T> From<(T, String)> for FromIntoContainer<T> {
    fn from((value, metadata): (T, String)) -> Self {
        FromIntoContainer { value, metadata }
    }
}

// 状态枚举
#[derive(Debug)]
pub enum FromIntoStatus {
    Idle,
    Active,
    Error(String),
}

// 从字符串转换
impl From<String> for FromIntoStatus {
    fn from(message: String) -> Self {
        FromIntoStatus::Error(message)
    }
}

// 从字符串切片转换
impl From<&str> for FromIntoStatus {
    fn from(message: &str) -> Self {
        FromIntoStatus::Error(message.to_string())
    }
}

// 从数值转换
impl From<i32> for FromIntoStatus {
    fn from(code: i32) -> Self {
        match code {
            0 => FromIntoStatus::Idle,
            1 => FromIntoStatus::Active,
            _ => FromIntoStatus::Error(format!("Unknown code: {}", code)),
        }
    }
}

// 几何点
#[derive(Debug)]
pub struct FromIntoPoint {
    pub x: i32,
    pub y: i32,
}

// 从元组转换
impl From<(i32, i32)> for FromIntoPoint {
    fn from((x, y): (i32, i32)) -> Self {
        FromIntoPoint { x, y }
    }
}

// 从数组转换
impl From<[i32; 2]> for FromIntoPoint {
    fn from([x, y]: [i32; 2]) -> Self {
        FromIntoPoint { x, y }
    }
}

// 从单个数值转换
impl From<i32> for FromIntoPoint {
    fn from(value: i32) -> Self {
        FromIntoPoint { x: value, y: value }
    }
}

// 演示函数
pub fn demonstrate_from_into() {
    // 基本 From 转换
    let point1 = FromIntoPoint::from((10, 20));
    let point2 = FromIntoPoint::from([30, 40]);
    let point3 = FromIntoPoint::from(50);

    println!("Point1: {:?}", point1);
    println!("Point2: {:?}", point2);
    println!("Point3: {:?}", point3);

    // 基本 Into 转换
    let tuple: (i32, i32) = (60, 70);
    let point4: FromIntoPoint = tuple.into();

    let array: [i32; 2] = [80, 90];
    let point5: FromIntoPoint = array.into();

    let value: i32 = 100;
    let point6: FromIntoPoint = value.into();

    println!("Point4: {:?}", point4);
    println!("Point5: {:?}", point5);
    println!("Point6: {:?}", point6);

    // 结构体转换
    let example1 = FromIntoExample::from(("Alice".to_string(), 42, true));
    let example2 = FromIntoExample::from(("Bob", 100));
    let example3 = FromIntoExample::from("Charlie".to_string());

    println!("Example1: {:?}", example1);
    println!("Example2: {:?}", example2);
    println!("Example3: {:?}", example3);

    // 枚举转换
    let status1 = FromIntoStatus::from("Something went wrong".to_string());
    let status2 = FromIntoStatus::from("Another error");
    let status3 = FromIntoStatus::from(0);
    let status4 = FromIntoStatus::from(1);
    let status5 = FromIntoStatus::from(999);

    println!("Status1: {:?}", status1);
    println!("Status2: {:?}", status2);
    println!("Status3: {:?}", status3);
    println!("Status4: {:?}", status4);
    println!("Status5: {:?}", status5);

    // 泛型容器转换
    let container1: FromIntoContainer<i32> = 42.into();
    let container2: FromIntoContainer<i32> =
        FromIntoContainer::from((100, "Custom metadata".to_string()));

    println!("Container1: {:?}", container1);
    println!("Container2: {:?}", container2);

    // 链式转换演示
    demonstrate_chained_conversions();

    // 函数参数转换演示
    demonstrate_function_conversions();
}

// 链式转换演示
fn demonstrate_chained_conversions() {
    // u8 -> Point -> String (通过 i32)
    let point: FromIntoPoint = 42i32.into();
    let string = format!("Point: {:?}", point);
    println!("Chain result: {}", string);

    // 元组 -> Point -> 字符串表示
    let tuple = (10, 20);
    let point: FromIntoPoint = tuple.into();
    let representation = format!("({}, {})", point.x, point.y);
    println!("Representation: {}", representation);
}

// 函数参数转换演示
fn demonstrate_function_conversions() {
    fn process_point<P: Into<FromIntoPoint>>(point: P) {
        let point = point.into();
        println!("Processing point: {:?}", point);
    }

    fn process_example<E: Into<FromIntoExample>>(example: E) {
        let example = example.into();
        println!("Processing example: {:?}", example);
    }

    fn process_status<S: Into<FromIntoStatus>>(status: S) {
        let status = status.into();
        println!("Processing status: {:?}", status);
    }

    // 使用不同类型的参数
    process_point((1, 2));
    process_point([3, 4]);
    process_point(5);

    process_example(("Alice".to_string(), 42, true));
    process_example(("Bob", 100));
    process_example("Charlie".to_string());

    process_status("Error message".to_string());
    process_status("Another error");
    process_status(0);
    process_status(1);
}

// 错误处理示例
#[derive(Debug)]
pub struct CustomError {
    pub message: String,
    pub code: i32,
}

impl From<String> for CustomError {
    fn from(message: String) -> Self {
        CustomError { message, code: -1 }
    }
}

impl From<&str> for CustomError {
    fn from(message: &str) -> Self {
        CustomError {
            message: message.to_string(),
            code: -1,
        }
    }
}

impl From<i32> for CustomError {
    fn from(code: i32) -> Self {
        CustomError {
            message: format!("Error with code: {}", code),
            code,
        }
    }
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_from_tuple() {
        let point = FromIntoPoint::from((1, 2));
        assert_eq!(point.x, 1);
        assert_eq!(point.y, 2);
    }

    #[test]
    fn test_point_from_array() {
        let point = FromIntoPoint::from([3, 4]);
        assert_eq!(point.x, 3);
        assert_eq!(point.y, 4);
    }

    #[test]
    fn test_point_from_value() {
        let point = FromIntoPoint::from(5);
        assert_eq!(point.x, 5);
        assert_eq!(point.y, 5);
    }

    #[test]
    fn test_example_from_tuple() {
        let example = FromIntoExample::from(("Test".to_string(), 100, true));
        assert_eq!(example.name, "Test");
        assert_eq!(example.value, 100);
        assert_eq!(example.active, true);
    }

    #[test]
    fn test_status_from_string() {
        let status = FromIntoStatus::from("Error message");
        match status {
            FromIntoStatus::Error(msg) => assert_eq!(msg, "Error message"),
            _ => panic!("Expected Error variant"),
        }
    }

    #[test]
    fn test_status_from_code() {
        let status = FromIntoStatus::from(0);
        assert!(matches!(status, FromIntoStatus::Idle));

        let status = FromIntoStatus::from(1);
        assert!(matches!(status, FromIntoStatus::Active));
    }

    #[test]
    fn test_into_conversion() {
        let tuple = (10, 20);
        let point: FromIntoPoint = tuple.into();
        assert_eq!(point.x, 10);
        assert_eq!(point.y, 20);
    }
}
