/*
Display trait 是 Rust 中用于用户友好输出的重要特征。
它定义了 `fmt` 方法，允许类型以人类可读的格式进行输出。

## 定义

Display trait 定义了一个 `fmt` 方法，用于格式化用户友好的输出：

```rust
pub trait Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}
```

## 重要特性

1. **用户友好**: 提供人类可读的输出格式
2. **手动实现**: 不能通过 derive 自动实现
3. **格式化控制**: 支持不同的格式化选项
4. **错误处理**: 返回 Result 类型处理格式化错误

## 实现示例

### 1. 基本结构体实现 Display

```rust
struct Point {
    x: i32,
    y: i32,
}

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}
```

### 2. 泛型结构体实现 Display

```rust
struct Container<T> {
    value: T,
    name: String,
}

impl<T: std::fmt::Display> std::fmt::Display for Container<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Container '{}' with value: {}", self.name, self.value)
    }
}
```

### 3. 枚举实现 Display

```rust
enum Status {
    Active,
    Inactive,
    Error(String),
}

impl std::fmt::Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Status::Active => write!(f, "Active"),
            Status::Inactive => write!(f, "Inactive"),
            Status::Error(msg) => write!(f, "Error: {}", msg),
        }
    }
}
```

## 使用场景

### 1. 基本输出

```rust
fn main() {
    let point = Point { x: 10, y: 20 };
    println!("Point: {}", point);
    println!("Point: {point}"); // 新的内联语法
}
```

### 2. 格式化选项

```rust
fn main() {
    let point = Point { x: 10, y: 20 };
    
    // 基本输出
    println!("{}", point);
    
    // 宽度控制
    println!("{:10}", point);
    
    // 左对齐
    println!("{:<10}", point);
    
    // 右对齐
    println!("{:>10}", point);
    
    // 居中对齐
    println!("{:^10}", point);
}
```

### 3. 错误处理

```rust
fn process_point(p: Point) -> Result<(), String> {
    if p.x < 0 || p.y < 0 {
        return Err(format!("Invalid point: {}", p));
    }
    Ok(())
}
```

## 与 Debug 的区别

### 1. 用途不同

- **Display**: 面向最终用户，提供友好的输出格式
- **Debug**: 面向开发者，提供详细的调试信息

### 2. 实现方式

- **Display**: 必须手动实现，不能 derive
- **Debug**: 可以通过 derive 自动实现

### 3. 输出格式

- **Display**: 简洁、用户友好
- **Debug**: 详细、技术性

## 性能考虑

1. **字符串分配**: 避免不必要的字符串分配
2. **格式化效率**: 使用高效的格式化方法
3. **内存使用**: 控制内存使用量
4. **缓存**: 考虑缓存常用的格式化结果

## 最佳实践

1. **用户友好**: 提供清晰、易懂的输出格式
2. **一致性**: 保持输出格式的一致性
3. **国际化**: 考虑多语言支持
4. **错误处理**: 正确处理格式化错误

## 高级用法

### 1. 条件格式化

```rust
impl std::fmt::Display for Config {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.debug {
            write!(f, "Config(debug: true, timeout: {}, retries: {})", 
                   self.timeout, self.retries)
        } else {
            write!(f, "Config(timeout: {}, retries: {})", 
                   self.timeout, self.retries)
        }
    }
}
```

### 2. 多行格式化

```rust
impl std::fmt::Display for ComplexData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Complex Data:")?;
        writeln!(f, "  Name: {}", self.name)?;
        writeln!(f, "  Value: {}", self.value)?;
        writeln!(f, "  Active: {}", self.active)
    }
}
```

### 3. 自定义分隔符

```rust
impl std::fmt::Display for List<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for item in &self.items {
            if !first {
                write!(f, " | ")?;
            }
            write!(f, "{}", item)?;
            first = false;
        }
        Ok(())
    }
}
```

## 总结

Display trait 为 Rust 提供了用户友好的输出机制。
通过正确实现 Display，可以创建更易用和专业的 API，
同时需要注意性能影响和用户体验。
*/

// 示例结构体
pub struct DisplayExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

impl std::fmt::Display for DisplayExample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (value: {}, active: {})", 
               self.name, self.value, self.active)
    }
}

// 泛型容器
pub struct DisplayContainer<T> {
    pub value: T,
    pub description: String,
}

impl<T: std::fmt::Display> std::fmt::Display for DisplayContainer<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Container '{}': {}", self.description, self.value)
    }
}

// 状态枚举
pub enum DisplayStatus {
    Idle,
    Working { progress: f64 },
    Complete { result: String },
    Error { message: String },
}

impl std::fmt::Display for DisplayStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DisplayStatus::Idle => write!(f, "Idle"),
            DisplayStatus::Working { progress } => {
                write!(f, "Working ({:.1}%)", progress * 100.0)
            }
            DisplayStatus::Complete { result } => {
                write!(f, "Complete: {}", result)
            }
            DisplayStatus::Error { message } => {
                write!(f, "Error: {}", message)
            }
        }
    }
}

// 几何点
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:.2}, {:.2})", self.x, self.y)
    }
}

// 演示函数
pub fn demonstrate_display() {
    // 基本显示
    let example = DisplayExample {
        name: String::from("Test Example"),
        value: 42,
        active: true,
    };
    
    println!("Example: {}", example);
    
    // 格式化选项
    println!("Example: {:20}", example);
    println!("Example: {:<20}", example);
    println!("Example: {:>20}", example);
    println!("Example: {:^20}", example);
    
    // 泛型容器显示
    let container = DisplayContainer {
        value: 100,
        description: String::from("Number container"),
    };
    
    println!("Container: {}", container);
    
    // 状态显示
    let status = DisplayStatus::Working { progress: 0.75 };
    println!("Status: {}", status);
    
    let error_status = DisplayStatus::Error {
        message: String::from("Something went wrong"),
    };
    println!("Error status: {}", error_status);
    
    // 几何点显示
    let point = Point { x: std::f64::consts::PI, y: std::f64::consts::E };
    println!("Point: {}", point);
    
    // 错误处理示例
    let result = process_display_example(example);
    match result {
        Ok(_) => println!("Processing successful"),
        Err(e) => println!("Processing failed: {}", e),
    }
}

// 处理函数
fn process_display_example(example: DisplayExample) -> Result<(), String> {
    if example.value < 0 {
        return Err(format!("Invalid value in example: {}", example));
    }
    Ok(())
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_display_example() {
        let example = DisplayExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };
        
        let display_str = format!("{}", example);
        assert!(display_str.contains("Test"));
        assert!(display_str.contains("100"));
        assert!(display_str.contains("false"));
    }
    
    #[test]
    fn test_point_display() {
        let point = Point { x: 1.5, y: 2.5 };
        let display_str = format!("{}", point);
        assert_eq!(display_str, "(1.50, 2.50)");
    }
    
    #[test]
    fn test_status_display() {
        let status = DisplayStatus::Working { progress: 0.5 };
        let display_str = format!("{}", status);
        assert!(display_str.contains("50.0%"));
    }
}
