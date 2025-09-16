/*
Debug trait 是 Rust 中用于调试输出的重要特征。
它定义了 `fmt` 方法，允许类型以可读的格式进行调试输出。

## 定义

Debug trait 定义了一个 `fmt` 方法，用于格式化调试输出：

```rust
pub trait Debug {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}
```

## 重要特性

1. **调试输出**: 提供人类可读的调试信息
2. **自动派生**: 可以通过 `#[derive(Debug)]` 自动实现
3. **格式化控制**: 支持不同的格式化选项
4. **错误处理**: 返回 Result 类型处理格式化错误

## 实现示例

### 1. 基本结构体实现 Debug

```rust
#[derive(Debug)]
struct Person {
    name: String,
    age: u32,
}

// 手动实现 Debug
impl std::fmt::Debug for Person {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Person")
            .field("name", &self.name)
            .field("age", &self.age)
            .finish()
    }
}
```

### 2. 泛型结构体实现 Debug

```rust
#[derive(Debug)]
struct Container<T: std::fmt::Debug> {
    value: T,
    count: usize,
}

// 手动实现
impl<T: std::fmt::Debug> std::fmt::Debug for Container<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Container")
            .field("value", &self.value)
            .field("count", &self.count)
            .finish()
    }
}
```

### 3. 枚举实现 Debug

```rust
#[derive(Debug)]
enum Message {
    Text(String),
    Number(i32),
    Empty,
}

// 手动实现
impl std::fmt::Debug for Message {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Message::Text(s) => f.debug_tuple("Text").field(s).finish(),
            Message::Number(n) => f.debug_tuple("Number").field(n).finish(),
            Message::Empty => f.debug_tuple("Empty").finish(),
        }
    }
}
```

## 使用场景

### 1. 基本调试输出

```rust
fn main() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };

    println!("Debug: {:?}", person);
    println!("Pretty debug: {:#?}", person);
}
```

### 2. 错误处理中的调试

```rust
fn process_data(data: &[i32]) -> Result<(), String> {
    if data.is_empty() {
        return Err(format!("Empty data: {:?}", data));
    }
    Ok(())
}
```

### 3. 测试中的调试输出

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_person_debug() {
        let person = Person {
            name: String::from("Bob"),
            age: 25,
        };

        let debug_str = format!("{:?}", person);
        assert!(debug_str.contains("Bob"));
        assert!(debug_str.contains("25"));
    }
}
```

## 格式化选项

### 1. 基本调试格式

```rust
println!("{:?}", value);      // 单行格式
println!("{:#?}", value);     // 多行格式
```

### 2. 宽度和精度控制

```rust
println!("{:10?}", value);    // 最小宽度10
println!("{:.3?}", value);    // 精度3
```

## 性能考虑

1. **编译时优化**: Debug 实现通常在编译时被优化
2. **条件编译**: 可以使用 `#[cfg(debug_assertions)]` 条件编译
3. **避免复杂计算**: Debug 实现应该避免复杂的计算逻辑
4. **内存分配**: 尽量减少不必要的字符串分配

## 最佳实践

1. **优先使用 derive**: 对于简单类型，使用 `#[derive(Debug)]`
2. **手动实现**: 对于复杂类型，考虑手动实现以提供更好的调试信息
3. **一致性**: 保持 Debug 输出的一致性和可读性
4. **安全性**: 避免在 Debug 输出中暴露敏感信息

## 高级用法

### 1. 自定义调试格式

```rust
impl std::fmt::Debug for CustomType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CustomType({})", self.internal_value)
    }
}
```

### 2. 条件调试信息

```rust
impl std::fmt::Debug for SensitiveData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(debug_assertions) {
            f.debug_struct("SensitiveData")
                .field("data", &self.data)
                .finish()
        } else {
            f.debug_struct("SensitiveData")
                .field("data", &"***")
                .finish()
        }
    }
}
```

## 总结

Debug trait 是 Rust 中实现调试输出的基础特征。
通过正确实现 Debug，可以创建易于调试和测试的代码，
同时需要注意性能影响和安全性考虑。
*/

// 示例结构体
#[derive(Debug)]
pub struct DebugExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

// 手动实现 Debug 的示例
pub struct ManualDebugExample {
    pub data: Vec<i32>,
    pub metadata: String,
}

impl std::fmt::Debug for ManualDebugExample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ManualDebugExample")
            .field("data", &self.data)
            .field("metadata", &self.metadata)
            .field("length", &self.data.len())
            .finish()
    }
}

// 泛型容器
#[derive(Debug)]
pub struct DebugContainer<T: std::fmt::Debug> {
    pub value: T,
    pub description: String,
}

// 状态枚举
#[derive(Debug)]
pub enum DebugStatus {
    Idle,
    Working { progress: f64 },
    Complete { result: String },
    Error { message: String },
}

// 演示函数
pub fn demonstrate_debug() {
    // 基本调试输出
    let example = DebugExample {
        name: String::from("Test Example"),
        value: 42,
        active: true,
    };

    println!("Basic debug: {:?}", example);
    println!("Pretty debug: {:#?}", example);

    // 手动实现的调试
    let manual = ManualDebugExample {
        data: vec![1, 2, 3, 4, 5],
        metadata: String::from("Sample data"),
    };

    println!("Manual debug: {:?}", manual);

    // 泛型容器调试
    let container = DebugContainer {
        value: vec![10, 20, 30],
        description: String::from("Number container"),
    };

    println!("Container debug: {:?}", container);

    // 枚举调试
    let status = DebugStatus::Working { progress: 0.75 };
    println!("Status debug: {:?}", status);

    let error_status = DebugStatus::Error {
        message: String::from("Something went wrong"),
    };
    println!("Error status: {:?}", error_status);
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_debug_example() {
        let example = DebugExample {
            name: String::from("Test"),
            value: 100,
            active: false,
        };

        let debug_str = format!("{:?}", example);
        assert!(debug_str.contains("Test"));
        assert!(debug_str.contains("100"));
        assert!(debug_str.contains("false"));
    }

    #[test]
    fn test_manual_debug() {
        let manual = ManualDebugExample {
            data: vec![1, 2, 3],
            metadata: String::from("Test metadata"),
        };

        let debug_str = format!("{:?}", manual);
        assert!(debug_str.contains("ManualDebugExample"));
        assert!(debug_str.contains("length"));
    }
}
