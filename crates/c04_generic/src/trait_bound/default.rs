/*
Default trait 是 Rust 中用于提供默认值的重要特征。
它定义了 `default` 方法，允许类型提供合理的默认实例。

## 定义

Default trait 定义了一个 `default` 方法，用于创建默认值：

```rust
pub trait Default {
    fn default() -> Self;
}
```

## 重要特性

1. **默认值**: 提供类型的合理默认实例
2. **自动派生**: 可以通过 `#[derive(Default)]` 自动实现
3. **零成本**: 默认实现通常是零成本的
4. **一致性**: 为类型系统提供一致的默认值机制

## 实现示例

### 1. 基本结构体实现 Default

```rust
#[derive(Default)]
struct Config {
    timeout: u64,
    retries: u32,
    debug: bool,
}

// 手动实现 Default
impl Default for Config {
    fn default() -> Self {
        Config {
            timeout: 30,
            retries: 3,
            debug: false,
        }
    }
}
```

### 2. 泛型结构体实现 Default

```rust
#[derive(Default)]
struct Container<T: Default> {
    value: T,
    count: usize,
}

// 手动实现
impl<T: Default> Default for Container<T> {
    fn default() -> Self {
        Container {
            value: T::default(),
            count: 0,
        }
    }
}
```

### 3. 枚举实现 Default

```rust
#[derive(Default)]
enum Status {
    #[default]
    Idle,
    Active,
    Error,
}

// 手动实现
impl Default for Status {
    fn default() -> Self {
        Status::Idle
    }
}
```

## 使用场景

### 1. 基本默认值

```rust
fn main() {
    let config = Config::default();
    println!("Default config: {:?}", config);

    // 部分使用默认值
    let custom_config = Config {
        timeout: 60,
        ..Config::default()
    };
}
```

### 2. 集合初始化

```rust
fn main() {
    let mut vec: Vec<i32> = Vec::default();
    vec.push(1);
    vec.push(2);

    let mut map: HashMap<String, i32> = HashMap::default();
    map.insert("key".to_string(), 42);
}
```

### 3. 泛型函数

```rust
fn create_container<T: Default>() -> Container<T> {
    Container::default()
}

fn main() {
    let int_container = create_container::<i32>();
    let string_container = create_container::<String>();
}
```

## 标准库中的 Default

### 1. 数值类型

```rust
assert_eq!(i32::default(), 0);
assert_eq!(f64::default(), 0.0);
assert_eq!(bool::default(), false);
```

### 2. 集合类型

```rust
assert_eq!(Vec::<i32>::default(), vec![]);
assert_eq!(String::default(), "");
assert_eq!(HashMap::<String, i32>::default(), HashMap::new());
```

### 3. Option 和 Result

```rust
assert_eq!(Option::<i32>::default(), None);
// Result 没有实现 Default，因为错误类型不确定
```

## 性能考虑

1. **零成本**: Default 实现通常是零成本的
2. **编译时优化**: 编译器可以优化默认值的使用
3. **内存效率**: 避免不必要的内存分配
4. **缓存友好**: 默认值可以预计算和缓存

## 最佳实践

1. **合理默认值**: 提供有意义的默认值
2. **一致性**: 保持默认值的一致性
3. **文档化**: 明确说明默认值的含义
4. **测试**: 为默认值编写测试

## 高级用法

### 1. 条件默认值

```rust
impl Default for Config {
    fn default() -> Self {
        let debug = cfg!(debug_assertions);
        Config {
            timeout: if debug { 10 } else { 30 },
            retries: if debug { 1 } else { 3 },
            debug,
        }
    }
}
```

### 2. 环境相关默认值

```rust
impl Default for DatabaseConfig {
    fn default() -> Self {
        DatabaseConfig {
            host: std::env::var("DB_HOST").unwrap_or_else(|_| "localhost".to_string()),
            port: std::env::var("DB_PORT").unwrap_or_else(|_| "5432".to_string()),
            database: std::env::var("DB_NAME").unwrap_or_else(|_| "app".to_string()),
        }
    }
}
```

### 3. 组合默认值

```rust
impl Default for ComplexConfig {
    fn default() -> Self {
        ComplexConfig {
            basic: Config::default(),
            advanced: AdvancedConfig::default(),
            custom: CustomConfig::default(),
        }
    }
}
```

## 总结

Default trait 为 Rust 提供了统一的默认值机制。
通过正确实现 Default，可以创建更易用和一致的 API，
同时保持零成本抽象的优势。
*/

// 示例结构体
#[derive(Debug)]
pub struct DefaultExample {
    pub name: String,
    pub count: u32,
    pub active: bool,
}

impl Default for DefaultExample {
    fn default() -> Self {
        DefaultExample {
            name: String::from("Default Name"),
            count: 0,
            active: false,
        }
    }
}

// 泛型容器
#[derive(Debug)]
pub struct DefaultContainer<T: Default> {
    pub value: T,
    pub metadata: String,
}

impl<T: Default> Default for DefaultContainer<T> {
    fn default() -> Self {
        DefaultContainer {
            value: T::default(),
            metadata: String::from("Default metadata"),
        }
    }
}

// 配置结构体
#[derive(Debug)]
pub struct Config {
    pub timeout: u64,
    pub retries: u32,
    pub debug: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            timeout: 30,
            retries: 3,
            debug: false,
        }
    }
}

// 状态枚举
#[derive(Debug, Default)]
pub enum DefaultStatus {
    #[default]
    Idle,
    Active,
    Error,
}

// 演示函数
pub fn demonstrate_default() {
    // 基本默认值
    let example = DefaultExample::default();
    println!("Default example: {:?}", example);

    // 部分使用默认值
    let custom_example = DefaultExample {
        name: String::from("Custom Name"),
        ..DefaultExample::default()
    };
    println!("Custom example: {:?}", custom_example);

    // 泛型容器默认值
    let int_container = DefaultContainer::<i32>::default();
    let string_container = DefaultContainer::<String>::default();

    println!("Int container: {:?}", int_container);
    println!("String container: {:?}", string_container);

    // 配置默认值
    let config = Config::default();
    println!("Default config: {:?}", config);

    let debug_config = Config {
        debug: true,
        ..Config::default()
    };
    println!("Debug config: {:?}", debug_config);

    // 枚举默认值
    let status = DefaultStatus::default();
    println!("Default status: {:?}", status);

    // 集合默认值
    let vec: Vec<i32> = vec![1, 2];
    println!("Vector: {:?}", vec);

    let mut map: std::collections::HashMap<String, i32> = std::collections::HashMap::default();
    map.insert("key".to_string(), 42);
    println!("HashMap: {:?}", map);
}

// 泛型函数示例
pub fn create_default_container<T: Default>() -> DefaultContainer<T> {
    DefaultContainer::default()
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_example() {
        let default = DefaultExample::default();
        assert_eq!(default.name, "Default Name");
        assert_eq!(default.count, 0);
        assert_eq!(default.active, false);
    }

    #[test]
    fn test_config_default() {
        let config = Config::default();
        assert_eq!(config.timeout, 30);
        assert_eq!(config.retries, 3);
        assert_eq!(config.debug, false);
    }

    #[test]
    fn test_status_default() {
        let status = DefaultStatus::default();
        assert!(matches!(status, DefaultStatus::Idle));
    }

    #[test]
    fn test_container_default() {
        let container = DefaultContainer::<i32>::default();
        assert_eq!(container.value, 0);
        assert_eq!(container.metadata, "Default metadata");
    }
}
