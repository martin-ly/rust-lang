/*
Clone trait 是 Rust 中用于创建值副本的重要特征。
它定义了 `clone` 方法，允许创建数据的深度副本。

## 定义

Clone trait 定义了一个 `clone` 方法，用于创建值的副本：

```rust
pub trait Clone: Sized {
    fn clone(&self) -> Self;
    fn clone_from(&mut self, source: &Self) { ... }
}
```

## 实现示例

### 1. 基本结构体实现 Clone

```rust
#[derive(Clone)]
struct Person {
    name: String,
    age: u32,
}

// 手动实现 Clone（等同于 #[derive(Clone)]）
impl Clone for Person {
    fn clone(&self) -> Self {
        Person {
            name: self.name.clone(),
            age: self.age,
        }
    }
}
```

### 2. 泛型结构体实现 Clone

```rust
#[derive(Clone)]
struct Container<T: Clone> {
    value: T,
    count: usize,
}

// 手动实现
impl<T: Clone> Clone for Container<T> {
    fn clone(&self) -> Self {
        Container {
            value: self.value.clone(),
            count: self.count,
        }
    }
}
```

### 3. 枚举实现 Clone

```rust
#[derive(Clone)]
enum Message {
    Text(String),
    Number(i32),
    Empty,
}

// 手动实现
impl Clone for Message {
    fn clone(&self) -> Self {
        match self {
            Message::Text(s) => Message::Text(s.clone()),
            Message::Number(n) => Message::Number(*n),
            Message::Empty => Message::Empty,
        }
    }
}
```

## 使用场景

### 1. 数据复制

```rust
fn main() {
    let original = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let cloned = original.clone();
    println!("Original: {:?}", original);
    println!("Cloned: {:?}", cloned);
}
```

### 2. 集合操作

```rust
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let numbers_copy = numbers.clone();

    // 现在可以同时使用两个集合
    println!("Original: {:?}", numbers);
    println!("Copy: {:?}", numbers_copy);
}
```

### 3. 函数参数

```rust
fn process_data<T: Clone>(data: T) -> (T, T) {
    let copy = data.clone();
    (data, copy)
}

fn main() {
    let result = process_data(String::from("hello"));
    println!("Result: {:?}", result);
}
```

## 性能考虑

1. **深度复制**: Clone 通常进行深度复制，可能影响性能
2. **引用类型**: 对于包含引用的类型，需要确保引用的数据也是可克隆的
3. **自定义实现**: 可以为特定类型提供优化的 Clone 实现

## 最佳实践

1. **优先使用 derive**: 对于简单类型，使用 `#[derive(Clone)]`
2. **手动实现**: 对于复杂类型，考虑手动实现以优化性能
3. **约束传播**: 在泛型类型中正确传播 Clone 约束
4. **避免不必要的克隆**: 只在确实需要副本时才调用 clone

## 总结

Clone trait 是 Rust 中实现数据复制的基础特征。
通过正确实现 Clone，可以创建灵活且安全的代码，
同时需要注意性能影响和正确性。
*/

// 示例结构体
#[derive(Debug)]
pub struct CloneExample {
    pub data: String,
    pub count: usize,
}

impl Clone for CloneExample {
    fn clone(&self) -> Self {
        CloneExample {
            data: self.data.clone(),
            count: self.count,
        }
    }
}

// 泛型容器
#[derive(Debug)]
pub struct GenericContainer<T: Clone> {
    pub value: T,
    pub metadata: String,
}

impl<T: Clone> Clone for GenericContainer<T> {
    fn clone(&self) -> Self {
        GenericContainer {
            value: self.value.clone(),
            metadata: self.metadata.clone(),
        }
    }
}

// 演示函数
pub fn demonstrate_clone() {
    // 基本克隆
    let original = CloneExample {
        data: String::from("Hello, Clone!"),
        count: 42,
    };

    let cloned = original.clone();
    println!("Original: {:?}", original);
    println!("Cloned: {:?}", cloned);

    // 泛型容器克隆
    let container = GenericContainer {
        value: vec![1, 2, 3],
        metadata: String::from("Vector container"),
    };

    let container_clone = container.clone();
    println!("Container: {:?}", container);
    println!("Container clone: {:?}", container_clone);
}
