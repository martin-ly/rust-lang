/*
Copy trait 是 Rust 中用于实现值语义的重要特征。
当一个类型实现了 Copy trait 时，它在赋值或传递时会进行复制而不是移动。

## 定义

Copy trait 是一个标记特征，没有方法定义：

```rust
pub trait Copy: Clone { }
```

## 重要特性

1. **值语义**: 实现了 Copy 的类型在赋值时会被复制
2. **栈复制**: 复制操作在栈上进行，性能很高
3. **自动派生**: 可以通过 `#[derive(Copy)]` 自动实现
4. **Clone 依赖**: Copy 要求类型同时实现 Clone

## 实现条件

类型要实现 Copy trait，必须满足以下条件：

1. 所有字段都实现了 Copy
2. 类型大小在编译时确定
3. 类型不包含需要特殊清理的资源

## 实现示例

### 1. 基本类型实现 Copy

```rust
#[derive(Copy, Clone, Debug)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现（等同于 #[derive(Copy, Clone)]）
impl Copy for Point { }

impl Clone for Point {
    fn clone(&self) -> Self {
        *self
    }
}
```

### 2. 泛型类型实现 Copy

```rust
#[derive(Copy, Clone, Debug)]
struct Container<T: Copy> {
    value: T,
    count: u32,
}

impl<T: Copy> Copy for Container<T> { }

impl<T: Copy> Clone for Container<T> {
    fn clone(&self) -> Self {
        *self
    }
}
```

### 3. 枚举实现 Copy

```rust
#[derive(Copy, Clone, Debug)]
enum Status {
    Active,
    Inactive,
    Pending,
}

impl Copy for Status { }

impl Clone for Status {
    fn clone(&self) -> Self {
        *self
    }
}
```

## 使用场景

### 1. 基本赋值

```rust
fn main() {
    let point1 = Point { x: 10, y: 20 };
    let point2 = point1; // 复制，不是移动

    println!("Point1: {:?}", point1); // 仍然可用
    println!("Point2: {:?}", point2);
}
```

### 2. 函数参数

```rust
fn process_point(p: Point) -> Point {
    // 函数接收 p 的副本
    Point { x: p.x * 2, y: p.y * 2 }
}

fn main() {
    let original = Point { x: 5, y: 10 };
    let result = process_point(original);

    println!("Original: {:?}", original); // 仍然可用
    println!("Result: {:?}", result);
}
```

### 3. 集合操作

```rust
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];

    // 由于 i32 实现了 Copy，这里进行复制
    for num in numbers.iter() {
        println!("Number: {}", num);
    }

    // numbers 仍然可用
    println!("All numbers: {:?}", numbers);
}
```

## 性能考虑

1. **栈复制**: Copy 操作在栈上进行，性能很高
2. **内存效率**: 避免了堆分配和释放的开销
3. **大小限制**: 只适用于较小的数据类型
4. **避免大对象**: 大对象不应该实现 Copy

## 最佳实践

1. **小数据类型**: 为小的、简单的数据类型实现 Copy
2. **避免大对象**: 不要为包含大量数据或资源的类型实现 Copy
3. **组合使用**: 通常与 Clone 一起使用
4. **性能测试**: 在性能关键代码中测试 Copy vs Clone 的影响

## 常见实现 Copy 的类型

- 基本数值类型: `i32`, `u32`, `f64`, `bool`, `char`
- 固定大小数组: `[T; N]` (当 T: Copy)
- 元组: `(T1, T2, ...)` (当所有元素都实现 Copy)
- 引用: `&T` (引用本身是可复制的)

## 总结

Copy trait 为 Rust 提供了高效的值语义支持。
通过正确实现 Copy，可以创建性能优异的代码，
但需要注意只适用于适合复制的数据类型。
*/

// 示例结构体
#[derive(Debug)]
pub struct CopyExample {
    pub x: i32,
    pub y: i32,
}

impl Copy for CopyExample {}

impl Clone for CopyExample {
    fn clone(&self) -> Self {
        *self
    }
}

// 泛型容器
#[derive(Debug)]
pub struct CopyContainer<T: Copy> {
    pub value: T,
    pub flag: bool,
}

impl<T: Copy> Copy for CopyContainer<T> {}

impl<T: Copy> Clone for CopyContainer<T> {
    fn clone(&self) -> Self {
        *self
    }
}

// 状态枚举
#[derive(Debug)]
pub enum CopyStatus {
    Ready,
    Processing,
    Complete,
}

impl Copy for CopyStatus {}

impl Clone for CopyStatus {
    fn clone(&self) -> Self {
        *self
    }
}

// 演示函数
pub fn demonstrate_copy() {
    // 基本复制
    let point1 = CopyExample { x: 10, y: 20 };
    let point2 = point1; // 复制操作

    println!("Point1: {:?}", point1); // 仍然可用
    println!("Point2: {:?}", point2);

    // 泛型容器复制
    let container1 = CopyContainer {
        value: 42,
        flag: true,
    };
    let container2 = container1; // 复制操作

    println!("Container1: {:?}", container1); // 仍然可用
    println!("Container2: {:?}", container2);

    // 枚举复制
    let status1 = CopyStatus::Ready;
    let status2 = status1; // 复制操作

    println!("Status1: {:?}", status1); // 仍然可用
    println!("Status2: {:?}", status2);

    // 函数参数复制
    let result = process_copy_example(point1);
    println!("Processed result: {:?}", result);
}

// 处理 Copy 类型的函数
fn process_copy_example(p: CopyExample) -> CopyExample {
    CopyExample {
        x: p.x * 2,
        y: p.y * 2,
    }
}
