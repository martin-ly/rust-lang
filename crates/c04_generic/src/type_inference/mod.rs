/*
在Rust中，**类型推断（type inference）**是指编译器在没有显式指定类型的情况下，
自动推断出变量或表达式的类型的能力。
Rust的类型系统是静态的，这意味着所有类型在编译时都必须是已知的。
类型推断使得代码更加简洁，减少了开发者的负担，因为开发者不需要在每个地方都显式地指定类型。

## 定义

- **类型推断**：
类型推断是Rust编译器根据上下文自动确定变量、函数参数和返回值类型的过程。
通过类型推断，Rust能够在不显式声明类型的情况下，推导出正确的类型。

## 重要特性

类型推断的主要特点包括：

1. **上下文依赖**：
编译器根据变量的使用上下文来推断类型。
例如，如果一个变量被赋值为一个整数，编译器会推断该变量的类型为`i32`（默认整数类型）。
2. **局部推断**：
类型推断通常在局部范围内进行，编译器会根据当前作用域内的上下文信息来推断类型。
3. **减少冗余**：
通过类型推断，开发者可以编写更简洁的代码，避免重复的类型声明。
4. **类型安全**：
编译时类型检查，确保类型正确性。
5. **零成本抽象**：
编译时优化，无运行时开销。

## 基本示例

以下是一个使用类型推断的基本示例：

```rust
fn main() {
    // 类型推断：编译器推断x为i32
    let x = 5; // x的类型被推断为i32

    // 类型推断：编译器推断y为f64
    let y = 3.14; // y的类型被推断为f64

    // 类型推断：编译器推断s为String
    let s = String::from("Hello, Rust!"); // s的类型被推断为String

    // 使用类型推断的变量
    println!("x: {}, y: {}, s: {}", x, y, s);

    // 显式指定类型
    let z: i32 = 10; // z的类型被显式指定为i32
    println!("z: {}", z);
}
```

## 高级示例

### 1. 泛型函数中的类型推断

```rust
// 定义一个泛型函数，使用类型推断
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

fn main() {
    let result = add(5, 10); // 类型推断：result的类型被推断为i32
    println!("Result: {}", result); // 输出: Result: 15
}
```

### 2. 闭包中的类型推断

```rust
fn main() {
    // 闭包类型推断
    let add_one = |x| x + 1; // 类型推断：x和返回值的类型被推断为i32

    let result = add_one(5);
    println!("Result: {}", result); // 输出: Result: 6

    // 带类型的闭包
    let multiply: fn(i32, i32) -> i32 = |a, b| a * b;
    let product = multiply(3, 4);
    println!("Product: {}", product); // 输出: Product: 12
}
```

### 3. 迭代器中的类型推断

```rust
fn main() {
    let numbers = [1, 2, 3, 4, 5];

    // 迭代器类型推断
    let doubled: Vec<i32> = numbers.iter()
        .map(|&x| x * 2) // 类型推断：x的类型被推断为i32
        .collect();

    println!("Doubled: {:?}", doubled); // 输出: Doubled: [2, 4, 6, 8, 10]

    // 过滤和映射
    let filtered: Vec<i32> = numbers.iter()
        .filter(|&&x| x > 2) // 类型推断：x的类型被推断为i32
        .map(|&x| x * 3)     // 类型推断：x的类型被推断为i32
        .collect();

    println!("Filtered and tripled: {:?}", filtered); // 输出: Filtered and tripled: [9, 12, 15]
}
```

## 使用场景

### 1. 变量声明

```rust
fn main() {
    // 基本类型推断
    let integer = 42;           // 推断为 i32
    let float = std::f64::consts::PI;           // 推断为 f64
    let boolean = true;         // 推断为 bool
    let character = 'a';        // 推断为 char
    let string = "hello";       // 推断为 &str
    let owned_string = String::from("world"); // 推断为 String

    // 数组类型推断
    let array = [1, 2, 3, 4, 5]; // 推断为 [i32; 5]
    let matrix = [[1, 2], [3, 4]]; // 推断为 [[i32; 2]; 2]

    // 向量类型推断
    let vector = [1, 2, 3]; // 推断为 [i32; 3]
    let string_vector = ["a", "b", "c"]; // 推断为 [&str; 3]
}
```

### 2. 函数参数和返回值

```rust
// 参数类型推断
fn process_numbers(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}

fn main() {
    let data = vec![1, 2, 3, 4, 5];
    let sum = process_numbers(&data); // 类型推断：data的类型被推断为Vec<i32>
    println!("Sum: {}", sum);
}

// 返回类型推断
fn create_counter() -> impl FnMut() -> i32 {
    let mut count = 0;
    move || {
        count += 1;
        count
    }
}

fn main() {
    let mut counter = create_counter();
    println!("Count: {}", counter()); // 输出: Count: 1
    println!("Count: {}", counter()); // 输出: Count: 2
}
```

### 3. 泛型结构体

```rust
struct Container<T> {
    items: Vec<T>,
}

impl<T> Container<T> {
    fn new() -> Self {
        Container { items: Vec::new() }
    }

    fn add(&mut self, item: T) {
        self.items.push(item);
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }
}

fn main() {
    let mut container = Container::new(); // 类型推断：T的类型被推断为i32
    container.add(42);

    if let Some(item) = container.get(0) {
        println!("Item: {}", item);
    }
}
```

## 高级用法

### 1. 关联类型推断

```rust
trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
}

struct NumberIterator {
    current: i32,
    max: i32,
}

impl Iterator for NumberIterator {
    type Item = i32; // 关联类型

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.max {
            let result = self.current;
            self.current += 1;
            Some(result)
        } else {
            None
        }
    }
}

fn main() {
    let mut iterator = NumberIterator { current: 1, max: 4 };

    // 类型推断：item的类型被推断为i32
    while let Some(item) = iterator.next() {
        println!("Item: {}", item);
    }
}
```

### 2. 生命周期推断

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = "short";
    let string2 = "longer";

    // 生命周期推断：'a被推断为string1和string2的生命周期
    let result = longest(string1, string2);
    println!("Longest: {}", result);
}
```

### 3. 类型约束推断

```rust
fn find_max<T>(items: &[T]) -> Option<&T>
where
    T: PartialOrd,
{
    items.iter().max_by(|a, b| a.partial_cmp(b).unwrap())
}

fn main() {
    let numbers = vec![3, 1, 4, 1, 5];

    // 类型推断：T被推断为i32，约束PartialOrd被自动推断
    if let Some(max) = find_max(&numbers) {
        println!("Maximum: {}", max);
    }
}
```

## 性能考虑

1. **零成本抽象**: 类型推断在编译时完成，无运行时开销
2. **编译时间**: 复杂的类型推断可能增加编译时间
3. **内存使用**: 不影响运行时内存使用
4. **优化**: 编译器可以根据推断的类型进行优化

## 最佳实践

1. **明确性**: 在类型不明确时显式指定类型
2. **一致性**: 保持代码中类型推断的一致性
3. **文档**: 为复杂的泛型函数添加类型注释
4. **测试**: 测试不同类型组合的类型推断

## 总结

类型推断是Rust编译器的一项重要特性，使得代码更加简洁和易于阅读。
通过自动推断类型，开发者可以减少冗余的类型声明，同时保持类型安全。
理解类型推断的工作原理对于编写高效和清晰的Rust代码至关重要。

类型推断在泛型编程中特别有用，它允许编译器自动推导出泛型参数的具体类型，
减少了显式类型注解的需要，使代码更加简洁和易读。
*/

// 基本类型推断示例
pub fn demonstrate_basic_inference() {
    println!("=== Basic Type Inference Demo ===\n");

    // 基本类型推断
    let integer = 42; // 推断为 i32
    let float = std::f64::consts::PI; // 推断为 f64
    let boolean = true; // 推断为 bool
    let character = 'a'; // 推断为 char
    let string = "hello"; // 推断为 &str
    let owned_string = String::from("world"); // 推断为 String

    println!("Integer: {} (type: i32)", integer);
    println!("Float: {} (type: f64)", float);
    println!("Boolean: {} (type: bool)", boolean);
    println!("Character: {} (type: char)", character);
    println!("String slice: {} (type: &str)", string);
    println!("Owned string: {} (type: String)", owned_string);

    // 数组类型推断
    let array = [1, 2, 3, 4, 5]; // 推断为 [i32; 5]
    let matrix = [[1, 2], [3, 4]]; // 推断为 [[i32; 2]; 2]

    println!("Array: {:?} (type: [i32; 5])", array);
    println!("Matrix: {:?} (type: [[i32; 2]; 2])", matrix);

    // 向量类型推断
    let vector = [1, 2, 3]; // 推断为 [i32; 3]
    let string_vector = ["a", "b", "c"]; // 推断为 [&str; 3]

    println!("Vector: {:?} (type: [i32; 3])", vector);
    println!("String vector: {:?} (type: [&str; 3])", string_vector);
    println!();
}

// 泛型函数中的类型推断
pub fn add<T: std::ops::Add<Output = T> + Copy>(a: T, b: T) -> T {
    a + b
}

pub fn multiply<T: std::ops::Mul<Output = T> + Copy>(a: T, b: T) -> T {
    a * b
}

pub fn demonstrate_generic_inference() {
    println!("--- Generic Function Inference Demo ---");

    // 整数类型推断
    let int_result = add(5, 10); // 类型推断：T被推断为i32
    println!("Integer addition: 5 + 10 = {} (type: i32)", int_result);

    // 浮点数类型推断
    let float_result = add(std::f64::consts::PI, 2.86); // 类型推断：T被推断为f64
    println!("Float addition: 3.14 + 2.86 = {} (type: f64)", float_result);

    // 乘法类型推断
    let product = multiply(6, 7); // 类型推断：T被推断为i32
    println!("Integer multiplication: 6 * 7 = {} (type: i32)", product);

    let float_product = multiply(2.5, 3.0); // 类型推断：T被推断为f64
    println!(
        "Float multiplication: 2.5 * 3.0 = {} (type: f64)",
        float_product
    );
    println!();
}

// 闭包中的类型推断
pub fn demonstrate_closure_inference() {
    println!("--- Closure Inference Demo ---");

    // 基本闭包类型推断
    let add_one = |x| x + 1; // 类型推断：x和返回值的类型被推断为i32
    let result = add_one(5);
    println!("Add one: 5 + 1 = {} (type: i32)", result);

    // 带类型的闭包
    let multiply: fn(i32, i32) -> i32 = |a, b| a * b;
    let product = multiply(3, 4);
    println!("Multiply: 3 * 4 = {} (type: i32)", product);

    // 复杂闭包类型推断
    let process_numbers = |numbers: &[i32]| {
        numbers
            .iter()
            .filter(|&&x| x > 2)
            .map(|&x| x * 2)
            .collect::<Vec<i32>>()
    };

    let numbers = vec![1, 2, 3, 4, 5];
    let processed = process_numbers(&numbers);
    println!("Processed numbers: {:?} (type: Vec<i32>)", processed);
    println!();
}

// 迭代器中的类型推断
pub fn demonstrate_iterator_inference() {
    println!("--- Iterator Inference Demo ---");

    let numbers = [1, 2, 3, 4, 5];

    // 基本迭代器类型推断
    let doubled: Vec<i32> = numbers
        .iter()
        .map(|&x| x * 2) // 类型推断：x的类型被推断为i32
        .collect();

    println!("Doubled: {:?} (type: Vec<i32>)", doubled);

    // 过滤和映射
    let filtered: Vec<i32> = numbers
        .iter()
        .filter(|&&x| x > 2) // 类型推断：x的类型被推断为i32
        .map(|&x| x * 3) // 类型推断：x的类型被推断为i32
        .collect();

    println!("Filtered and tripled: {:?} (type: Vec<i32>)", filtered);

    // 链式操作
    let result: Vec<i32> = numbers
        .iter()
        .enumerate()
        .filter(|(i, x)| i % 2 == 0 && **x > 1)
        .map(|(_, x)| x * x)
        .collect();

    println!("Complex transformation: {:?} (type: Vec<i32>)", result);
    println!();
}

// 泛型结构体中的类型推断
pub struct Container<T> {
    items: Vec<T>,
}

impl<T> Container<T> {
    pub fn new() -> Self {
        Container { items: Vec::new() }
    }

    pub fn add(&mut self, item: T) {
        self.items.push(item);
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<T> Default for Container<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub fn demonstrate_struct_inference() {
    println!("--- Struct Inference Demo ---");

    let mut container = Container::new(); // 类型推断：T的类型被推断为i32
    container.add(42);
    container.add(100);

    println!("Container length: {} (type: usize)", container.len());

    if let Some(item) = container.get(0) {
        println!("First item: {} (type: i32)", item);
    }

    // 字符串容器
    let mut string_container = Container::new(); // 类型推断：T的类型被推断为String
    string_container.add("hello".to_string());
    string_container.add("world".to_string());

    println!(
        "String container length: {} (type: usize)",
        string_container.len()
    );

    if let Some(item) = string_container.get(0) {
        println!("First string: {} (type: String)", item);
    }
    println!();
}

// 关联类型推断
pub trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn count(&self) -> usize;
}

pub struct NumberIterator {
    current: i32,
    max: i32,
}

impl Iterator for NumberIterator {
    type Item = i32; // 关联类型

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.max {
            let result = self.current;
            self.current += 1;
            Some(result)
        } else {
            None
        }
    }

    fn count(&self) -> usize {
        (self.max - self.current) as usize
    }
}

pub fn demonstrate_associated_type_inference() {
    println!("--- Associated Type Inference Demo ---");

    let mut iterator = NumberIterator { current: 1, max: 4 };

    // 类型推断：item的类型被推断为i32（来自关联类型Item）
    while let Some(item) = iterator.next() {
        println!("Item: {} (type: i32)", item);
    }

    println!("Remaining count: {} (type: usize)", iterator.count());
    println!();
}

// 生命周期推断
pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

pub fn demonstrate_lifetime_inference() {
    println!("--- Lifetime Inference Demo ---");

    let string1 = "short";
    let string2 = "longer";

    // 生命周期推断：'a被推断为string1和string2的生命周期
    let result = longest(string1, string2);
    println!("Longest: {} (lifetime inferred)", result);

    // 嵌套作用域中的生命周期
    {
        let inner_string = "very long string";
        let result = longest(string1, inner_string);
        println!("Longest in inner scope: {} (lifetime inferred)", result);
    }
    println!();
}

// 类型约束推断
pub fn find_max<T>(items: &[T]) -> Option<&T>
where
    T: PartialOrd,
{
    items.iter().max_by(|a, b| a.partial_cmp(b).unwrap())
}

pub fn sort_items<T>(items: &mut [T])
where
    T: Ord,
{
    items.sort();
}

pub fn demonstrate_constraint_inference() {
    println!("--- Constraint Inference Demo ---");

    let numbers = vec![3, 1, 4, 1, 5];

    // 类型推断：T被推断为i32，约束PartialOrd被自动推断
    if let Some(max) = find_max(&numbers) {
        println!("Maximum: {} (type: i32, constraint: PartialOrd)", max);
    }

    let mut numbers_to_sort = numbers.clone();
    // 类型推断：T被推断为i32，约束Ord被自动推断
    sort_items(&mut numbers_to_sort);
    println!(
        "Sorted: {:?} (type: Vec<i32>, constraint: Ord)",
        numbers_to_sort
    );
    println!();
}

// 主演示函数
pub fn demonstrate_type_inference() {
    println!("=== Type Inference Demonstration ===\n");

    // 基本类型推断演示
    demonstrate_basic_inference();

    // 泛型函数类型推断演示
    demonstrate_generic_inference();

    // 闭包类型推断演示
    demonstrate_closure_inference();

    // 迭代器类型推断演示
    demonstrate_iterator_inference();

    // 结构体类型推断演示
    demonstrate_struct_inference();

    // 关联类型推断演示
    demonstrate_associated_type_inference();

    // 生命周期推断演示
    demonstrate_lifetime_inference();

    // 类型约束推断演示
    demonstrate_constraint_inference();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_inference() {
        let result = add(5, 10);
        assert_eq!(result, 15);
    }

    #[test]
    fn test_multiply_inference() {
        let result = multiply(3, 4);
        assert_eq!(result, 12);
    }

    #[test]
    fn test_container_inference() {
        let mut container = Container::new();
        container.add(42);
        container.add(100);

        assert_eq!(container.len(), 2);
        assert_eq!(*container.get(0).unwrap(), 42);
        assert_eq!(*container.get(1).unwrap(), 100);
    }

    #[test]
    fn test_number_iterator() {
        let mut iterator = NumberIterator { current: 1, max: 4 };

        assert_eq!(iterator.next(), Some(1));
        assert_eq!(iterator.next(), Some(2));
        assert_eq!(iterator.next(), Some(3));
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.count(), 0);
    }

    #[test]
    fn test_find_max() {
        let numbers = vec![3, 1, 4, 1, 5];
        let max = find_max(&numbers);
        assert_eq!(max, Some(&5));
    }

    #[test]
    fn test_sort_items() {
        let mut numbers = vec![3, 1, 4, 1, 5];
        sort_items(&mut numbers);
        assert_eq!(numbers, vec![1, 1, 3, 4, 5]);
    }
}
