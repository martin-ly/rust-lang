/*
在Rust中，**类型构造器（type constructor）**
是指用于创建新类型的泛型类型或结构体的机制。

类型构造器允许开发者定义可以接受类型参数的类型，从而实现代码的重用和灵活性。
通过使用类型构造器，开发者可以创建适用于多种类型的通用数据结构和函数。

## 定义

- **类型构造器**：
在Rust中，类型构造器是指那些可以接受类型参数并生成新类型的结构体、枚举或特征。
它们允许开发者定义泛型类型，使得同一代码可以处理多种不同类型的数据。

## 重要特性

类型构造器的主要特点包括：

1. **泛型类型**：
类型构造器通常是泛型类型，例如结构体或枚举，可以接受一个或多个类型参数。
2. **类型参数**：
类型参数是类型构造器的占位符，允许在实例化时指定具体的类型。
3. **灵活性和重用性**：
通过使用类型构造器，开发者可以编写更灵活和可重用的代码，避免重复定义相似的结构。
4. **类型安全**：
编译时类型检查，确保类型正确性。
5. **零成本抽象**：
编译时优化，无运行时开销。

## 基本示例

以下是一个使用类型构造器的基本示例：

```rust
// 定义一个泛型结构体
struct Pair<T, U> {
    first: T,
    second: U,
}

// 定义一个方法来创建Pair实例
impl<T, U> Pair<T, U> {
    fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }
}

// 定义一个方法来获取第一个元素
impl<T, U> Pair<T, U> {
    fn first(&self) -> &T {
        &self.first
    }
}

// 定义一个方法来获取第二个元素
impl<T, U> Pair<T, U> {
    fn second(&self) -> &U {
        &self.second
    }
}
```

## 高级示例

### 1. 泛型容器

```rust
struct Container<T> {
    items: Vec<T>,
    capacity: usize,
}

impl<T> Container<T> {
    fn new(capacity: usize) -> Self {
        Container {
            items: Vec::with_capacity(capacity),
            capacity,
        }
    }

    fn add(&mut self, item: T) -> bool {
        if self.items.len() < self.capacity {
            self.items.push(item);
            true
        } else {
            false
        }
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    fn len(&self) -> usize {
        self.items.len()
    }

    fn is_full(&self) -> bool {
        self.items.len() >= self.capacity
    }
}
```

### 2. 泛型算法

```rust
fn find_max<T>(items: &[T]) -> Option<&T>
where
    T: PartialOrd,
{
    items.iter().max_by(|a, b| a.partial_cmp(b).unwrap())
}

fn sort_items<T>(items: &mut [T])
where
    T: Ord,
{
    items.sort();
}

fn filter_items<T, F>(items: &[T], predicate: F) -> Vec<&T>
where
    F: Fn(&T) -> bool,
{
    items.iter().filter(|item| predicate(item)).collect()
}
```

### 3. 泛型特征

```rust
trait Processor<T> {
    fn process(&self, input: T) -> T;
    fn validate(&self, input: &T) -> bool;
}

struct StringProcessor;
struct NumberProcessor;

impl Processor<String> for StringProcessor {
    fn process(&self, input: String) -> String {
        input.to_uppercase()
    }

    fn validate(&self, input: &String) -> bool {
        !input.is_empty()
    }
}

impl Processor<i32> for NumberProcessor {
    fn process(&self, input: i32) -> i32 {
        input * 2
    }

    fn validate(&self, input: &i32) -> bool {
        *input > 0
    }
}
```

## 使用场景

### 1. 数据结构

```rust
struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Stack { items: Vec::new() }
    }

    fn push(&mut self, item: T) {
        self.items.push(item);
    }

    fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }

    fn peek(&self) -> Option<&T> {
        self.items.last()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

struct Queue<T> {
    items: Vec<T>,
}

impl<T> Queue<T> {
    fn new() -> Self {
        Queue { items: Vec::new() }
    }

    fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    fn dequeue(&mut self) -> Option<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    fn front(&self) -> Option<&T> {
        self.items.first()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}
```

### 2. 数学运算

```rust
trait Numeric {
    fn add(&self, other: &Self) -> Self;
    fn subtract(&self, other: &Self) -> Self;
    fn multiply(&self, other: &Self) -> Self;
    fn divide(&self, other: &Self) -> Option<Self>
    where
        Self: Sized;
}

impl Numeric for i32 {
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn subtract(&self, other: &Self) -> Self {
        self - other
    }

    fn multiply(&self, other: &Self) -> Self {
        self * other
    }

    fn divide(&self, other: &Self) -> Option<Self> {
        if *other == 0 {
            None
        } else {
            Some(self / other)
        }
    }
}

impl Numeric for f64 {
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn subtract(&self, other: &Self) -> Self {
        self - other
    }

    fn multiply(&self, other: &Self) -> Self {
        self * other
    }

    fn divide(&self, other: &Self) -> Option<Self> {
        if *other == 0.0 {
            None
        } else {
            Some(self / other)
        }
    }
}

fn calculate<T: Numeric + Clone>(a: &T, b: &T, operation: char) -> Option<T> {
    match operation {
        '+' => Some(a.add(b)),
        '-' => Some(a.subtract(b)),
        '*' => Some(a.multiply(b)),
        '/' => a.divide(b),
        _ => None,
    }
}
```

### 3. 序列化/反序列化

```rust
trait Serializable {
    fn serialize(&self) -> String;
    fn deserialize(data: &str) -> Option<Self>
    where
        Self: Sized;
}

struct DataContainer<T> {
    data: T,
    metadata: String,
}

impl<T> DataContainer<T> {
    fn new(data: T, metadata: String) -> Self {
        DataContainer { data, metadata }
    }

    fn get_data(&self) -> &T {
        &self.data
    }

    fn get_metadata(&self) -> &str {
        &self.metadata
    }
}

impl<T: std::fmt::Display> Serializable for DataContainer<T> {
    fn serialize(&self) -> String {
        format!("Data: {}, Metadata: {}", self.data, self.metadata)
    }

    fn deserialize(_data: &str) -> Option<Self> {
        // 这里可以实现实际的反序列化逻辑
        None
    }
}
```

## 高级用法

### 1. 关联类型

```rust
trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn count(&self) -> usize;
}

struct NumberIterator {
    current: i32,
    max: i32,
}

impl Iterator for NumberIterator {
    type Item = i32;

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
```

### 2. 生命周期参数

```rust
struct ReferenceContainer<'a, T> {
    data: &'a T,
    reference_count: usize,
}

impl<'a, T> ReferenceContainer<'a, T> {
    fn new(data: &'a T) -> Self {
        ReferenceContainer {
            data,
            reference_count: 1,
        }
    }

    fn get_data(&self) -> &'a T {
        self.data
    }

    fn increment_reference(&mut self) {
        self.reference_count += 1;
    }

    fn decrement_reference(&mut self) -> bool {
        if self.reference_count > 0 {
            self.reference_count -= 1;
            true
        } else {
            false
        }
    }
}
```

## 性能考虑

1. **零成本抽象**: 类型构造器在编译时被解析
2. **单态化**: 为每个具体类型生成专用代码
3. **编译时间**: 泛型代码会增加编译时间
4. **二进制大小**: 可能增加最终二进制文件大小

## 最佳实践

1. **命名约定**: 使用有意义的类型参数名称
2. **约束最小化**: 只要求必要的特征约束
3. **文档清晰**: 明确说明类型构造器的要求
4. **测试全面**: 为不同类型组合编写测试

## 总结

类型构造器在Rust的泛型编程中扮演着重要角色。
通过定义泛型类型，开发者可以创建灵活和可重用的代码，处理多种不同类型的数据。
类型构造器使得Rust能够在保持类型安全的同时，提供强大的抽象能力。

理解类型构造器的使用对于编写高效和安全的Rust代码至关重要。
*/

use std::collections::HashMap;

// 类型别名 - 简化复杂类型
type GenVec<T> = Vec<T>;
type GenSlice<'a, T> = &'a [T];
type GenMutSlice<'a, T> = &'a mut [T];
type GenOption<T> = Option<T>;
#[allow(dead_code)]
type GenResult<T, E> = Result<T, E>;
#[allow(dead_code)]
type GenHashMap<K, V> = HashMap<K, V>;
#[allow(dead_code)]
type GenString = String;
#[allow(dead_code)]
type GenFn<T, U> = fn(T) -> U;

// 基本泛型结构体
pub struct Pair<T, U> {
    pub first: T,
    pub second: U,
}

impl<T, U> Pair<T, U> {
    pub fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }

    pub fn first(&self) -> &T {
        &self.first
    }

    pub fn second(&self) -> &U {
        &self.second
    }
}

// 泛型容器
pub struct Container<T> {
    pub items: GenVec<T>,
    pub capacity: usize,
}

impl<T> Container<T> {
    pub fn new(capacity: usize) -> Self {
        Container {
            items: Vec::with_capacity(capacity),
            capacity,
        }
    }

    pub fn add(&mut self, item: T) -> bool {
        if self.items.len() < self.capacity {
            self.items.push(item);
            true
        } else {
            false
        }
    }

    pub fn get(&self, index: usize) -> GenOption<&T> {
        self.items.get(index)
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.items.len() >= self.capacity
    }
}

// 泛型算法
pub fn find_max<T>(items: GenSlice<'_, T>) -> GenOption<&T>
where
    T: PartialOrd,
{
    items.iter().max_by(|a, b| a.partial_cmp(b).unwrap())
}

pub fn sort_items<T>(items: GenMutSlice<T>)
where
    T: Ord,
{
    items.sort();
}

pub fn filter_items<T, F>(items: GenSlice<'_, T>, predicate: F) -> GenVec<&T>
where
    F: Fn(&T) -> bool,
{
    items.iter().filter(|item| predicate(item)).collect()
}

// 泛型特征
pub trait Processor<T> {
    fn process(&self, input: T) -> T;
    fn validate(&self, input: &T) -> bool;
}

pub struct StringProcessor;
pub struct NumberProcessor;

impl Processor<String> for StringProcessor {
    fn process(&self, input: String) -> String {
        input.to_uppercase()
    }

    fn validate(&self, input: &String) -> bool {
        !input.is_empty()
    }
}

impl Processor<i32> for NumberProcessor {
    fn process(&self, input: i32) -> i32 {
        input * 2
    }

    fn validate(&self, input: &i32) -> bool {
        *input > 0
    }
}

// 数据结构
pub struct Stack<T> {
    pub items: GenVec<T>,
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack { items: Vec::new() }
    }

    pub fn push(&mut self, item: T) {
        self.items.push(item);
    }

    pub fn pop(&mut self) -> GenOption<T> {
        self.items.pop()
    }

    pub fn peek(&self) -> GenOption<&T> {
        self.items.last()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Queue<T> {
    pub items: GenVec<T>,
}

impl<T> Queue<T> {
    pub fn new() -> Self {
        Queue { items: Vec::new() }
    }

    pub fn enqueue(&mut self, item: T) {
        self.items.push(item);
    }

    pub fn dequeue(&mut self) -> GenOption<T> {
        if self.items.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    pub fn front(&self) -> GenOption<&T> {
        self.items.first()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self::new()
    }
}

// 数学运算
pub trait Numeric {
    fn add(&self, other: &Self) -> Self;
    fn subtract(&self, other: &Self) -> Self;
    fn multiply(&self, other: &Self) -> Self;
    fn divide(&self, other: &Self) -> Option<Self>
    where
        Self: Sized;
}

impl Numeric for i32 {
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn subtract(&self, other: &Self) -> Self {
        self - other
    }

    fn multiply(&self, other: &Self) -> Self {
        self * other
    }

    fn divide(&self, other: &Self) -> Option<Self> {
        if *other == 0 {
            None
        } else {
            Some(self / other)
        }
    }
}

impl Numeric for f64 {
    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn subtract(&self, other: &Self) -> Self {
        self - other
    }

    fn multiply(&self, other: &Self) -> Self {
        self * other
    }

    fn divide(&self, other: &Self) -> Option<Self> {
        if *other == 0.0 {
            None
        } else {
            Some(self / other)
        }
    }
}

pub fn calculate<T: Numeric + Clone>(a: &T, b: &T, operation: char) -> Option<T> {
    match operation {
        '+' => Some(a.add(b)),
        '-' => Some(a.subtract(b)),
        '*' => Some(a.multiply(b)),
        '/' => a.divide(b),
        _ => None,
    }
}

// 序列化/反序列化
pub trait Serializable {
    fn serialize(&self) -> String;
    fn deserialize(data: &str) -> Option<Self>
    where
        Self: Sized;
}

pub struct DataContainer<T> {
    pub data: T,
    pub metadata: String,
}

impl<T> DataContainer<T> {
    pub fn new(data: T, metadata: String) -> Self {
        DataContainer { data, metadata }
    }

    pub fn get_data(&self) -> &T {
        &self.data
    }

    pub fn get_metadata(&self) -> &str {
        &self.metadata
    }
}

impl<T: std::fmt::Display> Serializable for DataContainer<T> {
    fn serialize(&self) -> String {
        format!("Data: {}, Metadata: {}", self.data, self.metadata)
    }

    fn deserialize(_data: &str) -> Option<Self> {
        // 这里可以实现实际的反序列化逻辑
        None
    }
}

// 关联类型示例
pub trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
    fn count(&self) -> usize;
}

pub struct NumberIterator {
    pub current: i32,
    pub max: i32,
}

impl Iterator for NumberIterator {
    type Item = i32;

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

// 生命周期参数示例
pub struct ReferenceContainer<'a, T> {
    pub data: &'a T,
    pub reference_count: usize,
}

impl<'a, T> ReferenceContainer<'a, T> {
    pub fn new(data: &'a T) -> Self {
        ReferenceContainer {
            data,
            reference_count: 1,
        }
    }

    pub fn get_data(&self) -> &'a T {
        self.data
    }

    pub fn increment_reference(&mut self) {
        self.reference_count += 1;
    }

    pub fn decrement_reference(&mut self) -> bool {
        if self.reference_count > 0 {
            self.reference_count -= 1;
            true
        } else {
            false
        }
    }
}

// 演示函数
pub fn demonstrate_type_constructors() {
    println!("=== Type Constructors Demonstration ===\n");

    // 基本泛型演示
    demonstrate_basic_generics();

    // 容器演示
    demonstrate_containers();

    // 算法演示
    demonstrate_algorithms();

    // 处理器演示
    demonstrate_processors();

    // 数据结构演示
    demonstrate_data_structures();

    // 数学运算演示
    demonstrate_math_operations();

    // 序列化演示
    demonstrate_serialization();

    // 迭代器演示
    demonstrate_iterators();

    // 生命周期演示
    demonstrate_lifetimes();
}

// 基本泛型演示
fn demonstrate_basic_generics() {
    println!("--- Basic Generics Demo ---");

    let pair1 = Pair::new(1, "hello");
    let pair2 = Pair::new(std::f64::consts::PI, true);

    println!("Pair1: first={}, second={}", pair1.first(), pair1.second());
    println!("Pair2: first={}, second={}", pair2.first(), pair2.second());
    println!();
}

// 容器演示
fn demonstrate_containers() {
    println!("--- Container Demo ---");

    let mut container: Container<i32> = Container::new(5);

    for i in 1..=6 {
        let success = container.add(i);
        println!("Added {}: {}", i, success);
    }

    println!("Container length: {}", container.len());
    println!("Is full: {}", container.is_full());
    println!();
}

// 算法演示
fn demonstrate_algorithms() {
    println!("--- Algorithm Demo ---");

    let numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let mut sorted_numbers = numbers.clone();

    if let Some(max) = find_max(&numbers) {
        println!("Maximum value: {}", max);
    }

    sort_items(&mut sorted_numbers);
    println!("Sorted numbers: {:?}", sorted_numbers);

    let filtered = filter_items(&numbers, |&x| x > 5);
    println!("Numbers greater than 5: {:?}", filtered);
    println!();
}

// 处理器演示
fn demonstrate_processors() {
    println!("--- Processor Demo ---");

    let string_processor = StringProcessor;
    let number_processor = NumberProcessor;

    let test_string = "hello world".to_string();
    let test_number = 42;

    if string_processor.validate(&test_string) {
        let processed = string_processor.process(test_string);
        println!("Processed string: {}", processed);
    }

    if number_processor.validate(&test_number) {
        let processed = number_processor.process(test_number);
        println!("Processed number: {}", processed);
    }
    println!();
}

// 数据结构演示
fn demonstrate_data_structures() {
    println!("--- Data Structure Demo ---");

    // Stack 演示
    let mut stack: Stack<i32> = Stack::new();
    for i in 1..=5 {
        stack.push(i);
    }

    println!("Stack operations:");
    while let Some(item) = stack.pop() {
        println!("  Popped: {}", item);
    }

    // Queue 演示
    let mut queue: Queue<String> = Queue::new();
    for word in ["hello", "world", "rust"].iter() {
        queue.enqueue(word.to_string());
    }

    println!("Queue operations:");
    while let Some(item) = queue.dequeue() {
        println!("  Dequeued: {}", item);
    }
    println!();
}

// 数学运算演示
fn demonstrate_math_operations() {
    println!("--- Math Operations Demo ---");

    let a = 10;
    let b = 3;

    println!("Operations with i32:");
    println!("  {} + {} = {:?}", a, b, calculate(&a, &b, '+'));
    println!("  {} - {} = {:?}", a, b, calculate(&a, &b, '-'));
    println!("  {} * {} = {:?}", a, b, calculate(&a, &b, '*'));
    println!("  {} / {} = {:?}", a, b, calculate(&a, &b, '/'));

    let x = 10.5;
    let y = 2.0;

    println!("Operations with f64:");
    println!("  {} + {} = {:?}", x, y, calculate(&x, &y, '+'));
    println!("  {} / {} = {:?}", x, y, calculate(&x, &y, '/'));
    println!();
}

// 序列化演示
fn demonstrate_serialization() {
    println!("--- Serialization Demo ---");

    let container = DataContainer::new(42, "Important number".to_string());
    let serialized = container.serialize();

    println!("Serialized data: {}", serialized);
    println!();
}

// 迭代器演示
fn demonstrate_iterators() {
    println!("--- Iterator Demo ---");

    let mut iterator = NumberIterator { current: 1, max: 5 };

    println!("Number iterator:");
    while let Some(number) = iterator.next() {
        println!("  {}", number);
    }
    println!("Remaining count: {}", iterator.count());
    println!();
}

// 生命周期演示
fn demonstrate_lifetimes() {
    println!("--- Lifetime Demo ---");

    let data = 42;
    let mut container = ReferenceContainer::new(&data);

    println!("Reference count: {}", container.reference_count);
    container.increment_reference();
    println!("After increment: {}", container.reference_count);

    let decremented = container.decrement_reference();
    println!("Decrement successful: {}", decremented);
    println!("Final count: {}", container.reference_count);
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pair() {
        let pair = Pair::new(1, "hello");
        assert_eq!(*pair.first(), 1);
        assert_eq!(*pair.second(), "hello");
    }

    #[test]
    fn test_container() {
        let mut container = Container::new(3);

        assert!(container.add(1));
        assert!(container.add(2));
        assert!(container.add(3));
        assert!(!container.add(4)); // 超出容量

        assert_eq!(container.len(), 3);
        assert!(container.is_full());
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

    #[test]
    fn test_filter_items() {
        let numbers = vec![1, 2, 3, 4, 5];
        let filtered = filter_items(&numbers, |&x| x > 3);
        assert_eq!(filtered, vec![&4, &5]);
    }

    #[test]
    fn test_stack() {
        let mut stack = Stack::new();
        stack.push(1);
        stack.push(2);

        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn test_queue() {
        let mut queue = Queue::new();
        queue.enqueue("hello".to_string());
        queue.enqueue("world".to_string());

        assert_eq!(queue.dequeue(), Some("hello".to_string()));
        assert_eq!(queue.dequeue(), Some("world".to_string()));
        assert_eq!(queue.dequeue(), None);
    }

    #[test]
    fn test_numeric_i32() {
        let a = 10;
        let b = 3;

        assert_eq!(a.add(&b), 13);
        assert_eq!(a.subtract(&b), 7);
        assert_eq!(a.multiply(&b), 30);
        assert_eq!(a.divide(&b), Some(3));
        assert_eq!(a.divide(&0), None);
    }

    #[test]
    fn test_calculate() {
        let a = 10;
        let b = 3;

        assert_eq!(calculate(&a, &b, '+'), Some(13));
        assert_eq!(calculate(&a, &b, '-'), Some(7));
        assert_eq!(calculate(&a, &b, '*'), Some(30));
        assert_eq!(calculate(&a, &b, '/'), Some(3));
        assert_eq!(calculate(&a, &b, '?'), None);
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
    fn test_reference_container() {
        let data = 42;
        let mut container = ReferenceContainer::new(&data);

        assert_eq!(container.reference_count, 1);
        container.increment_reference();
        assert_eq!(container.reference_count, 2);

        assert!(container.decrement_reference());
        assert_eq!(container.reference_count, 1);
    }
}
