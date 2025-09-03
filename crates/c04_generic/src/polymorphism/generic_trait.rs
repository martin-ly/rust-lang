/*
Generic Trait 是 Rust 中实现多态性的核心机制之一。
它允许我们定义可以处理多种类型的特征，实现编译时多态。

## 定义

Generic Trait 是具有类型参数的特征：

```rust
trait Container<T> {
    fn add(&mut self, item: T);
    fn get(&self, index: usize) -> Option<&T>;
    fn len(&self) -> usize;
}
```

## 重要特性

1. **类型参数**: 使用泛型类型参数 `<T>`
2. **编译时多态**: 在编译时确定具体类型
3. **零成本抽象**: 没有运行时开销
4. **类型安全**: 编译时保证类型正确性

## 实现示例

### 1. 基本泛型特征

```rust
trait Storage<T> {
    fn store(&mut self, item: T);
    fn retrieve(&self, id: usize) -> Option<&T>;
    fn remove(&mut self, id: usize) -> Option<T>;
}

struct MemoryStorage<T> {
    items: Vec<T>,
}

impl<T> Storage<T> for MemoryStorage<T> {
    fn store(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn retrieve(&self, id: usize) -> Option<&T> {
        self.items.get(id)
    }
    
    fn remove(&mut self, id: usize) -> Option<T> {
        if id < self.items.len() {
            Some(self.items.remove(id))
        } else {
            None
        }
    }
}
```

### 2. 带约束的泛型特征

```rust
use std::fmt::Display;

trait Printable<T> 
where
    T: Display + Clone,
{
    fn print(&self, item: &T);
    fn print_all(&self, items: &[T]);
}

struct ConsolePrinter;

impl<T> Printable<T> for ConsolePrinter
where
    T: Display + Clone,
{
    fn print(&self, item: &T) {
        println!("Item: {}", item);
    }
    
    fn print_all(&self, items: &[T]) {
        for (i, item) in items.iter().enumerate() {
            println!("{}: {}", i, item);
        }
    }
}
```

### 3. 关联类型与泛型

```rust
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

trait Container<T> {
    type Iterator: Iterator<Item = T>;
    
    fn iter(&self) -> Self::Iterator;
    fn add(&mut self, item: T);
}

struct VecContainer<T> {
    items: Vec<T>,
}

impl<T> Container<T> for VecContainer<T> {
    type Iterator = std::vec::IntoIter<T>;
    
    fn iter(self) -> Self::Iterator {
        self.items.into_iter()
    }
    
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
}
```

## 使用场景

### 1. 集合类型抽象

```rust
trait Collection<T> {
    fn add(&mut self, item: T);
    fn remove(&mut self, index: usize) -> Option<T>;
    fn get(&self, index: usize) -> Option<&T>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

struct DynamicArray<T> {
    items: Vec<T>,
}

impl<T> Collection<T> for DynamicArray<T> {
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn remove(&mut self, index: usize) -> Option<T> {
        if index < self.items.len() {
            Some(self.items.remove(index))
        } else {
            None
        }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }
    
    fn len(&self) -> usize {
        self.items.len()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
}

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> Collection<T> for LinkedList<T> {
    fn add(&mut self, item: T) {
        let new_node = Box::new(Node {
            data: item,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
    
    fn remove(&mut self, index: usize) -> Option<T> {
        if index == 0 {
            self.head.take().map(|node| node.data)
        } else {
            let mut current = &mut self.head;
            for _ in 0..index - 1 {
                if let Some(ref mut node) = current {
                    current = &mut node.next;
                } else {
                    return None;
                }
            }
            current.take().map(|node| node.data)
        }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        let mut current = &self.head;
        for _ in 0..index {
            if let Some(ref node) = current {
                current = &node.next;
            } else {
                return None;
            }
        }
        current.as_ref().map(|node| &node.data)
    }
    
    fn len(&self) -> usize {
        let mut count = 0;
        let mut current = &self.head;
        while let Some(ref node) = current {
            count += 1;
            current = &node.next;
        }
        count
    }
    
    fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}
```

### 2. 算法抽象

```rust
trait Algorithm<T, R> {
    fn execute(&self, input: T) -> R;
    fn name(&self) -> &str;
}

struct SortingAlgorithm;

impl<T> Algorithm<Vec<T>, Vec<T>> for SortingAlgorithm
where
    T: Ord + Clone,
{
    fn execute(&self, mut input: Vec<T>) -> Vec<T> {
        input.sort();
        input
    }
    
    fn name(&self) -> &str {
        "Quick Sort"
    }
}

struct FilteringAlgorithm<F> {
    predicate: F,
}

impl<T, F> Algorithm<Vec<T>, Vec<T>> for FilteringAlgorithm<F>
where
    F: Fn(&T) -> bool,
    T: Clone,
{
    fn execute(&self, input: Vec<T>) -> Vec<T> {
        input.into_iter().filter(|x| (self.predicate)(x)).collect()
    }
    
    fn name(&self) -> &str {
        "Filter"
    }
}
```

### 3. 工厂模式

```rust
trait Factory<T> {
    fn create(&self) -> T;
    fn create_with_params(&self, params: Vec<String>) -> T;
}

struct StringFactory;

impl Factory<String> for StringFactory {
    fn create(&self) -> String {
        String::new()
    }
    
    fn create_with_params(&self, params: Vec<String>) -> String {
        params.join(" ")
    }
}

struct NumberFactory;

impl Factory<i32> for NumberFactory {
    fn create(&self) -> i32 {
        0
    }
    
    fn create_with_params(&self, params: Vec<String>) -> i32 {
        params.iter()
            .filter_map(|s| s.parse::<i32>().ok())
            .sum()
    }
}
```

## 高级用法

### 1. 特征对象与泛型

```rust
trait Processor<T> {
    fn process(&self, input: T) -> T;
}

struct StringProcessor;
struct NumberProcessor;

impl Processor<String> for StringProcessor {
    fn process(&self, input: String) -> String {
        input.to_uppercase()
    }
}

impl Processor<i32> for NumberProcessor {
    fn process(&self, input: i32) -> i32 {
        input * 2
    }
}

// 使用特征对象
fn process_with_trait_object<T>(processor: &dyn Processor<T>, input: T) -> T
where
    T: Clone,
{
    processor.process(input)
}

// 使用泛型
fn process_with_generic<T, P>(processor: &P, input: T) -> T
where
    P: Processor<T>,
{
    processor.process(input)
}
```

### 2. 条件实现

```rust
trait Convertible<T> {
    fn convert(&self) -> T;
}

impl<T, U> Convertible<U> for T
where
    T: Clone,
    U: From<T>,
{
    fn convert(&self) -> U {
        U::from(self.clone())
    }
}

// 为特定类型组合提供特殊实现
impl<T> Convertible<Vec<T>> for T
where
    T: Clone,
{
    fn convert(&self) -> Vec<T> {
        vec![self.clone()]
    }
}
```

## 性能考虑

1. **零成本抽象**: 泛型特征调用在编译时被内联
2. **单态化**: 为每个具体类型生成专用代码
3. **编译时间**: 泛型代码会增加编译时间
4. **二进制大小**: 可能增加最终二进制文件大小

## 最佳实践

1. **约束最小化**: 只要求必要的特征约束
2. **文档清晰**: 明确说明泛型参数的要求
3. **测试全面**: 为不同类型组合编写测试
4. **性能测试**: 验证泛型代码的性能表现

## 总结

Generic Trait 为 Rust 提供了强大的编译时多态能力。
通过合理使用泛型特征，可以创建灵活、高效、类型安全的代码。
*/

use std::fmt::Display;

// 基本泛型特征
pub trait Storage<T> {
    fn store(&mut self, item: T);
    fn retrieve(&self, id: usize) -> Option<&T>;
    fn remove(&mut self, id: usize) -> Option<T>;
}

// 内存存储实现
pub struct MemoryStorage<T> {
    items: Vec<T>,
}

impl<T> MemoryStorage<T> {
    pub fn new() -> Self {
        MemoryStorage { items: Vec::new() }
    }
    
    pub fn len(&self) -> usize {
        self.items.len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<T> Default for MemoryStorage<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Storage<T> for MemoryStorage<T> {
    fn store(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn retrieve(&self, id: usize) -> Option<&T> {
        self.items.get(id)
    }
    
    fn remove(&mut self, id: usize) -> Option<T> {
        if id < self.items.len() {
            Some(self.items.remove(id))
        } else {
            None
        }
    }
}

// 带约束的泛型特征
pub trait Printable<T> 
where
    T: Display + Clone,
{
    fn print(&self, item: &T);
    fn print_all(&self, items: &[T]);
}

pub struct ConsolePrinter;

impl<T> Printable<T> for ConsolePrinter
where
    T: Display + Clone,
{
    fn print(&self, item: &T) {
        println!("Item: {}", item);
    }
    
    fn print_all(&self, items: &[T]) {
        for (i, item) in items.iter().enumerate() {
            println!("{}: {}", i, item);
        }
    }
}

// 集合类型抽象
pub trait Collection<T> {
    fn add(&mut self, item: T);
    fn remove(&mut self, index: usize) -> Option<T>;
    fn get(&self, index: usize) -> Option<&T>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

// 动态数组实现
pub struct DynamicArray<T> {
    items: Vec<T>,
}

impl<T> DynamicArray<T> {
    pub fn new() -> Self {
        DynamicArray { items: Vec::new() }
    }
}

impl<T> Default for DynamicArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Collection<T> for DynamicArray<T> {
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn remove(&mut self, index: usize) -> Option<T> {
        if index < self.items.len() {
            Some(self.items.remove(index))
        } else {
            None
        }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }
    
    fn len(&self) -> usize {
        self.items.len()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// 算法抽象
pub trait Algorithm<T, R> {
    fn execute(&self, input: T) -> R;
    fn name(&self) -> &str;
}

pub struct SortingAlgorithm;

impl<T> Algorithm<Vec<T>, Vec<T>> for SortingAlgorithm
where
    T: Ord + Clone,
{
    fn execute(&self, mut input: Vec<T>) -> Vec<T> {
        input.sort();
        input
    }
    
    fn name(&self) -> &str {
        "Quick Sort"
    }
}

pub struct FilteringAlgorithm<F> {
    predicate: F,
}

impl<T, F> Algorithm<Vec<T>, Vec<T>> for FilteringAlgorithm<F>
where
    F: Fn(&T) -> bool,
    T: Clone,
{
    fn execute(&self, input: Vec<T>) -> Vec<T> {
        input.into_iter().filter(|x| (self.predicate)(x)).collect()
    }
    
    fn name(&self) -> &str {
        "Filter"
    }
}

// 工厂模式
pub trait Factory<T> {
    fn create(&self) -> T;
    fn create_with_params(&self, params: Vec<String>) -> T;
}

pub struct StringFactory;

impl Factory<String> for StringFactory {
    fn create(&self) -> String {
        String::new()
    }
    
    fn create_with_params(&self, params: Vec<String>) -> String {
        params.join(" ")
    }
}

pub struct NumberFactory;

impl Factory<i32> for NumberFactory {
    fn create(&self) -> i32 {
        0
    }
    
    fn create_with_params(&self, params: Vec<String>) -> i32 {
        params.iter()
            .filter_map(|s| s.parse::<i32>().ok())
            .sum()
    }
}

// 演示函数
pub fn demonstrate_generic_trait() {
    println!("=== Generic Trait Demonstration ===\n");
    
    // 存储演示
    demonstrate_storage();
    
    // 打印演示
    demonstrate_printable();
    
    // 集合演示
    demonstrate_collection();
    
    // 算法演示
    demonstrate_algorithm();
    
    // 工厂演示
    demonstrate_factory();
}

// 存储演示
fn demonstrate_storage() {
    println!("--- Storage Demo ---");
    
    let mut storage: MemoryStorage<String> = MemoryStorage::new();
    
    storage.store("Hello".to_string());
    storage.store("World".to_string());
    storage.store("Rust".to_string());
    
    println!("Stored items:");
    for i in 0..storage.len() {
        if let Some(item) = storage.retrieve(i) {
            println!("  {}: {}", i, item);
        }
    }
    
    if let Some(removed) = storage.remove(1) {
        println!("Removed: {}", removed);
    }
    
    println!("After removal:");
    for i in 0..storage.len() {
        if let Some(item) = storage.retrieve(i) {
            println!("  {}: {}", i, item);
        }
    }
    println!();
}

// 打印演示
fn demonstrate_printable() {
    println!("--- Printable Demo ---");
    
    let printer = ConsolePrinter;
    let items = vec!["Apple", "Banana", "Cherry"];
    
    printer.print(&items[0]);
    printer.print_all(&items);
    println!();
}

// 集合演示
fn demonstrate_collection() {
    println!("--- Collection Demo ---");
    
    let mut array: DynamicArray<i32> = DynamicArray::new();
    
    array.add(10);
    array.add(20);
    array.add(30);
    
    println!("Array length: {}", array.len());
    println!("Is empty: {}", array.is_empty());
    
    if let Some(item) = array.get(1) {
        println!("Item at index 1: {}", item);
    }
    
    if let Some(removed) = array.remove(0) {
        println!("Removed item: {}", removed);
    }
    
    println!("After removal, length: {}", array.len());
    println!();
}

// 算法演示
fn demonstrate_algorithm() {
    println!("--- Algorithm Demo ---");
    
    let sorter: SortingAlgorithm = SortingAlgorithm;
    let numbers: Vec<i32> = vec![3, 1, 4, 1, 5, 9, 2, 6];
    
    println!("Original: {:?}", numbers);
    let sorted = sorter.execute(numbers);
    println!("Sorted: {:?}", sorted);
    println!("Algorithm: {}", <SortingAlgorithm as Algorithm<Vec<i32>, Vec<i32>>>::name(&sorter));
    
    let filter: FilteringAlgorithm<fn(&i32) -> bool> = FilteringAlgorithm { 
        predicate: |&x| x > 5 
    };
    let filtered = filter.execute(sorted);
    println!("Filtered (>5): {:?}", filtered);
    println!("Algorithm: {}", filter.name());
    println!();
}

// 工厂演示
fn demonstrate_factory() {
    println!("--- Factory Demo ---");
    
    let string_factory = StringFactory;
    let number_factory = NumberFactory;
    
    let empty_string = string_factory.create();
    let custom_string = string_factory.create_with_params(
        vec!["Hello".to_string(), "Rust".to_string(), "World".to_string()]
    );
    
    let default_number = number_factory.create();
    let sum_number = number_factory.create_with_params(
        vec!["10".to_string(), "20".to_string(), "30".to_string()]
    );
    
    println!("Empty string: '{}'", empty_string);
    println!("Custom string: '{}'", custom_string);
    println!("Default number: {}", default_number);
    println!("Sum number: {}", sum_number);
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_memory_storage() {
        let mut storage: MemoryStorage<i32> = MemoryStorage::new();
        
        storage.store(10);
        storage.store(20);
        
        assert_eq!(storage.len(), 2);
        assert_eq!(storage.retrieve(0), Some(&10));
        assert_eq!(storage.retrieve(1), Some(&20));
        
        assert_eq!(storage.remove(0), Some(10));
        assert_eq!(storage.len(), 1);
    }
    
    #[test]
    fn test_dynamic_array() {
        let mut array: DynamicArray<String> = DynamicArray::new();
        
        array.add("Hello".to_string());
        array.add("World".to_string());
        
        assert_eq!(array.len(), 2);
        assert!(!array.is_empty());
        assert_eq!(array.get(0), Some(&"Hello".to_string()));
        
        assert_eq!(array.remove(0), Some("Hello".to_string()));
        assert_eq!(array.len(), 1);
    }
    
    #[test]
    fn test_sorting_algorithm() {
        let sorter: SortingAlgorithm = SortingAlgorithm;
        let numbers: Vec<i32> = vec![3, 1, 4, 1, 5];
        let sorted = sorter.execute(numbers);
        
        assert_eq!(sorted, vec![1, 1, 3, 4, 5]);
        assert_eq!(<SortingAlgorithm as Algorithm<Vec<i32>, Vec<i32>>>::name(&sorter), "Quick Sort");
    }
    
    #[test]
    fn test_filtering_algorithm() {
        let filter: FilteringAlgorithm<fn(&i32) -> bool> = FilteringAlgorithm { 
            predicate: |&x| x > 3 
        };
        let numbers = vec![1, 2, 3, 4, 5, 6];
        let filtered = filter.execute(numbers);
        
        assert_eq!(filtered, vec![4, 5, 6]);
        assert_eq!(filter.name(), "Filter");
    }
    
    #[test]
    fn test_factories() {
        let string_factory = StringFactory;
        let number_factory = NumberFactory;
        
        let empty_string = string_factory.create();
        assert_eq!(empty_string, "");
        
        let custom_string = string_factory.create_with_params(
            vec!["A".to_string(), "B".to_string()]
        );
        assert_eq!(custom_string, "A B");
        
        let default_number = number_factory.create();
        assert_eq!(default_number, 0);
        
        let sum_number = number_factory.create_with_params(
            vec!["10".to_string(), "20".to_string()]
        );
        assert_eq!(sum_number, 30);
    }
}
