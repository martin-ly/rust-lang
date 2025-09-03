/*
在 Rust 中，自然变换的概念通常与函数式编程和类型系统相关，尽管 Rust 本身并不直接支持范畴论的概念。
我们可以通过使用 trait 和泛型来模拟自然变换的行为。

## 定义
在 Rust 中，自然变换可以被视为两个类型之间的转换，通常通过 trait 来实现。
我们可以定义一个 trait，表示从一个类型到另一个类型的转换，同时保持某种结构的兼容性。

## 重要特性

1. **结构保持**: 保持类型结构的一致性
2. **类型安全**: 编译时类型检查
3. **可组合性**: 支持变换的组合
4. **零成本**: 编译时优化，无运行时开销

## 基本概念

自然变换在范畴论中是一个重要的概念，它描述了函子之间的映射。
在 Rust 中，我们可以通过 trait 系统来模拟这种行为。

## 实现示例

### 1. 基本自然变换

```rust
// 定义一个 trait，表示从类型 A 到类型 B 的转换
trait NaturalTransformation<A, B> {
    fn transform(&self, a: A) -> B;
}

// 定义类型 A 和 B
struct A {
    value: i32,
}

struct B {
    value: String,
}

// 实现自然变换，将 A 转换为 B
struct AtoB;

impl NaturalTransformation<A, B> for AtoB {
    fn transform(&self, a: A) -> B {
        B {
            value: a.value.to_string(), // 将 i32 转换为 String
        }
    }
}
```

### 2. 泛型自然变换

```rust
trait Functor<A, B> {
    type Output;
    
    fn map<F>(self, f: F) -> Self::Output
    where
        F: Fn(A) -> B;
}

struct OptionFunctor<T>(Option<T>);

impl<T> Functor<T, T> for OptionFunctor<T> {
    type Output = OptionFunctor<T>;
    
    fn map<F>(self, f: F) -> Self::Output
    where
        F: Fn(T) -> T,
    {
        OptionFunctor(self.0.map(f))
    }
}

// 自然变换：Option<T> -> Result<T, E>
struct OptionToResult<E>(std::marker::PhantomData<E>);

impl<T, E> NaturalTransformation<Option<T>, Result<T, E>> for OptionToResult<E>
where
    E: Default,
{
    fn transform(&self, opt: Option<T>) -> Result<T, E> {
        opt.ok_or_else(E::default)
    }
}
```

### 3. 高阶自然变换

```rust
trait HigherOrderFunctor<A, B> {
    type Inner;
    type Output;
    
    fn lift<F>(self, f: F) -> Self::Output
    where
        F: NaturalTransformation<A, B>;
}

struct VecFunctor<T>(Vec<T>);

impl<T> HigherOrderFunctor<T, T> for VecFunctor<T> {
    type Inner = T;
    type Output = VecFunctor<T>;
    
    fn lift<F>(self, _f: F) -> Self::Output
    where
        F: NaturalTransformation<T, T>,
    {
        self
    }
}
```

## 使用场景

### 1. 类型转换系统

```rust
trait TypeConverter<From, To> {
    fn convert(&self, from: From) -> To;
}

struct StringToNumber;
struct NumberToString;

impl TypeConverter<String, i32> for StringToNumber {
    fn convert(&self, from: String) -> i32 {
        from.parse().unwrap_or(0)
    }
}

impl TypeConverter<i32, String> for NumberToString {
    fn convert(&self, from: i32) -> String {
        from.to_string()
    }
}

// 自然变换：String -> i32 -> String
struct StringTransformation;

impl NaturalTransformation<String, String> for StringTransformation {
    fn transform(&self, s: String) -> String {
        let number_converter = StringToNumber;
        let string_converter = NumberToString;
        
        let number = number_converter.convert(s);
        string_converter.convert(number)
    }
}
```

### 2. 数据结构变换

```rust
trait DataStructure<A> {
    fn add(&mut self, item: A);
    fn get(&self, index: usize) -> Option<&A>;
    fn len(&self) -> usize;
}

struct VecStructure<T> {
    data: Vec<T>,
}

struct LinkedListStructure<T> {
    data: std::collections::LinkedList<T>,
}

impl<T> DataStructure<T> for VecStructure<T> {
    fn add(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
}

impl<T> DataStructure<T> for LinkedListStructure<T> {
    fn add(&mut self, item: T) {
        self.data.push_back(item);
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.iter().nth(index)
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
}

// 自然变换：Vec<T> -> LinkedList<T>
struct VecToLinkedList;

impl<T> NaturalTransformation<VecStructure<T>, LinkedListStructure<T>> for VecToLinkedList {
    fn transform(&self, vec_struct: VecStructure<T>) -> LinkedListStructure<T> {
        let mut linked_list = LinkedListStructure {
            data: std::collections::LinkedList::new(),
        };
        
        for item in vec_struct.data {
            linked_list.add(item);
        }
        
        linked_list
    }
}
```

### 3. 错误处理变换

```rust
trait ErrorHandler<E> {
    fn handle(&self, error: E) -> String;
}

struct StringErrorHandler;
struct IoErrorHandler;

impl ErrorHandler<String> for StringErrorHandler {
    fn handle(&self, error: String) -> String {
        format!("String error: {}", error)
    }
}

impl ErrorHandler<std::io::Error> for IoErrorHandler {
    fn handle(&self, error: std::io::Error) -> String {
        format!("IO error: {}", error)
    }
}

// 自然变换：统一错误处理
struct UnifiedErrorHandler;

impl NaturalTransformation<String, String> for UnifiedErrorHandler {
    fn transform(&self, error: String) -> String {
        let handler = StringErrorHandler;
        handler.handle(error)
    }
}

impl NaturalTransformation<std::io::Error, String> for UnifiedErrorHandler {
    fn transform(&self, error: std::io::Error) -> String {
        let handler = IoErrorHandler;
        handler.handle(error)
    }
}
```

## 高级用法

### 1. 变换组合

```rust
trait TransformComposition<A, B, C> {
    fn compose<F, G>(self, f: F, g: G) -> impl NaturalTransformation<A, C>
    where
        F: NaturalTransformation<A, B>,
        G: NaturalTransformation<B, C>;
}

struct Composer;

impl TransformComposition<String, i32, f64> for Composer {
    fn compose<F, G>(self, f: F, g: G) -> impl NaturalTransformation<String, f64>
    where
        F: NaturalTransformation<String, i32>,
        G: NaturalTransformation<i32, f64>,
    {
        struct ComposedTransform<F, G> {
            f: F,
            g: G,
        }
        
        impl<F, G> NaturalTransformation<String, f64> for ComposedTransform<F, G>
        where
            F: NaturalTransformation<String, i32>,
            G: NaturalTransformation<i32, f64>,
        {
            fn transform(&self, input: String) -> f64 {
                let intermediate = self.f.transform(input);
                self.g.transform(intermediate)
            }
        }
        
        ComposedTransform { f, g }
    }
}
```

### 2. 条件变换

```rust
trait ConditionalTransformation<A, B> {
    fn transform_if<F>(&self, input: A, condition: F) -> Option<B>
    where
        F: Fn(&A) -> bool;
}

struct ConditionalConverter;

impl ConditionalTransformation<String, i32> for ConditionalConverter {
    fn transform_if<F>(&self, input: String, condition: F) -> Option<i32>
    where
        F: Fn(&String) -> bool,
    {
        if condition(&input) {
            input.parse().ok()
        } else {
            None
        }
    }
}
```

## 性能考虑

1. **零成本抽象**: 自然变换在编译时被解析
2. **类型安全**: 编译时类型检查，无运行时开销
3. **代码生成**: 为每个具体类型生成专用代码
4. **内存效率**: 避免不必要的内存分配

## 最佳实践

1. **语义清晰**: 变换名称应该清晰表达其用途
2. **类型安全**: 确保变换的类型安全性
3. **性能优化**: 实现高效的变换逻辑
4. **测试覆盖**: 为变换逻辑编写测试

## 总结

自然变换为 Rust 提供了强大的类型转换和抽象能力。
通过合理使用自然变换，可以创建更加灵活、类型安全的代码，
同时保持零成本抽象的优势。
*/

// 基本自然变换 trait
pub trait NaturalTransformation<A, B> {
    fn transform(&self, a: A) -> B;
}

// 基本类型
pub struct A {
    pub value: i32,
}

pub struct B {
    pub value: String,
}

// 实现自然变换，将 A 转换为 B
pub struct AtoB;

impl NaturalTransformation<A, B> for AtoB {
    fn transform(&self, a: A) -> B {
        B {
            value: a.value.to_string(),
        }
    }
}

// 泛型自然变换
pub trait Functor<A, B> {
    type Output;
    
    fn map<F>(self, f: F) -> Self::Output
    where
        F: Fn(A) -> B;
}

pub struct OptionFunctor<T>(pub Option<T>);

impl<T> Functor<T, T> for OptionFunctor<T> {
    type Output = OptionFunctor<T>;
    
    fn map<F>(self, f: F) -> Self::Output
    where
        F: Fn(T) -> T,
    {
        OptionFunctor(self.0.map(f))
    }
}

// 自然变换：Option<T> -> Result<T, E>
pub struct OptionToResult<E>(pub std::marker::PhantomData<E>);

impl<T, E> NaturalTransformation<Option<T>, Result<T, E>> for OptionToResult<E>
where
    E: Default,
{
    fn transform(&self, opt: Option<T>) -> Result<T, E> {
        opt.ok_or_else(E::default)
    }
}

// 类型转换系统
pub trait TypeConverter<From, To> {
    fn convert(&self, from: From) -> To;
}

pub struct StringToNumber;
pub struct NumberToString;

impl TypeConverter<String, i32> for StringToNumber {
    fn convert(&self, from: String) -> i32 {
        from.parse().unwrap_or(0)
    }
}

impl TypeConverter<i32, String> for NumberToString {
    fn convert(&self, from: i32) -> String {
        from.to_string()
    }
}

// 自然变换：String -> i32 -> String
pub struct StringTransformation;

impl NaturalTransformation<String, String> for StringTransformation {
    fn transform(&self, s: String) -> String {
        let number_converter = StringToNumber;
        let string_converter = NumberToString;
        
        let number = number_converter.convert(s);
        string_converter.convert(number)
    }
}

// 数据结构变换
pub trait DataStructure<A> {
    fn add(&mut self, item: A);
    fn get(&self, index: usize) -> Option<&A>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

pub struct VecStructure<T> {
    pub data: Vec<T>,
}

pub struct LinkedListStructure<T> {
    pub data: std::collections::LinkedList<T>,
}

impl<T> DataStructure<T> for VecStructure<T> {
    fn add(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
    
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<T> DataStructure<T> for LinkedListStructure<T> {
    fn add(&mut self, item: T) {
        self.data.push_back(item);
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.iter().nth(index)
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
    
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

// 自然变换：Vec<T> -> LinkedList<T>
pub struct VecToLinkedList;

impl<T> NaturalTransformation<VecStructure<T>, LinkedListStructure<T>> for VecToLinkedList {
    fn transform(&self, vec_struct: VecStructure<T>) -> LinkedListStructure<T> {
        let mut linked_list = LinkedListStructure {
            data: std::collections::LinkedList::new(),
        };
        
        for item in vec_struct.data {
            linked_list.add(item);
        }
        
        linked_list
    }
}

// 错误处理变换
pub trait ErrorHandler<E> {
    fn handle(&self, error: E) -> String;
}

pub struct StringErrorHandler;
pub struct IoErrorHandler;

impl ErrorHandler<String> for StringErrorHandler {
    fn handle(&self, error: String) -> String {
        format!("String error: {}", error)
    }
}

impl ErrorHandler<std::io::Error> for IoErrorHandler {
    fn handle(&self, error: std::io::Error) -> String {
        format!("IO error: {}", error)
    }
}

// 自然变换：统一错误处理
pub struct UnifiedErrorHandler;

impl NaturalTransformation<String, String> for UnifiedErrorHandler {
    fn transform(&self, error: String) -> String {
        let handler = StringErrorHandler;
        handler.handle(error)
    }
}

impl NaturalTransformation<std::io::Error, String> for UnifiedErrorHandler {
    fn transform(&self, error: std::io::Error) -> String {
        let handler = IoErrorHandler;
        handler.handle(error)
    }
}

// 条件变换
pub trait ConditionalTransformation<A, B> {
    fn transform_if<F>(&self, input: A, condition: F) -> Option<B>
    where
        F: Fn(&A) -> bool;
}

pub struct ConditionalConverter;

impl ConditionalTransformation<String, i32> for ConditionalConverter {
    fn transform_if<F>(&self, input: String, condition: F) -> Option<i32>
    where
        F: Fn(&String) -> bool,
    {
        if condition(&input) {
            input.parse().ok()
        } else {
            None
        }
    }
}

// 演示函数
pub fn demonstrate_natural_transformation() {
    println!("=== Natural Transformation Demonstration ===\n");
    
    // 基本变换演示
    demonstrate_basic_transformation();
    
    // 类型转换演示
    demonstrate_type_conversion();
    
    // 数据结构变换演示
    demonstrate_data_structure_transformation();
    
    // 错误处理变换演示
    demonstrate_error_handling_transformation();
    
    // 条件变换演示
    demonstrate_conditional_transformation();
}

// 基本变换演示
fn demonstrate_basic_transformation() {
    println!("--- Basic Transformation Demo ---");
    
    let a = A { value: 42 };
    let transformer = AtoB;
    
    let b = transformer.transform(a);
    println!("A's value: 42");
    println!("B's value: {}", b.value);
    println!();
}

// 类型转换演示
fn demonstrate_type_conversion() {
    println!("--- Type Conversion Demo ---");
    
    let string_value = "123".to_string();
    let transformer = StringTransformation;
    
    let result = transformer.transform(string_value);
    println!("Original string: 123");
    println!("Transformed string: {}", result);
    println!();
}

// 数据结构变换演示
fn demonstrate_data_structure_transformation() {
    println!("--- Data Structure Transformation Demo ---");
    
    let vec_struct = VecStructure { data: vec![1, 2, 3, 4, 5] };
    let transformer = VecToLinkedList;
    
    println!("Vector structure length: {}", vec_struct.len());
    
    let linked_list_struct = transformer.transform(vec_struct);
    println!("LinkedList structure length: {}", linked_list_struct.len());
    
    if let Some(value) = linked_list_struct.get(2) {
        println!("Value at index 2: {}", value);
    }
    println!();
}

// 错误处理变换演示
fn demonstrate_error_handling_transformation() {
    println!("--- Error Handling Transformation Demo ---");
    
    let string_error = "Something went wrong".to_string();
    let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "File not found");
    
    let handler = UnifiedErrorHandler;
    
    let string_result = handler.transform(string_error);
    let io_result = handler.transform(io_error);
    
    println!("String error result: {}", string_result);
    println!("IO error result: {}", io_result);
    println!();
}

// 条件变换演示
fn demonstrate_conditional_transformation() {
    println!("--- Conditional Transformation Demo ---");
    
    let converter = ConditionalConverter;
    
    let valid_string = "42".to_string();
    let invalid_string = "not a number".to_string();
    
    let valid_result = converter.transform_if(valid_string, |s| s.parse::<i32>().is_ok());
    let invalid_result = converter.transform_if(invalid_string, |s| s.parse::<i32>().is_ok());
    
    println!("Valid string transformation: {:?}", valid_result);
    println!("Invalid string transformation: {:?}", invalid_result);
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_basic_transformation() {
        let a = A { value: 42 };
        let transformer = AtoB;
        let b = transformer.transform(a);
        
        assert_eq!(b.value, "42");
    }
    
    #[test]
    fn test_string_transformation() {
        let transformer = StringTransformation;
        let result = transformer.transform("123".to_string());
        
        assert_eq!(result, "123");
    }
    
    #[test]
    fn test_vec_to_linked_list() {
        let vec_struct = VecStructure { data: vec![1, 2, 3] };
        let transformer = VecToLinkedList;
        
        assert_eq!(vec_struct.len(), 3);
        
        let linked_list_struct = transformer.transform(vec_struct);
        assert_eq!(linked_list_struct.len(), 3);
        
        if let Some(value) = linked_list_struct.get(1) {
            assert_eq!(*value, 2);
        }
    }
    
    #[test]
    fn test_error_handling_transformation() {
        let handler = UnifiedErrorHandler;
        let string_error = "Test error".to_string();
        
        let result = handler.transform(string_error);
        assert!(result.contains("String error: Test error"));
    }
    
    #[test]
    fn test_conditional_transformation() {
        let converter = ConditionalConverter;
        let valid_string = "42".to_string();
        
        let result = converter.transform_if(valid_string, |s| s.parse::<i32>().is_ok());
        assert_eq!(result, Some(42));
    }
}
