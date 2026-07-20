# Generic Programming Examples

## 📊 目录

- [Generic Programming Examples](#generic-programming-examples)
  - [📊 目录](#-目录)
  - [1. Basic Generic Examples](#1-basic-generic-examples)
    - [1.1 Identity Function](#11-identity-function)
      - [Example 1.1: Generic Identity Function](#example-11-generic-identity-function)
    - [1.2 Generic Swap Function](#12-generic-swap-function)
      - [Example 1.2: Type-Safe Swap](#example-12-type-safe-swap)
    - [1.3 Generic Container](#13-generic-container)
      - [Example 1.3: Simple Generic Container](#example-13-simple-generic-container)
  - [2. Constrained Generic Examples](#2-constrained-generic-examples)
    - [2.1 Display Function](#21-display-function)
      - [Example 2.1: Generic Display Function](#example-21-generic-display-function)
    - [2.2 Generic Comparison Functions](#22-generic-comparison-functions)
      - [Example 2.2: Ord-Constrained Functions](#example-22-ord-constrained-functions)
    - [2.3 Clone and Display Function](#23-clone-and-display-function)
      - [Example 2.3: Multiple Trait Bounds](#example-23-multiple-trait-bounds)
  - [3. Advanced Generic Examples](#3-advanced-generic-examples)
    - [3.1 Generic Iterator Adapter](#31-generic-iterator-adapter)
      - [Example 3.1: Custom Iterator Adapter](#example-31-custom-iterator-adapter)
    - [3.2 Generic Builder Pattern](#32-generic-builder-pattern)
      - [Example 3.2: Type-Safe Builder](#example-32-type-safe-builder)
    - [3.3 Generic State Machine](#33-generic-state-machine)
      - [Example 3.3: Type-Level State Machine](#example-33-type-level-state-machine)
  - [4. Real-World Examples](#4-real-world-examples)
    - [4.1 Generic Database Connection](#41-generic-database-connection)
      - [Example 4.1: Type-Safe Database Connection](#example-41-type-safe-database-connection)
    - [4.2 Generic Configuration System](#42-generic-configuration-system)
      - [Example 4.2: Type-Safe Configuration](#example-42-type-safe-configuration)
  - [5. Performance Examples](#5-performance-examples)
    - [5.1 Zero-Cost Abstractions](#51-zero-cost-abstractions)
      - [Example 5.1: Zero-Cost Generic Functions](#example-51-zero-cost-generic-functions)
    - [5.2 Generic vs Trait Objects](#52-generic-vs-trait-objects)
      - [Example 5.2: Performance Comparison](#example-52-performance-comparison)
  - [6. Summary](#6-summary)

## 1. Basic Generic Examples

### 1.1 Identity Function

#### Example 1.1: Generic Identity Function

The identity function demonstrates the most basic form of generic programming.

```rust
fn identity<T>(x: T) -> T {
    x
}

// Usage examples
fn main() {
    let int_result = identity(42);
    let string_result = identity("hello".to_string());
    let float_result = identity(3.14);
    
    println!("Integer: {}", int_result);
    println!("String: {}", string_result);
    println!("Float: {}", float_result);
    
    // Type inference works automatically
    assert_eq!(int_result, 42);
    assert_eq!(string_result, "hello");
    assert_eq!(float_result, 3.14);
}
```

**Key Points:**

- `T` is a type parameter that can be any type
- The function works identically for all types
- Type inference automatically determines the concrete type
- No runtime overhead compared to monomorphic versions

### 1.2 Generic Swap Function

#### Example 1.2: Type-Safe Swap

A generic swap function that works with any type.

```rust
fn swap<T>(a: T, b: T) -> (T, T) {
    (b, a)
}

// Usage with different types
fn main() {
    // Integer swap
    let (x, y) = swap(1, 2);
    assert_eq!((x, y), (2, 1));
    
    // String swap
    let (s1, s2) = swap("hello".to_string(), "world".to_string());
    assert_eq!(s1, "world");
    assert_eq!(s2, "hello");
    
    // Custom type swap
    #[derive(Debug, PartialEq)]
    struct Point {
        x: i32,
        y: i32,
    }
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 3, y: 4 };
    let (p3, p4) = swap(p1, p2);
    
    assert_eq!(p3.x, 3);
    assert_eq!(p3.y, 4);
    assert_eq!(p4.x, 1);
    assert_eq!(p4.y, 2);
}
```

### 1.3 Generic Container

#### Example 1.3: Simple Generic Container

A basic container that can hold any type.

```rust
struct Container<T> {
    data: Vec<T>,
}

impl<T> Container<T> {
    fn new() -> Self {
        Container { data: Vec::new() }
    }
    
    fn push(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn pop(&mut self) -> Option<T> {
        self.data.pop()
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
    
    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    
    fn clear(&mut self) {
        self.data.clear();
    }
}

// Usage
fn main() {
    let mut int_container = Container::<i32>::new();
    int_container.push(1);
    int_container.push(2);
    int_container.push(3);
    
    assert_eq!(int_container.len(), 3);
    assert_eq!(int_container.pop(), Some(3));
    assert_eq!(int_container.len(), 2);
    
    let mut string_container = Container::<String>::new();
    string_container.push("hello".to_string());
    string_container.push("world".to_string());
    
    assert_eq!(string_container.len(), 2);
    assert_eq!(string_container.pop(), Some("world".to_string()));
}
```

## 2. Constrained Generic Examples

### 2.1 Display Function

#### Example 2.1: Generic Display Function

A function that requires its type parameter to implement Display.

```rust
use std::fmt::Display;

fn print<T: Display>(item: T) {
    println!("{}", item);
}

fn print_multiple<T: Display>(items: &[T]) {
    for (i, item) in items.iter().enumerate() {
        println!("Item {}: {}", i, item);
    }
}

// Usage
fn main() {
    // Works with built-in types that implement Display
    print(42);
    print("hello");
    print(3.14);
    
    // Works with custom types that implement Display
    #[derive(Debug)]
    struct Person {
        name: String,
        age: u32,
    }
    
    impl Display for Person {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{} (age {})", self.name, self.age)
        }
    }
    
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    print(person);
    
    // Works with collections
    let numbers = vec![1, 2, 3, 4, 5];
    print_multiple(&numbers);
    
    let people = vec![
        Person { name: "Alice".to_string(), age: 30 },
        Person { name: "Bob".to_string(), age: 25 },
    ];
    print_multiple(&people);
}
```

### 2.2 Generic Comparison Functions

#### Example 2.2: Ord-Constrained Functions

Functions that require their type parameters to implement Ord.

```rust
use std::cmp::Ord;

fn max<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

fn min<T: Ord>(a: T, b: T) -> T {
    if a < b { a } else { b }
}

fn sort<T: Ord>(items: &mut [T]) {
    items.sort();
}

fn find_max<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().max()
}

fn find_min<T: Ord>(items: &[T]) -> Option<&T> {
    items.iter().min()
}

// Usage
fn main() {
    // Integer comparisons
    assert_eq!(max(10, 20), 20);
    assert_eq!(min(10, 20), 10);
    
    // String comparisons
    assert_eq!(max("apple", "banana"), "banana");
    assert_eq!(min("apple", "banana"), "apple");
    
    // Custom type comparisons
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    struct Student {
        name: String,
        grade: u32,
    }
    
    let mut students = vec![
        Student { name: "Alice".to_string(), grade: 85 },
        Student { name: "Bob".to_string(), grade: 92 },
        Student { name: "Charlie".to_string(), grade: 78 },
    ];
    
    sort(&mut students);
    
    assert_eq!(find_max(&students).unwrap().name, "Bob");
    assert_eq!(find_min(&students).unwrap().name, "Charlie");
}
```

### 2.3 Clone and Display Function

#### Example 2.3: Multiple Trait Bounds

A function that requires multiple trait bounds.

```rust
use std::fmt::Display;

fn print_and_clone<T: Clone + Display>(item: T) -> T {
    println!("Original: {}", item);
    let cloned = item.clone();
    println!("Cloned: {}", cloned);
    cloned
}

fn process_items<T: Clone + Display + Debug>(items: &[T]) -> Vec<T> {
    items.iter().map(|item| {
        println!("Processing: {:?}", item);
        item.clone()
    }).collect()
}

// Usage
fn main() {
    use std::fmt::Debug;
    
    // Works with types that implement both Clone and Display
    let result = print_and_clone("hello".to_string());
    assert_eq!(result, "hello");
    
    let result = print_and_clone(42);
    assert_eq!(result, 42);
    
    // Custom type with multiple trait implementations
    #[derive(Debug, Clone)]
    struct Product {
        name: String,
        price: f64,
    }
    
    impl Display for Product {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{} - ${:.2}", self.name, self.price)
        }
    }
    
    let products = vec![
        Product { name: "Laptop".to_string(), price: 999.99 },
        Product { name: "Mouse".to_string(), price: 29.99 },
    ];
    
    let processed = process_items(&products);
    assert_eq!(processed.len(), 2);
}
```

## 3. Advanced Generic Examples

### 3.1 Generic Iterator Adapter

#### Example 3.1: Custom Iterator Adapter

A generic iterator adapter that transforms elements.

```rust
struct MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    iter: I,
    f: F,
    _phantom: std::marker::PhantomData<(T, U)>,
}

impl<I, F, T, U> MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    fn new(iter: I, f: F) -> Self {
        MapIterator {
            iter,
            f,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<I, F, T, U> Iterator for MapIterator<I, F, T, U>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> U
{
    type Item = U;
    
    fn next(&mut self) -> Option<U> {
        self.iter.next().map(&self.f)
    }
}

// Usage
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled = MapIterator::new(numbers.into_iter(), |x| x * 2);
    
    let result: Vec<i32> = doubled.collect();
    assert_eq!(result, vec![2, 4, 6, 8, 10]);
    
    // String transformation
    let words = vec!["hello", "world", "rust"];
    let uppercased = MapIterator::new(words.into_iter(), |s| s.to_uppercase());
    
    let result: Vec<String> = uppercased.collect();
    assert_eq!(result, vec!["HELLO", "WORLD", "RUST"]);
}
```

### 3.2 Generic Builder Pattern

#### Example 3.2: Type-Safe Builder

A generic builder that constructs objects with type safety.

```rust
struct Builder<T> {
    data: Option<T>,
    validations: Vec<Box<dyn Fn(&T) -> bool>>,
}

impl<T> Builder<T> {
    fn new() -> Self {
        Builder {
            data: None,
            validations: Vec::new(),
        }
    }
    
    fn with_data(mut self, data: T) -> Self {
        self.data = Some(data);
        self
    }
    
    fn with_validation<F>(mut self, validation: F) -> Self
    where
        F: Fn(&T) -> bool + 'static
    {
        self.validations.push(Box::new(validation));
        self
    }
    
    fn build(self) -> Result<T, String> {
        let data = self.data.ok_or_else(|| "No data provided".to_string())?;
        
        for (i, validation) in self.validations.iter().enumerate() {
            if !validation(&data) {
                return Err(format!("Validation {} failed", i));
            }
        }
        
        Ok(data)
    }
}

// Usage
fn main() {
    // Integer builder with validation
    let result = Builder::<i32>::new()
        .with_data(42)
        .with_validation(|x| *x > 0)
        .with_validation(|x| *x < 100)
        .build();
    
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
    
    // String builder with validation
    let result = Builder::<String>::new()
        .with_data("hello".to_string())
        .with_validation(|s| !s.is_empty())
        .with_validation(|s| s.len() < 10)
        .build();
    
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "hello");
    
    // Failed validation
    let result = Builder::<i32>::new()
        .with_data(-5)
        .with_validation(|x| *x > 0)
        .build();
    
    assert!(result.is_err());
}
```

### 3.3 Generic State Machine

#### Example 3.3: Type-Level State Machine

A state machine where states are represented as types.

```rust
use std::marker::PhantomData;

// State types
struct Uninitialized;
struct Initialized;
struct Running;
struct Stopped;

// State machine
struct StateMachine<State> {
    data: String,
    _phantom: PhantomData<State>,
}

// Uninitialized state
impl StateMachine<Uninitialized> {
    fn new() -> Self {
        StateMachine {
            data: String::new(),
            _phantom: PhantomData,
        }
    }
    
    fn initialize(self, data: String) -> StateMachine<Initialized> {
        StateMachine {
            data,
            _phantom: PhantomData,
        }
    }
}

// Initialized state
impl StateMachine<Initialized> {
    fn start(self) -> StateMachine<Running> {
        StateMachine {
            data: self.data,
            _phantom: PhantomData,
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// Running state
impl StateMachine<Running> {
    fn stop(self) -> StateMachine<Stopped> {
        StateMachine {
            data: self.data,
            _phantom: PhantomData,
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
    
    fn update_data(&mut self, new_data: String) {
        self.data = new_data;
    }
}

// Stopped state
impl StateMachine<Stopped> {
    fn restart(self) -> StateMachine<Running> {
        StateMachine {
            data: self.data,
            _phantom: PhantomData,
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// Usage
fn main() {
    // Create new state machine
    let machine = StateMachine::<Uninitialized>::new();
    
    // Initialize
    let machine = machine.initialize("Hello, World!".to_string());
    assert_eq!(machine.get_data(), "Hello, World!");
    
    // Start
    let mut machine = machine.start();
    assert_eq!(machine.get_data(), "Hello, World!");
    
    // Update data while running
    machine.update_data("Updated data".to_string());
    assert_eq!(machine.get_data(), "Updated data");
    
    // Stop
    let machine = machine.stop();
    assert_eq!(machine.get_data(), "Updated data");
    
    // Restart
    let machine = machine.restart();
    assert_eq!(machine.get_data(), "Updated data");
    
    // Invalid transitions are prevented at compile time
    // let machine = StateMachine::<Uninitialized>::new();
    // machine.start(); // Compile error: method not found
}
```

## 4. Real-World Examples

### 4.1 Generic Database Connection

#### Example 4.1: Type-Safe Database Connection

A generic database connection with different permission levels.

```rust
use std::marker::PhantomData;

// Permission types
struct ReadOnly;
struct ReadWrite;
struct Admin;

// Database connection
struct DatabaseConnection<Permission> {
    connection_string: String,
    _phantom: PhantomData<Permission>,
}

impl DatabaseConnection<ReadOnly> {
    fn new_readonly(connection_string: String) -> Self {
        DatabaseConnection {
            connection_string,
            _phantom: PhantomData,
        }
    }
    
    fn query(&self, sql: &str) -> Result<String, String> {
        Ok(format!("Read-only query: {}", sql))
    }
}

impl DatabaseConnection<ReadWrite> {
    fn new_readwrite(connection_string: String) -> Self {
        DatabaseConnection {
            connection_string,
            _phantom: PhantomData,
        }
    }
    
    fn query(&self, sql: &str) -> Result<String, String> {
        Ok(format!("Read-write query: {}", sql))
    }
    
    fn execute(&self, sql: &str) -> Result<usize, String> {
        Ok(format!("Executed: {}", sql).len())
    }
}

impl DatabaseConnection<Admin> {
    fn new_admin(connection_string: String) -> Self {
        DatabaseConnection {
            connection_string,
            _phantom: PhantomData,
        }
    }
    
    fn query(&self, sql: &str) -> Result<String, String> {
        Ok(format!("Admin query: {}", sql))
    }
    
    fn execute(&self, sql: &str) -> Result<usize, String> {
        Ok(format!("Admin executed: {}", sql).len())
    }
    
    fn create_user(&self, username: &str) -> Result<(), String> {
        Ok(println!("Created user: {}", username))
    }
    
    fn drop_database(&self, name: &str) -> Result<(), String> {
        Ok(println!("Dropped database: {}", name))
    }
}

// Usage
fn main() {
    // Read-only connection
    let readonly = DatabaseConnection::<ReadOnly>::new_readonly(
        "postgresql://localhost/db".to_string()
    );
    let result = readonly.query("SELECT * FROM users");
    assert!(result.is_ok());
    
    // Read-write connection
    let readwrite = DatabaseConnection::<ReadWrite>::new_readwrite(
        "postgresql://localhost/db".to_string()
    );
    let result = readwrite.query("SELECT * FROM users");
    assert!(result.is_ok());
    let result = readwrite.execute("INSERT INTO users VALUES (1, 'Alice')");
    assert!(result.is_ok());
    
    // Admin connection
    let admin = DatabaseConnection::<Admin>::new_admin(
        "postgresql://localhost/db".to_string()
    );
    let result = admin.create_user("newuser");
    assert!(result.is_ok());
    let result = admin.drop_database("olddb");
    assert!(result.is_ok());
    
    // Type safety prevents invalid operations
    // readonly.execute("INSERT ..."); // Compile error: method not found
    // readwrite.create_user("user"); // Compile error: method not found
}
```

### 4.2 Generic Configuration System

#### Example 4.2: Type-Safe Configuration

A generic configuration system with validation.

```rust
use std::collections::HashMap;
use std::fmt::Display;

trait ConfigValue: Clone + Display {
    fn validate(&self) -> Result<(), String>;
}

impl ConfigValue for String {
    fn validate(&self) -> Result<(), String> {
        if self.is_empty() {
            Err("String cannot be empty".to_string())
        } else {
            Ok(())
        }
    }
}

impl ConfigValue for i32 {
    fn validate(&self) -> Result<(), String> {
        if *self < 0 {
            Err("Integer must be non-negative".to_string())
        } else {
            Ok(())
        }
    }
}

impl ConfigValue for bool {
    fn validate(&self) -> Result<(), String> {
        Ok(()) // All boolean values are valid
    }
}

struct Configuration<T: ConfigValue> {
    values: HashMap<String, T>,
}

impl<T: ConfigValue> Configuration<T> {
    fn new() -> Self {
        Configuration {
            values: HashMap::new(),
        }
    }
    
    fn set(&mut self, key: String, value: T) -> Result<(), String> {
        value.validate()?;
        self.values.insert(key, value);
        Ok(())
    }
    
    fn get(&self, key: &str) -> Option<&T> {
        self.values.get(key)
    }
    
    fn remove(&mut self, key: &str) -> Option<T> {
        self.values.remove(key)
    }
    
    fn keys(&self) -> Vec<&String> {
        self.values.keys().collect()
    }
    
    fn len(&self) -> usize {
        self.values.len()
    }
}

// Usage
fn main() {
    // String configuration
    let mut string_config = Configuration::<String>::new();
    string_config.set("app_name".to_string(), "MyApp".to_string()).unwrap();
    string_config.set("version".to_string(), "1.0.0".to_string()).unwrap();
    
    assert_eq!(string_config.get("app_name"), Some(&"MyApp".to_string()));
    assert_eq!(string_config.len(), 2);
    
    // Integer configuration
    let mut int_config = Configuration::<i32>::new();
    int_config.set("port".to_string(), 8080).unwrap();
    int_config.set("timeout".to_string(), 30).unwrap();
    
    assert_eq!(int_config.get("port"), Some(&8080));
    
    // Boolean configuration
    let mut bool_config = Configuration::<bool>::new();
    bool_config.set("debug".to_string(), true).unwrap();
    bool_config.set("production".to_string(), false).unwrap();
    
    assert_eq!(bool_config.get("debug"), Some(&true));
    
    // Validation errors
    let result = string_config.set("empty".to_string(), "".to_string());
    assert!(result.is_err());
    
    let result = int_config.set("negative".to_string(), -5);
    assert!(result.is_err());
}
```

## 5. Performance Examples

### 5.1 Zero-Cost Abstractions

#### Example 5.1: Zero-Cost Generic Functions

Demonstrating that generics have no runtime overhead.

```rust
use std::time::Instant;

// Generic function
fn generic_add<T: std::ops::Add<Output = T> + Copy>(a: T, b: T) -> T {
    a + b
}

// Monomorphic versions for comparison
fn add_i32(a: i32, b: i32) -> i32 {
    a + b
}

fn add_f64(a: f64, b: f64) -> f64 {
    a + b
}

// Performance test
fn main() {
    let iterations = 1_000_000;
    
    // Test generic function
    let start = Instant::now();
    for i in 0..iterations {
        let _ = generic_add(i as i32, 1);
    }
    let generic_time = start.elapsed();
    
    // Test monomorphic function
    let start = Instant::now();
    for i in 0..iterations {
        let _ = add_i32(i as i32, 1);
    }
    let mono_time = start.elapsed();
    
    println!("Generic time: {:?}", generic_time);
    println!("Monomorphic time: {:?}", mono_time);
    println!("Difference: {:?}", generic_time - mono_time);
    
    // The difference should be negligible (zero-cost abstraction)
    assert!(generic_time - mono_time < std::time::Duration::from_millis(1));
}
```

### 5.2 Generic vs Trait Objects

#### Example 5.2: Performance Comparison

Comparing generic functions with trait objects.

```rust
use std::time::Instant;

trait Processor {
    fn process(&self, input: i32) -> i32;
}

struct Adder;
struct Multiplier;

impl Processor for Adder {
    fn process(&self, input: i32) -> i32 {
        input + 1
    }
}

impl Processor for Multiplier {
    fn process(&self, input: i32) -> i32 {
        input * 2
    }
}

// Generic function (static dispatch)
fn generic_process<T: Processor>(processor: &T, input: i32) -> i32 {
    processor.process(input)
}

// Trait object function (dynamic dispatch)
fn trait_object_process(processor: &dyn Processor, input: i32) -> i32 {
    processor.process(input)
}

// Performance test
fn main() {
    let iterations = 1_000_000;
    let adder = Adder;
    let multiplier = Multiplier;
    
    // Test generic function
    let start = Instant::now();
    for i in 0..iterations {
        let _ = generic_process(&adder, i);
        let _ = generic_process(&multiplier, i);
    }
    let generic_time = start.elapsed();
    
    // Test trait object function
    let start = Instant::now();
    for i in 0..iterations {
        let _ = trait_object_process(&adder, i);
        let _ = trait_object_process(&multiplier, i);
    }
    let trait_object_time = start.elapsed();
    
    println!("Generic time: {:?}", generic_time);
    println!("Trait object time: {:?}", trait_object_time);
    println!("Generic is {}x faster", 
             trait_object_time.as_nanos() as f64 / generic_time.as_nanos() as f64);
    
    // Generic should be faster due to static dispatch
    assert!(generic_time < trait_object_time);
}
```

## 6. Summary

These examples demonstrate:

1. **Type Safety**: Compile-time guarantees for all generic code
2. **Zero Cost**: No runtime overhead compared to monomorphic code
3. **Expressiveness**: Complex abstractions with simple interfaces
4. **Reusability**: Single implementation works with multiple types
5. **Performance**: Static dispatch provides optimal performance

Generic programming in Rust provides powerful abstractions while maintaining compile-time safety and zero runtime overhead, making it ideal for systems programming and performance-critical applications.

---

**References:**

- [Rust Book - Generic Types](https://doc.rust-lang.org/book/ch10-01-syntax.html)
- [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Rust Reference - Generics](https://doc.rust-lang.org/reference/items/generics.html)
