# Rust 所有权系统高级模式与最佳实践

## 概述

本文档深入解析 Rust 所有权系统的高级模式与最佳实践，包括详细的中英文注释、规范的语言使用、全面的解释和丰富的示例，充分挖掘 Rust 1.89 版本的语言特性。

## 1. 高级所有权模式

### 1.1 所有权转移模式

```rust
//! 高级所有权模式 / Advanced Ownership Patterns
//! 
//! 所有权转移模式是 Rust 中管理资源的核心模式 / Ownership transfer patterns are core patterns for managing resources in Rust
//! 通过精心设计的所有权转移，可以实现高效的内存管理 / Through carefully designed ownership transfer, efficient memory management can be achieved

/// 所有权转移模式详解 / Ownership Transfer Patterns Explained
fn ownership_transfer_patterns() {
    // 模式 1：函数参数所有权转移 / Pattern 1: Function parameter ownership transfer
    let data = String::from("hello");
    takes_ownership(data);
    // data 不再有效，因为所有权已经转移 / data is no longer valid because ownership has been transferred
    
    // 模式 2：返回值所有权转移 / Pattern 2: Return value ownership transfer
    let new_data = gives_ownership();
    println!("New data: {}", new_data);
    
    // 模式 3：链式所有权转移 / Pattern 3: Chained ownership transfer
    let processed_data = takes_and_gives_back(new_data);
    println!("Processed data: {}", processed_data);
}

/// 获取所有权的函数 / Function that takes ownership
fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string 在这里离开作用域并被丢弃 / some_string goes out of scope and is dropped

/// 返回所有权的函数 / Function that returns ownership
fn gives_ownership() -> String {
    let some_string = String::from("yours");
    some_string // 返回所有权 / return ownership
}

/// 获取并返回所有权的函数 / Function that takes and returns ownership
fn takes_and_gives_back(a_string: String) -> String {
    a_string // 返回所有权 / return ownership
}
```

### 1.2 智能指针所有权模式

```rust
/// 智能指针所有权模式 / Smart Pointer Ownership Patterns
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

fn smart_pointer_ownership_patterns() {
    // 模式 1：Rc 共享所有权 / Pattern 1: Rc shared ownership
    let data = Rc::new(String::from("hello"));
    let data_clone1 = Rc::clone(&data);
    let data_clone2 = Rc::clone(&data);
    
    println!("Data: {}, Clone1: {}, Clone2: {}", data, data_clone1, data_clone2);
    
    // 模式 2：RefCell 内部可变性 / Pattern 2: RefCell interior mutability
    let mutable_data = RefCell::new(String::from("world"));
    {
        let mut borrowed = mutable_data.borrow_mut();
        borrowed.push_str("!");
    }
    println!("Mutable data: {}", mutable_data.borrow());
    
    // 模式 3：Arc 线程安全共享所有权 / Pattern 3: Arc thread-safe shared ownership
    let shared_data = Arc::new(Mutex::new(String::from("rust")));
    let shared_clone = Arc::clone(&shared_data);
    
    {
        let mut data_guard = shared_data.lock().unwrap();
        data_guard.push_str("!");
    }
    
    println!("Shared data: {}", shared_clone.lock().unwrap());
}
```

### 1.3 所有权模式组合

```rust
/// 所有权模式组合 / Ownership Pattern Combinations
fn ownership_pattern_combinations() {
    // 组合 1：Rc + RefCell / Combination 1: Rc + RefCell
    let shared_mutable_data = Rc::new(RefCell::new(vec![1, 2, 3]));
    let shared_clone1 = Rc::clone(&shared_mutable_data);
    let shared_clone2 = Rc::clone(&shared_mutable_data);
    
    // 可以同时修改共享数据 / Can modify shared data simultaneously
    shared_clone1.borrow_mut().push(4);
    shared_clone2.borrow_mut().push(5);
    
    println!("Shared mutable data: {:?}", shared_mutable_data.borrow());
    
    // 组合 2：Arc + Mutex / Combination 2: Arc + Mutex
    let thread_safe_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let thread_safe_clone = Arc::clone(&thread_safe_data);
    
    // 线程安全的修改 / Thread-safe modification
    {
        let mut data_guard = thread_safe_data.lock().unwrap();
        data_guard.push(4);
    }
    
    println!("Thread safe data: {:?}", thread_safe_clone.lock().unwrap());
}
```

## 2. 高级借用模式

### 2.1 借用模式优化

```rust
/// 借用模式优化 / Borrowing Pattern Optimization
fn borrowing_pattern_optimization() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 优化 1：最小化借用作用域 / Optimization 1: Minimize borrow scopes
    {
        let reference = &data[0];
        println!("Reference: {}", reference);
    } // 借用在这里结束 / Borrow ends here
    
    // 现在可以安全地修改 data / Now it's safe to modify data
    data.push(6);
    
    // 优化 2：使用切片避免索引 / Optimization 2: Use slices to avoid indexing
    let slice = &data[1..4];
    println!("Slice: {:?}", slice);
    
    // 优化 3：使用迭代器避免借用 / Optimization 3: Use iterators to avoid borrowing
    let sum: i32 = data.iter().sum();
    println!("Sum: {}", sum);
    
    // 优化 4：使用引用避免所有权转移 / Optimization 4: Use references to avoid ownership transfer
    let processed = process_data(&data);
    println!("Processed: {:?}", processed);
}

/// 处理数据的函数 / Function to process data
fn process_data(data: &[i32]) -> Vec<i32> {
    data.iter().map(|&x| x * 2).collect()
}
```

### 2.2 复杂借用模式

```rust
/// 复杂借用模式 / Complex Borrowing Patterns
fn complex_borrowing_patterns() {
    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 模式 1：同时借用不同部分 / Pattern 1: Borrowing different parts simultaneously
    let (left, right) = data.split_at_mut(5);
    let (left_first, left_second) = left.split_at_mut(2);
    let (right_first, right_second) = right.split_at_mut(2);
    
    // 可以同时修改不同部分 / Can modify different parts simultaneously
    left_first[0] = 10;
    left_second[0] = 20;
    right_first[0] = 30;
    right_second[0] = 40;
    
    println!("Modified data: {:?}", data);
    
    // 模式 2：结构体字段借用 / Pattern 2: Struct field borrowing
    let mut container = DataContainer {
        data: vec![1, 2, 3],
        metadata: String::from("test"),
    };
    
    let data_ref = &container.data;
    let metadata_ref = &container.metadata;
    
    println!("Data: {:?}, Metadata: {}", data_ref, metadata_ref);
    
    // 模式 3：可变字段借用 / Pattern 3: Mutable field borrowing
    let data_mut_ref = &mut container.data;
    data_mut_ref.push(4);
    println!("Modified data: {:?}", data_mut_ref);
}

/// 数据容器结构体 / Data Container Struct
struct DataContainer {
    data: Vec<i32>,
    metadata: String,
}
```

### 2.3 借用模式最佳实践

```rust
/// 借用模式最佳实践 / Borrowing Pattern Best Practices
fn borrowing_pattern_best_practices() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 最佳实践 1：优先使用引用 / Best Practice 1: Prefer references
    let result = calculate_sum(&data);
    println!("Sum: {}", result);
    
    // 最佳实践 2：最小化借用作用域 / Best Practice 2: Minimize borrow scopes
    {
        let reference = &data[0];
        println!("Reference: {}", reference);
    }
    
    // 最佳实践 3：使用切片 / Best Practice 3: Use slices
    let slice = &data[1..4];
    println!("Slice: {:?}", slice);
    
    // 最佳实践 4：使用迭代器 / Best Practice 4: Use iterators
    let filtered: Vec<_> = data.iter().filter(|&&x| x > 2).collect();
    println!("Filtered: {:?}", filtered);
    
    // 最佳实践 5：使用智能指针 / Best Practice 5: Use smart pointers
    let shared_data = Rc::new(data);
    let shared_clone = Rc::clone(&shared_data);
    
    println!("Shared data: {:?}", shared_data);
    println!("Shared clone: {:?}", shared_clone);
}

/// 计算和的函数 / Function to calculate sum
fn calculate_sum(data: &[i32]) -> i32 {
    data.iter().sum()
}
```

## 3. 高级生命周期模式

### 3.1 生命周期模式设计

```rust
/// 生命周期模式设计 / Lifetime Pattern Design
fn lifetime_pattern_design() {
    let string1 = String::from("hello");
    let string2 = "world";
    
    // 模式 1：最小化生命周期参数 / Pattern 1: Minimize lifetime parameters
    let result = minimal_lifetime_function(&string1, string2);
    println!("Minimal lifetime result: {}", result);
    
    // 模式 2：使用生命周期约束 / Pattern 2: Use lifetime constraints
    let result2 = constrained_lifetime_function(&string1, string2);
    println!("Constrained lifetime result: {}", result2);
    
    // 模式 3：利用生命周期省略 / Pattern 3: Leverage lifetime elision
    let result3 = elided_lifetime_function(&string1, string2);
    println!("Elided lifetime result: {}", result3);
}

/// 最小化生命周期参数的函数 / Function with Minimal Lifetime Parameters
fn minimal_lifetime_function<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 带生命周期约束的函数 / Function with Lifetime Constraints
fn constrained_lifetime_function<'a, 'b: 'a>(x: &'a str, y: &'b str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 利用生命周期省略的函数 / Function Leveraging Lifetime Elision
fn elided_lifetime_function(x: &str, y: &str) -> &str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 3.2 复杂生命周期模式

```rust
/// 复杂生命周期模式 / Complex Lifetime Patterns
fn complex_lifetime_patterns() {
    let string1 = String::from("hello");
    let string2 = "world";
    let string3 = String::from("rust");
    
    // 模式 1：多个生命周期参数 / Pattern 1: Multiple lifetime parameters
    let result = multiple_lifetime_function(&string1, string2, &string3);
    println!("Multiple lifetime result: {}", result);
    
    // 模式 2：生命周期约束 / Pattern 2: Lifetime constraints
    let result2 = constrained_multiple_lifetime_function(&string1, string2, &string3);
    println!("Constrained multiple lifetime result: {}", result2);
    
    // 模式 3：复杂生命周期约束 / Pattern 3: Complex lifetime constraints
    let result3 = complex_constrained_lifetime_function(&string1, string2, &string3);
    println!("Complex constrained lifetime result: {}", result3);
}

/// 带多个生命周期参数的函数 / Function with Multiple Lifetime Parameters
fn multiple_lifetime_function<'a, 'b>(x: &'a str, y: &'b str, z: &'a str) -> &'a str {
    if x.len() > y.len() && x.len() > z.len() {
        x
    } else if z.len() > y.len() {
        z
    } else {
        y
    }
}

/// 带约束的多个生命周期参数函数 / Function with Constrained Multiple Lifetime Parameters
fn constrained_multiple_lifetime_function<'a, 'b: 'a>(x: &'a str, y: &'b str, z: &'a str) -> &'a str {
    if x.len() > y.len() && x.len() > z.len() {
        x
    } else if z.len() > y.len() {
        z
    } else {
        y
    }
}

/// 带复杂约束的生命周期函数 / Function with Complex Lifetime Constraints
fn complex_constrained_lifetime_function<'a, 'b: 'a, 'c: 'a>(x: &'a str, y: &'b str, z: &'c str) -> &'a str {
    if x.len() > y.len() && x.len() > z.len() {
        x
    } else if z.len() > y.len() {
        z
    } else {
        y
    }
}
```

## 4. 内存安全模式

### 4.1 内存安全设计模式

```rust
/// 内存安全设计模式 / Memory Safety Design Patterns
fn memory_safety_design_patterns() {
    // 模式 1：RAII 模式 / Pattern 1: RAII Pattern
    let resource = Resource::new("test");
    println!("Resource: {:?}", resource);
    // 资源在离开作用域时自动释放 / Resource is automatically released when it goes out of scope
    
    // 模式 2：智能指针模式 / Pattern 2: Smart Pointer Pattern
    let smart_resource = SmartResource::new("smart");
    let smart_clone = SmartResource::clone(&smart_resource);
    println!("Smart resource: {:?}, Clone: {:?}", smart_resource, smart_clone);
    
    // 模式 3：借用模式 / Pattern 3: Borrowing Pattern
    let data = vec![1, 2, 3];
    let reference = &data[0];
    println!("Reference: {}", reference);
    // 借用结束后可以安全地修改数据 / After borrow ends, data can be safely modified
}

/// 资源结构体 / Resource Struct
#[derive(Debug)]
struct Resource {
    name: String,
}

impl Resource {
    fn new(name: &str) -> Self {
        println!("Creating resource: {}", name);
        Self {
            name: name.to_string(),
        }
    }
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Dropping resource: {}", self.name);
    }
}

/// 智能资源结构体 / Smart Resource Struct
#[derive(Debug, Clone)]
struct SmartResource {
    name: String,
    reference_count: Rc<RefCell<usize>>,
}

impl SmartResource {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            reference_count: Rc::new(RefCell::new(1)),
        }
    }
    
    fn clone(&self) -> Self {
        *self.reference_count.borrow_mut() += 1;
        Self {
            name: self.name.clone(),
            reference_count: Rc::clone(&self.reference_count),
        }
    }
}
```

### 4.2 内存泄漏防护模式

```rust
/// 内存泄漏防护模式 / Memory Leak Prevention Patterns
fn memory_leak_prevention_patterns() {
    // 模式 1：循环引用防护 / Pattern 1: Circular Reference Prevention
    let node1 = Rc::new(RefCell::new(Node::new("node1")));
    let node2 = Rc::new(RefCell::new(Node::new("node2")));
    
    // 使用 Weak 引用避免循环引用 / Use Weak references to avoid circular references
    node1.borrow_mut().set_parent(Rc::downgrade(&node2));
    node2.borrow_mut().set_parent(Rc::downgrade(&node1));
    
    println!("Node1: {:?}", node1);
    println!("Node2: {:?}", node2);
    
    // 模式 2：资源管理 / Pattern 2: Resource Management
    let manager = ResourceManager::new();
    let resource1 = manager.create_resource("resource1");
    let resource2 = manager.create_resource("resource2");
    
    println!("Manager: {:?}", manager);
    println!("Resource1: {:?}", resource1);
    println!("Resource2: {:?}", resource2);
}

/// 节点结构体 / Node Struct
#[derive(Debug)]
struct Node {
    name: String,
    parent: Option<std::rc::Weak<RefCell<Node>>>,
}

impl Node {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            parent: None,
        }
    }
    
    fn set_parent(&mut self, parent: std::rc::Weak<RefCell<Node>>) {
        self.parent = Some(parent);
    }
}

/// 资源管理器 / Resource Manager
#[derive(Debug)]
struct ResourceManager {
    resources: Vec<String>,
}

impl ResourceManager {
    fn new() -> Self {
        Self {
            resources: Vec::new(),
        }
    }
    
    fn create_resource(&mut self, name: &str) -> String {
        let resource = name.to_string();
        self.resources.push(resource.clone());
        resource
    }
}
```

## 5. 并发安全模式

### 5.1 线程安全模式

```rust
/// 线程安全模式 / Thread Safety Patterns
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

fn thread_safety_patterns() {
    // 模式 1：Mutex 模式 / Pattern 1: Mutex Pattern
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut data_guard = data_clone.lock().unwrap();
            data_guard.push(i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Mutex data: {:?}", data.lock().unwrap());
    
    // 模式 2：RwLock 模式 / Pattern 2: RwLock Pattern
    let rw_data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程 / Multiple reader threads
    for i in 0..3 {
        let data_clone = Arc::clone(&rw_data);
        let handle = thread::spawn(move || {
            let data_guard = data_clone.read().unwrap();
            println!("Reader {}: {:?}", i, *data_guard);
        });
        handles.push(handle);
    }
    
    // 一个写线程 / One writer thread
    let data_clone = Arc::clone(&rw_data);
    let handle = thread::spawn(move || {
        let mut data_guard = data_clone.write().unwrap();
        data_guard.push(4);
        println!("Writer: {:?}", *data_guard);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 5.2 异步安全模式

```rust
/// 异步安全模式 / Async Safety Patterns
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

fn async_safety_patterns() {
    // 模式 1：异步所有权管理 / Pattern 1: Async Ownership Management
    let data = vec![1, 2, 3];
    let future = async_ownership_example(data);
    
    println!("Async result: {:?}", futures::executor::block_on(future));
    
    // 模式 2：异步借用管理 / Pattern 2: Async Borrowing Management
    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let future2 = async_borrowing_example(shared_data);
    
    println!("Async borrowing result: {:?}", futures::executor::block_on(future2));
}

async fn async_ownership_example(data: Vec<i32>) -> Vec<i32> {
    // 异步环境中的所有权管理 / Ownership management in async environments
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    data.into_iter().map(|x| x * 2).collect()
}

async fn async_borrowing_example(data: Arc<Mutex<Vec<i32>>>) -> Vec<i32> {
    // 异步环境中的借用管理 / Borrowing management in async environments
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    
    let data_guard = data.lock().unwrap();
    data_guard.clone()
}
```

## 6. 性能优化模式

### 6.1 零成本抽象模式

```rust
/// 零成本抽象模式 / Zero-Cost Abstraction Patterns
fn zero_cost_abstraction_patterns() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 模式 1：迭代器链 / Pattern 1: Iterator Chains
    let result: Vec<i32> = data
        .iter()
        .filter(|&&x| x > 2)
        .map(|&x| x * 2)
        .collect();
    
    println!("Iterator chain result: {:?}", result);
    
    // 模式 2：借用优化 / Pattern 2: Borrowing Optimization
    let sum: i32 = data.iter().sum();
    println!("Sum: {}", sum);
    
    // 模式 3：移动优化 / Pattern 3: Move Optimization
    let moved_data = data;
    let processed = process_moved_data(moved_data);
    println!("Processed: {:?}", processed);
}

/// 处理移动数据的函数 / Function to process moved data
fn process_moved_data(mut data: Vec<i32>) -> Vec<i32> {
    data.push(6);
    data.sort();
    data
}
```

### 6.2 内存布局优化模式

```rust
/// 内存布局优化模式 / Memory Layout Optimization Patterns
fn memory_layout_optimization_patterns() {
    // 模式 1：结构体内存布局优化 / Pattern 1: Struct Memory Layout Optimization
    let optimized_struct = OptimizedStruct {
        field1: 42,
        field2: 3.14,
        field3: true,
    };
    
    println!("Optimized struct: {:?}", optimized_struct);
    
    // 模式 2：枚举内存布局优化 / Pattern 2: Enum Memory Layout Optimization
    let optimized_enum = OptimizedEnum::Variant1(42);
    println!("Optimized enum: {:?}", optimized_enum);
    
    // 模式 3：数组内存布局优化 / Pattern 3: Array Memory Layout Optimization
    let optimized_array = [1, 2, 3, 4, 5];
    println!("Optimized array: {:?}", optimized_array);
}

/// 优化的结构体 / Optimized Struct
#[derive(Debug)]
#[repr(C)]
struct OptimizedStruct {
    field1: i32,
    field2: f64,
    field3: bool,
}

/// 优化的枚举 / Optimized Enum
#[derive(Debug)]
#[repr(C)]
enum OptimizedEnum {
    Variant1(i32),
    Variant2(f64),
    Variant3(bool),
}
```

## 7. 错误处理模式

### 7.1 所有权错误处理

```rust
/// 所有权错误处理模式 / Ownership Error Handling Patterns
fn ownership_error_handling_patterns() {
    // 模式 1：Result 模式 / Pattern 1: Result Pattern
    let result = safe_ownership_function();
    match result {
        Ok(value) => println!("Success: {}", value),
        Err(error) => println!("Error: {}", error),
    }
    
    // 模式 2：Option 模式 / Pattern 2: Option Pattern
    let option = safe_option_function();
    match option {
        Some(value) => println!("Some: {}", value),
        None => println!("None"),
    }
    
    // 模式 3：自定义错误类型 / Pattern 3: Custom Error Types
    let custom_result = safe_custom_error_function();
    match custom_result {
        Ok(value) => println!("Custom success: {}", value),
        Err(error) => println!("Custom error: {}", error),
    }
}

/// 安全的所有权函数 / Safe Ownership Function
fn safe_ownership_function() -> Result<String, String> {
    let data = String::from("hello");
    if data.len() > 0 {
        Ok(data)
    } else {
        Err("Empty string".to_string())
    }
}

/// 安全的 Option 函数 / Safe Option Function
fn safe_option_function() -> Option<String> {
    let data = String::from("world");
    if data.len() > 0 {
        Some(data)
    } else {
        None
    }
}

/// 安全的自定义错误函数 / Safe Custom Error Function
fn safe_custom_error_function() -> Result<String, CustomError> {
    let data = String::from("rust");
    if data.len() > 0 {
        Ok(data)
    } else {
        Err(CustomError::EmptyString)
    }
}

/// 自定义错误类型 / Custom Error Type
#[derive(Debug)]
enum CustomError {
    EmptyString,
    InvalidInput,
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CustomError::EmptyString => write!(f, "Empty string"),
            CustomError::InvalidInput => write!(f, "Invalid input"),
        }
    }
}

impl std::error::Error for CustomError {}
```

### 7.2 借用错误处理

```rust
/// 借用错误处理模式 / Borrowing Error Handling Patterns
fn borrowing_error_handling_patterns() {
    let mut data = vec![1, 2, 3];
    
    // 模式 1：借用检查 / Pattern 1: Borrow Checking
    let result = safe_borrowing_function(&data);
    match result {
        Ok(value) => println!("Borrow success: {}", value),
        Err(error) => println!("Borrow error: {}", error),
    }
    
    // 模式 2：RefCell 错误处理 / Pattern 2: RefCell Error Handling
    let refcell_data = RefCell::new(vec![1, 2, 3]);
    let result2 = safe_refcell_function(&refcell_data);
    match result2 {
        Ok(value) => println!("RefCell success: {:?}", value),
        Err(error) => println!("RefCell error: {}", error),
    }
}

/// 安全的借用函数 / Safe Borrowing Function
fn safe_borrowing_function(data: &[i32]) -> Result<i32, String> {
    if data.is_empty() {
        Err("Empty data".to_string())
    } else {
        Ok(data[0])
    }
}

/// 安全的 RefCell 函数 / Safe RefCell Function
fn safe_refcell_function(data: &RefCell<Vec<i32>>) -> Result<Vec<i32>, String> {
    match data.try_borrow() {
        Ok(borrowed) => Ok(borrowed.clone()),
        Err(_) => Err("Borrow failed".to_string()),
    }
}
```

## 8. 设计模式应用

### 8.1 工厂模式

```rust
/// 工厂模式 / Factory Pattern
fn factory_pattern() {
    // 模式 1：简单工厂 / Pattern 1: Simple Factory
    let resource1 = ResourceFactory::create("type1");
    let resource2 = ResourceFactory::create("type2");
    
    println!("Resource1: {:?}", resource1);
    println!("Resource2: {:?}", resource2);
    
    // 模式 2：抽象工厂 / Pattern 2: Abstract Factory
    let factory = AbstractFactory::new();
    let product1 = factory.create_product_a();
    let product2 = factory.create_product_b();
    
    println!("Product1: {:?}", product1);
    println!("Product2: {:?}", product2);
}

/// 资源工厂 / Resource Factory
struct ResourceFactory;

impl ResourceFactory {
    fn create(resource_type: &str) -> Box<dyn Resource> {
        match resource_type {
            "type1" => Box::new(Type1Resource::new()),
            "type2" => Box::new(Type2Resource::new()),
            _ => panic!("Unknown resource type"),
        }
    }
}

/// 资源 trait / Resource Trait
trait Resource {
    fn get_name(&self) -> &str;
}

/// 类型1资源 / Type1 Resource
#[derive(Debug)]
struct Type1Resource {
    name: String,
}

impl Type1Resource {
    fn new() -> Self {
        Self {
            name: "Type1".to_string(),
        }
    }
}

impl Resource for Type1Resource {
    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 类型2资源 / Type2 Resource
#[derive(Debug)]
struct Type2Resource {
    name: String,
}

impl Type2Resource {
    fn new() -> Self {
        Self {
            name: "Type2".to_string(),
        }
    }
}

impl Resource for Type2Resource {
    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 抽象工厂 / Abstract Factory
struct AbstractFactory;

impl AbstractFactory {
    fn new() -> Self {
        Self
    }
    
    fn create_product_a(&self) -> ProductA {
        ProductA::new()
    }
    
    fn create_product_b(&self) -> ProductB {
        ProductB::new()
    }
}

/// 产品A / Product A
#[derive(Debug)]
struct ProductA {
    name: String,
}

impl ProductA {
    fn new() -> Self {
        Self {
            name: "ProductA".to_string(),
        }
    }
}

/// 产品B / Product B
#[derive(Debug)]
struct ProductB {
    name: String,
}

impl ProductB {
    fn new() -> Self {
        Self {
            name: "ProductB".to_string(),
        }
    }
}
```

### 8.2 观察者模式

```rust
/// 观察者模式 / Observer Pattern
fn observer_pattern() {
    let mut subject = Subject::new();
    
    let observer1 = Observer::new("Observer1");
    let observer2 = Observer::new("Observer2");
    
    subject.add_observer(observer1);
    subject.add_observer(observer2);
    
    subject.notify("Hello, observers!");
}

/// 主题 / Subject
struct Subject {
    observers: Vec<Box<dyn Observer>>,
}

impl Subject {
    fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }
    
    fn add_observer(&mut self, observer: Box<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn notify(&self, message: &str) {
        for observer in &self.observers {
            observer.update(message);
        }
    }
}

/// 观察者 trait / Observer Trait
trait Observer {
    fn update(&self, message: &str);
}

/// 具体观察者 / Concrete Observer
struct ConcreteObserver {
    name: String,
}

impl ConcreteObserver {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, message: &str) {
        println!("{} received: {}", self.name, message);
    }
}
```

## 9. 最佳实践总结

### 9.1 所有权最佳实践

```rust
/// 所有权最佳实践 / Ownership Best Practices
fn ownership_best_practices() {
    // 最佳实践 1：优先使用引用 / Best Practice 1: Prefer references
    let data = String::from("hello");
    let length = calculate_length(&data);
    println!("Length: {}, Data: {}", length, data);
    
    // 最佳实践 2：使用智能指针管理复杂所有权 / Best Practice 2: Use smart pointers for complex ownership
    let shared_data = Rc::new(RefCell::new(vec![1, 2, 3]));
    let shared_clone = Rc::clone(&shared_data);
    
    // 最佳实践 3：合理使用生命周期注解 / Best Practice 3: Use lifetime annotations appropriately
    let string1 = String::from("abcd");
    let string2 = "xyz";
    let result = longest(&string1, string2);
    println!("Longest: {}", result);
    
    // 最佳实践 4：避免不必要的克隆 / Best Practice 4: Avoid unnecessary clones
    let processed = process_string(&data);
    println!("Processed: {}", processed);
}

/// 计算长度的函数 / Function to calculate length
fn calculate_length(s: &str) -> usize {
    s.len()
}

/// 最长的函数 / Longest function
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 处理字符串的函数 / Function to process string
fn process_string(s: &str) -> String {
    s.to_uppercase()
}
```

### 9.2 性能优化最佳实践

```rust
/// 性能优化最佳实践 / Performance Optimization Best Practices
fn performance_optimization_best_practices() {
    // 最佳实践 1：使用 Copy 类型避免移动开销 / Best Practice 1: Use Copy types to avoid move overhead
    let x = 5;
    let y = x; // 复制，不是移动 / Copy, not move
    
    // 最佳实践 2：使用引用避免克隆开销 / Best Practice 2: Use references to avoid clone overhead
    let data = vec![1, 2, 3, 4, 5];
    let sum = calculate_sum(&data);
    println!("Sum: {}", sum);
    
    // 最佳实践 3：使用智能指针共享数据 / Best Practice 3: Use smart pointers to share data
    let shared_data = Rc::new(data);
    let shared_clone = Rc::clone(&shared_data);
    
    // 最佳实践 4：最小化借用作用域 / Best Practice 4: Minimize borrow scopes
    {
        let reference = &shared_data[0];
        println!("Reference: {}", reference);
    } // 借用在这里结束 / Borrow ends here
    
    // 现在可以安全地修改数据 / Now it's safe to modify the data
}

/// 计算和的函数 / Function to calculate sum
fn calculate_sum(data: &[i32]) -> i32 {
    data.iter().sum()
}
```

## 10. 总结

Rust 的所有权系统高级模式与最佳实践是编写高质量 Rust 代码的关键。通过深入理解所有权转移、借用模式、生命周期管理、内存安全、并发安全、性能优化和错误处理等各个方面，开发者可以编写出既安全又高效的 Rust 代码。

关键要点：

1. **高级所有权模式**：包括所有权转移、智能指针组合等
2. **高级借用模式**：包括借用优化、复杂借用模式等
3. **高级生命周期模式**：包括生命周期设计、复杂约束等
4. **内存安全模式**：包括 RAII、智能指针、内存泄漏防护等
5. **并发安全模式**：包括线程安全、异步安全等
6. **性能优化模式**：包括零成本抽象、内存布局优化等
7. **错误处理模式**：包括所有权错误处理、借用错误处理等
8. **设计模式应用**：包括工厂模式、观察者模式等
9. **最佳实践**：包括所有权最佳实践、性能优化最佳实践等

通过遵循这些高级模式和最佳实践，开发者可以充分利用 Rust 的所有权系统，编写出既安全又高效的代码，充分发挥 Rust 语言的优势。
