//! # Rust 基础语法详解模块 / Rust Basic Syntax Detailed Module
//!
//! 本模块提供了 Rust 所有权、借用和作用域系统的基础语法详解，
//! 包含详细的注释、规范的语言使用和全面的解释示例。
//! This module provides detailed explanations of Rust's ownership, borrowing, and scope system basic syntax,
//! including detailed comments, standardized language usage, and comprehensive explanatory examples.

// use std::collections::HashMap; // 未使用，已注释 / unused, commented out
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

/// # 1. 所有权基础语法 / Ownership Basic Syntax
/// 
/// 所有权是 Rust 的核心特性，确保内存安全而不需要垃圾回收器。
/// Ownership is Rust's core feature that ensures memory safety without a garbage collector.

pub mod ownership_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 1.1 变量声明和所有权 / Variable Declaration and Ownership
    /// 
    /// 在 Rust 中，每个值都有一个所有者，当所有者离开作用域时，值会被自动释放。
    /// In Rust, every value has an owner, and when the owner goes out of scope, the value is automatically freed.

    /// 基础变量声明示例 / Basic Variable Declaration Example
    pub fn basic_variable_declaration() {
        // 整数类型 - 实现了 Copy trait，按值复制 / Integer type - implements Copy trait, copied by value
        let x = 5;                    // x 拥有值 5 / x owns the value 5
        let y = x;                    // y 获得 x 的副本 / y gets a copy of x
        println!("x = {}, y = {}", x, y); // 两者都可以使用 / both can be used

        // 字符串类型 - 未实现 Copy trait，所有权转移 / String type - doesn't implement Copy trait, ownership moves
        let s1 = String::from("hello"); // s1 拥有字符串 / s1 owns the string
        let s2 = s1;                    // s1 的所有权转移给 s2 / s1's ownership moves to s2
        // println!("{}", s1);          // 编译错误：s1 不再有效 / Compile error: s1 is no longer valid
        println!("s2 = {}", s2);        // s2 可以使用 / s2 can be used
    }

    /// ## 1.2 所有权转移 / Ownership Transfer
    /// 
    /// 当将值赋给另一个变量时，所有权会发生转移（移动）。
    /// When assigning a value to another variable, ownership is transferred (moved).

    /// 所有权转移示例 / Ownership Transfer Example
    pub fn ownership_transfer() {
        let s1 = String::from("hello");
        let s2 = s1; // 所有权从 s1 转移到 s2 / Ownership transfers from s1 to s2
        
        // s1 不再有效 / s1 is no longer valid
        // println!("{}", s1); // 编译错误 / Compile error
        
        println!("s2 = {}", s2); // s2 现在拥有字符串 / s2 now owns the string
    }

    /// ## 1.3 函数参数所有权转移 / Function Parameter Ownership Transfer
    /// 
    /// 将值传递给函数时，所有权会转移给函数参数。
    /// When passing a value to a function, ownership is transferred to the function parameter.

    /// 函数参数所有权转移示例 / Function Parameter Ownership Transfer Example
    pub fn function_ownership_transfer() {
        let s = String::from("hello");
        takes_ownership(s); // s 的所有权转移给函数 / s's ownership moves to the function
        // println!("{}", s); // 编译错误：s 不再有效 / Compile error: s is no longer valid
    }

    /// 接受所有权的函数 / Function that takes ownership
    fn takes_ownership(some_string: String) {
        println!("{}", some_string);
    } // some_string 离开作用域，内存被释放 / some_string goes out of scope, memory is freed

    /// ## 1.4 返回值所有权转移 / Return Value Ownership Transfer
    /// 
    /// 函数可以返回值的所有权。
    /// Functions can return ownership of values.

    /// 返回值所有权转移示例 / Return Value Ownership Transfer Example
    pub fn return_ownership_transfer() {
        let s1 = gives_ownership(); // 函数返回值的所有权转移给 s1 / Function returns ownership to s1
        let s2 = String::from("hello");
        let s3 = takes_and_gives_back(s2); // s2 的所有权转移给函数，然后返回给 s3 / s2's ownership moves to function, then returns to s3
        
        println!("s1 = {}, s3 = {}", s1, s3);
    }

    /// 返回所有权的函数 / Function that gives ownership
    fn gives_ownership() -> String {
        let some_string = String::from("yours");
        some_string // 返回所有权 / return ownership
    }

    /// 接受并返回所有权的函数 / Function that takes and gives back ownership
    fn takes_and_gives_back(a_string: String) -> String {
        a_string // 返回所有权 / return ownership
    }
}

/// # 2. 借用基础语法 / Borrowing Basic Syntax
/// 
/// 借用允许在不转移所有权的情况下访问数据。
/// Borrowing allows accessing data without transferring ownership.

pub mod borrowing_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 2.1 不可变借用 / Immutable Borrowing
    /// 
    /// 不可变借用允许读取数据，但不能修改。
    /// Immutable borrowing allows reading data but not modifying it.

    /// 不可变借用示例 / Immutable Borrowing Example
    pub fn immutable_borrowing() {
        let s1 = String::from("hello");
        let len = calculate_length(&s1); // 传递 s1 的引用 / pass reference to s1
        println!("The length of '{}' is {}.", s1, len); // s1 仍然有效 / s1 is still valid
    }

    /// 计算字符串长度的函数 / Function that calculates string length
    fn calculate_length(s: &String) -> usize {
        s.len()
    } // s 离开作用域，但因为它不拥有数据，所以不会释放 / s goes out of scope, but since it doesn't own the data, it's not freed

    /// ## 2.2 可变借用 / Mutable Borrowing
    /// 
    /// 可变借用允许修改数据。
    /// Mutable borrowing allows modifying data.

    /// 可变借用示例 / Mutable Borrowing Example
    pub fn mutable_borrowing() {
        let mut s = String::from("hello");
        change(&mut s); // 传递可变引用 / pass mutable reference
        println!("s = {}", s);
    }

    /// 修改字符串的函数 / Function that modifies string
    fn change(some_string: &mut String) {
        some_string.push_str(", world");
    }

    /// ## 2.3 借用规则 / Borrowing Rules
    /// 
    /// Rust 的借用规则确保内存安全：
    /// Rust's borrowing rules ensure memory safety:
    /// 1. 同一时间只能有一个可变借用或多个不可变借用
    /// 2. 借用必须始终有效

    /// 借用规则示例 / Borrowing Rules Example
    pub fn borrowing_rules() {
        let mut s = String::from("hello");

        // 可以有多个不可变借用 / Can have multiple immutable borrows
        let r1 = &s;
        let r2 = &s;
        println!("r1 = {}, r2 = {}", r1, r2);

        // 不可变借用结束后可以有可变借用 / Can have mutable borrow after immutable borrows end
        let r3 = &mut s;
        r3.push_str(", world");
        println!("r3 = {}", r3);
    }

    /// ## 2.4 悬垂引用 / Dangling References
    /// 
    /// Rust 编译器防止悬垂引用。
    /// Rust compiler prevents dangling references.

    /// 悬垂引用示例（编译错误）/ Dangling Reference Example (Compile Error)
    pub fn dangling_reference_example() {
        // 以下代码会编译错误 / The following code will compile error
        // let reference_to_nothing = dangle();
    }

    /// 会产生悬垂引用的函数（编译错误）/ Function that would create dangling reference (Compile Error)
    // fn dangle() -> &String {
    //     let s = String::from("hello");
    //     &s // 返回 s 的引用，但 s 即将离开作用域 / return reference to s, but s is about to go out of scope
    // } // s 离开作用域，内存被释放 / s goes out of scope, memory is freed

    /// 正确的做法：返回所有权 / Correct approach: return ownership
    #[allow(unused)]
    fn no_dangle() -> String {
        let s = String::from("hello");
        s // 返回所有权 / return ownership
    }
}

/// # 3. 生命周期基础语法 / Lifetime Basic Syntax
/// 
/// 生命周期确保引用在其指向的数据有效期间有效。
/// Lifetimes ensure that references are valid for as long as the data they point to.

pub mod lifetime_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 3.1 生命周期注解 / Lifetime Annotations
    /// 
    /// 生命周期注解描述引用的生命周期关系。
    /// Lifetime annotations describe the lifetime relationships of references.

    /// 生命周期注解示例 / Lifetime Annotation Example
    pub fn lifetime_annotations() {
        let string1 = String::from("long string is long");
        let string2 = String::from("xyz");
        let result = longest(&string1, &string2);
        println!("The longest string is {}", result);
    }

    /// 返回较长字符串的函数 / Function that returns the longer string
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() {
            x
        } else {
            y
        }
    }

    /// ## 3.2 结构体生命周期 / Struct Lifetimes
    /// 
    /// 结构体可以包含引用，需要生命周期注解。
    /// Structs can contain references and need lifetime annotations.

    /// 结构体生命周期示例 / Struct Lifetime Example
    pub fn struct_lifetime() {
        let novel = String::from("Call me Ishmael. Some years ago...");
        let first_sentence = novel.split('.').next().expect("Could not find a '.'");
        let i = ImportantExcerpt {
            part: first_sentence,
        };
        println!("Important part: {}", i.part);
    }

    /// 包含引用的结构体 / Struct containing reference
    struct ImportantExcerpt<'a> {
        part: &'a str,
    }

    impl<'a> ImportantExcerpt<'a> {
        /// 方法生命周期 / Method lifetime
        #[allow(unused)]
        fn announce_and_return_part(&self, announcement: &str) -> &str {
            println!("Attention please: {}", announcement);
            self.part
        }
    }

    /// ## 3.3 生命周期省略 / Lifetime Elision
    /// 
    /// 在某些情况下，编译器可以推断生命周期。
    /// In some cases, the compiler can infer lifetimes.

    /// 生命周期省略示例 / Lifetime Elision Example
    pub fn lifetime_elision() {
        let s = String::from("hello");
        let first_word = first_word(&s);
        println!("First word: {}", first_word);
    }

    /// 编译器可以推断生命周期的函数 / Function where compiler can infer lifetime
    fn first_word(s: &str) -> &str {
        let bytes = s.as_bytes();

        for (i, &item) in bytes.iter().enumerate() {
            if item == b' ' {
                return &s[0..i];
            }
        }

        &s[..]
    }
}

/// # 4. 作用域基础语法 / Scope Basic Syntax
/// 
/// 作用域定义了变量的可见性和生命周期。
/// Scope defines the visibility and lifetime of variables.

pub mod scope_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 4.1 基本作用域 / Basic Scope
    /// 
    /// 变量在声明的作用域内有效。
    /// Variables are valid within the scope where they are declared.

    /// 基本作用域示例 / Basic Scope Example
    pub fn basic_scope() {
        let s = String::from("hello"); // s 进入作用域 / s comes into scope

        {
            let t = String::from("world"); // t 进入作用域 / t comes into scope
            println!("{} {}", s, t);
        } // t 离开作用域，内存被释放 / t goes out of scope, memory is freed

        println!("{}", s); // s 仍然有效 / s is still valid
    } // s 离开作用域，内存被释放 / s goes out of scope, memory is freed

    /// ## 4.2 嵌套作用域 / Nested Scope
    /// 
    /// 作用域可以嵌套，内层作用域可以访问外层作用域的变量。
    /// Scopes can be nested, inner scopes can access variables from outer scopes.

    /// 嵌套作用域示例 / Nested Scope Example
    pub fn nested_scope() {
        let x = 5; // 外层作用域 / outer scope

        {
            let y = 10; // 内层作用域 / inner scope
            println!("x = {}, y = {}", x, y); // 可以访问 x 和 y / can access x and y
        } // y 离开作用域 / y goes out of scope

        println!("x = {}", x); // 只能访问 x / can only access x
    }

    /// ## 4.3 作用域与所有权 / Scope and Ownership
    /// 
    /// 作用域影响所有权的生命周期。
    /// Scope affects the lifetime of ownership.

    /// 作用域与所有权示例 / Scope and Ownership Example
    pub fn scope_and_ownership() {
        let s1 = String::from("hello");
        let s2 = s1; // 所有权转移 / ownership transfer

        {
            let s3 = s2; // 所有权再次转移 / ownership transfers again
            println!("s3 = {}", s3);
        } // s3 离开作用域，内存被释放 / s3 goes out of scope, memory is freed

        // println!("s2 = {}", s2); // 编译错误：s2 不再有效 / Compile error: s2 is no longer valid
    }
}

/// # 5. 智能指针基础语法 / Smart Pointer Basic Syntax
/// 
/// 智能指针提供了额外的功能，如引用计数和内部可变性。
/// Smart pointers provide additional functionality like reference counting and interior mutability.

pub mod smart_pointer_basics {
    use super::*;

    /// ## 5.1 Box<T> - 堆分配 / Box<T> - Heap Allocation
    /// 
    /// Box 允许在堆上分配数据。
    /// Box allows allocating data on the heap.

    /// Box 示例 / Box Example
    pub fn box_example() {
        let b = Box::new(5);
        println!("b = {}", b);
    } // b 离开作用域，堆内存被释放 / b goes out of scope, heap memory is freed

    /// ## 5.2 Rc<T> - 引用计数 / Rc<T> - Reference Counting
    /// 
    /// Rc 允许多个所有者共享数据。
    /// Rc allows multiple owners to share data.

    /// Rc 示例 / Rc Example
    pub fn rc_example() {
        let a = Rc::new(Cons(5, Rc::new(Cons(10, Rc::new(Nil)))));
        let b = Cons(3, Rc::clone(&a));
        let c = Cons(4, Rc::clone(&a));
        
        println!("a = {:?}", a);
        println!("b = {:?}", b);
        println!("c = {:?}", c);
    }

    /// 链表节点 / List node
    #[derive(Debug)]
    #[allow(dead_code)]
    enum List {
        Cons(i32, Rc<List>),
        Nil,
    }

    use List::{Cons, Nil};

    /// ## 5.3 RefCell<T> - 内部可变性 / RefCell<T> - Interior Mutability
    /// 
    /// RefCell 允许在不可变引用的情况下修改数据。
    /// RefCell allows modifying data even with immutable references.

    /// RefCell 示例 / RefCell Example
    pub fn refcell_example() {
        let data = Rc::new(RefCell::new(5));
        let data_clone = Rc::clone(&data);
        
        *data.borrow_mut() += 10;
        *data_clone.borrow_mut() += 5;
        
        println!("data = {}", data.borrow());
    }
}

/// # 6. 错误处理基础语法 / Error Handling Basic Syntax
/// 
/// Rust 使用 Result 和 Option 类型进行错误处理。
/// Rust uses Result and Option types for error handling.

pub mod error_handling_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 6.1 Option<T> / Option<T>
    /// 
    /// Option 表示可能存在或不存在的值。
    /// Option represents a value that may or may not exist.

    /// Option 示例 / Option Example
    #[allow(unused)]
    pub fn option_example() {
        let some_number = Some(5);
        let some_string = Some("a string");
        let absent_number: Option<i32> = None;

        match some_number {
            Some(value) => println!("Got: {}", value),
            None => println!("Got nothing"),
        }
    }

    /// ## 6.2 Result<T, E> / Result<T, E>
    /// 
    /// Result 表示可能成功或失败的操作。
    /// Result represents an operation that may succeed or fail.

    /// Result 示例 / Result Example
    #[allow(unused)]
    pub fn result_example() {
        let result = divide(10, 2);
        match result {
            Ok(value) => println!("Result: {}", value),
            Err(error) => println!("Error: {}", error),
        }
    }

    /// 除法函数 / Division function
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }
}

/// # 7. 并发基础语法 / Concurrency Basic Syntax
/// 
/// Rust 提供了安全的并发编程工具。
/// Rust provides safe concurrency programming tools.

pub mod concurrency_basics {
    use super::*;

    /// ## 7.1 线程 / Threads
    /// 
    /// 使用线程进行并发编程。
    /// Use threads for concurrent programming.

    /// 线程示例 / Thread Example
    pub fn thread_example() {
        let handle = std::thread::spawn(|| {
            for i in 1..10 {
                println!("hi number {} from the spawned thread!", i);
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
        });

        for i in 1..5 {
            println!("hi number {} from the main thread!", i);
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        handle.join().unwrap();
    }

    /// ## 7.2 消息传递 / Message Passing
    /// 
    /// 使用通道进行线程间通信。
    /// Use channels for inter-thread communication.

    /// 消息传递示例 / Message Passing Example
    pub fn message_passing_example() {
        let (tx, rx) = std::sync::mpsc::channel();

        std::thread::spawn(move || {
            let val = String::from("hi");
            tx.send(val).unwrap();
        });

        let received = rx.recv().unwrap();
        println!("Got: {}", received);
    }

    /// ## 7.3 共享状态 / Shared State
    /// 
    /// 使用 Mutex 进行共享状态管理。
    /// Use Mutex for shared state management.

    /// 共享状态示例 / Shared State Example
    pub fn shared_state_example() {
        let counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            let handle = std::thread::spawn(move || {
                let mut num = counter.lock().unwrap();
                *num += 1;
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        println!("Result: {}", *counter.lock().unwrap());
    }
}

/// # 8. 性能优化基础语法 / Performance Optimization Basic Syntax
/// 
/// Rust 提供了多种性能优化技术。
/// Rust provides various performance optimization techniques.

pub mod performance_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 8.1 零成本抽象 / Zero-cost Abstractions
    /// 
    /// Rust 的抽象在运行时没有额外开销。
    /// Rust's abstractions have no runtime overhead.

    /// 零成本抽象示例 / Zero-cost Abstraction Example
    pub fn zero_cost_abstraction() {
        let numbers = vec![1, 2, 3, 4, 5];
        
        // 迭代器是零成本抽象 / Iterators are zero-cost abstractions
        let sum: i32 = numbers.iter().map(|x| x * 2).sum();
        println!("Sum: {}", sum);
    }

    /// ## 8.2 内联优化 / Inline Optimization
    /// 
    /// 使用内联函数提高性能。
    /// Use inline functions to improve performance.

    /// 内联优化示例 / Inline Optimization Example
    pub fn inline_optimization() {
        let result = add_numbers(5, 10);
        println!("Result: {}", result);
    }

    /// 内联函数 / Inline function
    #[inline]
    fn add_numbers(a: i32, b: i32) -> i32 {
        a + b
    }

    /// ## 8.3 内存布局优化 / Memory Layout Optimization
    /// 
    /// 优化结构体的内存布局。
    /// Optimize struct memory layout.

    /// 内存布局优化示例 / Memory Layout Optimization Example
    pub fn memory_layout_optimization() {
        // 使用 #[repr(C)] 优化内存布局 / Use #[repr(C)] to optimize memory layout
        #[repr(C)]
        struct OptimizedStruct {
            a: u8,
            b: u32,
            c: u8,
        }

        let _s = OptimizedStruct { a: 1, b: 2, c: 3 };
        println!("Size: {}", std::mem::size_of::<OptimizedStruct>());
    }
}

/// # 9. 测试基础语法 / Testing Basic Syntax
/// 
/// Rust 内置了测试框架。
/// Rust has a built-in testing framework.

pub mod testing_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 9.1 单元测试 / Unit Tests
    /// 
    /// 编写单元测试。
    /// Write unit tests.

    /// 单元测试示例 / Unit Test Example
    pub fn unit_test_example() {
        let result = add(2, 3);
        assert_eq!(result, 5);
    }

    /// 加法函数 / Addition function
    fn add(a: i32, b: i32) -> i32 {
        a + b
    }

    /// ## 9.2 集成测试 / Integration Tests
    /// 
    /// 编写集成测试。
    /// Write integration tests.

    /// 集成测试示例 / Integration Test Example
    pub fn integration_test_example() {
        let result = complex_calculation(10, 20);
        assert!(result > 0);
    }

    /// 复杂计算函数 / Complex calculation function
    fn complex_calculation(a: i32, b: i32) -> i32 {
        a * b + a + b
    }
}

/// # 10. 模块系统基础语法 / Module System Basic Syntax
/// 
/// Rust 的模块系统提供了代码组织功能。
/// Rust's module system provides code organization functionality.

pub mod module_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 10.1 模块声明 / Module Declaration
    /// 
    /// 声明和使用模块。
    /// Declare and use modules.

    /// 模块声明示例 / Module Declaration Example
    #[allow(unused)]
    pub fn module_declaration() {
        println!("This is a module function");
    }

    /// ## 10.2 可见性 / Visibility
    /// 
    /// 控制模块和项的可见性。
    /// Control visibility of modules and items.

    /// 可见性示例 / Visibility Example
    #[allow(unused)]
    pub fn visibility_example() {
        // pub 函数可以在模块外部访问 / pub functions can be accessed outside the module
        public_function();
        // private_function(); // 编译错误：私有函数 / Compile error: private function
    }

    /// 公共函数 / Public function
    #[allow(unused)]
    pub fn public_function() {
        println!("This is a public function");
    }

    /// 私有函数 / Private function
    #[allow(unused)]
    fn private_function() {
        println!("This is a private function");
    }
}

/// # 错误类型定义 / Error Type Definitions

/// 所有权错误 / Ownership Error
#[derive(Debug)]
pub enum OwnershipError {
    /// 所有者未找到 / Owner not found
    OwnerNotFound,
    /// 所有权转移不允许 / Ownership transfer not allowed
    TransferNotAllowed,
    /// 借用规则违反 / Borrowing rule violation
    BorrowRuleViolation,
}

impl fmt::Display for OwnershipError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OwnershipError::OwnerNotFound => write!(f, "Owner not found"),
            OwnershipError::TransferNotAllowed => write!(f, "Ownership transfer not allowed"),
            OwnershipError::BorrowRuleViolation => write!(f, "Borrowing rule violation"),
        }
    }
}

impl std::error::Error for OwnershipError {}

/// # 主要功能函数 / Main Function Functions

/// 运行所有基础语法示例 / Run all basic syntax examples
pub fn run_all_basic_syntax_examples() {
    println!("=== Rust 基础语法示例 / Rust Basic Syntax Examples ===");
    
    println!("\n1. 所有权基础 / Ownership Basics");
    ownership_basics::basic_variable_declaration();
    ownership_basics::ownership_transfer();
    ownership_basics::function_ownership_transfer();
    ownership_basics::return_ownership_transfer();
    
    println!("\n2. 借用基础 / Borrowing Basics");
    borrowing_basics::immutable_borrowing();
    borrowing_basics::mutable_borrowing();
    borrowing_basics::borrowing_rules();
    
    println!("\n3. 生命周期基础 / Lifetime Basics");
    lifetime_basics::lifetime_annotations();
    lifetime_basics::struct_lifetime();
    lifetime_basics::lifetime_elision();
    
    println!("\n4. 作用域基础 / Scope Basics");
    scope_basics::basic_scope();
    scope_basics::nested_scope();
    scope_basics::scope_and_ownership();
    
    println!("\n5. 智能指针基础 / Smart Pointer Basics");
    smart_pointer_basics::box_example();
    smart_pointer_basics::rc_example();
    smart_pointer_basics::refcell_example();
    
    println!("\n6. 错误处理基础 / Error Handling Basics");
    error_handling_basics::option_example();
    error_handling_basics::result_example();
    
    println!("\n7. 并发基础 / Concurrency Basics");
    concurrency_basics::thread_example();
    concurrency_basics::message_passing_example();
    concurrency_basics::shared_state_example();
    
    println!("\n8. 性能优化基础 / Performance Optimization Basics");
    performance_basics::zero_cost_abstraction();
    performance_basics::inline_optimization();
    performance_basics::memory_layout_optimization();
    
    println!("\n9. 测试基础 / Testing Basics");
    testing_basics::unit_test_example();
    testing_basics::integration_test_example();
    
    println!("\n10. 模块系统基础 / Module System Basics");
    module_basics::module_declaration();
    module_basics::visibility_example();
    
    println!("\n=== 所有基础语法示例运行完成 / All Basic Syntax Examples Completed ===");
}

/// 获取基础语法模块信息 / Get Basic Syntax Module Information
pub fn get_basic_syntax_info() -> &'static str {
    "Rust Basic Syntax Module - Comprehensive examples and explanations of ownership, borrowing, and scope"
}
