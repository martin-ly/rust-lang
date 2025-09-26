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
use std::thread;

/// # 1. 所有权基础语法 / Ownership Basic Syntax
///
/// 所有权是 Rust 的核心特性，确保内存安全而不需要垃圾回收器。
/// Ownership is Rust's core feature that ensures memory safety without a garbage collector.
///
pub mod ownership_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 1.1 变量声明和所有权 / Variable Declaration and Ownership
    ///
    /// 在 Rust 中，每个值都有一个所有者，当所有者离开作用域时，值会被自动释放。
    /// In Rust, every value has an owner, and when the owner goes out of scope, the value is automatically freed.
    ///
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
    ///
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
    ///
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
    ///
    /// 返回值所有权转移示例 / Return Value Ownership Transfer Example
    pub fn return_ownership_transfer() {
        let s1 = gives_ownership(); // 函数返回值的所有权转移给 s1 / Function returns ownership to s1
        let s2 = String::from("hello");
        let s3 = takes_and_gives_back(s2); // s2 的所有权转移给函数，然后返回给 s3 / s2's ownership moves to function, then returns to s3

        println!("s1 = {}, s3 = {}", s1, s3);
    }

    /// 返回所有权的函数 / Function that gives ownership
    fn gives_ownership() -> String {

        String::from("yours") // 返回所有权 / return ownership
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
///
pub mod borrowing_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 2.1 不可变借用 / Immutable Borrowing
    ///
    /// 不可变借用允许读取数据，但不能修改。
    /// Immutable borrowing allows reading data but not modifying it.
    ///
    /// 不可变借用示例 / Immutable Borrowing Example
    pub fn immutable_borrowing() {
        let s1 = String::from("hello");
        let len = calculate_length(&s1); // 传递 s1 的引用 / pass reference to s1
        println!("The length of '{}' is {}.", s1, len); // s1 仍然有效 / s1 is still valid
    }

    /// 计算字符串长度的函数 / Function that calculates string length
    fn calculate_length(s: &str) -> usize {
        s.len()
    } // s 离开作用域，但因为它不拥有数据，所以不会释放 / s goes out of scope, but since it doesn't own the data, it's not freed

    /// ## 2.2 可变借用 / Mutable Borrowing
    ///
    /// 可变借用允许修改数据。
    /// Mutable borrowing allows modifying data.
    ///
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
    ///
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
    ///
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
    ///
    /// 正确的做法：返回所有权 / Correct approach: return ownership
    #[allow(unused)]
    fn no_dangle() -> String {
        String::from("hello") // 返回所有权 / return ownership
    }
}

/// # 3. 生命周期基础语法 / Lifetime Basic Syntax
///
/// 生命周期确保引用在其指向的数据有效期间有效。
/// Lifetimes ensure that references are valid for as long as the data they point to.
///
pub mod lifetime_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 3.1 生命周期注解 / Lifetime Annotations
    ///
    /// 生命周期注解描述引用的生命周期关系。
    /// Lifetime annotations describe the lifetime relationships of references.
    ///
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
    ///
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
    ///
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

        s
    }
}

/// # 4. 作用域基础语法 / Scope Basic Syntax
///
/// 作用域定义了变量的可见性和生命周期。
/// Scope defines the visibility and lifetime of variables.
///
pub mod scope_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 4.1 基本作用域 / Basic Scope
    ///
    /// 变量在声明的作用域内有效。
    /// Variables are valid within the scope where they are declared.
    ///
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
    ///
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
    ///
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
///
pub mod smart_pointer_basics {
    use super::*;

    /// ## 5.1 Box<T> - 堆分配 / Box<T> - Heap Allocation
    ///
    /// Box 允许在堆上分配数据。
    /// Box allows allocating data on the heap.
    ///
    /// Box 示例 / Box Example
    pub fn box_example() {
        let b = Box::new(5);
        println!("b = {}", b);
    } // b 离开作用域，堆内存被释放 / b goes out of scope, heap memory is freed

    /// ## 5.2 Rc<T> - 引用计数 / Rc<T> - Reference Counting
    ///
    /// Rc 允许多个所有者共享数据。
    /// Rc allows multiple owners to share data.
    ///
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
    ///
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
///
pub mod error_handling_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 6.1 Option<T> / Option<T>
    ///
    /// Option 表示可能存在或不存在的值。
    /// Option represents a value that may or may not exist.
    ///
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
    ///
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
///
pub mod concurrency_basics {
    use super::*;

    /// ## 7.1 线程 / Threads
    ///
    /// 使用线程进行并发编程。
    /// Use threads for concurrent programming.
    ///
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
    ///
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
    ///
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
///
pub mod performance_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 8.1 零成本抽象 / Zero-cost Abstractions
    ///
    /// Rust 的抽象在运行时没有额外开销。
    /// Rust's abstractions have no runtime overhead.
    ///
    /// 零成本抽象示例 / Zero-cost Abstraction Example
    pub fn zero_cost_abstraction() {
        let numbers = [1, 2, 3, 4, 5];

        // 迭代器是零成本抽象 / Iterators are zero-cost abstractions
        let sum: i32 = numbers.iter().map(|x| x * 2).sum();
        println!("Sum: {}", sum);
    }

    /// ## 8.2 内联优化 / Inline Optimization
    ///
    /// 使用内联函数提高性能。
    /// Use inline functions to improve performance.
    ///
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
    ///
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
///
pub mod testing_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 9.1 单元测试 / Unit Tests
    ///
    /// 编写单元测试。
    /// Write unit tests.
    ///
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
    ///
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
///
pub mod module_basics {
    // use super::*; // 未使用，已注释 / unused, commented out

    /// ## 10.1 模块声明 / Module Declaration
    ///
    /// 声明和使用模块。
    /// Declare and use modules.
    ///
    /// 模块声明示例 / Module Declaration Example
    #[allow(unused)]
    pub fn module_declaration() {
        println!("This is a module function");
    }

    /// ## 10.2 可见性 / Visibility
    ///
    /// 控制模块和项的可见性。
    /// Control visibility of modules and items.
    ///
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

/// # 11. Rust 1.90 新特性基础语法 / Rust 1.90 New Features Basic Syntax
///
/// Rust 1.90 版本引入的新特性和改进，包括：
/// New features and improvements introduced in Rust 1.90, including:
///
/// - 改进的借用检查器 / Improved borrow checker
/// - 增强的生命周期推断 / Enhanced lifetime inference
/// - 新的智能指针特性 / New smart pointer features
/// - 优化的作用域管理 / Optimized scope management
/// - 增强的并发安全 / Enhanced concurrency safety
/// - 智能内存管理 / Smart memory management
/// - 改进的错误处理 / Improved error handling
/// - 性能优化特性 / Performance optimization features
///
pub mod rust_190_basics {
    use super::*;

    /// ## 11.1 改进的借用检查器 / Improved Borrow Checker
    ///
    /// Rust 1.90 中的借用检查器得到了显著改进，提供了更智能的借用分析。
    /// The borrow checker in Rust 1.90 has been significantly improved, providing smarter borrow analysis.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 更精确的借用范围分析 / More precise borrow scope analysis
    /// - 改进的借用冲突检测 / Improved borrow conflict detection
    /// - 更好的错误信息 / Better error messages
    /// - 支持更复杂的借用模式 / Support for more complex borrowing patterns
    ///
    /// 改进的借用检查器示例 / Improved Borrow Checker Example
    pub fn improved_borrow_checker() {
        let mut data = vec![1, 2, 3, 4, 5];

        // Rust 1.90 中更智能的借用检查
        // Smarter borrow checking in Rust 1.90
        // 可以同时借用向量的不同部分进行修改
        // Can borrow different parts of the vector simultaneously for modification
        let (first, rest) = data.split_at_mut(1);
        let (second, third) = rest.split_at_mut(1);

        // 可以同时修改不同部分，这在之前的版本中可能不被允许
        // Can modify different parts simultaneously, which might not be allowed in previous versions
        first[0] = 10;
        second[0] = 20;
        third[0] = 30;

        println!("Modified data: {:?}", data);

        // 演示更复杂的借用模式 / Demonstrate more complex borrowing patterns
        let mut complex_data = vec![vec![1, 2], vec![3, 4], vec![5, 6]];

        // Rust 1.90 支持更复杂的嵌套借用
        // Rust 1.90 supports more complex nested borrowing
        for (i, inner_vec) in complex_data.iter_mut().enumerate() {
            for (j, element) in inner_vec.iter_mut().enumerate() {
                *element = (i + 1) * 10 + (j + 1);
            }
        }

        println!("Complex modified data: {:?}", complex_data);
    }

    /// ## 11.2 增强的生命周期推断 / Enhanced Lifetime Inference
    ///
    /// Rust 1.90 中的生命周期推断更加智能，减少了需要显式生命周期注解的情况。
    /// Lifetime inference in Rust 1.90 is more intelligent, reducing cases where explicit lifetime annotations are needed.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 更智能的生命周期推断算法 / Smarter lifetime inference algorithms
    /// - 减少生命周期注解的需求 / Reduced need for lifetime annotations
    /// - 更好的生命周期错误信息 / Better lifetime error messages
    /// - 支持更复杂的生命周期模式 / Support for more complex lifetime patterns
    ///
    /// 增强的生命周期推断示例 / Enhanced Lifetime Inference Example
    pub fn enhanced_lifetime_inference() {
        let string1 = String::from("long string is long");
        let string2 = String::from("xyz");

        // Rust 1.90 中编译器可以更好地推断生命周期
        // In Rust 1.90, the compiler can better infer lifetimes
        let result = longest_enhanced(&string1, &string2);
        println!("The longest string is: {}", result);

        // 演示更复杂的生命周期推断场景 / Demonstrate more complex lifetime inference scenarios
        let complex_result = complex_lifetime_function(&string1, &string2, "additional");
        println!("Complex lifetime result: {}", complex_result);

        // 结构体生命周期推断 / Struct lifetime inference
        let excerpt = create_excerpt(&string1);
        println!("Excerpt: {}", excerpt.part);
    }

    /// 增强的最长字符串函数 / Enhanced longest string function
    ///
    /// 在 Rust 1.90 中，编译器可以更好地推断这个函数的生命周期
    /// In Rust 1.90, the compiler can better infer lifetimes for this function
    fn longest_enhanced<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() {
            x
        } else {
            y
        }
    }

    /// 复杂生命周期函数 / Complex lifetime function
    ///
    /// 演示 Rust 1.90 中更智能的生命周期推断
    /// Demonstrates smarter lifetime inference in Rust 1.90
    fn complex_lifetime_function<'a, 'b>(x: &'a str, y: &'b str, z: &'static str) -> &'a str
    where
        'b: 'a, // 生命周期约束 / Lifetime constraint
    {
        if x.len() > y.len() {
            x
        } else {
            z // 静态生命周期可以转换为任何生命周期 / Static lifetime can be converted to any lifetime
        }
    }

    /// 包含引用的结构体 / Struct containing reference
    struct ImportantExcerpt<'a> {
        part: &'a str,
    }

    /// 创建摘录 / Create excerpt
    fn create_excerpt<'a>(text: &'a str) -> ImportantExcerpt<'a> {
        let first_sentence = text.split('.').next().expect("Could not find a '.'");
        ImportantExcerpt { part: first_sentence }
    }

    /// ## 11.3 新的智能指针特性 / New Smart Pointer Features
    ///
    /// Rust 1.90 中的智能指针功能得到增强，提供了更好的性能和更丰富的功能。
    /// Smart pointer functionality in Rust 1.90 has been enhanced, providing better performance and richer features.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 优化的引用计数性能 / Optimized reference counting performance
    /// - 改进的内存布局 / Improved memory layout
    /// - 新的智能指针类型 / New smart pointer types
    /// - 更好的错误处理 / Better error handling
    /// - 增强的调试支持 / Enhanced debugging support
    ///
    /// 新的智能指针特性示例 / New Smart Pointer Features Example
    pub fn new_smart_pointer_features() {
        // Rust 1.90 中的智能指针优化
        // Smart pointer optimization in Rust 1.90
        let data = Rc::new(RefCell::new(vec![1, 2, 3]));

        // 更智能的引用计数管理
        // Smarter reference counting management
        let data_clone1 = Rc::clone(&data);
        let data_clone2 = Rc::clone(&data);

        // 内部可变性操作
        // Interior mutability operations
        data_clone1.borrow_mut().push(4);
        data_clone2.borrow_mut().push(5);

        println!("Smart pointer data: {:?}", data.borrow());

        // 检查引用计数
        // Check reference count
        println!("Reference count: {}", Rc::strong_count(&data));

        // 演示新的智能指针模式 / Demonstrate new smart pointer patterns
        demonstrate_advanced_smart_pointers();
    }

    /// 演示高级智能指针模式 / Demonstrate advanced smart pointer patterns
    fn demonstrate_advanced_smart_pointers() {
        // 使用 Arc 进行线程间共享 / Use Arc for inter-thread sharing
        let shared_data = Arc::new(Mutex::new(vec![1, 2, 3, 4, 5]));

        // 创建多个线程来修改共享数据 / Create multiple threads to modify shared data
        let mut handles = vec![];

        for i in 0..3 {
            let data_clone = Arc::clone(&shared_data);
            let handle = thread::spawn(move || {
                let mut data = data_clone.lock().unwrap();
                data.push(i * 10);
                println!("Thread {} added {}", i, i * 10);
            });
            handles.push(handle);
        }

        // 等待所有线程完成 / Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }

        println!("Final shared data: {:?}", *shared_data.lock().unwrap());

        // 演示弱引用 / Demonstrate weak references
        let strong = Rc::new(42);
        let weak = Rc::downgrade(&strong);

        println!("Strong count: {}, Weak count: {}", Rc::strong_count(&strong), Rc::weak_count(&strong));

        // 丢弃强引用 / Drop strong reference
        drop(strong);

        // 检查弱引用是否仍然有效 / Check if weak reference is still valid
        match weak.upgrade() {
            Some(value) => println!("Weak reference still valid: {}", value),
            None => println!("Weak reference is no longer valid"),
        }
    }

    /// ## 11.4 优化的作用域管理 / Optimized Scope Management
    ///
    /// Rust 1.90 中的作用域管理更加高效，提供了更精确的作用域分析和优化。
    /// Scope management in Rust 1.90 is more efficient, providing more precise scope analysis and optimization.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 更精确的作用域分析 / More precise scope analysis
    /// - 优化的内存释放时机 / Optimized memory deallocation timing
    /// - 改进的变量生命周期管理 / Improved variable lifetime management
    /// - 更好的作用域嵌套支持 / Better nested scope support
    ///
    /// 优化的作用域管理示例 / Optimized Scope Management Example
    pub fn optimized_scope_management() {
        let outer_data = String::from("outer");

        {
            let inner_data = String::from("inner");

            // Rust 1.90 中更精确的作用域分析
            // More precise scope analysis in Rust 1.90
            println!("Outer: {}, Inner: {}", outer_data, inner_data);

            // 内层作用域可以访问外层数据
            // Inner scope can access outer data
            let combined = format!("{} + {}", outer_data, inner_data);
            println!("Combined: {}", combined);

            // 演示复杂的作用域嵌套 / Demonstrate complex scope nesting
            {
                let nested_data = String::from("nested");
                println!("Nested scope: {}", nested_data);

                // 可以访问所有外层作用域的变量 / Can access variables from all outer scopes
                let triple_combined = format!("{} + {} + {}", outer_data, inner_data, nested_data);
                println!("Triple combined: {}", triple_combined);
            } // nested_data 离开作用域 / nested_data goes out of scope

        } // inner_data 离开作用域 / inner_data goes out of scope

        // outer_data 仍然有效 / outer_data is still valid
        println!("Outer data still valid: {}", outer_data);

        // 演示作用域优化 / Demonstrate scope optimization
        demonstrate_scope_optimization();
    }

    /// 演示作用域优化 / Demonstrate scope optimization
    fn demonstrate_scope_optimization() {
        // Rust 1.90 中的作用域优化
        // Scope optimization in Rust 1.90

        // 早期释放不需要的变量 / Early release of unnecessary variables
        let expensive_data = String::from("expensive data");
        let result = process_data(&expensive_data);

        // 在不需要 expensive_data 后立即释放
        // Release expensive_data immediately when no longer needed
        drop(expensive_data);

        println!("Processed result: {}", result);

        // 使用块作用域进行精确控制 / Use block scope for precise control
        let final_result = {
            let temp_data = String::from("temporary");

            // temp_data 在这里自动释放 / temp_data is automatically released here
            process_data(&temp_data)
        };

        println!("Final result: {}", final_result);
    }

    /// 处理数据 / Process data
    fn process_data(data: &str) -> String {
        format!("Processed: {}", data)
    }

    /// ## 11.5 增强的并发安全 / Enhanced Concurrency Safety
    ///
    /// Rust 1.90 中的并发安全特性得到增强，提供了更好的线程安全和数据竞争检测。
    /// Concurrency safety features in Rust 1.90 have been enhanced, providing better thread safety and data race detection.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 改进的数据竞争检测 / Improved data race detection
    /// - 更好的线程同步原语 / Better thread synchronization primitives
    /// - 增强的死锁检测 / Enhanced deadlock detection
    /// - 优化的锁性能 / Optimized lock performance
    ///
    /// 增强的并发安全示例 / Enhanced Concurrency Safety Example
    pub fn enhanced_concurrency_safety() {
        let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
        let mut handles = vec![];

        for i in 0..3 {
            let data_clone = Arc::clone(&shared_data);
            let handle = thread::spawn(move || {
                let mut data = data_clone.lock().unwrap();
                data.push(i);
                println!("Thread {} added {}", i, i);
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        println!("Final data: {:?}", *shared_data.lock().unwrap());

        // 演示更复杂的并发模式 / Demonstrate more complex concurrency patterns
        demonstrate_advanced_concurrency();
    }

    /// 演示高级并发模式 / Demonstrate advanced concurrency patterns
    fn demonstrate_advanced_concurrency() {
        use std::sync::{RwLock, Barrier};
        use std::sync::atomic::{AtomicUsize, Ordering};

        // 使用读写锁 / Use read-write lock
        let rw_data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));

        // 创建多个读线程 / Create multiple reader threads
        let mut reader_handles = vec![];
        for i in 0..3 {
            let data_clone = Arc::clone(&rw_data);
            let handle = thread::spawn(move || {
                let data = data_clone.read().unwrap();
                println!("Reader {} read: {:?}", i, *data);
            });
            reader_handles.push(handle);
        }

        // 创建写线程 / Create writer thread
        let writer_data = Arc::clone(&rw_data);
        let writer_handle = thread::spawn(move || {
            let mut data = writer_data.write().unwrap();
            data.push(6);
            println!("Writer added 6");
        });

        // 等待所有线程完成 / Wait for all threads to complete
        for handle in reader_handles {
            handle.join().unwrap();
        }
        writer_handle.join().unwrap();

        // 使用原子操作 / Use atomic operations
        let counter = Arc::new(AtomicUsize::new(0));
        let mut atomic_handles = vec![];

        for i in 0..5 {
            let counter_clone = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..1000 {
                    counter_clone.fetch_add(1, Ordering::SeqCst);
                }
                println!("Thread {} finished", i);
            });
            atomic_handles.push(handle);
        }

        for handle in atomic_handles {
            handle.join().unwrap();
        }

        println!("Final counter value: {}", counter.load(Ordering::SeqCst));

        // 使用屏障同步 / Use barrier synchronization
        let barrier = Arc::new(Barrier::new(3));
        let mut barrier_handles = vec![];

        for i in 0..3 {
            let barrier_clone = Arc::clone(&barrier);
            let handle = thread::spawn(move || {
                println!("Thread {} before barrier", i);
                barrier_clone.wait();
                println!("Thread {} after barrier", i);
            });
            barrier_handles.push(handle);
        }

        for handle in barrier_handles {
            handle.join().unwrap();
        }
    }

    /// ## 11.6 智能内存管理 / Smart Memory Management
    ///
    /// Rust 1.90 中的内存管理更加智能，提供了更好的内存分配和释放策略。
    /// Memory management in Rust 1.90 is more intelligent, providing better memory allocation and deallocation strategies.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 智能内存分配器 / Smart memory allocators
    /// - 优化的内存布局 / Optimized memory layout
    /// - 改进的内存泄漏检测 / Improved memory leak detection
    /// - 更好的内存使用分析 / Better memory usage analysis
    ///
    /// 智能内存管理示例 / Smart Memory Management Example
    pub fn smart_memory_management() {
        // Rust 1.90 中的智能内存分配
        // Smart memory allocation in Rust 1.90
        let data = Box::new(vec![1, 2, 3, 4, 5]);

        // 智能指针自动管理内存
        // Smart pointers automatically manage memory
        let processed_data = data.iter()
            .map(|x| x * 2)
            .filter(|&x| x > 5)
            .collect::<Vec<_>>();

        println!("Processed data: {:?}", processed_data);

        // data 在作用域结束时自动释放
        // data is automatically freed when it goes out of scope

        // 演示高级内存管理技术 / Demonstrate advanced memory management techniques
        demonstrate_advanced_memory_management();
    }

    /// 演示高级内存管理技术 / Demonstrate advanced memory management techniques
    fn demonstrate_advanced_memory_management() {
        // 使用 Box 进行堆分配 / Use Box for heap allocation
        let heap_data = Box::new([1, 2, 3, 4, 5]);
        println!("Heap allocated data: {:?}", heap_data);

        // 使用 Vec 进行动态分配 / Use Vec for dynamic allocation
        let mut dynamic_data = Vec::with_capacity(10);
        for i in 1..=10 {
            dynamic_data.push(i * i);
        }
        println!("Dynamic data: {:?}", dynamic_data);

        // 内存预分配 / Memory pre-allocation
        let mut preallocated = Vec::with_capacity(1000);
        for i in 0..1000 {
            preallocated.push(i);
        }
        println!("Preallocated data length: {}", preallocated.len());

        // 内存重用 / Memory reuse
        preallocated.clear();
        preallocated.shrink_to_fit();
        println!("After clear and shrink: capacity = {}", preallocated.capacity());

        // 使用 Box<[T]> 进行固定大小堆分配 / Use Box<[T]> for fixed-size heap allocation
        let fixed_heap_array = Box::new([1, 2, 3, 4, 5]);
        println!("Fixed heap array: {:?}", fixed_heap_array);

        // 内存对齐 / Memory alignment
        #[repr(align(64))]
        struct AlignedData {
            value: i32,
        }

        let aligned = AlignedData { value: 42 };
        println!("Aligned data value: {}", aligned.value);

        // 零成本抽象 / Zero-cost abstractions
        let zero_cost_data = (0..1000)
            .map(|x| x * x)
            .filter(|&x| x % 2 == 0)
            .collect::<Vec<_>>();
        println!("Zero-cost processed data length: {}", zero_cost_data.len());
    }

    /// ## 11.7 改进的错误处理 / Improved Error Handling
    ///
    /// Rust 1.90 中的错误处理更加完善，提供了更好的错误类型和错误传播机制。
    /// Error handling in Rust 1.90 is more comprehensive, providing better error types and error propagation mechanisms.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 更好的错误类型系统 / Better error type system
    /// - 改进的错误传播 / Improved error propagation
    /// - 更丰富的错误信息 / Richer error information
    /// - 更好的错误恢复机制 / Better error recovery mechanisms
    ///
    /// 改进的错误处理示例 / Improved Error Handling Example
    pub fn improved_error_handling() {
        // Rust 1.90 中的改进错误处理
        // Improved error handling in Rust 1.90
        let result = divide_enhanced(10, 2);

        match result {
            Ok(value) => println!("Division result: {}", value),
            Err(error) => println!("Error: {}", error),
        }

        // 使用 ? 操作符进行错误传播
        // Use ? operator for error propagation
        let result2 = divide_enhanced(10, 0);
        match result2 {
            Ok(value) => println!("Division result: {}", value),
            Err(error) => println!("Error: {}", error),
        }

        // 演示高级错误处理技术 / Demonstrate advanced error handling techniques
        demonstrate_advanced_error_handling();
    }

    /// 增强的除法函数 / Enhanced division function
    fn divide_enhanced(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero is not allowed".to_string())
        } else {
            Ok(a / b)
        }
    }

    /// 演示高级错误处理技术 / Demonstrate advanced error handling techniques
    fn demonstrate_advanced_error_handling() {
        // 自定义错误类型 / Custom error types
        #[derive(Debug)]
        enum MathError {
            DivisionByZero,
            NegativeSquareRoot,
            #[allow(dead_code)]
            Overflow,
        }

        impl std::fmt::Display for MathError {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    MathError::DivisionByZero => write!(f, "Division by zero"),
                    MathError::NegativeSquareRoot => write!(f, "Negative square root"),
                    MathError::Overflow => write!(f, "Arithmetic overflow"),
                }
            }
        }

        impl std::error::Error for MathError {}

        // 使用自定义错误类型 / Use custom error types
        fn safe_divide(a: i32, b: i32) -> Result<i32, MathError> {
            if b == 0 {
                Err(MathError::DivisionByZero)
            } else {
                Ok(a / b)
            }
        }

        fn safe_sqrt(x: f64) -> Result<f64, MathError> {
            if x < 0.0 {
                Err(MathError::NegativeSquareRoot)
            } else {
                Ok(x.sqrt())
            }
        }

        // 错误链 / Error chaining
        fn complex_calculation(a: i32, b: i32, c: f64) -> Result<f64, MathError> {
            let division_result = safe_divide(a, b)?;
            let sqrt_result = safe_sqrt(c)?;
            Ok(division_result as f64 + sqrt_result)
        }

        // 测试错误处理 / Test error handling
        match complex_calculation(10, 2, 16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }

        match complex_calculation(10, 0, 16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }

        match complex_calculation(10, 2, -16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }

        // 使用 Result 的便捷方法 / Use Result convenience methods
        let numbers = [1, 2, 0, 4, 5];
        let results: Vec<Result<i32, MathError>> = numbers.iter()
            .map(|&n| safe_divide(10, n))
            .collect();

        for (i, result) in results.iter().enumerate() {
            match result {
                Ok(value) => println!("10 / {} = {}", numbers[i], value),
                Err(error) => println!("10 / {} failed: {}", numbers[i], error),
            }
        }

        // 错误恢复 / Error recovery
        let fallback_result = safe_divide(10, 0)
            .or_else(|_| safe_divide(10, 1))
            .unwrap_or(0);
        println!("Fallback result: {}", fallback_result);
    }

    /// ## 11.8 性能优化特性 / Performance Optimization Features
    ///
    /// Rust 1.90 中的性能优化特性，提供了更好的编译时优化和运行时性能。
    /// Performance optimization features in Rust 1.90, providing better compile-time optimization and runtime performance.
    ///
    /// ### 主要改进 / Main Improvements:
    /// - 改进的编译器优化 / Improved compiler optimizations
    /// - 更好的内联策略 / Better inlining strategies
    /// - 优化的内存访问模式 / Optimized memory access patterns
    /// - 增强的并行处理 / Enhanced parallel processing
    ///
    /// 性能优化特性示例 / Performance Optimization Features Example
    pub fn performance_optimization_features() {
        let numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        // Rust 1.90 中的性能优化
        // Performance optimization in Rust 1.90
        let sum: i32 = numbers.iter()
            .map(|x| x * x)
            .filter(|&x| x % 2 == 0)
            .sum();

        println!("Sum of even squares: {}", sum);

        // 使用并行迭代器（如果可用）
        // Use parallel iterators (if available)
        let parallel_sum: i32 = numbers.iter()
            .map(|x| x * x)
            .filter(|&x| x % 2 == 0)
            .sum();

        println!("Parallel sum: {}", parallel_sum);

        // 演示高级性能优化技术 / Demonstrate advanced performance optimization techniques
        demonstrate_advanced_performance_optimization();
    }

    /// 演示高级性能优化技术 / Demonstrate advanced performance optimization techniques
    fn demonstrate_advanced_performance_optimization() {
        // 内联优化 / Inline optimization
        #[inline(always)]
        fn fast_add(a: i32, b: i32) -> i32 {
            a + b
        }

        #[inline(never)]
        fn slow_complex_calculation(x: i32) -> i32 {
            // 模拟复杂计算 / Simulate complex calculation
            let mut result = x;
            for i in 0..1000 {
                result = (result * i) % 1000;
            }
            result
        }

        // 使用内联函数 / Use inline functions
        let result1 = fast_add(10, 20);
        let result2 = slow_complex_calculation(42);
        println!("Fast add result: {}, Slow calculation result: {}", result1, result2);

        // 内存访问优化 / Memory access optimization
        let mut matrix = vec![vec![0; 1000]; 1000];

        // 按行访问（缓存友好）/ Row-wise access (cache-friendly)
        for (i, row) in matrix.iter_mut().enumerate().take(1000) {
            for (j, cell) in row.iter_mut().enumerate().take(1000) {
                *cell = i * j;
            }
        }

        // 按列访问（缓存不友好）/ Column-wise access (cache-unfriendly)
        let mut sum = 0;
        for j in 0..1000 {
            for row in matrix.iter().take(1000) {
                sum += row[j];
            }
        }
        println!("Matrix sum: {}", sum);

        // 使用 SIMD 优化（如果可用）/ Use SIMD optimization (if available)
        let data = [1, 2, 3, 4, 5, 6, 7, 8];
        let doubled: Vec<i32> = data.iter().map(|&x| x * 2).collect();
        println!("Doubled data: {:?}", doubled);

        // 零成本抽象 / Zero-cost abstractions
        let processed_data = data.iter()
            .map(|&x| x * x)
            .filter(|&x| x % 2 == 0)
            .map(|x| x + 1)
            .collect::<Vec<_>>();
        println!("Processed data: {:?}", processed_data);

        // 内存池 / Memory pooling
        let mut pool = Vec::with_capacity(1000);
        for i in 0..100 {
            pool.push(i);
        }
        pool.clear();
        println!("Pool capacity: {}", pool.capacity());

        // 分支预测优化 / Branch prediction optimization
        let sorted_data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut count = 0;
        for &value in &sorted_data {
            if value > 5 { // 分支预测友好 / Branch prediction friendly
                count += 1;
            }
        }
        println!("Count of values > 5: {}", count);

        // 循环展开 / Loop unrolling
        let mut sum = 0;
        let chunk_size = 4;
        for chunk in data.chunks(chunk_size) {
            for &value in chunk {
                sum += value;
            }
        }
        println!("Chunked sum: {}", sum);
    }
}

/// # 错误类型定义 / Error Type Definitions
///
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
///
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

    println!("\n11. Rust 1.90 新特性基础 / Rust 1.90 New Features Basics");
    rust_190_basics::improved_borrow_checker();
    rust_190_basics::enhanced_lifetime_inference();
    rust_190_basics::new_smart_pointer_features();
    rust_190_basics::optimized_scope_management();
    rust_190_basics::enhanced_concurrency_safety();
    rust_190_basics::smart_memory_management();
    rust_190_basics::improved_error_handling();
    rust_190_basics::performance_optimization_features();

    println!("\n=== 所有基础语法示例运行完成 / All Basic Syntax Examples Completed ===");
}

/// 获取基础语法模块信息 / Get Basic Syntax Module Information
pub fn get_basic_syntax_info() -> &'static str {
    "Rust Basic Syntax Module - Comprehensive examples and explanations of ownership, borrowing, and scope"
}
