//! 各模块完整示例集合
//!
//! 本文件包含所有12个核心模块的完整示例，展示每个模块的核心功能
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// C01 - 所有权与借用完整示例
pub fn ownership_borrow_complete_example() {
    println!("📦 C01 - 所有权与借用完整示例");

    // 所有权转移
    let s1 = String::from("hello");
    let s2 = s1; // s1的所有权转移到s2
    // println!("{}", s1); // 错误：s1不再有效
    println!("  - 所有权转移: {}", s2);

    // 借用
    let s3 = String::from("world");
    let len = calculate_length(&s3); // 借用s3
    println!("  - 借用示例: {} 的长度是 {}", s3, len);

    // 可变借用
    let mut s4 = String::from("hello");
    change_string(&mut s4);
    println!("  - 可变借用: {}", s4);
}

fn calculate_length(s: &String) -> usize {
    s.len()
}

fn change_string(s: &mut String) {
    s.push_str(", world");
}

/// C02 - 类型系统完整示例
pub fn type_system_complete_example() {
    println!("\n🔷 C02 - 类型系统完整示例");

    // 基本类型
    let int_val: i32 = 42;
    let float_val: f64 = 3.14;
    let bool_val: bool = true;
    println!("  - 基本类型: i32={}, f64={}, bool={}", int_val, float_val, bool_val);

    // 复合类型
    let tuple: (i32, f64, bool) = (42, 3.14, true);
    println!("  - 元组: {:?}", tuple);

    let array: [i32; 3] = [1, 2, 3];
    println!("  - 数组: {:?}", array);

    // 自定义类型
    struct Point {
        x: i32,
        y: i32,
    }

    let point = Point { x: 10, y: 20 };
    println!("  - 结构体: Point {{ x: {}, y: {} }}", point.x, point.y);
}

/// C03 - 控制流与函数完整示例
pub fn control_flow_complete_example() {
    println!("\n🔄 C03 - 控制流与函数完整示例");

    // if-else
    let number = 42;
    if number < 50 {
        println!("  - if-else: 数字小于50");
    } else {
        println!("  - if-else: 数字大于等于50");
    }

    // loop
    let mut counter = 0;
    loop {
        counter += 1;
        if counter >= 3 {
            break;
        }
    }
    println!("  - loop: 循环了{}次", counter);

    // while
    let mut count = 0;
    while count < 3 {
        count += 1;
    }
    println!("  - while: 循环了{}次", count);

    // for
    for i in 1..=3 {
        println!("  - for: 迭代 {}", i);
    }

    // 函数
    let result = add_numbers(10, 20);
    println!("  - 函数: add_numbers(10, 20) = {}", result);
}

fn add_numbers(a: i32, b: i32) -> i32 {
    a + b
}

/// C04 - 泛型编程完整示例
pub fn generic_programming_complete_example() {
    println!("\n🔀 C04 - 泛型编程完整示例");

    // 泛型函数
    fn largest<T: PartialOrd + Copy>(list: &[T]) -> T {
        let mut largest = list[0];
        for &item in list.iter() {
            if item > largest {
                largest = item;
            }
        }
        largest
    }

    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    println!("  - 泛型函数: 最大数字是 {}", result);

    // 泛型结构体
    struct Point<T> {
        x: T,
        y: T,
    }

    let integer_point = Point { x: 5, y: 10 };
    let float_point = Point { x: 1.0, y: 4.0 };
    println!("  - 泛型结构体: Point<i32> {{ x: {}, y: {} }}, Point<f64> {{ x: {}, y: {} }}",
             integer_point.x, integer_point.y, float_point.x, float_point.y);
}

/// C05 - 线程与并发完整示例
pub fn threads_concurrency_complete_example() {
    println!("\n🧵 C05 - 线程与并发完整示例");

    // 创建线程
    let handle = thread::spawn(|| {
        for i in 1..=3 {
            println!("  - 线程: 数字 {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });

    handle.join().unwrap();

    // 共享数据
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..3 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("  - 共享数据: 计数器值 = {}", *counter.lock().unwrap());
}

/// C06 - 异步编程完整示例
pub fn async_programming_complete_example() {
    println!("\n⚡ C06 - 异步编程完整示例");

    // 注意：实际异步代码需要tokio或async-std运行时
    println!("  - 异步编程需要运行时支持（如tokio）");
    println!("  - 示例：async fn fetch_data() -> Result<String, Error>");
    println!("  - 示例：使用.await等待异步操作完成");
}

/// C07 - 进程管理完整示例
pub fn process_management_complete_example() {
    println!("\n🔧 C07 - 进程管理完整示例");

    use std::process::Command;

    // 注意：实际进程管理需要根据平台调整
    println!("  - 进程管理需要根据平台实现");
    println!("  - 示例：Command::new(\"ls\").output()");
}

/// C08 - 算法与数据结构完整示例
pub fn algorithms_data_structures_complete_example() {
    println!("\n📊 C08 - 算法与数据结构完整示例");

    // 排序
    let mut numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    numbers.sort();
    println!("  - 排序: {:?}", numbers);

    // 搜索
    let index = numbers.binary_search(&5);
    match index {
        Ok(i) => println!("  - 搜索: 找到5在索引{}", i),
        Err(_) => println!("  - 搜索: 未找到5"),
    }

    // 集合操作
    let vec1 = vec![1, 2, 3];
    let vec2 = vec![3, 4, 5];
    let intersection: Vec<_> = vec1.iter().filter(|&x| vec2.contains(x)).collect();
    println!("  - 集合操作: 交集 = {:?}", intersection);
}

/// C09 - 设计模式完整示例
pub fn design_patterns_complete_example() {
    println!("\n🎨 C09 - 设计模式完整示例");

    // 单例模式（简化版）
    struct Singleton {
        value: i32,
    }

    impl Singleton {
        fn new() -> Self {
            Singleton { value: 42 }
        }

        fn get_value(&self) -> i32 {
            self.value
        }
    }

    let singleton = Singleton::new();
    println!("  - 单例模式: 值 = {}", singleton.get_value());

    // 策略模式（简化版）
    trait Strategy {
        fn execute(&self) -> i32;
    }

    struct AddStrategy;
    impl Strategy for AddStrategy {
        fn execute(&self) -> i32 {
            10 + 20
        }
    }

    let strategy = AddStrategy;
    println!("  - 策略模式: 结果 = {}", strategy.execute());
}

/// C10 - 网络编程完整示例
pub fn network_programming_complete_example() {
    println!("\n🌐 C10 - 网络编程完整示例");

    // 注意：实际网络编程需要tokio或async-std
    println!("  - 网络编程需要异步运行时支持");
    println!("  - 示例：TcpListener::bind(\"127.0.0.1:8080\")");
    println!("  - 示例：TcpStream::connect(\"127.0.0.1:8080\")");
}

/// C11 - 宏系统完整示例
pub fn macro_system_complete_example() {
    println!("\n🔧 C11 - 宏系统完整示例");

    // 声明宏
    macro_rules! say_hello {
        () => {
            println!("  - 声明宏: Hello, World!");
        };
    }

    say_hello!();

    // 带参数的宏
    macro_rules! create_function {
        ($func_name:ident) => {
            fn $func_name() {
                println!("  - 宏生成函数: {}()", stringify!($func_name));
            }
        };
    }

    create_function!(foo);
    foo();
}

/// C12 - WASM完整示例
pub fn wasm_complete_example() {
    println!("\n🌍 C12 - WASM完整示例");

    // 注意：实际WASM需要wasm-bindgen或wasm-pack
    println!("  - WASM需要特殊工具链支持");
    println!("  - 示例：使用#[wasm_bindgen]导出函数");
    println!("  - 示例：在浏览器中调用Rust函数");
}

/// 主函数
fn main() {
    println!("🚀 Rust 各模块完整示例集合");
    println!("==========================\n");

    ownership_borrow_complete_example();
    type_system_complete_example();
    control_flow_complete_example();
    generic_programming_complete_example();
    threads_concurrency_complete_example();
    async_programming_complete_example();
    process_management_complete_example();
    algorithms_data_structures_complete_example();
    design_patterns_complete_example();
    network_programming_complete_example();
    macro_system_complete_example();
    wasm_complete_example();

    println!("\n✅ 所有模块完整示例完成！");
}
