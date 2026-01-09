//! 高级作用域管理示例 / Advanced Scope Management Examples
//!
//! 本文件展示了 Rust 中作用域管理的高级用法，包括：
//! - 复杂的作用域嵌套
//! - 生命周期管理
//! - 借用检查器优化
//! - 异步和并发作用域

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 示例1：复杂的作用域嵌套和变量生命周期
fn complex_scope_nesting() {
    println!("=== 复杂作用域嵌套示例 ===");

    let mut global_counter = 0;

    // 主作用域
    {
        println!("进入主作用域");
        let main_var = String::from("main variable");

        // 循环作用域
        for i in 0..3 {
            println!("  进入循环迭代 {}", i);
            let loop_var = format!("loop_var_{}", i);

            // 条件分支作用域
            if i % 2 == 0 {
                println!("    进入偶数分支");
                let branch_var = format!("branch_var_{}", i);

                // 嵌套代码块
                {
                    let nested_var = format!("nested_{}", branch_var);
                    println!("      嵌套变量: {}", nested_var);
                    global_counter += 1;
                } // nested_var 在这里被销毁

                println!("    分支变量: {}", branch_var);
            } else {
                println!("    进入奇数分支");
                let odd_var = format!("odd_var_{}", i);
                println!("    奇数变量: {}", odd_var);
                global_counter += 2;
            } // branch_var 或 odd_var 在这里被销毁

            println!("  循环变量: {}", loop_var);
        } // loop_var 在这里被销毁

        println!("主变量: {}", main_var);
    } // main_var 在这里被销毁

    println!("全局计数器: {}", global_counter);
}

/// 示例2：借用检查器优化模式
fn borrow_checker_optimization() {
    println!("\n=== 借用检查器优化示例 ===");

    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 模式1：使用代码块限制借用范围
    {
        let first_half = &data[0..5];
        let second_half = &data[5..10];

        println!("前半部分: {:?}", first_half);
        println!("后半部分: {:?}", second_half);
    } // 借用在这里结束

    // 现在可以修改 data
    data.push(11);
    println!("添加元素后: {:?}", data);

    // 模式2：使用 split_at_mut 避免借用冲突
    let (left, right) = data.split_at_mut(5);
    left[0] = 100;
    right[0] = 200;

    println!("分割修改后: {:?}", data);

    // 模式3：使用迭代器避免借用
    let sum: i32 = data.iter().sum();
    println!("总和: {}", sum);
}

/// 示例3：生命周期管理
fn lifetime_management() {
    println!("\n=== 生命周期管理示例 ===");

    // 结构体生命周期
    struct DataHolder<'a> {
        data: &'a [i32],
        name: &'a str,
    }

    impl<'a> DataHolder<'a> {
        fn new(data: &'a [i32], name: &'a str) -> Self {
            Self { data, name }
        }

        fn get_data(&self) -> &'a [i32] {
            self.data
        }

        fn get_name(&self) -> &'a str {
            self.name
        }
    }

    let numbers = vec![1, 2, 3, 4, 5];
    let holder = DataHolder::new(&numbers, "numbers");

    println!(
        "数据持有者: {} - {:?}",
        holder.get_name(),
        holder.get_data()
    );

    // 函数生命周期
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() { x } else { y }
    }

    let string1 = "short";
    let string2 = "longer string";
    let result = longest(string1, string2);
    println!("较长的字符串: {}", result);
}

/// 示例4：闭包作用域
fn closure_scope_examples() {
    println!("\n=== 闭包作用域示例 ===");

    let mut counter = 0;

    // 闭包捕获可变借用
    let mut increment = || {
        counter += 1;
        println!("计数器: {}", counter);
    };

    increment();
    increment();
    increment();

    // 闭包捕获不可变借用
    let data = vec![1, 2, 3, 4, 5];
    let print_data = || {
        println!("数据: {:?}", data);
    };

    print_data();

    // 闭包所有权转移
    let data_clone = data.clone();
    let move_closure = move || {
        println!("移动的数据: {:?}", data_clone);
    };

    move_closure();
    // println!("{:?}", data_clone); // 错误：data_clone 已被移动
}

/// 示例5：异步作用域（简化版本，不依赖外部运行时）
fn async_scope_examples() {
    println!("\n=== 异步作用域示例 ===");

    use std::future::Future;
    use std::pin::Pin;

    let data = [1, 2, 3, 4, 5];

    // 异步闭包（简化版本）
    let _async_closure: Pin<Box<dyn Future<Output = ()>>> = Box::pin(async move {
        let sum: i32 = data.iter().sum();
        println!("异步计算总和: {}", sum);
    });

    // 注意：这里需要运行时支持才能实际执行
    println!("异步闭包已创建，需要运行时支持才能执行");

    // 模拟异步任务
    println!("模拟任务1开始");
    std::thread::sleep(Duration::from_millis(100));
    println!("模拟任务1完成");

    println!("模拟任务2开始");
    std::thread::sleep(Duration::from_millis(50));
    println!("模拟任务2完成");
}

/// 示例6：线程安全作用域
fn thread_safe_scope() {
    println!("\n=== 线程安全作用域示例 ===");

    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 创建多个线程
    for i in 0..5 {
        let data_clone = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut data = data_clone.lock().unwrap();
            data.push(i);
            println!("线程 {} 添加了元素 {}", i, i);
        });
        handles.push(handle);
    }

    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }

    // 显示最终结果
    let final_data = shared_data.lock().unwrap();
    println!("最终数据: {:?}", final_data);
}

/// 示例7：RAII 模式和作用域
fn raii_pattern_examples() {
    println!("\n=== RAII 模式示例 ===");

    // 自定义 RAII 类型
    struct Resource {
        name: String,
    }

    impl Resource {
        fn new(name: &str) -> Self {
            println!("创建资源: {}", name);
            Self {
                name: name.to_string(),
            }
        }
    }

    impl Drop for Resource {
        fn drop(&mut self) {
            println!("销毁资源: {}", self.name);
        }
    }

    // 使用 RAII 模式
    {
        let resource1 = Resource::new("resource1");
        let resource2 = Resource::new("resource2");

        println!("使用资源: {} 和 {}", resource1.name, resource2.name);
    } // 资源在这里自动销毁

    println!("作用域结束");
}

/// 示例8：作用域性能优化
fn scope_performance_optimization() {
    println!("\n=== 作用域性能优化示例 ===");

    // 不好的做法：在循环中创建大量临时变量
    let mut bad_sum = 0;
    for i in 0..1000 {
        let temp = i * 2;
        bad_sum += temp;
    }
    println!("不好的做法结果: {}", bad_sum);

    // 好的做法：使用迭代器
    let good_sum: i32 = (0..1000).map(|i| i * 2).sum();
    println!("好的做法结果: {}", good_sum);

    // 使用代码块限制变量作用域
    let result = {
        let temp_data = [1, 2, 3, 4, 5];
        temp_data.iter().sum::<i32>()
    }; // temp_data 在这里被销毁

    println!("优化后的结果: {}", result);
}

/// 示例9：错误处理和作用域
fn error_handling_and_scope() {
    println!("\n=== 错误处理和作用域示例 ===");

    // 使用 Result 和 ? 操作符
    fn process_data() -> Result<i32, Box<dyn std::error::Error>> {
        let data = [1, 2, 3, 4, 5];

        // 在作用域内处理错误
        let result: Result<i32, Box<dyn std::error::Error>> = {
            let sum: i32 = data.iter().sum();
            if sum > 10 {
                Ok(sum)
            } else {
                Err("数据总和太小".into())
            }
        };

        result
    }

    match process_data() {
        Ok(value) => println!("处理成功: {}", value),
        Err(e) => println!("处理失败: {}", e),
    }
}

/// 示例10：作用域可视化
fn scope_visualization() {
    println!("\n=== 作用域可视化示例 ===");

    fn visualize_scope(depth: usize, name: &str) {
        let indent = "  ".repeat(depth);
        println!("{}├─ 进入作用域: {}", indent, name);
    }

    fn visualize_exit(depth: usize, name: &str) {
        let indent = "  ".repeat(depth);
        println!("{}└─ 退出作用域: {}", indent, name);
    }

    visualize_scope(0, "main");

    {
        visualize_scope(1, "block1");
        let x = 42;
        println!("    x = {}", x);

        {
            visualize_scope(2, "block2");
            let y = 100;
            println!("      y = {}", y);
            visualize_exit(2, "block2");
        } // y 被销毁

        println!("    x = {}", x);
        visualize_exit(1, "block1");
    } // x 被销毁

    visualize_exit(0, "main");
}

/// 主函数
fn main() {
    println!("Rust 高级作用域管理示例");
    println!("{}", "=".repeat(50));

    // 运行所有示例
    complex_scope_nesting();
    borrow_checker_optimization();
    lifetime_management();
    closure_scope_examples();
    async_scope_examples();
    thread_safe_scope();
    raii_pattern_examples();
    scope_performance_optimization();
    error_handling_and_scope();
    scope_visualization();

    // 异步示例说明
    println!("\n注意：异步示例已简化为模拟版本，实际使用时需要 tokio 运行时支持");

    println!("\n所有示例执行完成！");
}
