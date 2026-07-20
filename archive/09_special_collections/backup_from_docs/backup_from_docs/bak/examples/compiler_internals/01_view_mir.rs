// 示例：查看MIR的不同场景
// 编译命令: rustc +nightly -Z unpretty=mir examples/compiler_internals/01_view_mir.rs

/// 简单函数 - 查看基本的MIR结构
pub fn simple_add(a: i32, b: i32) -> i32 {
    a + b
}

/// 控制流 - 查看分支的MIR表示
pub fn max_value(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

/// 循环 - 查看循环的MIR CFG
pub fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 1;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}

/// 模式匹配 - 查看match的MIR展开
pub fn classify_number(n: i32) -> &'static str {
    match n {
        0 => "zero",
        1..=10 => "small",
        11..=100 => "medium",
        _ => "large",
    }
}

/// 所有权转移 - 查看move的MIR表示
pub fn take_ownership(s: String) -> usize {
    s.len()
}

/// 借用 - 查看借用的MIR追踪
pub fn borrow_example(s: &str) -> usize {
    s.len()
}

/// 闭包 - 查看闭包的MIR展开
pub fn closure_example() -> impl Fn(i32) -> i32 {
    let x = 10;
    move |y| x + y
}

/// 泛型 - 观察单态化
pub fn generic_function<T: std::fmt::Display>(value: T) {
    println!("{}", value);
}

/// Option处理 - 查看?操作符的展开
pub fn try_operation(opt: Option<i32>) -> Option<i32> {
    let value = opt?;
    Some(value + 1)
}

/// Result处理 - 查看错误处理的MIR
pub fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

fn main() {
    // 这些调用会被优化掉，但有助于理解MIR
    println!("Simple add: {}", simple_add(1, 2));
    println!("Max: {}", max_value(5, 3));
    println!("Sum: {}", sum_to_n(10));
    println!("Classify: {}", classify_number(50));
}

