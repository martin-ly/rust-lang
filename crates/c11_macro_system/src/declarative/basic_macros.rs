//! 基础声明宏示例

/// 简单的打印宏
///
/// # 示例
///
/// ```
/// # use c11_macro_system::say_hello;
/// say_hello!();
/// ```
#[macro_export]
macro_rules! say_hello {
    () => {
        println!("Hello from Rust Macros!");
    };
}

/// 创建函数的宏
///
/// # 示例
///
/// ```
/// # use c11_macro_system::create_function;
/// create_function!(foo);
/// foo(); // 输出: "function foo was called"
/// ```
#[macro_export]
macro_rules! create_function {
    ($func_name:ident) => {
        fn $func_name() {
            println!("function {} was called", stringify!($func_name));
        }
    };
}

/// 计算表达式并打印结果
///
/// # 示例
///
/// ```
/// # use c11_macro_system::calculate;
/// calculate!(1 + 2);
/// ```
#[macro_export]
macro_rules! calculate {
    ($e:expr) => {
        {
            let val = $e;
            println!("{} = {}", stringify!($e), val);
            val
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_calculate_macro() {
        let result = calculate!(2 + 3);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_create_function_macro() {
        create_function!(test_func);
        test_func(); // 应该成功运行
    }
}
