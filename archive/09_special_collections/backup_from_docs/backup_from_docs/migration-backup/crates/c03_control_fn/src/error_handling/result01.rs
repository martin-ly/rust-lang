use std::fmt;

#[allow(unused)]
// 自定义错误类型
#[derive(Debug)]
enum MyError {
    DivisionByZero,
    NegativeSqrt,
}

// 实现 fmt::Display trait 以便于打印错误信息
impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::DivisionByZero => write!(f, "错误: 除以零"),
            MyError::NegativeSqrt => write!(f, "错误: 负数的平方根"),
        }
    }
}

// 实现 std::error::Error trait
impl std::error::Error for MyError {}

#[allow(unused)]
// 计算除法
fn divide(numerator: f64, denominator: f64) -> Result<f64, MyError> {
    if denominator == 0.0 {
        Err(MyError::DivisionByZero)
    } else {
        Ok(numerator / denominator)
    }
}

#[allow(unused)]
// 计算平方根
fn sqrt(value: f64) -> Result<f64, MyError> {
    if value < 0.0 {
        Err(MyError::NegativeSqrt)
    } else {
        Ok(value.sqrt())
    }
}

#[allow(unused)]
// 主函数
pub fn test_result01() {
    // 测试除法
    match divide(10.0, 0.0) {
        Ok(result) => println!("结果: {}", result),
        Err(e) => eprintln!("发生错误: {}", e),
    }

    // 测试平方根
    match sqrt(-9.0) {
        Ok(result) => println!("结果: {}", result),
        Err(e) => eprintln!("发生错误: {}", e),
    }

    // 正常的计算示例
    match divide(10.0, 2.0) {
        Ok(result) => {
            println!("10.0 除以 2.0 的结果: {}", result);
            match sqrt(result) {
                Ok(sqrt_result) => println!("平方根: {}", sqrt_result),
                Err(e) => eprintln!("发生错误: {}", e),
            }
        }
        Err(e) => eprintln!("发生错误: {}", e),
    }
}
