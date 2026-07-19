//! 控制流集成测试
//! 
//! 测试Rust控制流结构

use c03_control_fn::*;

#[test]
fn test_conditional_logic() {
    let x = 10;
    let result = if x > 5 {
        "greater"
    } else {
        "less or equal"
    };
    
    assert_eq!(result, "greater");
}

#[test]
fn test_loop_constructs() {
    // 测试 for 循环
    let mut sum = 0;
    for i in 1..=5 {
        sum += i;
    }
    assert_eq!(sum, 15);
    
    // 测试 while 循环
    let mut count = 0;
    while count < 3 {
        count += 1;
    }
    assert_eq!(count, 3);
}

#[test]
fn test_pattern_matching() {
    let number = 7;
    
    let result = match number {
        1..=5 => "small",
        6..=10 => "medium",
        _ => "large",
    };
    
    assert_eq!(result, "medium");
}

#[test]
fn test_function_parameters() {
    let result = add_numbers(5, 3);
    assert_eq!(result, 8);
    
    let result = multiply_numbers(4, 6);
    assert_eq!(result, 24);
}

#[test]
fn test_closure_usage() {
    let add_one = |x| x + 1;
    assert_eq!(add_one(5), 6);
    
    let multiply = |x, y| x * y;
    assert_eq!(multiply(3, 4), 12);
}

#[test]
fn test_error_handling() {
    let success_result = divide(10, 2);
    assert!(success_result.is_ok());
    assert_eq!(success_result.unwrap(), 5);
    
    let error_result = divide(10, 0);
    assert!(error_result.is_err());
}

#[test]
fn test_iterators() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 测试 map
    let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();
    assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
    
    // 测试 filter
    let evens: Vec<&i32> = numbers.iter().filter(|x| *x % 2 == 0).collect();
    assert_eq!(evens, vec![&2, &4]);
    
    // 测试 fold
    let sum: i32 = numbers.iter().fold(0, |acc, x| acc + x);
    assert_eq!(sum, 15);
}

// 辅助函数
fn add_numbers(a: i32, b: i32) -> i32 {
    a + b
}

fn multiply_numbers(a: i32, b: i32) -> i32 {
    a * b
}

fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}
