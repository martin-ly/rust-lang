//! 控制流与函数模块集成测试套件 / Control Flow and Functions Module Integration Test Suite

/// 测试控制流集成
#[test]
fn test_control_flow_integration() {
    let value = 5;
    let result = if value > 0 {
        "positive"
    } else {
        "non-positive"
    };
    
    assert_eq!(result, "positive");
}

/// 测试函数调用集成
#[test]
fn test_function_call_integration() {
    fn add(a: i32, b: i32) -> i32 {
        a + b
    }
    
    let result = add(3, 4);
    assert_eq!(result, 7);
}

/// 测试循环集成
#[test]
fn test_loop_integration() {
    let mut sum = 0;
    for i in 1..=10 {
        sum += i;
    }
    
    assert_eq!(sum, 55);
}

/// 测试模式匹配集成
#[test]
fn test_pattern_matching_integration() {
    let value = Some(42);
    
    match value {
        Some(x) => assert_eq!(x, 42),
        None => panic!("Expected Some value"),
    }
}

/// 测试错误处理集成
#[test]
fn test_error_handling_integration() {
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }
    
    assert_eq!(divide(10, 2), Ok(5));
    assert!(divide(10, 0).is_err());
}

/// 测试闭包集成
#[test]
fn test_closure_integration() {
    let add_one = |x: i32| x + 1;
    assert_eq!(add_one(5), 6);
    
    let multiply = |x: i32, y: i32| x * y;
    assert_eq!(multiply(3, 4), 12);
}
