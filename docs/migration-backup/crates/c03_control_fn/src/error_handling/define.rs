/*
Rust 使用 Result 和 Option 类型进行错误处理，这些类型可以被视为单子。
它们提供了一种结构化的方式来处理可能失败的计算，
控制流可以根据这些类型的状态进行分支
*/

#[allow(unused)]
pub fn test_error_handling() -> () {
    let x: i32 = 5;

    let result = Some(x).and_then(|val| val.checked_add(10));

    match result {
        Some(x) => println!("x is {}", x),
        None => println!("overflow"),
    }
}

/*
错误处理（Error Handling）与控制结构（Control Structure）：
组合关系：
    Rust 的错误处理机制（如 Result 和 Option）与控制结构结合使用，
    以便在出现错误时控制程序的执行流。
形式：
    例如，使用 match 处理 Result：
*/

#[allow(unused)]
pub fn test_error_handling_2() -> () {
    let result: Result<i32, &str> = Ok(10);
    match result {
        Ok(value) => println!("Value is: {}", value), // 控制结构
        Err(e) => println!("Error: {}", e),           // 控制结构
    }
}
