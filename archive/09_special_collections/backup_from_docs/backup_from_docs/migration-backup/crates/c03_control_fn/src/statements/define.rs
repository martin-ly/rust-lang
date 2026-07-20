/*
    语句是执行某种操作的代码片段，但不返回值。
    Rust 中的语句包括变量声明、函数调用等。
    语句可以被视为一种特殊的表达式，它们在执行时改变程序的状态，但不直接产生值。
*/

#[allow(unused)]
pub fn test_statement() {
    // 变量声明语句
    let x = 5;

    // 函数调用语句
    println!("x is {}", x);

    // 循环语句
    for i in 0..10 {
        println!("i is {}", i);
    }

    // 条件语句
    if x > 0 {
        println!("x is positive");
    } else {
        println!("x is negative");
    }
}

/*
表达式（Expression）与语句（Statement）：
组合关系：
    表达式可以作为语句的一部分，语句通常由一个或多个表达式组成。
    语句执行操作但不返回值，而表达式则计算并返回值。
形式：
    在 Rust 中，语句可以包含表达式，
例如：
*/

#[allow(unused)]
pub fn test_statement_2() {
    let x = 5; // 语句，包含表达式
    let y = {
        // 语句，包含块表达式
        let temp = x + 2; // 表达式
        temp * 2 // 表达式
    };

    println!("y is {}", y); // 语句
}
