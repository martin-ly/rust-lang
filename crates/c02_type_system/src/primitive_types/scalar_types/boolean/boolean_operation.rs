/*
在 Rust 中，布尔类型（Boolean Type）是用于表示真（true）或假（false）的基本数据类型。
布尔类型在控制流、条件判断和逻辑运算中起着重要作用。
以下是对布尔类型的定义、操作、概念解释和示例的详细说明。
1. 布尔类型的定义
    布尔类型：在 Rust 中，布尔类型用 bool 表示。它只有两个可能的值：true 和 false。
2. 布尔类型的操作
    布尔类型支持以下操作：
        逻辑与（AND）：使用 && 操作符。短路求值。
        逻辑或（OR）：使用 || 操作符。短路求值。
        逻辑非（NOT）：使用 ! 操作符。
        逻辑异或（XOR）：使用 ^ 操作符。
            它的结果为 true 当且仅当两个操作数中有且只有一个为 true。
        同或（XNOR）运算是异或运算的反向操作。组合实现!(a ^ b).
            它的结果为 true 当且仅当两个操作数相同（即都为 true 或都为 false）。
3. 概念解释
    条件判断：布尔类型常用于条件判断，例如在 if 语句和循环中。
    逻辑运算：布尔类型可以与其他布尔值进行逻辑运算，以组合条件。
*/

#[allow(unused)]
pub fn test_boolean_operation() -> () {
    let a: bool = true;
    let b: bool = false;
    println!("--------------------------------");
    println!("a: {}", a);
    println!("b: {}", b);

    // 逻辑与
    let and_result = a && b; // 结果: false
    println!("a && b = {}", and_result); // 打印: a && b = false

    // 逻辑或
    let or_result = a || b; // 结果: true
    println!("a || b = {}", or_result); // 打印: a || b = true

    // 逻辑非
    let not_result = !a; // 结果: false
    println!("!a = {}", not_result); // 打印: !a = false

    // 使用布尔类型进行条件判断
    if a {
        println!("a is true!"); // 打印: a is true!
    } else {
        println!("a is false!");
    }

    // 结合布尔运算进行复杂条件判断
    if a && !b {
        println!("a is true and b is false!"); // 打印: a is true and b is false!
    }

    let xor_result = a ^ b; // 结果: true
    println!("{} ^ {} = {}", a, b, xor_result); // 打印: true ^ false = true

    // 使用逻辑非和异或实现同或
    let xnor_result = !(a ^ b); // 结果: false
    println!("!({} ^ {}) = {}", a, b, xnor_result); // 打印: !(true ^ false) = false
}

