/* 
在 Rust 中，`byte` 通常指的是一个字节（8 位），用于表示原始数据。
Rust 提供了多种与字节相关的类型和操作，最常用的类型是 `u8`，
它是一个无符号的 8 位整数，范围从 0 到 255。
以下是对字节的定义、解释和示例的详细说明。

字节的定义
- **字节（Byte）**：在计算机科学中，字节是数据存储的基本单位，通常由 8 位组成。
在 Rust 中，字节通常用 `u8` 类型表示。

字节的特性
- **无符号整数**：`u8` 是一个无符号整数类型，表示范围从 0 到 255 的整数。
- **原始数据**：字节常用于处理原始数据，如文件 I/O、网络通信、图像处理等。
- **字符编码**：字节也可以用于表示字符的 UTF-8 编码，尤其是在处理字符串时。
*/



#[allow(unused)]
pub fn test_byte_operation() -> () {
    println!("--------------------------------");
    // 定义一个字节
    let byte: u8 = 255; // 最大值

    // 打印字节的值
    println!("Byte value: {}", byte); // 打印: Byte value: 255

    // 字节的基本运算
    let byte1: u8 = 100;
    let byte2: u8 = 50;
    println!("Byte1: {}, Byte2: {}", byte1, byte2);

    let sum = byte1 + byte2; // 结果: 150
    println!("Sum: {}", sum); // 打印: Sum: 150

    // 字节与整数的运算
    let product = byte1 * 2; // 结果: 200
    println!("Product: {}", product); // 打印: Product: 200

    let quotient = byte1 / 2; // 结果: 50
    println!("Quotient: {}", quotient); // 打印: Quotient: 50

    let remainder = byte1 % 3; // 结果: 1
    println!("Remainder: {}", remainder); // 打印: Remainder: 1

    println!("------------byte array--------------------");
    // 字节数组
    let byte_array: [u8; 5] = [1, 2, 3, 4, 5];
    println!("Byte array: {:?}", byte_array); // 打印: Byte array: [1, 2, 3, 4, 5]

    // 遍历字节数组
    for byte in &byte_array {
        println!("Byte: {}", byte); // 打印每个字节
    }

    println!("------------byte char--------------------");
    // 字节与字符的转换
    let char_byte: u8 = 'A' as u8; // 将字符 'A' 转换为字节
    println!("Byte representation of 'A': {}", char_byte); // 打印: Byte representation of 'A': 65
}

/* 
Byte value: 255
Sum: 150
Byte array: [1, 2, 3, 4, 5]
Byte: 1
Byte: 2
Byte: 3
Byte: 4
Byte: 5
Byte representation of 'A': 65
*/
