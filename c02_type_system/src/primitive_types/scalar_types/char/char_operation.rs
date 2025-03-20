/*
在 Rust 中，`char` 类型用于表示单个 Unicode 字符。
它是一个非常重要的基本数据类型，能够处理各种字符，包括字母、数字、符号和其他 Unicode 字符。
以下是对 `char` 类型的定义、解释、操作和示例的详细说明。
1. `char` 类型的定义
    `char` 是 Rust 中的字符类型，用于表示一个 Unicode 字符。
    它占用 4 个字节（32 位），可以表示任何有效的 Unicode 字符。

2. `char` 类型的特性
**Unicode 支持**：`char` 类型支持所有 Unicode 字符，包括汉字、emoji 等。
**固定大小**：每个 `char` 类型的值占用 4 个字节，确保能够表示所有 Unicode 字符。
**单个字符**：`char` 类型只能存储一个字符，不能存储多个字符或字符串。

3. `char` 类型的操作
**创建字符**：可以使用单引号（`'`）来定义字符。
**字符转换**：可以将字符转换为其对应的 Unicode 值（整数）。
**字符比较**：可以使用比较运算符（如 `==`, `!=`）来比较字符。
可以创建字符、转换为 Unicode 值、进行字符比较和遍历字符串中的字符。
*/
#[allow(unused)]
pub fn char_operation() {
    // 创建字符
    let letter: char = 'R'; // 定义一个字符
    let emoji: char = '😊'; // 定义一个 emoji 字符

    // 打印字符
    println!("Character: {}", letter); // 打印: Character: R
    println!("Emoji: {}", emoji); // 打印: Emoji: 😊

    // 字符转换为 Unicode 值
    let unicode_value = letter as u32; // 将字符转换为 Unicode 值
    println!("Unicode value of '{}' is: {:X}", letter, unicode_value); 
    // 打印: Unicode value of 'R' is: 52
    let emoji_unicode = emoji as u32; // 将 emoji 转换为 Unicode 值
    println!("Unicode value of '{}' is: {:X}", emoji, emoji_unicode); 
    // 打印: Unicode value of '😊' is: 1F60A
    
    // 字符比较
    let another_letter: char = 'R';
    if letter == another_letter {
        println!("Both characters are the same!"); // 打印: Both characters are the same!
    }

    // 遍历字符
    let string = "Hello, 世界!";
    for c in string.chars() {
        println!("Character in string: {}", c); // 打印字符串中的每个字符
    }
}
/*
Character: R
Emoji: 😊
Unicode value of 'R' is: 52
Unicode value of '😊' is: 1F60A
Both characters are the same!
Character in string: H
Character in string: e
Character in string: l
Character in string: l
Character in string: o
Character in string: ,
Character in string:  
Character in string: 世
Character in string: 界
Character in string: !
*/
