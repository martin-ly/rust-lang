/*
在Rust中，String类型是一个可变的、动态大小的字符串类型。
它是Rust标准库中最常用的字符串类型之一，主要用于存储和操作文本数据。
以下是String类型的核心概念和解释：
核心概念
1. 动态大小：与固定大小的字符串切片（&str）不同，String可以在运行时动态增长或缩小。
2. 可变性：String是可变的，这意味着你可以在创建后修改它的内容。
3. 拥有权：String类型拥有其内容的所有权，这意味着当String被销毁时，它所占用的内存也会被释放。
4. UTF-8编码：String使用UTF-8编码来存储文本，这使得它能够处理多种语言的字符。

*/

#[allow(unused)]
pub fn string_operation() {
    // 创建一个新的String
    let mut my_string = String::from("Hello");

    // 追加字符串
    my_string.push_str(", world!");

    // 输出字符串
    println!("{}", my_string); // 输出: Hello, world!

    // 获取字符串长度
    let length = my_string.len();
    println!("Length: {}", length); // 输出: Length: 13

    // 清空字符串
    my_string.clear();
    println!("After clear: {}", my_string); // 输出: After clear: 
}
/*
String::from("Hello")用于创建一个新的String实例。
push_str方法用于在现有字符串后追加内容。
len方法返回字符串的字节长度。
clear方法用于清空字符串的内容。
*/

#[allow(unused)]
pub fn string_operation_2() {
    // 创建字符串
    let mut my_string = String::from("Hello");

    // 追加内容
    my_string.push(' ');
    my_string.push_str("world!");

    // 输出字符串
    println!("String after push: {}", my_string); // 输出: Hello world!

    // 插入内容
    my_string.insert(5, ',');
    println!("String after insert: {}", my_string); // 输出: Hello, world!

    // 删除内容
    my_string.remove(5);
    println!("String after remove: {}", my_string); // 输出: Hello world!

    // 替换内容
    let mut new_string = my_string.replace("world", "Rust");
    println!("String after replace: {}", new_string); // 输出: Hello Rust!

    // 获取长度
    let length = new_string.len();
    println!("Length: {}", length); // 输出: Length: 12

    // 切片
    let slice = &new_string[0..5];
    println!("Slice: {}", slice); // 输出: Slice: Hello

    // 清空字符串
    new_string.clear();
    println!("After clear: {}", new_string); // 输出: After clear: 
}
