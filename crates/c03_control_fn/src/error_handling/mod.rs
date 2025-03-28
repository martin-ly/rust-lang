/*
在Rust中，错误处理是一个重要的概念，主要通过两种方式来实现：
Result和Option类型。

定义和概念

Result：
    Result是一个枚举类型，用于表示操作的成功或失败。
    它有两个变体：
        Ok(T)：表示成功，并包含一个值。
        Err(E)：表示失败，并包含一个错误值。
    语法：Result<T, E>，其中T是成功时的返回类型，E是错误类型。

Option：
    Option也是一个枚举类型，用于表示一个值可能存在或不存在。
    它有两个变体：
        Some(T)：表示存在一个值。
        None：表示没有值。
    语法：Option<T>，其中T是值的类型。
*/


pub mod define;
pub mod result01;