/*
在 Rust 中，元组（Tuple）是一种用于将多个不同类型的值组合在一起的数据结构。
元组的大小是固定的，并且可以包含不同类型的元素。
1. 定义
    元组是一个有序的集合，可以包含任意数量的元素，每个元素可以是不同的类型。
    元组的类型由其元素的类型组成，使用小括号 () 来定义。
2. 核心概念
    固定大小：元组的大小在定义时确定，不能动态改变。
    不同类型：元组可以包含不同类型的元素。
    访问元素：可以通过索引访问元组中的元素，索引从 0 开始。
3. 类型表示
    元组类型表示为 (T1, T2, ..., TN)，其中 T1, T2, ..., TN 是元组中元素的类型。

元组的基本语法如下：

let tuple_name: (Type1, Type2, ..., TypeN) = (value1, value2, ..., valueN);

Type1, Type2, ..., TypeN 是元组中元素的类型。
value1, value2, ..., valueN 是元组中元素的值。

1. 元组本身遵循 Rust 的移动语义，当元组被赋值给另一个变量时，所有权会被移动。
2. 如果元组的元素类型实现了 Copy trait，则在赋值时会发生复制，而不是移动。
3. 使用 .clone() 方法可以创建元组的深拷贝，从而保留原始元组的所有权。

元组与 Sized Trait 的联系：
    元组类型没有实现 Sized trait。
    元组是一个聚合类型，它包含多个类型的值。
    元组类型的大小在编译时是未知的，因为它的元素类型可能不同。
    因此，元组类型不能直接用于某些上下文，如函数参数、返回值或存储在数据结构中。
    元组类型的元素类型可以是标量类型，但元组类型本身并不实现 Sized trait。
    但是，元组类型可以包含标量类型作为其元素，并且这些标量类型实现了 Sized trait。

*/

#[allow(unused)]
pub fn test_tuple() -> () {
    // 定义一个元组，包含一个整数、一个浮点数和一个字符串
    let person: (i32, f64, &str) = (30, 5.9, "Alice");

    // 访问元组的元素
    let age = person.0; // 访问第一个元素
    let height = person.1; // 访问第二个元素
    let name = person.2; // 访问第三个元素

    println!("Name: {}, Age: {}, Height: {}", name, age, height);

    // 解构元组
    let (p_age, p_height, p_name) = person;
    println!(
        "Destructured - Name: {}, Age: {}, Height: {}",
        p_name, p_age, p_height
    );
}

#[allow(unused)]
pub fn test_tuple_string() -> () {
    // 定义一个元组，包含一个字符串、一个整数和一个浮点数
    let person: (String, i32, f64) = (String::from("Alice"), 30, 5.9);

    // 访问元组的元素
    let name = &person.0; // 访问第一个元素（字符串）
    let age = person.1; // 访问第二个元素（整数）
    let height = person.2; // 访问第三个元素（浮点数）

    println!("Name: {}, Age: {}, Height: {}", name, age, height);

    // 解构元组
    let (ref p_name, p_age, p_height) = person;
    println!(
        "Destructured - Name: {}, Age: {}, Height: {}",
        p_name, p_age, p_height
    );

    println!("{:?}", person); //不加 ref 就会报错? String 是moving 语义
}

#[allow(unused)]
pub fn test_tuple_copy() -> () {
    let tuple1 = (1, 2.5); // 包含 Copy 类型的元组
    let tuple2 = tuple1; // 这里发生的是复制，而不是移动

    println!("{:?}", tuple1); // tuple1 仍然有效: (1, 2.5)
    println!("{:?}", tuple2); // 打印 tuple2: (1, 2.5)
}

#[allow(unused)]
pub fn test_tuple_clone() -> () {
    let tuple1 = (String::from("Hello"), 42); // 包含 String 类型的元组
    let tuple2 = tuple1.clone(); // 克隆 tuple1，tuple2 拥有 tuple1 的副本

    println!("tuple1: {:?}", tuple1); // 打印 tuple1: ("Hello", 42)
    println!("tuple2: {:?}", tuple2); // 打印 tuple2: ("Hello", 42)
}
