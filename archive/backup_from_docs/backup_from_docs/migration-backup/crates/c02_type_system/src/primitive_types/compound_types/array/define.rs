/*
1. 定义
    数组是一个具有固定大小的集合，所有元素的类型相同。数组的大小在编译时确定，并且在运行时不可更改。
2. 核心概念
    固定大小：数组的大小在定义时确定，不能动态改变。
    同质性：数组中的所有元素必须是相同类型。
    内存布局：数组在内存中是连续存储的，这使得访问元素非常高效。
3. 类型表示
    数组类型表示为 [T; N]，其中 T 是元素类型，N 是元素数量。

数组的基本语法如下：

let array_name: [Type; size] = [value1, value2, ..., valueN];

Type 是数组中元素的类型。
size 是数组的大小（元素数量）。
value1, value2, ..., valueN 是数组的初始值。

1. 数组本身遵循 Rust 的移动语义，当数组被赋值给另一个变量时，所有权会被移动。
2. 如果数组的元素类型实现了 Copy trait，则在赋值时会发生复制，而不是移动。
3. 使用 .clone() 方法可以创建数组的深拷贝，从而保留原始数组的所有权。
4. 数组的长度是固定的，不能动态改变。如果需要动态改变数组的长度，可以使用 Vec 类型。

在 Rust 中，数组与 trait 的联系主要体现在以下几个方面：
1. Sized Trait
    定义：
        Sized 是一个特殊的 trait，用于表示类型的大小在编译时是已知的。
        所有固定大小的类型（包括数组）都实现了 Sized trait。
    联系：
        数组的大小是固定的，因此数组类型实现了 Sized trait。
        这意味着你可以在需要 Sized 类型的上下文中使用数组。
2. Copy Trait
    定义：
        Copy 是一个 trait，表示类型的值可以按位复制。
        实现 Copy trait 的类型在赋值时不会发生移动，而是创建一个副本。
    联系：
        数组的元素类型必须实现 Copy trait，整个数组才能实现 Copy trait。
        这意味着如果数组的元素是基本类型（如整数、浮点数等），则数组本身也可以被复制。

*/

#[allow(unused)]
pub fn test_array() -> () {
    // 定义一个包含 5 个整数的数组
    let numbers: [i32; 5] = [1, 2, 3, 4, 5];

    // 访问数组元素
    println!("First element: {}", numbers[0]); // 打印第一个元素: 1
    println!("Second element: {}", numbers[1]); // 打印第二个元素: 2

    // 遍历数组
    for number in &numbers {
        println!("{}", number); // 打印数组中的每个元素
    }
    println!("array: {:?}", numbers); // 打印: array: [1,2,3,4,5]    

    for number in numbers {
        println!("{}", number); // 打印数组中的每个元素
    }
    println!("array: {:?}", numbers); // 打印? 可以打印数组 i32 是copy语义   

    // 定义一个数组并使用相同的值初始化
    let repeated: [i32; 4] = [0; 4]; // 创建一个包含 4 个 0 的数组
    println!("Repeated array: {:?}", repeated); // 打印: Repeated array: [0, 0, 0, 0]
}

#[allow(unused)]
pub fn test_array_str() -> () {
    // 定义一个包含字符串的数组
    let fruits: [&str; 4] = ["Apple", "Banana", "Cherry", "Date"];

    // 访问数组元素
    println!("First fruit: {}", fruits[0]); // 打印第一个水果: Apple
    println!("Second fruit: {}", fruits[1]); // 打印第二个水果: Banana

    // 遍历数组
    println!("Fruits in the array:");
    for fruit in &fruits {
        println!("{}", *fruit); // 打印数组中的每个水果
        //println!("{}", fruit); // 打印数组中的每个水果
        //println!("{}", **fruit); // 打印数组中的每个水果 ？ str在编译期是无法确定大小
    }

    println!("array: {:?}", fruits);
}

#[allow(unused)]
pub fn test_array_string() -> () {
    // 定义一个包含 3 个 String 类型的数组
    let mut fruits: [String; 3] = [
        String::from("Apple"),
        String::from("Banana"),
        String::from("Cherry"),
    ];

    // 访问数组元素
    println!("First fruit: {}", fruits[0]); // 打印第一个水果: Apple

    // 修改数组中的元素
    fruits[1] = String::from("Blueberry");
    println!("Updated second fruit: {}", fruits[1]); // 打印更新后的第二个水果: Blueberry

    // 遍历数组
    println!("Fruits in the array:");
    for fruit in &fruits {
        println!("{}", fruit); // 打印数组中的每个水果
    }
    println!("array: {:?}", fruits); // 打印: array: ["Apple", "Blueberry", "Cherry"]

    // *moving*
    for fruit in fruits {
        println!("{}", fruit); // 打印数组中的每个水果 String 是moving 语义
    }
    //println!("array: {:?}", fruits); // 打印 报错? String 是moving 语义
}

#[allow(unused)]
pub fn test_array_copy() -> () {
    let arr1 = [1, 2, 3]; // 包含 Copy 类型的数组
    let arr2 = arr1; // 这里发生的是复制，而不是移动

    println!("{:?}", arr1); // arr1 仍然有效: [1, 2, 3]
    println!("{:?}", arr2); // 打印 arr2: [1, 2, 3]
}

#[allow(unused)]
pub fn test_array_clone() -> () {
    let arr1 = [1, 2, 3]; // 定义一个数组
    let arr2 = arr1.clone(); // 克隆 arr1，arr2 拥有 arr1 的副本

    println!("{:?}", arr1); // 打印 arr1: [1, 2, 3]
    println!("{:?}", arr2); // 打印 arr2: [1, 2, 3]
}

#[allow(unused)]
pub fn test_array_clone_str() -> () {
    let arr1 = ["Apple", "Banana", "Cherry"];
    let arr2 = arr1.clone();

    println!("{:?}", arr1); // arr1 仍然有效: ["Apple", "Banana", "Cherry"]
    println!("{:?}", arr2); // 打印 arr2: ["Apple", "Banana", "Cherry"]
}

#[allow(unused)]
pub fn test_array_clone_string() -> () {
    let arr1 = [
        String::from("Apple"),
        String::from("Banana"),
        String::from("Cherry"),
    ];

    let arr2 = arr1.clone();

    println!("{:?}", arr1); // arr1 仍然有效: ["Apple", "Banana", "Cherry"]
    println!("{:?}", arr2); // 打印 arr2: ["Apple", "Banana", "Cherry"]
}
