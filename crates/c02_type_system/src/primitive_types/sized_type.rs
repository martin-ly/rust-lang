/*

Sized trait 是 Rust 中的一个 trait，用于限制类型的大小。

定义：
    在 Rust 中，Sized 是一个特殊的 trait，用于表示类型的大小在编译时是已知的。
    所有具有固定大小的类型（如标量类型、数组、结构体等）都实现了 Sized trait。

特征：
    Sized trait 是 Rust 类型系统的一个核心部分，确保在编译时能够确定类型的大小。
    只有实现了 Sized trait 的类型才能在某些上下文中使用（例如，作为函数参数或返回值）。

标量类型与 Sized Trait 的联系：
    标量类型实现 Sized：
        所有标量类型都实现了 Sized trait，因为它们的大小在编译时是已知的。
        例如，i32、f64、bool 和 char 都是固定大小的类型，因此它们都实现了 Sized trait。
    使用 Sized Trait：
        在 Rust 中，许多函数和数据结构要求其类型实现 Sized trait。
        这意味着你可以安全地使用标量类型作为函数参数、返回值或存储在数据结构中。

标量类型（Scalar Types）
定义：
    标量类型是表示单一值的基本数据类型。
Rust 中的标量类型主要包括：
    整数类型（如 i32, u32 等）
    浮点数类型（如 f32, f64）
    布尔类型（bool）
    字符类型（char）
特征：
    标量类型的大小在编译时是已知的。
    它们通常直接映射到底层硬件的基本数据类型，具有高效的性能。

*/

use std::any::type_name;
use std::fmt::Debug;
use std::mem::size_of_val;

#[allow(unused)]
pub fn print_sized_value<T: Sized + Debug>(value: T, type_name: &str) {
    // 这里 T 必须实现 Sized trait
    println!(
        "sized-type: Size of Value: {:?} bytes,Type: {}",
        size_of_val(&value),
        type_name
    );
    println!("sized-type: Value: {:?}, Type: {}", value, type_name);
    println!("--------------------------------");
}

#[allow(unused)]
pub fn print_unsized_value<T: ?Sized + Debug>(value: &T, type_name: &str) {
    println!(
        "unsized-type: Size of Value: {:?} bytes,Type: {}",
        size_of_val(value),
        type_name
    );
    println!("unsized-type: Value: {:?}, Type: {}", value, type_name);
    println!("--------------------------------");
}

#[allow(unused)]
pub fn test_sized_type() {
    let a: i32 = 1;
    let b: &str = "Hello, world!";
    let c: [i32; 3] = [1, 2, 3];
    let d: (i32, i32) = (1, 2);
    let e: String = String::from("Hello, world!");
    let f: &String = &e;
    let g: &[i32] = &[1, 2, 3];

    println!("--------sized-type------------------------");
    print_sized_value(a, type_name::<i32>());
    print_sized_value(b, type_name::<&str>());
    print_sized_value(c, type_name::<[i32; 3]>());
    print_sized_value(d, type_name::<(i32, i32)>());
    print_sized_value(f, type_name::<&String>());
    print_sized_value(e, type_name::<String>());
    print_sized_value(g, type_name::<&[i32]>());
}

pub fn test_unsized_type() {
    let a: &str = "Hello, world!";
    let b: &[i32] = &[1, 2, 3];
    let c: &String = &String::from("Hello, world!");

    println!("--------unsized-type------------------------");
    print_unsized_value(a, type_name::<&str>());
    print_unsized_value(b, type_name::<&[i32]>());
    print_unsized_value(c, type_name::<&String>());
}
