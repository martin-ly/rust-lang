//! # 示例03: 重复语法
//!
//! 演示宏中的重复模式 $(...)*

use std::collections::HashMap;

/// 打印所有参数
macro_rules! print_all {
    ($($arg:expr),* $(,)?) => {
        $(
            println!("{}", $arg);
        )*
    };
}

/// 创建元组
macro_rules! make_tuple {
    ($($elem:expr),* $(,)?) => {
        ($($elem,)*)
    };
}

/// 创建结构体
macro_rules! struct_builder {
    ($name:ident { $($field:ident: $ty:ty),* $(,)? }) => {
        struct $name {
            $(
                $field: $ty,
            )*
        }

        impl $name {
            fn new($($field: $ty),*) -> Self {
                Self {
                    $($field,)*
                }
            }
        }
    };
}

fn main() {
    println!("=== 重复语法示例 ===\n");

    // 1. 打印多个值
    println!("1. 打印多个值:");
    print_all!("Hello", "World", "from", "Rust", "Macros");
    println!();

    // 2. 创建元组
    println!("2. 创建元组:");
    let tuple = make_tuple!(1, "two", 3.0, true);
    println!("元组: {:?}", tuple);
    println!();

    // 3. 动态创建结构体
    println!("3. 动态创建结构体:");
    struct_builder!(Person {
        name: String,
        age: u32,
        email: String,
    });

    let person = Person::new(
        "Alice".to_string(),
        30,
        "alice@example.com".to_string(),
    );
    println!("Person: {{ name: {}, age: {}, email: {} }}",
        person.name, person.age, person.email);
    println!();

    // 4. 使用hashmap宏
    use c11_macro_system::hashmap;
    println!("4. 创建HashMap:");
    let config: HashMap<&str, i32> = hashmap! {
        "timeout" => 30,
        "retries" => 3,
        "port" => 8080,
    };
    println!("配置: {:?}", config);
    println!();

    println!("=== 示例完成 ===");
}

