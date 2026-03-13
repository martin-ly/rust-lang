use c04_generic::{
    advanced_patterns::*,
    basic_syntax::*,
    generic_define::{
        Dog, Point, hashmap_test, largest, longest, print_description, summarize_item,
    },
    practical_examples::*,
    rust_194_features::*,
    trait_bound::{
        clone::*, copy::*, debug::*, default::*, display::*, drop::*, eq::*, from_into::*, hash::*,
        order::*, partial_eq::*, partial_order::*, send::*, sync::*,
    },
};

fn main() {
    println!("=== Rust Generics 1.94 Demo ===\n");

    // 1. 基本泛型定义演示
    println!("1. Basic Generic Definitions");
    println!("================================");
    demonstrate_basic_generics();
    println!();

    // 2. 特征约束演示
    println!("2. Trait Bounds");
    println!("================");
    demonstrate_trait_bounds();
    println!();

    // 3. 基础语法演示
    println!("3. Basic Syntax");
    println!("===============");
    demonstrate_basic_syntax();
    println!();

    // 4. 高级模式演示
    println!("4. Advanced Patterns");
    println!("====================");
    demonstrate_advanced_patterns();
    println!();

    // 5. 实用示例演示
    println!("5. Practical Examples");
    println!("=====================");
    demonstrate_practical_examples();
    println!();

    // 6. Rust 1.94 特性演示
    println!("6. Rust 1.94 Features");
    println!("=====================");
    demonstrate_rust_194_generic_features();
    println!();

    println!("\n🎉 All demos completed!");
}

fn demonstrate_basic_generics() {
    let point = Point { x: 1, y: 2 };
    println!("Point: ({}, {})", point.x, point.y);

    let my_string = String::from("Hello, Rust!");
    summarize_item(my_string);

    let numbers = vec![34, 50, 25, 100, 65];
    let largest_num = largest(&numbers);
    println!("The largest number is {}", largest_num);

    let string1 = String::from("long string");
    let string2 = String::from("short");
    let result = longest(string1.as_str(), string2.as_str());
    println!("The longest string is {}", result);

    let dog = Dog {
        name: String::from("Buddy"),
    };
    print_description(dog);
    hashmap_test();
}

fn demonstrate_trait_bounds() {
    demonstrate_clone();
    demonstrate_copy();
    demonstrate_debug();
    demonstrate_default();
    demonstrate_display();
    demonstrate_eq();
    demonstrate_hash();
    demonstrate_ord();
    demonstrate_partial_eq();
    demonstrate_partial_ord();
    demonstrate_from_into();
    demonstrate_drop();
    demonstrate_send();
    demonstrate_sync();
}
