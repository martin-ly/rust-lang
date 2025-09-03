use c04_generic::{
    generic_define::{Point, Dog, summarize_item, largest, longest, print_description, hashmap_test},
    trait_bound::{
        clone::*,
        copy::*,
        debug::*,
        default::*,
        display::*,
        eq::*,
        hash::*,
        order::*,
        partial_eq::*,
        partial_order::*,
        from_into::*,
        drop::*,
        send::*,
        sync::*,
    },
    polymorphism::{
        generic_trait::*,
        trait_object::*,
    },
    associated_type::*,
    natural_transformation::*,

    type_constructor::*,
    type_inference::*,
};

fn main() {
    println!("=== Rust Generics Comprehensive Demo ===\n");
    
    // 1. 基本泛型定义演示
    println!("1. Basic Generic Definitions");
    println!("================================");
    demonstrate_basic_generics();
    println!();
    
    // 2. 特征约束演示
    println!("2. Trait Bounds");
    println!("================");
    
    // Clone/Copy
    println!("--- Clone/Copy ---");
    demonstrate_clone();
    demonstrate_copy();
    println!();
    
    // Debug/Default
    println!("--- Debug/Default ---");
    demonstrate_debug();
    demonstrate_default();
    println!();
    
    // Display/Eq
    println!("--- Display/Eq ---");
    demonstrate_display();
    demonstrate_eq();
    println!();
    
    // Hash/Ord
    println!("--- Hash/Ord ---");
    demonstrate_hash();
    demonstrate_ord();
    println!();
    
    // Partial Eq/Ord
    println!("--- Partial Eq/Ord ---");
    demonstrate_partial_eq();
    demonstrate_partial_ord();
    println!();
    
    // From/Into
    println!("--- From/Into ---");
    demonstrate_from_into();
    println!();
    
    // Drop
    println!("--- Drop ---");
    demonstrate_drop();
    println!();
    
    // Send
    println!("--- Send ---");
    demonstrate_send();
    println!();
    
    // Sync
    println!("--- Sync ---");
    demonstrate_sync();
    println!();
    
    // 3. 多态性演示
    println!("3. Polymorphism");
    println!("================");
    
    // 泛型特征
    println!("--- Generic Traits ---");
    demonstrate_generic_trait();
    println!();
    
    // 特征对象
    println!("--- Trait Objects ---");
    demonstrate_trait_object();
    println!();
    
    // 4. 关联类型演示
    println!("4. Associated Types");
    println!("===================");
    demonstrate_associated_types();
    println!();
    
    // 5. 自然变换演示
    println!("5. Natural Transformations");
    println!("===========================");
    demonstrate_natural_transformation();
    println!();
    
    // 6. 类型构造器演示
    println!("7. Type Constructors");
    println!("=====================");
    demonstrate_type_constructors();
    println!();
    
    // 8. 类型推断演示
    println!("8. Type Inference");
    println!("==================");
    demonstrate_type_inference();
    println!();
    
    // 运行性能基准测试
    println!("\n{}", "=".repeat(50));
    println!("运行性能基准测试...");
    c04_generic::benchmarks::benchmark_generic_functions();
    c04_generic::benchmarks::benchmark_concurrency();
    c04_generic::benchmarks::benchmark_memory_usage();
    
    // 显示项目完成状态总结
    c04_generic::project_status_summary();
    
    println!("\n🎉 所有演示完成！Rust Generics 项目已成功推进完成！");
}

fn demonstrate_basic_generics() {
    // 使用泛型结构体
    let point = Point { x: 1, y: 2 };
    println!("Point: ({}, {})", point.x, point.y);

    // 使用特征
    let my_string = String::from("Hello, Rust!");
    summarize_item(my_string);

    let numbers = vec![34, 50, 25, 100, 65];
    println!("numbers: {:?}", numbers);
    let largest = largest(&numbers);
    println!("The largest number is {}", largest);
    println!("numbers: {:?}", numbers);

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
